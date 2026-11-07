#!/usr/bin/env python3
"""Generate the runtime schema from the C headers of the verified source.

    python3 scripts/gen_schema.py --zlib <verified source directory>

Reads the structs, the static tables and the constants of the headers (`zlib.h`, `zutil.h`, `deflate.h`,
`inflate.h`, `inftrees.h`, `trees.h`, `gzguts.h`, `crc32.h`) through clang's JSON AST dump and writes

  ZlibF/Runtime/Schema.lean   records, array/struct reference types, `Statics`, `Heap`, constants
  ZlibF/Runtime/Tables.lean   load and store per struct kind, with their rules
  ZlibF/Runtime/LibcTables.lean   malloc, free and memcpy per struct kind (the C library), with their rules
  docs/runtime-schema.md      one row per struct field: C type, Lean type, reason

The output depends only on the headers and on the explicit configuration below, so running the script
again gives the same files. Nothing in the generated files is written by hand.
Configuration of the default build: x86_64 Linux, LP64, `./configure --static`
(`-D_LARGEFILE64_SOURCE=1`).
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

HEADERS = ["zlib.h", "zutil.h", "inftrees.h", "inflate.h", "deflate.h", "trees.h", "gzguts.h", "crc32.h"]

# macros that trees.c / deflate.c define before the headers are used (needed to parse trees.h)
PRE_DEFINES = ["#define ZLIB_INTERNAL", "#define DIST_CODE_LEN 512"]

# ------------------------------------------------------------------------------------------------------------
# Configuration: decisions that the headers cannot make. Each one is explained in docs/runtime-schema.md.
# ------------------------------------------------------------------------------------------------------------

# C struct -> (Lean name, role, table field of the heap, short name used in constructor names)
#   table:    allocated; one table of the heap holds the records (block number -> record)
#   embedded: only ever a field of another struct; reachable by a reference constructor `in_<owner>_<field>`
#   static:   a constant instance (read-only); reachable by a reference constructor `st_<name>`
#   elem:     element of an array (`ct_data`, `code`); a pointer is a `Ptr` into an array
STRUCTS = [
    # name,            aliases,                Lean name,        role,       table,       short
    ("z_stream",       ["z_stream_s"],         "ZStream",        "table",    "streams",   "stream"),
    ("gz_header",      ["gz_header_s"],        "GzHeader",       "table",    "gzheaders", "gzheader"),
    ("deflate_state",  ["internal_state"],     "DeflateState",   "table",    "dstates",   "dstate"),
    ("inflate_state",  [],                     "InflateState",   "table",    "istates",   "istate"),
    ("gz_state",       [],                     "GzState",        "table",    "gzstates",  "gzstate"),
    ("gzFile_s",       [],                     "GzFile",         "embedded", None,        "gzfile"),
    ("tree_desc",      ["tree_desc_s"],        "TreeDesc",       "embedded", None,        "treedesc"),
    ("static_tree_desc", ["static_tree_desc_s"], "StaticTreeDesc", "static", None,        "sdesc"),
    ("ct_data",        ["ct_data_s"],          "CtData",         "elem",     None,        "ct"),
    ("code",           [],                     "Code",           "elem",     None,        "code"),
]

# `struct internal_state *` (z_stream.state) points to a deflate state or to an inflate state.
OPAQUE = ("internal_state", "StateRef", [("deflate", "deflate_state"), ("inflate", "inflate_state")])

# static objects that are not declared in the headers (they are `local` in trees.c or in inffixed.h, which
# inftrees.c includes): (name, C element type, number of elements or macro name, source file)
EXTRA_STATIC_ARRAYS = [
    ("lenfix", "code", 512, "inffixed.h (included by inftrees.c; copy verbatim)"),
    ("distfix", "code", 32, "inffixed.h (included by inftrees.c; copy verbatim)"),
    ("extra_lbits", "int", "LENGTH_CODES", "trees.c"),
    ("extra_dbits", "int", "D_CODES", "trees.c"),
    ("extra_blbits", "int", "BL_CODES", "trees.c"),
]
# (name, struct, source file)
EXTRA_STATIC_INSTANCES = [
    ("static_l_desc", "static_tree_desc", "trees.c"),
    ("static_d_desc", "static_tree_desc", "trees.c"),
    ("static_bl_desc", "static_tree_desc", "trees.c"),
]

# the enum types of the headers that zlib itself defines (the system headers define others)
ENUM_TYPEDEFS = ["codetype", "inflate_mode"]

# structs whose definition is in a `.c` file (the headers only declare them): C struct -> (source, fields)
EXTRA_STRUCT_FIELDS = {
    "static_tree_desc": ("trees.c", [("static_tree", "const ct_data *"), ("extra_bits", "const intf *"),
                                      ("extra_base", "int"), ("elems", "int"), ("max_length", "int")]),
}

SCALARS = {
    "char": "Int8", "signed char": "Int8", "unsigned char": "UInt8",
    "short": "Int16", "unsigned short": "UInt16",
    "int": "Int32", "unsigned int": "UInt32",
    "long": "Int64", "unsigned long": "UInt64",
    "long long": "Int64", "unsigned long long": "UInt64",
}
# family of arrays by element type: (prefix of the Lean types `<P>Ref`, `<P>Ptr`)
FAMILY = {"UInt8": "B", "UInt16": "W", "UInt32": "U", "UInt64": "Q",
          "Int8": "SB", "Int16": "SH", "Int32": "I", "Int64": "L"}
ALWAYS_FAMILIES = ["UInt8", "UInt16"]  # byte blocks and word blocks exist in every heap

LEAN_RESERVED = set("""have in at from fun let do then else if match with where open end show by this theorem def
instance class structure namespace section variable universe import export mutual calc for try catch finally return
break continue deriving extends forall exists nomatch Type Sort Prop local private protected partial unsafe macro
syntax notation infix infixl infixr prefix postfix attribute abbrev example inductive opaque axiom set_option using
mod skip rfl sorry matches fresh lemma assert universe elab suffices obtain rcases rintro intro intros exact apply""".split())


def esc(name):
    """A Lean identifier for a C name."""
    return "«%s»" % name if name in LEAN_RESERVED or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) else name


def die(msg):
    sys.exit("gen_schema: " + msg)


# ------------------------------------------------------------------------------------------------------------
# clang
# ------------------------------------------------------------------------------------------------------------

def tu_text(zdir):
    return "\n".join(PRE_DEFINES + ['#include "%s"' % h if h != "gzguts.h" else '#undef GZIP\n#include "gzguts.h"'
                                    for h in HEADERS]) + "\n"


def run_clang(zdir):
    with tempfile.TemporaryDirectory() as tmp:
        tu = os.path.join(tmp, "tu.c")
        with open(tu, "w") as f:
            f.write(tu_text(zdir))
        base = ["clang", "-I", zdir, "-D_LARGEFILE64_SOURCE=1"]
        ast = subprocess.run(base + ["-fsyntax-only", "-Xclang", "-ast-dump=json", tu],
                             capture_output=True, text=True)
        if ast.returncode != 0:
            die("clang failed on the translation unit:\n" + ast.stderr[:2000])
        pre = subprocess.run(base + ["-E", "-dD", tu], capture_output=True, text=True)
        if pre.returncode != 0:
            die("clang -E failed:\n" + pre.stderr[:2000])
        return json.loads(ast.stdout), pre.stdout


def zlib_commit(zdir):
    try:
        return subprocess.run(["git", "-C", zdir, "rev-parse", "HEAD"], capture_output=True, text=True,
                              check=True).stdout.strip()
    except Exception:
        return "unknown"


# ------------------------------------------------------------------------------------------------------------
# AST: typedefs, records, enums, static arrays
# ------------------------------------------------------------------------------------------------------------

class Ast:
    def __init__(self, tu):
        self.typedefs = {}      # name -> underlying qualType
        self.records = {}       # tag or typedef name -> RecordDecl
        self.enum_typedefs = {}  # typedef name -> EnumDecl
        self.enums = []          # (enum decl)
        self.statics = []        # (name, qualType) of non-extern arrays
        by_id = {}
        for n in tu["inner"]:
            if n["kind"] == "RecordDecl" and n.get("completeDefinition"):
                by_id[n["id"]] = n
                if n.get("name"):
                    self.records[n["name"]] = n
            if n["kind"] == "EnumDecl":
                by_id[n["id"]] = n
                self.enums.append(n)
        for n in tu["inner"]:
            if n["kind"] == "TypedefDecl":
                self.typedefs[n["name"]] = n["type"]["qualType"]
                for c in n.get("inner", []):
                    tag = c.get("ownedTagDecl")
                    if tag and tag["id"] in by_id:
                        d = by_id[tag["id"]]
                        if d["kind"] == "RecordDecl":
                            self.records.setdefault(n["name"], d)
                        else:
                            self.enum_typedefs[n["name"]] = d
            if n["kind"] == "VarDecl" and n.get("storageClass") != "extern" and "[" in n["type"]["qualType"]:
                self.statics.append((n["name"], n["type"]["qualType"]))


def norm(t):
    t = re.sub(r"\b(const|volatile|restrict|FAR)\b", " ", t)
    return re.sub(r"\s+", " ", t).strip()


class Typer:
    """C type string -> description. Kinds: scalar, enum, fn, ptr, array, struct."""

    def __init__(self, ast, consts):
        self.ast = ast
        self.consts = consts
        self.struct_by_alias = {}
        for (cname, aliases, lean, role, table, short) in STRUCTS:
            for a in [cname] + aliases:
                self.struct_by_alias[a] = cname

    def classify(self, t):
        t = norm(t)
        m = re.fullmatch(r"(.*?)((?:\[[^\]]+\])+)", t)
        if m:
            dims = []
            for d in re.findall(r"\[([^\]]+)\]", m.group(2)):
                dims.append(self.dim(d))
            return ("array", self.classify(m.group(1)), dims)
        if "(*)" in t:
            return ("fn",)
        if t.endswith("*"):
            inner = t[:-1].strip()
            if inner == "struct " + OPAQUE[0]:
                return ("opaqueptr",)
            if inner.endswith("*"):
                return ("ptrptr", self.classify(inner[:-1].strip()))
            return ("ptr", self.classify(inner))
        return self.base(t)

    def dim(self, d):
        if d.isdigit():
            return int(d)
        if d in self.consts:
            return self.consts[d][0]
        die("array size %r is not a constant" % d)

    def base(self, t):
        t = norm(t)
        if t == "void":
            return ("void",)
        if t in SCALARS:
            return ("scalar", SCALARS[t])
        for kw in ("struct ", "union "):
            if t.startswith(kw):
                tag = t[len(kw):].strip()
                if tag in self.struct_by_alias:
                    return ("struct", self.struct_by_alias[tag])
                if tag in self.ast.records:
                    die("struct %s is not in the configuration" % tag)
                die("unknown struct %s" % tag)
        if t.startswith("enum "):
            return self.enum_type(None)
        if t in self.ast.enum_typedefs:
            return self.enum_type(self.ast.enum_typedefs[t])
        if t in self.struct_by_alias and t in self.ast.records:
            return ("struct", self.struct_by_alias[t])
        if t in self.ast.typedefs:
            return self.classify(self.ast.typedefs[t])
        die("cannot resolve the C type %r" % t)

    def enum_type(self, decl):
        neg = False
        if decl is not None:
            for v in enum_values(decl):
                neg |= v < 0
        return ("enum", "Int32" if neg else "UInt32")


def enum_values(decl):
    out, cur = [], -1
    for c in decl.get("inner", []):
        if c["kind"] != "EnumConstantDecl":
            continue
        val = None
        for e in c.get("inner", []):
            if e["kind"] == "ConstantExpr" and "value" in e:
                val = int(e["value"])
        cur = val if val is not None else cur + 1
        out.append(cur)
    return out


# ------------------------------------------------------------------------------------------------------------
# constants: a small evaluator for C integer constant expressions
# ------------------------------------------------------------------------------------------------------------

ITYPES = ["int", "uint", "long", "ulong"]
IBITS = {"int": 32, "uint": 32, "long": 64, "ulong": 64}
ISIGNED = {"int": True, "uint": False, "long": True, "ulong": False}
LEAN_OF = {"int": "Int32", "uint": "UInt32", "long": "Int64", "ulong": "UInt64"}
CAST_TYPES = {"int": "int", "signed": "int", "signed int": "int", "unsigned": "uint", "unsigned int": "uint",
              "long": "long", "signed long": "long", "unsigned long": "ulong", "long long": "long",
              "unsigned long long": "ulong"}


class NotConst(Exception):
    pass


def wrapv(v, t):
    bits = IBITS[t]
    if ISIGNED[t]:
        if not -(1 << (bits - 1)) <= v < (1 << (bits - 1)):
            raise NotConst("signed overflow")
        return v
    return v % (1 << bits)


def conv(a, b):
    """usual arithmetic conversions of two C integer types (LP64)"""
    if a == b:
        return a
    if "ulong" in (a, b):
        return "ulong"
    if "long" in (a, b):
        return "long"  # long represents every unsigned int
    return "uint"


TOKEN = re.compile(r"\s*(0[xX][0-9a-fA-F]+[uUlL]*|\d+[uUlL]*|[A-Za-z_]\w*|<<|>>|<=|>=|==|!=|&&|\|\||'(?:\\.|[^'])'|\"|[-+*/%&|^~!<>?:()])")


class Eval:
    def __init__(self, macros, enumerators, typedefs):
        self.macros, self.enumerators, self.typedefs = macros, enumerators, typedefs
        self.cache = {}
        self.busy = set()

    def macro(self, name):
        if name in self.cache:
            v = self.cache[name]
            if v is None:
                raise NotConst(name)
            return v
        if name in self.busy:
            raise NotConst("cycle " + name)
        self.busy.add(name)
        try:
            v = self.expr(self.macros[name])
        except NotConst:
            self.cache[name] = None
            raise
        finally:
            self.busy.discard(name)
        self.cache[name] = v
        return v

    def expr(self, body):
        toks, pos = [], 0
        body = body.strip()
        if not body:
            raise NotConst("empty")
        while pos < len(body):
            m = TOKEN.match(body, pos)
            if not m:
                raise NotConst("token")
            toks.append(m.group(1))
            pos = m.end()
            while pos < len(body) and body[pos].isspace():
                pos += 1
        self.toks, self.i = toks, 0
        r = self.cond()
        if self.i != len(self.toks):
            raise NotConst("trailing tokens")
        return r

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def take(self, t=None):
        if t is not None and self.peek() != t:
            raise NotConst("expected " + t)
        self.i += 1
        return self.toks[self.i - 1]

    def cond(self):
        c = self.binary(0)
        if self.peek() == "?":
            self.take()
            a = self.cond_save()
            self.take(":")
            b = self.cond_save()
            t = conv(a[1], b[1])
            return (wrapv(a[0] if c[0] != 0 else b[0], t), t)
        return c

    def cond_save(self):
        return self.cond()

    LEVELS = [["||"], ["&&"], ["|"], ["^"], ["&"], ["==", "!="], ["<", ">", "<=", ">="], ["<<", ">>"],
              ["+", "-"], ["*", "/", "%"]]

    def binary(self, lvl):
        if lvl == len(self.LEVELS):
            return self.unary()
        left = self.binary(lvl + 1)
        while self.peek() in self.LEVELS[lvl]:
            op = self.take()
            right = self.binary(lvl + 1)
            left = self.apply(op, left, right)
        return left

    def apply(self, op, a, b):
        (x, tx), (y, ty) = a, b
        if op in ("||", "&&"):
            return (int(bool(x) or bool(y)) if op == "||" else int(bool(x) and bool(y)), "int")
        if op in ("==", "!=", "<", ">", "<=", ">="):
            t = conv(tx, ty)
            x, y = wrapv(x, t), wrapv(y, t)
            return (int({"==": x == y, "!=": x != y, "<": x < y, ">": x > y, "<=": x <= y, ">=": x >= y}[op]), "int")
        if op in ("<<", ">>"):
            if y < 0 or y >= IBITS[tx]:
                raise NotConst("shift")
            return (wrapv(x << y if op == "<<" else x >> y, tx), tx)
        t = conv(tx, ty)
        x, y = wrapv(x, t), wrapv(y, t)
        if op == "+":
            r = x + y
        elif op == "-":
            r = x - y
        elif op == "*":
            r = x * y
        elif op in ("/", "%"):
            if y == 0:
                raise NotConst("division by zero")
            q = abs(x) // abs(y) * (1 if (x < 0) == (y < 0) else -1)
            r = q if op == "/" else x - q * y
        elif op == "&":
            r = x & y
        elif op == "|":
            r = x | y
        else:
            r = x ^ y
        return (wrapv(r, t), t)

    def unary(self):
        t = self.peek()
        if t == "-":
            self.take()
            v, ty = self.unary()
            return (wrapv(-v, ty), ty)
        if t == "+":
            self.take()
            return self.unary()
        if t == "~":
            self.take()
            v, ty = self.unary()
            return (wrapv(~v, ty), ty)
        if t == "!":
            self.take()
            v, ty = self.unary()
            return (int(v == 0), "int")
        if t == "(":
            cast = self.try_cast()
            if cast is not None:
                v, ty = self.unary()
                return ((wrapv(v, cast) if ISIGNED[cast] else v % (1 << IBITS[cast])), cast)
            self.take()
            r = self.cond()
            self.take(")")
            return r
        return self.primary()

    def try_cast(self):
        """at '(': if a type name follows, consume it and the ')' and return the integer type."""
        j, words = self.i + 1, []
        while j < len(self.toks) and self.toks[j] != ")":
            words.append(self.toks[j])
            j += 1
        if j >= len(self.toks) or not words or j + 1 >= len(self.toks):
            return None
        nxt = self.toks[j + 1]
        if not (re.fullmatch(r"\w+", nxt) or nxt in ("(", "-", "~", "!", "+")):
            return None
        names = []
        for w in words:
            if w in ("const", "FAR"):
                continue
            names.append(w)
        text = " ".join(names)
        for _ in range(8):
            if text in CAST_TYPES:
                self.i = j + 1
                return CAST_TYPES[text]
            if text in self.typedefs and len(names) == 1:
                text = norm(self.typedefs[text])
                continue
            return None
        return None

    def primary(self):
        t = self.take()
        if t[0].isdigit():
            return self.literal(t)
        if t[0] == "'":
            body = t[1:-1]
            return (ord(body) if len(body) == 1 else self._esc(body), "int")
        if re.fullmatch(r"[A-Za-z_]\w*", t):
            if t in self.macros:
                saved = (self.toks, self.i)
                try:
                    return self.macro(t)
                finally:
                    self.toks, self.i = saved
            if t in self.enumerators:
                return (self.enumerators[t], "int")
            raise NotConst("unknown identifier " + t)
        raise NotConst("primary " + t)

    @staticmethod
    def _esc(body):
        table = {"\\n": 10, "\\t": 9, "\\0": 0, "\\\\": 92, "\\'": 39}
        if body in table:
            return table[body]
        raise NotConst("char literal")

    @staticmethod
    def literal(t):
        m = re.fullmatch(r"(0[xX][0-9a-fA-F]+|\d+)([uUlL]*)", t)
        digits, suf = m.group(1), m.group(2).lower()
        base10 = not (digits.lower().startswith("0x") or (len(digits) > 1 and digits.startswith("0")))
        v = int(digits, 16) if digits.lower().startswith("0x") else int(digits, 8) if (len(digits) > 1 and digits[0] == "0") else int(digits)
        u, l = "u" in suf, "l" in suf
        if not u and not l:
            order = ["int", "long"] if base10 else ["int", "uint", "long", "ulong"]
        elif u and not l:
            order = ["uint", "ulong"]
        elif l and not u:
            order = ["long"] if base10 else ["long", "ulong"]
        else:
            order = ["ulong"]
        for ty in order:
            if (v < (1 << (IBITS[ty] - 1))) if ISIGNED[ty] else (v < (1 << IBITS[ty])):
                return (v, ty)
        raise NotConst("literal too large")


def read_macros(pre_text, zdir):
    """object-like macros that the zlib headers define (the last definition wins)"""
    zreal = os.path.realpath(zdir)
    cur, macros, order = None, {}, []
    for line in pre_text.splitlines():
        m = re.match(r'# \d+ "([^"]*)"', line)
        if m:
            cur = m.group(1)
            continue
        if cur is None:
            continue
        in_z = os.path.realpath(cur).startswith(zreal + os.sep) if not cur.startswith("<") else False
        m = re.match(r"#define (\w+)(\(?)(.*)$", line)
        if m and in_z:
            if m.group(2) == "(":
                macros.pop(m.group(1), None)
                continue
            macros[m.group(1)] = m.group(3).strip()
            if m.group(1) not in order:
                order.append(m.group(1))
        m = re.match(r"#undef (\w+)", line)
        if m:
            macros.pop(m.group(1), None)
    return macros


MACRO_RENAME_PREFIX = "GZ_"


def skip_reason(name, body, exc):
    """why a macro is not emitted as a constant"""
    if "sizeof" in body:
        return "uses sizeof, which the evaluator does not know"
    if not body.strip():
        return "empty: a feature flag"
    return "not an integer constant expression"


def compute_constants(ast, macros):
    enumerators, edecl = {}, []
    for tname in ENUM_TYPEDEFS:
        if tname not in ast.enum_typedefs:
            die("enum typedef %s not found" % tname)
        d = ast.enum_typedefs[tname]
        vals = enum_values(d)
        names = [c["name"] for c in d.get("inner", []) if c["kind"] == "EnumConstantDecl"]
        neg = any(v < 0 for v in vals)
        for n, v in zip(names, vals):
            enumerators[n] = v
        edecl.append((names, vals, "Int32" if neg else "UInt32"))
    ev = Eval(macros, enumerators, ast.typedefs)
    ints, strings, skipped, renamed = {}, {}, [], []
    for name in sorted(macros):
        body = macros[name]
        if re.fullmatch(r'"(?:[^"\\]|\\.)*"', body):
            strings[name] = body
            continue
        if name in enumerators:
            # the macro and an enumerator share the name (`COPY` of gzguts.h and of inflate.h): the enumerator keeps
            # the name, the macro is emitted as `GZ_<name>`
            new_name = MACRO_RENAME_PREFIX + name
            if new_name in macros or new_name in enumerators:
                die("the macro %s clashes with an enumerator and %s is taken" % (name, new_name))
            try:
                ints[new_name] = ev.macro(name)
                renamed.append((name, new_name))
            except NotConst as e:
                skipped.append((name, "same name as an enumerator, and not a constant (%s)" % e))
            continue
        try:
            ints[name] = ev.macro(name)
        except NotConst as e:
            skipped.append((name, skip_reason(name, body, e)))
    return ints, strings, edecl, skipped, enumerators, renamed


ESCAPES = {"n": 10, "t": 9, "r": 13, "a": 7, "b": 8, "f": 12, "v": 11, "\\": 92, "'": 39, '"': 34, "?": 63}


def _skip_blank(text, i):
    """index after white space, backslash-newlines and comments"""
    n = len(text)
    while i < n:
        if text[i] in " \t\r\n":
            i += 1
        elif text.startswith("\\\n", i):
            i += 2
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            i = n if j < 0 else j + 2
        elif text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            break
    return i


def _one_literal(text, i):
    """the bytes of the string literal that starts at `text[i] == '"'`, and the index after it"""
    n, j, buf = len(text), i + 1, bytearray()
    while j < n and text[j] != '"':
        ch = text[j]
        if ch != "\\":
            buf.extend(ch.encode("utf-8"))
            j += 1
            continue
        nx = text[j + 1]
        if nx in ESCAPES:
            buf.append(ESCAPES[nx])
            j += 2
        elif nx in "01234567":
            k = j + 1
            while k < n and k < j + 4 and text[k] in "01234567":
                k += 1
            buf.append(int(text[j + 1:k], 8) & 255)
            j = k
        elif nx == "x":
            k = j + 2
            while k < n and text[k] in "0123456789abcdefABCDEF":
                k += 1
            buf.append(int(text[j + 2:k], 16) & 255)
            j = k
        elif nx == "\n":
            j += 2
        else:
            die("unknown escape \\%s in a string literal" % nx)
    return bytes(buf), j + 1


def c_string_literals(text):
    """The string literals of one C source text as byte strings. Comments are skipped, adjacent literals are one
    literal, and the strings of the preprocessor lines `#include`, `#error`, `#pragma`, `#line` are skipped."""
    out, i, n = [], 0, len(text)
    while i < n:
        i = _skip_blank(text, i)
        if i >= n:
            break
        c = text[i]
        if c == "#" and (i == 0 or text[:i].rstrip(" \t").endswith("\n") or not text[:i].strip()):
            m = re.match(r"#[ \t]*(\w+)", text[i:])
            if m and m.group(1) in ("include", "error", "pragma", "line", "warning"):
                j = text.find("\n", i)
                i = n if j < 0 else j
                continue
        if c == "'":
            j = i + 1
            while j < n and text[j] != "'":
                j += 2 if text[j] == "\\" else 1
            i = j + 1
        elif c == '"':
            buf, i = _one_literal(text, i)
            while True:
                k = _skip_blank(text, i)
                if k < n and text[k] == '"':
                    more, i = _one_literal(text, k)
                    buf += more
                else:
                    break
            out.append(buf)
        else:
            i += 1
    return out


def lean_string(b):
    """a Lean string literal for ASCII bytes"""
    r = []
    for x in b:
        ch = chr(x)
        if ch == '"':
            r.append('\\"')
        elif ch == "\\":
            r.append("\\\\")
        elif ch == "\n":
            r.append("\\n")
        elif ch == "\t":
            r.append("\\t")
        elif ch == "\r":
            r.append("\\r")
        elif 0x20 <= x < 0x7f:
            r.append(ch)
        elif x < 0x80:
            r.append("\\x%02x" % x)
        else:
            die("a string literal has a non-ASCII byte")
    return '"' + "".join(r) + '"'


def read_string_table(zdir):
    """All string literals of the library sources (the `*.c` and `*.h` files of the top directory of the verified
    source), as a sorted list of byte strings, with the empty string."""
    lits = {b""}
    for fn in sorted(os.listdir(zdir)):
        if fn.endswith((".c", ".h")):
            with open(os.path.join(zdir, fn), encoding="utf-8", errors="replace") as f:
                for b in c_string_literals(f.read()):
                    lits.add(b)
    for b in lits:
        if any(x >= 0x80 for x in b):
            die("a string literal has a non-ASCII byte: %r" % b)
    return sorted(lits)


def read_trees_c(zdir, macros, ast):
    """The three `static_tree_desc` instances of `trees.c` and the declaration of their struct, read from the source
    (they are not in a header). Checks the field list of `EXTRA_STRUCT_FIELDS` against the declaration and returns
    {instance: (static_tree, extra_bits, extra_base, elems, max_length)} with the numbers evaluated."""
    with open(os.path.join(zdir, "trees.c")) as f:
        src = f.read()
    src = re.sub(r"/\*.*?\*/", " ", src, flags=re.S)
    m = re.search(r"struct static_tree_desc_s\s*\{(.*?)\};", src, flags=re.S)
    if not m:
        die("trees.c: the declaration of struct static_tree_desc_s was not found")
    decl = []
    for line in m.group(1).split(";"):
        line = line.strip()
        if not line:
            continue
        mm = re.fullmatch(r"(.*?)(\w+)", line)
        decl.append((mm.group(2), re.sub(r"\s+", " ", mm.group(1).replace("*", " *")).replace(" *", " *").strip()))
    want = [(n, re.sub(r"\s+", " ", t.replace("*", " *")).strip()) for n, t in EXTRA_STRUCT_FIELDS["static_tree_desc"][1]]
    want = [(n, t.replace("intf", "intf")) for n, t in want]
    if [n for n, _ in decl] != [n for n, _ in want] or \
            [t.replace(" ", "") for _, t in decl] != [t.replace(" ", "") for _, t in want]:
        die("trees.c: struct static_tree_desc_s is %r, the configuration says %r" % (decl, want))
    local = dict(macros)
    for mm in re.finditer(r"^[ \t]*#[ \t]*define[ \t]+(\w+)[ \t]+([^\n]+)$", src, flags=re.M):
        local.setdefault(mm.group(1), mm.group(2).strip())
    ev = Eval(local, {}, ast.typedefs)
    out = {}
    for name, _, _ in EXTRA_STATIC_INSTANCES:
        mm = re.search(r"static_tree_desc\s+%s\s*=\s*\{(.*?)\}\s*;" % name, src, flags=re.S)
        if not mm:
            die("trees.c: the instance %s was not found" % name)
        parts = [x.strip() for x in mm.group(1).split(",")]
        if len(parts) != 5:
            die("trees.c: the initializer of %s has %d members" % (name, len(parts)))
        nums = []
        for x in parts[2:]:
            try:
                nums.append(ev.expr(x)[0])
            except NotConst as e:
                die("trees.c: %s: cannot evaluate %r (%s)" % (name, x, e))
        out[name] = (parts[0], parts[1]) + tuple(nums)
    return out


# ------------------------------------------------------------------------------------------------------------
# the model of the schema
# ------------------------------------------------------------------------------------------------------------

class Field:
    def __init__(self, name, ctype, desc, lean, why, junk):
        self.name, self.ctype, self.desc, self.lean, self.why, self.garbage = name, ctype, desc, lean, why, junk
        # junk: ("scalar", T) | ("ptr",) | ("array", n, inner) | ("struct", name) | ("fn",)


class Model:
    def __init__(self, ast, consts):
        self.ast, self.consts = ast, consts
        self.typer = Typer(ast, consts)
        self.struct_info = {s[0]: s for s in STRUCTS}
        self.fields = {}       # struct -> [Field]
        self.families = set(ALWAYS_FAMILIES)
        self.family_elems = {}  # family key (Lean elem type or struct lean name) -> list of ref ctors
        self.embeds = {}        # struct -> [(owner, field)]
        self.statics = []       # (name, kind, lean type, size, source)
        for s in STRUCTS:
            self.embeds[s[0]] = []
        self.ref_ctors = {}     # family key -> [(ctor, kind, detail)] for arrays
        self.struct_ctors = {}  # struct -> [(ctor, kind)]
        self.build()

    # --- element families -------------------------------------------------------------------------------
    def fam_key(self, lean_elem):
        return lean_elem

    def fam_names(self, key):
        """(Ref type, Ptr type) of an element family"""
        if key in FAMILY:
            p = FAMILY[key]
            return p + "Ref", p + "Ptr"
        return key + "Ref", key + "Ptr"  # struct element (CtData -> CtDataRef)

    def add_family(self, key):
        self.families.add(key)
        self.ref_ctors.setdefault(key, [])

    # --- field typing -----------------------------------------------------------------------------------
    def lean_scalar_ptr(self, pointee):
        """pointer to a scalar element: (Lean type, why)"""
        if pointee[0] == "void" or (pointee[0] == "scalar" and pointee[1] in ("UInt8", "Int8")):
            self.add_family("UInt8")
            return "BPtr", "pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor"
        if pointee[0] == "scalar":
            self.add_family(pointee[1])
            return FAMILY[pointee[1]] + "Ptr", "pointer into an array of `%s`: `%sPtr`" % (pointee[1], FAMILY[pointee[1]])
        raise AssertionError

    def field_type(self, owner, name, ctype):
        t = self.typer.classify(ctype)
        return self.describe(owner, name, ctype, t)

    def describe(self, owner, name, ctype, t):
        k = t[0]
        if k == "scalar":
            return t[1], "scalar: LP64 (`char` is signed, `long` is 64 bits)", ("scalar", t[1])
        if k == "enum":
            return t[1], "enum: the enumerators are constants of this type (gcc: `unsigned int` unless negative)", ("scalar", t[1])
        if k == "fn":
            return "FnPtr", "function pointer: null or the name of the function (an allocator other than the default is not modelled)", ("fn",)
        if k == "opaqueptr":
            return ("Option " + OPAQUE[1], "opaque `struct internal_state *`: a deflate state or an inflate state (`%s`); the casts are in `Tables.lean`" % OPAQUE[1], ("ptr",))
        if k == "ptrptr":
            die("%s.%s: pointer to pointer is not modelled" % (owner, name))
        if k == "ptr":
            p = t[1]
            if p[0] in ("void", "scalar"):
                lean, why = self.lean_scalar_ptr(p)
                return lean, why, ("ptr",)
            if p[0] == "struct":
                cname = p[1]
                lean = self.struct_info[cname][2]
                role = self.struct_info[cname][3]
                if role == "elem":
                    self.add_family(lean)
                    return lean + "Ptr", "pointer into an array of `%s`: `%sPtr` (null, or an array and an index)" % (cname, lean), ("ptr",)
                return "Option %sRef" % lean, "pointer to a `%s`: `%sRef` (a table entry, or the struct inside its owner), `none` is null" % (cname, lean), ("ptr",)
            die("%s.%s: pointer to %r" % (owner, name, p))
        if k == "array":
            elem, dims = t[1], t[2]
            if len(dims) != 1:
                die("%s.%s: multi-dimensional array" % (owner, name))
            n = dims[0]
            if elem[0] == "scalar":
                self.add_family(elem[1])
                self.ref_ctors[elem[1]].append((self.array_ctor(owner, name), owner, name, n))
                return "Array " + elem[1], "array inside a struct: an `Array` field, so copying the struct copies it; a pointer to it is a constructor of `%sRef`" % FAMILY[elem[1]], ("array", n, ("scalar", elem[1]))
            if elem[0] == "struct" and self.struct_info[elem[1]][3] == "elem":
                lean = self.struct_info[elem[1]][2]
                self.add_family(lean)
                self.ref_ctors[lean].append((self.array_ctor(owner, name), owner, name, n))
                return "Array " + lean, "array of structs inside a struct: an `Array` of records; a pointer to it is a constructor of `%sRef`" % lean, ("array", n, ("struct", elem[1]))
            die("%s.%s: array of %r" % (owner, name, elem))
        if k == "struct":
            lean = self.struct_info[t[1]][2]
            self.embeds[t[1]].append((owner, name))
            return lean, "struct inside a struct: a nested record (value semantics); its address is the constructor `in_%s_%s` of `%sRef`" % (self.struct_info[owner][5], name, lean), ("struct", t[1])
        die("%s.%s: unsupported type %r" % (owner, name, ctype))

    def array_ctor(self, owner, field):
        return "%s_%s" % (self.struct_info[owner][5], field)

    # --- build ------------------------------------------------------------------------------------------
    def record_fields(self, cname):
        if cname in EXTRA_STRUCT_FIELDS:
            return [(n, t, None) for (n, t) in EXTRA_STRUCT_FIELDS[cname][1]]
        rec = None
        for a in [cname] + self.struct_info[cname][1]:
            if a in self.ast.records:
                rec = self.ast.records[a]
                break
        if rec is None:
            die("struct %s not found in the headers" % cname)
        out, pending_union = [], None
        for c in rec["inner"]:
            if c["kind"] == "RecordDecl":
                if c.get("tagUsed") == "union":
                    pending_union = c
                continue
            if c["kind"] != "FieldDecl":
                continue
            if c.get("isBitfield"):
                die("%s.%s: bit-field" % (cname, c["name"]))
            qt = c["type"]["qualType"]
            if "unnamed" in qt and pending_union is not None:
                out.append((c["name"], "union", pending_union))
                pending_union = None
            else:
                out.append((c["name"], qt, None))
        return out

    def build(self):
        # first pass: fields of every struct (creates the families and embeddings)
        for s in STRUCTS:
            cname = s[0]
            fl = []
            for (fname, qt, union) in self.record_fields(cname):
                if qt == "union":
                    members = [(m["name"], m["type"]["qualType"]) for m in union["inner"] if m["kind"] == "FieldDecl"]
                    leans = set()
                    for (mn, mt) in members:
                        d = self.typer.classify(mt)
                        if d[0] != "scalar":
                            die("%s.%s: union member %s is not a scalar" % (cname, fname, mn))
                        leans.add(d[1])
                    if len(leans) != 1:
                        die("%s.%s: union members of different types are not modelled" % (cname, fname))
                    lean = leans.pop()
                    ctext = "union { %s }" % "; ".join("%s %s" % (mt, mn) for mn, mt in members)
                    fl.append(Field(fname, ctext, None, lean,
                                    "union whose members all have type `%s`: one field (the members are the same bits)" % lean,
                                    ("scalar", lean)))
                else:
                    lean, why, junk = self.field_type(cname, fname, qt)
                    fl.append(Field(fname, qt, None, lean, why, junk))
            self.fields[cname] = fl
        # static arrays declared in the headers
        for (name, qt) in sorted(self.ast.statics):
            t = self.typer.classify(qt)
            if t[0] != "array" or len(t[2]) != 1:
                die("static %s: unsupported type %s" % (name, qt))
            elem = t[1]
            self.add_static_array(name, elem, t[2][0], "header")
        for (name, celem, size, src) in EXTRA_STATIC_ARRAYS:
            n = size if isinstance(size, int) else self.consts[size][0]
            self.add_static_array(name, self.typer.classify(celem), n, src)
        for (name, cs, src) in EXTRA_STATIC_INSTANCES:
            self.statics.append((name, "instance", self.struct_info[cs][2], 1, src, cs))
            self.struct_ctors.setdefault(cs, []).append(("st_" + name, "static"))
        # reference constructors of struct kinds
        for s in STRUCTS:
            cname, role = s[0], s[3]
            if role == "elem":
                continue
            ctors = []
            if role == "table":
                ctors.append(("tab", "table"))
            for (owner, field) in self.embeds[cname]:
                ctors.append(("in_%s_%s" % (self.struct_info[owner][5], field), ("embedded", owner, field)))
            ctors += self.struct_ctors.get(cname, [])
            self.struct_ctors[cname] = ctors
        # families used by pointer fields
        for k in list(self.families):
            self.ref_ctors.setdefault(k, [])

    def add_static_array(self, name, elem, n, src):
        if elem[0] == "scalar":
            key = elem[1]
            lean = elem[1]
        elif elem[0] == "struct" and self.struct_info[elem[1]][3] == "elem":
            key = self.struct_info[elem[1]][2]
            lean = key
        else:
            die("static %s: element type %r" % (name, elem))
        self.add_family(key)
        self.ref_ctors[key].append(("st_" + name.lstrip("_"), "static", name.lstrip("_"), n))
        self.statics.append((name.lstrip("_"), "array", lean, n, src, name))


# ------------------------------------------------------------------------------------------------------------
# Lean emission
# ------------------------------------------------------------------------------------------------------------

def lit(v, lean):
    if lean in ("Int32", "Int64", "Int8", "Int16") and v < 0:
        return "(%d : %s)" % (v, lean)
    return str(v)


def topo(model):
    """records in an order where embedded records come first"""
    order, seen = [], set()

    def visit(c):
        if c in seen:
            return
        seen.add(c)
        for f in model.fields[c]:
            if f.garbage[0] == "struct":
                visit(f.garbage[1])
            if f.garbage[0] == "array" and f.garbage[2][0] == "struct":
                visit(f.garbage[2][1])
        order.append(c)

    for s in STRUCTS:
        visit(s[0])
    return order


def slots(model, junk):
    kind = junk[0]
    if kind in ("scalar", "ptr", "fn"):
        return 1 if kind == "scalar" else 0
    if kind == "struct":
        return sum(slots(model, f.garbage) for f in model.fields[junk[1]])
    if kind == "array":
        return junk[1] * max(1, slots(model, junk[2]))
    return 0


def wf_conditions(model, cname):
    """the conjuncts of the well-formedness of a record of struct `cname`: array lengths, nested records"""
    out, nested = [], []
    for f in model.fields[cname]:
        k = f.garbage
        if k[0] == "array":
            if k[2][0] == "struct" and wf_conditions(model, k[2][1])[0]:
                die("%s.%s: an array of structs that have arrays is not supported" % (cname, f.name))
            out.append("v.%s.size = %d" % (esc(f.name), k[1]))
        elif k[0] == "struct" and wf_conditions(model, k[1])[0]:
            out.append("v.%s.WellFormed" % esc(f.name))
            nested.append(model.struct_info[k[1]][2])
    return out, nested


def emit_wellformed(model, w):
    S = model.struct_info
    w("/-! ## Well-formed records")
    w("")
    w("The array fields of a record are `Array`s of any length. The C declares the length. `K.WellFormed v` says that every")
    w("array field of `v` (and of the records nested in it) has exactly the declared length, so that `Ptr.load` of an")
    w("index inside the array is a read inside the C object. Nothing in the runtime checks it: `K.garbage` and `K.zeroed`")
    w("are well-formed, `Heap.RecordsWellFormed` says that every record of the heap is, and the lemmas")
    w("`Heap.RecordsWellFormed.set_*` and `clear_*` show that storing a well-formed record or freeing one keeps it. A")
    w("theorem about a record must state this as a hypothesis. -/")
    w("")
    w("/-- Every entry of the table `t` satisfies `P`. -/")
    w("def TableWF {K : Type} (P : K → Prop) (t : Tbl (Option K)) : Prop := ∀ i v, t i = some v → P v")
    w("")
    w("theorem TableWF.set {K : Type} {P : K → Prop} {t : Tbl (Option K)} (ht : TableWF P t) (i : Nat) {v : K} (hv : P v) :")
    w("    TableWF P (upd t i (some v)) := by")
    w("  intro j w hw")
    w("  by_cases hj : j = i")
    w("  · subst hj; simp at hw; subst hw; exact hv")
    w("  · rw [upd_ne _ _ _ _ hj] at hw; exact ht j w hw")
    w("")
    w("theorem TableWF.clear {K : Type} {P : K → Prop} {t : Tbl (Option K)} (ht : TableWF P t) (i : Nat) :")
    w("    TableWF P (upd t i none) := by")
    w("  intro j w hw")
    w("  by_cases hj : j = i")
    w("  · subst hj; simp at hw")
    w("  · rw [upd_ne _ _ _ _ hj] at hw; exact ht j w hw")
    w("")
    for cname in topo(model):
        lean = S[cname][2]
        conds, nested = wf_conditions(model, cname)
        w("/-- The array fields of a `%s` have the lengths of the C declaration. -/" % cname)
        w("def %s.WellFormed (v : %s) : Prop := %s" % (lean, lean, " ∧ ".join(conds) if conds else "True"))
        w("")
        simp = ["%s.garbage" % lean, "%s.WellFormed" % lean] + ["%s.garbage_wf" % n for n in nested]
        w("theorem %s.garbage_wf (g : Nat → UInt64) : (%s.garbage g).WellFormed := by" % (lean, lean))
        w("  simp [%s]" % ", ".join(simp))
        w("")
        w("theorem %s.zeroed_wf : %s.zeroed.WellFormed := %s.garbage_wf _" % (lean, lean, lean))
        w("")
    tabs = [s for s in STRUCTS if s[3] == "table"]
    w("/-- Every record in a table of the heap is well-formed. -/")
    w("def Heap.RecordsWellFormed (h : Heap) : Prop :=")
    w("  " + " ∧ ".join("TableWF %s.WellFormed h.%s" % (t[2], t[4]) for t in tabs))
    w("")
    w("theorem Heap.empty_recordsWellFormed : Heap.empty.RecordsWellFormed := by")
    w("  refine ⟨" + ", ".join("fun _ _ hv => by simp [Heap.empty] at hv" for _ in tabs) + "⟩")
    w("")
    names = ["t%d" % i for i in range(len(tabs))]
    for k, t in enumerate(tabs):
        for kind in ("set", "clear"):
            if kind == "set":
                w("theorem Heap.RecordsWellFormed.set_%s {h : Heap} (hw : h.RecordsWellFormed) (i : Nat) {v : %s}" % (t[4], t[2]))
                w("    (hv : v.WellFormed) : ({ h with %s := upd h.%s i (some v) } : Heap).RecordsWellFormed := by" % (t[4], t[4]))
                new = ["%s.set i hv" % n if j == k else n for j, n in enumerate(names)]
            else:
                w("theorem Heap.RecordsWellFormed.clear_%s {h : Heap} (hw : h.RecordsWellFormed) (i : Nat) :" % t[4])
                w("    ({ h with %s := upd h.%s i none } : Heap).RecordsWellFormed := by" % (t[4], t[4]))
                new = ["%s.clear i" % n if j == k else n for j, n in enumerate(names)]
            w("  unfold Heap.RecordsWellFormed at hw ⊢")
            w("  obtain ⟨%s⟩ := hw" % ", ".join(names))
            w("  exact ⟨%s⟩" % ", ".join("(%s)" % x for x in new))
            w("")
    # statics
    conds = []
    for (name, kind, lean, size, src, cname) in model.statics:
        if kind == "array":
            conds.append("v.%s.size = %d" % (esc(name), size))
    w("/-- The static tables have the lengths of the C declaration. Their content is a separate obligation of the")
    w("translation that fixes them (see `docs/runtime-schema.md`). -/")
    w("def Statics.WellFormed (v : Statics) : Prop := " + " ∧ ".join(conds))
    w("")
    w("/-- The records and the static tables of the heap are well-formed. -/")
    w("def Heap.WellFormed (h : Heap) : Prop := h.RecordsWellFormed ∧ h.static.WellFormed")
    w("")


def emit_schema(model, commit, consts):
    ints, strings, edecl, skipped, enumerators, renamed = consts
    L = []
    w = L.append
    S = model.struct_info
    w("import ZlibF.Runtime.Space")
    w("")
    w("/-!")
    w("# Runtime schema (GENERATED, do not edit)")
    w("")
    w("Generated by `scripts/gen_schema.py` from the C headers of the verified source (zlib commit `%s`)." % commit)
    w("Default build: x86_64 Linux, LP64. The decisions are explained in `docs/runtime-schema.md`.")
    w("")
    w("Contents: the constants of the headers, the reference types (where an array or a struct lives), the record of")
    w("every struct with all its fields in declaration order, the static tables, and the heap with one table per kind")
    w("of object. Nothing here is a computation on the heap; the primitives are in the other files of `Runtime/`.")
    w("-/")
    w("")
    w("namespace C")
    w("")
    w("/-! ## Constants of the headers (object-like macros that evaluate to an integer or a string) -/")
    w("")
    new_names = dict((n, o) for o, n in renamed)
    for name in sorted(ints):
        v, t = ints[name]
        if name in new_names:
            w("/-- The macro `%s` of the headers (`%s = %d`). The name `%s` itself is the enumerator of `inflate.h` below. -/"
              % (new_names[name], new_names[name], v, new_names[name]))
        w("def %s : %s := %s" % (esc(name), LEAN_OF[t], lit(v, LEAN_OF[t])))
    for name in sorted(strings):
        w("def %s : String := %s" % (esc(name), strings[name]))
    w("")
    w("/-! ## Enumerators")
    w("")
    w("In C an enumeration constant has type `int`. The object of enum type (`inflate_state.mode`, the `type` argument of")
    w("`inflate_table`) is stored as `unsigned int` by gcc, so the plain name `X` is a `UInt32`: it is right for a comparison")
    w("with such an object (the `int` constant is converted to `unsigned int`). Where the constant meets an `int`")
    w("(`x < HEAD` with `int x`, `-CODES`, arithmetic), use `X_i`, which is the `Int32` constant. -/")
    w("")
    for (names, vals, lean) in edecl:
        for n, v in zip(names, vals):
            w("def %s : %s := %s" % (esc(n), lean, lit(v, lean)))
        for n, v in zip(names, vals):
            w("/-- The enumeration constant `%s` with its C type `int`. -/" % n)
            w("def %s : Int32 := %s" % (esc(n + "_i"), lit(v, "Int32")))
    w("")
    w("/-! ## String literals")
    w("")
    w("A string literal of C is a static array of bytes: read-only, alive for the whole run, never freed, and the same")
    w("object every time the literal is evaluated. `strTable` lists every string literal of the library sources (the")
    w("`*.c` and `*.h` files of the top directory of the verified source, comments excluded, adjacent literals joined,")
    w("plus the empty string), sorted. The literal number `i` is the array `strTable[i]` followed by a NUL byte, and")
    w("`BRef.str i` is where it lives. It is not a block of the heap: it is not in any table, not in `Heap.live`, not")
    w("touched by `nextBlk`, and the same in every heap. `strLitRef` (in `Libc.lean`) is the pointer to a literal. -/")
    w("")
    w("/-- The string literals of the library sources, sorted (%d of them). Bytes are ASCII. -/" % len(model.strs))
    w("def strTable : Array String := #[")
    for i, b in enumerate(model.strs):
        w("  %s%s" % (lean_string(b), "," if i + 1 < len(model.strs) else ""))
    w("]")
    w("")
    w("/-- The bytes of a string literal in memory: its text and the terminating NUL. -/")
    w("def strBytes (s : String) : Array UInt8 := s.toUTF8.data.push 0")
    w("")
    w("/-! ## Where an array or a struct lives (reference types) -/")
    w("")
    # array families
    for key in sorted(model.families, key=lambda k: (k not in FAMILY, k)):
        ref, ptr = model.fam_names(key)
        ctors = []
        if key == "UInt8":
            ctors.append("  /-- a byte block of the heap (table `bytes`) -/\n  | blk (b : Nat)")
            ctors.append("  /-- the string literal number `i` of `strTable` (read-only, never freed, not a block of the heap) -/\n  | str (i : Nat)")
        if key == "UInt16":
            ctors.append("  /-- a block of 16-bit words of the heap (table `words`) -/\n  | blk (b : Nat)")
        for (ctor, *rest) in model.ref_ctors.get(key, []):
            if rest[0] == "static":
                ctors.append("  /-- the static table `%s` (read-only) -/\n  | %s" % (rest[1], ctor))
            else:
                owner, field = rest[0], rest[1]
                ctors.append("  /-- the array `%s` inside the %s with this block number -/\n  | %s (id : Nat)" % (field, S[owner][2], ctor))
        elem = key if key in FAMILY else key
        w("/-- Where an array of `%s` lives. -/" % elem)
        w("inductive %s where" % ref)
        for c in ctors:
            w(c)
        w("  deriving DecidableEq, Inhabited")
        w("")
        w("/-- A pointer into an array of `%s`: null, or an array and an index. -/" % elem)
        w("abbrev %s := Ptr %s" % (ptr, ref))
        w("")
        if key == "UInt8":
            w("/-- Identities whose byte-array origin has symbolic low address bits. Raw blocks retain their aligned origin. -/")
            w("inductive ByteBaseRef where")
            for c in ctors[1:]:
                w(c)
            w("  deriving DecidableEq, Inhabited")
            w("")
    # struct kinds
    for s in STRUCTS:
        cname, aliases, lean, role, table, short = s
        if role == "elem":
            continue
        w("/-- Where a `%s` lives. -/" % cname)
        w("inductive %sRef where" % lean)
        for (ctor, kind) in model.struct_ctors[cname]:
            if kind == "table":
                w("  /-- entry `id` of the table `%s` -/\n  | tab (id : Nat)" % table)
            elif kind == "static":
                w("  /-- the static instance `%s` (read-only) -/\n  | %s" % (ctor[3:], ctor))
            else:
                w("  /-- the field `%s` of the %s with this block number -/\n  | %s (id : Nat)" % (kind[2], S[kind[1]][2], ctor))
        w("  deriving DecidableEq, Inhabited")
        w("")
        w("abbrev %sPtr := Option %sRef" % (lean, lean))
        w("")
    w("/-- `struct internal_state *`: a deflate state or an inflate state. -/")
    w("inductive %s where" % OPAQUE[1])
    for (ctor, target) in OPAQUE[2]:
        w("  | %s (id : Nat)" % ctor)
    w("  deriving DecidableEq, Inhabited")
    w("")
    w("/-! ## Records (all fields, in declaration order) -/")
    w("")
    for cname in topo(model):
        lean = S[cname][2]
        w("/-- `struct %s`. -/" % cname)
        w("structure %s where" % lean)
        for f in model.fields[cname]:
            w("  /-- `%s` -/" % f.ctype.replace("-/", "- /"))
            w("  %s : %s" % (esc(f.name), f.lean))
        w("  deriving Inhabited")
        w("")
    w("/-! ## Static objects -/")
    w("")
    w("/-- The static tables and instances. Read-only: no primitive stores into them. Their contents are")
    w("fixed by the translation of the file that defines them (see `docs/runtime-schema.md`). -/")
    w("structure Statics where")
    for (name, kind, lean, size, src, cname) in model.statics:
        if kind == "array":
            w("  /-- `%s`, %d elements, from %s -/" % (cname, size, src))
            w("  %s : Array %s := #[]" % (esc(name), lean))
        else:
            w("  /-- the instance `%s` of `struct %s`, from %s -/" % (name, src and cname, src))
            w("  %s : %s := default" % (esc(name), lean))
    w("  deriving Inhabited")
    w("")
    w("/-! ## The heap -/")
    w("")
    w("/-- The heap: one table per kind of object. A table maps a block number to the object, or to `none` when the")
    w("block is free or was never allocated. Block numbers are never reused. -/")
    w("structure Heap where")
    w("  /-- byte blocks (`unsigned char` arrays: buffers, windows, strings) -/")
    w("  bytes : Tbl (Option (Array UInt8))")
    w("  /-- blocks of 16-bit words (`head`, `prev`) -/")
    w("  words : Tbl (Option (Array UInt16))")
    w("  /-- the byte blocks that are read-only (string literals, `const` buffers) -/")
    w("  ro : Tbl Bool")
    for s in STRUCTS:
        if s[3] == "table":
            w("  /-- the table of `struct %s` -/" % s[0])
            w("  %s : Tbl (Option %s)" % (s[4], s[2]))
    w("  /-- the static tables -/")
    w("  static : Statics")
    w("  /-- the next unused block number -/")
    w("  nextBlk : Nat")
    w("  /-- the number of allocation calls so far -/")
    w("  nalloc : Nat")
    w("  /-- the failure oracle: allocation call number `n` succeeds iff `allocOk n` -/")
    w("  allocOk : Nat → Bool")
    w("  /-- the content of fresh memory: position `i` of the memory returned by allocation call number `n` -/")
    w("  garbage : Nat → Nat → UInt64")
    w("  /-- low three origin-address bits for static and embedded byte arrays; read-only metadata -/")
    w("  byteBase : ByteBaseRef → Fin 8")
    w("")
    w("/-- The heap with nothing allocated. -/")
    w("def Heap.empty : Heap where")
    w("  bytes := Tbl.empty")
    w("  words := Tbl.empty")
    w("  ro := Tbl.empty")
    for s in STRUCTS:
        if s[3] == "table":
            w("  %s := Tbl.empty" % s[4])
    w("  static := default")
    w("  nextBlk := 0")
    w("  nalloc := 0")
    w("  allocOk := fun _ => true")
    w("  garbage := fun _ _ => 0")
    w("  byteBase := fun _ => 0")
    w("")
    w("instance : Inhabited Heap := ⟨Heap.empty⟩")
    w("")
    # live / ownership
    tables = [("bytes", "bytes"), ("words", "words")] + [(s[4], s[4]) for s in STRUCTS if s[3] == "table"]
    w("/-- The block number `b` is in use: some table holds an object under it. -/")
    w("def Heap.live (h : Heap) (b : Nat) : Prop :=")
    w("  " + " ∨ ".join("h.%s b ≠ none" % t for t, _ in tables))
    w("")
    w("/-- Every block number from `nextBlk` on is unused. -/")
    w("def Fresh (h : Heap) : Prop := ∀ b, h.nextBlk ≤ b → ¬ h.live b")
    w("")
    w("/-- The heap with nothing allocated is `Fresh`. -/")
    w("theorem Heap.empty_fresh : Fresh Heap.empty := by")
    w("  intro b _ hl")
    w("  simp [Heap.live, Heap.empty] at hl")
    w("")
    w("/-- The decidable form of `Heap.live`: some table holds an object under the block number `b`. Every allocation")
    w("primitive tests it for the number it is about to use and faults if it is set, so an allocation never overwrites a")
    w("live object. -/")
    w("def Heap.slotUsed (h : Heap) (b : Nat) : Bool :=")
    w("  " + " || ".join("(h.%s b).isSome" % t for t, _ in tables))
    w("")
    w("theorem Heap.slotUsed_eq_false {h : Heap} {b : Nat} : h.slotUsed b = false ↔ ¬ h.live b := by")
    w("  simp [Heap.slotUsed, Heap.live, and_assoc]")
    w("")
    w("/-- In a `Fresh` heap the number the next allocation takes is unused. -/")
    w("theorem Fresh.slotUsed_next {h : Heap} (hF : Fresh h) : h.slotUsed h.nextBlk = false :=")
    w("  Heap.slotUsed_eq_false.2 (hF h.nextBlk (Nat.le_refl _))")
    w("")
    w("/-- Discharges the hypothesis `h.slotUsed h.nextBlk = false` of the allocation rules (`allocB_some`, ...) from a")
    w("hypothesis of the context: itself, or `Fresh h`. -/")
    w("macro \"fresh_slot\" : tactic => `(tactic| first | assumption | exact Fresh.slotUsed_next ‹_›)")
    w("")
    w("/-- The live blocks are exactly those of `S`: the ownership statement, and with it the absence of leaks. -/")
    w("def Heap.Owns (h : Heap) (S : Nat → Prop) : Prop := ∀ b, h.live b ↔ S b")
    w("")
    w("theorem Heap.not_live {h : Heap} {b : Nat} :")
    w("    ¬ h.live b ↔ (" + " ∧ ".join("h.%s b = none" % t for t, _ in tables) + ") := by")
    w("  simp [Heap.live]")
    w("")
    w("/-- A heap whose tables agree with those of a `Fresh` heap from its own `nextBlk` on, and whose `nextBlk` is not")
    w("smaller, is `Fresh` too. -/")
    w("theorem Fresh.mono {h h' : Heap} (hF : Fresh h) (hnb : h.nextBlk ≤ h'.nextBlk)")
    w("    (ht : ∀ x, h'.nextBlk ≤ x → (" + " ∧ ".join("h'.%s x = h.%s x" % (t, t) for t, _ in tables) + ")) : Fresh h' := by")
    w("  intro x hx hl")
    w("  obtain ⟨" + ", ".join("e%d" % i for i in range(len(tables))) + "⟩ := ht x hx")
    w("  apply hF x (Nat.le_trans hnb hx)")
    w("  unfold Heap.live at hl ⊢")
    w("  rw [" + ", ".join("e%d" % i for i in range(len(tables))) + "] at hl")
    w("  exact hl")
    w("")
    w("/-- A live block number is below `nextBlk`. -/")
    w("theorem Fresh.lt {h : Heap} (hF : Fresh h) {b : Nat} (hl : h.live b) : b < h.nextBlk := by")
    w("  rcases Nat.lt_or_ge b h.nextBlk with hb | hb")
    w("  · exact hb")
    w("  · exact absurd hl (hF b hb)")
    w("")
    w("theorem Fresh.bytes {h : Heap} (hF : Fresh h) {b : Nat} (hb : h.nextBlk ≤ b) : h.bytes b = none := by")
    w("  cases hn : h.bytes b with")
    w("  | none => rfl")
    w("  | some a => exact absurd (Or.inl (by rw [hn]; simp)) (hF b hb)")
    w("")
    # junk
    w("/-! ## Fresh memory of every record (`ZALLOC` does not initialise)")
    w("")
    w("Integers are arbitrary (the values `g i`). Pointers are NULL: this is a documented gap, not C: a pointer read from")
    w("uninitialised memory is indeterminate in C, and here it is a valid null (see `docs/trusted-base.md`, item 2).")
    w("`K.zeroed` is the same record with every integer 0: the content after `memset(p, 0, sizeof *p)`, where NULL")
    w("is the right value of every pointer. -/")
    w("")
    base = 0
    for cname in topo(model):
        lean = S[cname][2]
        w("/-- A record whose integer fields are the arbitrary values `g 0`, `g 1`, ...; pointers are null. -/")
        w("def %s.garbage (g : Nat → UInt64) : %s where" % (lean, lean))
        off = 0
        for f in model.fields[cname]:
            k = f.garbage
            if k[0] == "scalar":
                w("  %s := Junk.of (g %d)" % (esc(f.name), off))
                off += 1
            elif k[0] in ("ptr", "fn"):
                w("  %s := default" % esc(f.name))
            elif k[0] == "struct":
                n = slots(model, k)
                w("  %s := %s.garbage (fun i => g (%d + i))" % (esc(f.name), S[k[1]][2], off))
                off += n
            elif k[0] == "array":
                inner = k[2]
                if inner[0] == "scalar":
                    w("  %s := Array.ofFn (n := %d) fun i => Junk.of (g (%d + i.val))" % (esc(f.name), k[1], off))
                    off += k[1]
                else:
                    st = max(1, slots(model, inner))
                    w("  %s := Array.ofFn (n := %d) fun i => %s.garbage (fun j => g (%d + %d * i.val + j))" % (
                        esc(f.name), k[1], S[inner[1]][2], off, st))
                    off += k[1] * st
        w("")
        w("/-- The record after `memset(p, 0, sizeof *p)` (`zmemzero`): every integer 0, every pointer NULL. -/")
        w("def %s.zeroed : %s := %s.garbage (fun _ => 0)" % (lean, lean, lean))
        w("")
    # well-formedness
    emit_wellformed(model, w)
    # instances
    w("/-! ## Reading and writing arrays and structs through a reference -/")
    w("")
    for key in sorted(model.families, key=lambda k: (k not in FAMILY, k)):
        ref, ptr = model.fam_names(key)
        # (constructor, variable, get, put, ro, modify, proof of modify_eq)
        ctors = []
        if key == "UInt8":
            ctors.append(("blk", "b", "h.bytes b", "{ h with bytes := upd h.bytes b (some a) }", "h.ro b",
                          "{ h with bytes := h.bytes.modify b (Option.map f) }",
                          ["rw [Tbl.modify_opt _ _ _ _ hg]"]))
            ctors.append(("str", "i", "(strTable[i]?).map strBytes", "h", "true", "h", ["try rfl"]))
        if key == "UInt16":
            ctors.append(("blk", "b", "h.words b", "{ h with words := upd h.words b (some a) }", "false",
                          "{ h with words := h.words.modify b (Option.map f) }",
                          ["rw [Tbl.modify_opt _ _ _ _ hg]"]))
        for (ctor, *rest) in model.ref_ctors.get(key, []):
            if rest[0] == "static":
                ctors.append((ctor, None, "some h.static.%s" % esc(rest[1]), "h", "true", "h", ["try rfl"]))
            else:
                owner, field = rest[0], rest[1]
                tbl = S[owner][4]
                fld = esc(field)
                ctors.append((ctor, "id", "(h.%s id).map (·.%s)" % (tbl, fld),
                              "(match h.%s id with | some s => { h with %s := upd h.%s id (some { s with %s := a }) } | none => h)" % (tbl, tbl, tbl, fld),
                              "false",
                              "{ h with %s := h.%s.modify id (Option.map (fun s => let l := s.%s; let s := { s with %s := #[] }; { s with %s := f l })) }" % (tbl, tbl, fld, fld, fld),
                              ["cases hs : h.%s id with" % tbl,
                               "| none => simp [hs] at hg",
                               "| some s =>",
                               "  have ha : s.%s = a := by simpa [hs] using hg" % fld,
                               "  subst ha",
                               "  have hm := Tbl.modify_opt h.%s id (fun s => { s with %s := f s.%s }) s hs" % (tbl, fld, fld),
                               "  simp only [hs]",
                               "  exact congrArg (fun t => ({ h with %s := t } : Heap)) hm" % tbl]))

        def used(text, name):
            return re.search(r"(?<![\w.])%s(?![\w])" % re.escape(name), text) is not None

        w("instance : Space Heap %s %s where" % (ref, key))
        for field, idx, aname in (("get", 2, False), ("put", 3, True), ("ro", 4, False), ("modify", 5, False)):
            bodies = " ".join(c[idx] for c in ctors)
            hh = "h" if used(bodies, "h") or "h." in bodies else "_"
            aa = ("a" if used(bodies, "a") else "_") if aname else None
            ff = ("f" if used(bodies, "f") else "_") if field == "modify" else None
            w("  %s %s r%s%s := match r with" % (field, hh, (" " + aa) if aa else "", (" " + ff) if ff else ""))
            for c in ctors:
                v = c[1]
                rv = (v if v and used(c[idx], v) else "_") if v else ""
                w("    | .%s%s => %s" % (c[0], " " + rv if rv else "", c[idx]))
        w("  modify_eq := by")
        w("    intro h r a f hg")
        w("    cases r with")
        for c in ctors:
            w("    | %s%s =>" % (c[0], (" " + c[1]) if c[1] else ""))
            w("      dsimp only at hg ⊢")
            for line in c[6]:
                w("      " + line)
        w("")
        for (ctor, *rest) in model.ref_ctors.get(key, []):
            if rest[0] == "static":
                w("@[simp] theorem %s.get_%s (h : Heap) : Space.get h %s.%s = some h.static.%s := rfl" % (
                    ref, ctor, ref, ctor, esc(rest[1])))
                w("@[simp] theorem %s.ro_%s (h : Heap) : Space.ro h %s.%s = true := rfl" % (ref, ctor, ref, ctor))
            else:
                owner, field = rest[0], rest[1]
                tbl = S[owner][4]
                w("theorem %s.get_%s {h : Heap} {id : Nat} {s : %s} (e : h.%s id = some s) :" % (ref, ctor, S[owner][2], tbl))
                w("    Space.get h (%s.%s id) = some s.%s := by simp [Space.get, e]" % (ref, ctor, esc(field)))
                w("theorem %s.put_%s {h : Heap} {id : Nat} {s : %s} (e : h.%s id = some s) (a : Array %s) :" % (ref, ctor, S[owner][2], tbl, key))
                w("    Space.put h (%s.%s id) a = { h with %s := upd h.%s id (some { s with %s := a }) } := by" % (ref, ctor, tbl, tbl, esc(field)))
                w("  simp [Space.put, e]")
                tabs = [t for t in STRUCTS if t[3] == "table"]
                names = ["t%d" % i for i in range(len(tabs))]
                k = [t[0] for t in tabs].index(owner)
                w("/-- Storing into an array field of a well-formed record, with an array of the same length, keeps every record")
                w("well-formed. -/")
                w("theorem %s.put_%s_wf {h : Heap} (hw : h.RecordsWellFormed) {id : Nat} {s : %s} (e : h.%s id = some s)" % (ref, ctor, S[owner][2], tbl))
                w("    {a : Array %s} (ha : a.size = s.%s.size) : (Space.put h (%s.%s id) a).RecordsWellFormed := by" % (key, esc(field), ref, ctor))
                w("  rw [%s.put_%s e a]" % (ref, ctor))
                w("  have hs : s.WellFormed := by")
                w("    unfold Heap.RecordsWellFormed at hw")
                w("    obtain ⟨%s⟩ := hw" % ", ".join(names))
                w("    exact %s id s e" % names[k])
                w("  apply Heap.RecordsWellFormed.set_%s hw" % tbl)
                w("  simpa [%s.WellFormed, ha] using hs" % S[owner][2])
                w("@[simp] theorem %s.ro_%s (h : Heap) (id : Nat) : Space.ro h (%s.%s id) = false := rfl" % (ref, ctor, ref, ctor))
        if key in ("UInt8", "UInt16"):
            tbl = "bytes" if key == "UInt8" else "words"
            w("@[simp] theorem %s.get_blk (h : Heap) (b : Nat) : Space.get h (%s.blk b) = h.%s b := rfl" % (ref, ref, tbl))
            w("@[simp] theorem %s.put_blk (h : Heap) (b : Nat) (a : Array %s) :" % (ref, key))
            w("    Space.put h (%s.blk b) a = { h with %s := upd h.%s b (some a) } := rfl" % (ref, tbl, tbl))
            w("@[simp] theorem %s.ro_blk (h : Heap) (b : Nat) : Space.ro h (%s.blk b) = %s := rfl" % (
                ref, ref, "h.ro b" if key == "UInt8" else "false"))
            if key == "UInt8":
                w("@[simp] theorem BRef.get_str (h : Heap) (i : Nat) : Space.get h (BRef.str i) = (strTable[i]?).map strBytes := by simp [Space.get]")
                w("@[simp] theorem BRef.put_str (h : Heap) (i : Nat) (a : Array UInt8) : Space.put h (BRef.str i) a = h := by simp [Space.put]")
                w("@[simp] theorem BRef.ro_str (h : Heap) (i : Nat) : Space.ro h (BRef.str i) = true := by simp [Space.ro]")
            w("")
    # struct refs
    for s in STRUCTS:
        cname, aliases, lean, role, table, short = s
        if role == "elem":
            continue
        ctors = model.struct_ctors[cname]
        w("/-- The record a reference denotes, if it is live. -/")
        w("def %sRef.get (h : Heap) : %sRef → Option %s" % (lean, lean, lean))
        for (ctor, kind) in ctors:
            if kind == "table":
                w("  | .tab i => h.%s i" % table)
            elif kind == "static":
                w("  | .%s => some h.static.%s" % (ctor, esc(ctor[3:])))
            else:
                w("  | .%s i => (h.%s i).map (·.%s)" % (ctor, S[kind[1]][4], esc(kind[2])))
        w("")
        w("/-- The heap after replacing the record a reference denotes (unchanged if it is not live: a freed record is not")
        w("brought back). -/")
        w("def %sRef.put (h : Heap) : %sRef → %s → Heap" % (lean, lean, lean))
        for (ctor, kind) in ctors:
            if kind == "table":
                w("  | .tab i, v => (match h.%s i with" % table)
                w("    | some _ => { h with %s := upd h.%s i (some v) }" % (table, table))
                w("    | none => h)")
            elif kind == "static":
                w("  | .%s, _ => h" % ctor)
            else:
                t = S[kind[1]][4]
                w("  | .%s i, v => (match h.%s i with" % (ctor, t))
                w("    | some s => { h with %s := upd h.%s i (some { s with %s := v }) }" % (t, t, esc(kind[2])))
                w("    | none => h)")
        w("")
        if role == "table":
            w("theorem %sRef.put_tab {h : Heap} {i : Nat} {v : %s} (e : h.%s i = some v) (v' : %s) :" % (lean, lean, table, lean))
            w("    (%sRef.tab i).put h v' = { h with %s := upd h.%s i (some v') } := by simp [%sRef.put, e]" % (lean, table, table, lean))
            w("")
        w("/-- Is the record read-only (a static instance)? -/")
        w("def %sRef.isRo : %sRef → Bool" % (lean, lean))
        for (ctor, kind) in ctors:
            if kind == "table":
                w("  | .tab _ => false")
            elif kind == "static":
                w("  | .%s => true" % ctor)
            else:
                w("  | .%s _ => false" % ctor)
        w("")
    w("/-! ## Constants and tables the generator could not turn into a definition -/")
    w("")
    w("/-")
    w("Macros of the headers that are not emitted as a constant: %d names, by reason." % len(skipped))
    reasons = sorted(set(r for _, r in skipped))
    for r in reasons:
        names = [n for n, rr in skipped if rr == r]
        w("  %s:" % r)
        for i in range(0, len(names), 6):
            w("    " + " ".join(names[i:i + 6]))
    w("")
    w("Names that are also an enumerator: %s." % ", ".join("`%s` is emitted as `%s`" % (o, n) for o, n in renamed))
    w("`GZ_OFF_MAX` (gzguts.h) is `((((z_off64_t)1 << (sizeof(z_off64_t) * CHAR_BIT - 2)) - 1) * 2 + 1)`, that is")
    w("9223372036854775807 here; it is defined with that value in the translation of gzguts.h.")
    w("-/")
    w("")
    w("end C")
    return "\n".join(L) + "\n"


def emit_tables(model):
    S = model.struct_info
    L = []
    w = L.append
    LC = []
    wl = LC.append
    w("import ZlibF.Runtime.Monad")
    w("")
    w("/-!")
    w("# Load and store for every struct kind (GENERATED, do not edit)")
    w("")
    w("`ldK p` is `*p` for a pointer to a struct of kind `K`, `stK p v` is `*p = v` (a whole-record store; a field")
    w("write is a load, a record update and a store). Every primitive faults on a null, dangling or read-only target, as")
    w("the C is undefined there. `malloc`, `free` and the whole-record `memcpy` of each kind are in `LibcTables.lean`.")
    w("-/")
    w("")
    w("namespace C")
    w("")
    wl("import ZlibF.Runtime.Tables")
    wl("")
    wl("/-!")
    wl("# `malloc`, `free` and `memcpy` of every struct kind (GENERATED, do not edit)")
    wl("")
    wl("`allocK` and `freeK` are `malloc(sizeof(K))` and `free` through the default allocator, `copyK dst src` is the")
    wl("`memcpy` of a whole record. They model the C library (see `Libc.lean` and `docs/trusted-base.md`); the loads and")
    wl("stores of the records are in `Tables.lean`.")
    wl("-/")
    wl("")
    wl("namespace C")
    wl("")
    for s in STRUCTS:
        cname, aliases, lean, role, table, short = s
        if role == "elem":
            continue
        ctors = model.struct_ctors[cname]
        w("/-- `*p` for a `%s *`: faults if `p` is null or does not point to a live object. -/" % cname)
        w("def ld%s (p : %sPtr) : M %s := fun h =>" % (lean, lean, lean))
        w("  match p with")
        w("  | none => .error (.ub \"null dereference (%s)\")" % cname)
        w("  | some r => match r.get h with")
        w("    | some v => .ok (v, h)")
        w("    | none => .error (.ub \"access through a dangling pointer (%s)\")" % cname)
        w("")
        w("/-- `*p = v` for a `%s *`: faults if `p` is null, dangling or read-only. -/" % cname)
        w("def st%s (p : %sPtr) (v : %s) : M Unit := fun h =>" % (lean, lean, lean))
        w("  match p with")
        w("  | none => .error (.ub \"null dereference (%s)\")" % cname)
        w("  | some r => match r.get h with")
        w("    | some _ => if r.isRo then .error (.ub \"store into a read-only object (%s)\") else .ok ((), r.put h v)" % cname)
        w("    | none => .error (.ub \"access through a dangling pointer (%s)\")" % cname)
        w("")
        w("theorem ld%s_ok {h : Heap} {r : %sRef} {v : %s} (e : r.get h = some v) :" % (lean, lean, lean))
        w("    ld%s (some r) h = .ok (v, h) := by simp [ld%s, e]" % (lean, lean))
        w("")
        w("theorem st%s_ok {h : Heap} {r : %sRef} {v v' : %s} (e : r.get h = some v) (hro : r.isRo = false) :" % (lean, lean, lean))
        w("    st%s (some r) v' h = .ok ((), r.put h v') := by simp [st%s, e, hro]" % (lean, lean))
        w("")
        if role == "table":
            w("theorem ld%s_tab {h : Heap} {i : Nat} {v : %s} (e : h.%s i = some v) :" % (lean, lean, table))
            w("    ld%s (some (.tab i)) h = .ok (v, h) := ld%s_ok e" % (lean, lean))
            w("")
            w("theorem st%s_tab {h : Heap} {i : Nat} {v v' : %s} (e : h.%s i = some v) :" % (lean, lean, table))
            w("    st%s (some (.tab i)) v' h = .ok ((), { h with %s := upd h.%s i (some v') }) := by" % (lean, table, table))
            w("  rw [st%s_ok (r := .tab i) e rfl]" % lean)
            w("  rw [%sRef.put_tab e v']" % lean)
            w("")
            wl("/-- `malloc(sizeof(%s))` through the default allocator: a fresh live record with arbitrary integers and" % cname)
            wl("null pointers (a documented gap: C leaves them indeterminate, see `docs/trusted-base.md`), or null when the")
            wl("failure oracle says so. It is a fault (not a C behaviour) if the block number `nextBlk` is already in use:")
            wl("the heap is then not `Fresh`, and a theorem about allocation carries `Fresh`. -/")
            wl("def alloc%s : M %sPtr := fun h =>" % (lean, lean))
            wl("  if h.allocOk h.nalloc then")
            wl("    if h.slotUsed h.nextBlk then .error (.ub \"allocation: the block number is in use (the heap is not Fresh)\")")
            wl("    else .ok (some (.tab h.nextBlk), { h with %s := upd h.%s h.nextBlk (some (%s.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 })"
              % (table, table, lean))
            wl("  else .ok (none, { h with nalloc := h.nalloc + 1 })")
            wl("")
            wl("/-- Alias of `alloc%s`. -/" % lean)
            wl("abbrev alloc%sChk := alloc%s" % (lean, lean))
            wl("")
            wl("theorem alloc%s_some {h : Heap} (hok : h.allocOk h.nalloc = true)" % lean)
            wl("    (hs : h.slotUsed h.nextBlk = false := by fresh_slot) :")
            wl("    alloc%s h = .ok (some (.tab h.nextBlk), { h with %s := upd h.%s h.nextBlk (some (%s.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }) := by simp [alloc%s, hok, hs]"
              % (lean, table, table, lean, lean))
            wl("")
            wl("theorem alloc%s_none {h : Heap} (hok : ¬ h.allocOk h.nalloc = true) :" % lean)
            wl("    alloc%s h = .ok (none, { h with nalloc := h.nalloc + 1 }) := by simp [alloc%s, hok]" % (lean, lean))
            wl("")
            wl("/-- `free(p)` for a `%s *`: a no-op for null; faults for a block that is not live (double free) and for a" % cname)
            wl("pointer that was not returned by the allocator. -/")
            wl("def free%s (p : %sPtr) : M Unit := fun h =>" % (lean, lean))
            wl("  match p with")
            wl("  | none => .ok ((), h)")
            wl("  | some (.tab i) => match h.%s i with" % table)
            wl("    | some _ => .ok ((), { h with %s := upd h.%s i none })" % (table, table))
            wl("    | none => .error (.ub \"free of a freed or invalid pointer (%s)\")" % cname)
            if len(ctors) > 1:
                wl("  | some _ => .error (.ub \"free of a pointer that was not allocated (%s)\")" % cname)
            wl("")
            wl("theorem free%s_null {h : Heap} : free%s none h = .ok ((), h) := rfl" % (lean, lean))
            wl("")
            wl("/-- `*dst = *src` for two `%s *` (`zmemcpy(dst, src, sizeof *dst)`): a whole-record copy. Faults if either pointer" % cname)
            wl("is null, dangling or the destination read-only, and if both denote the same object (`memcpy` with overlapping")
            wl("ranges is undefined; the `%s` objects of the heap do not contain one another). -/" % cname)
            wl("def copy%s (dst src : %sPtr) : M Unit := fun h =>" % (lean, lean))
            wl("  match dst, src with")
            wl("  | some d, some s =>")
            wl("    if d = s then .error (.ub \"memcpy of a %s onto itself (overlapping ranges)\")" % cname)
            wl("    else (ld%s (some s) >>= fun v => st%s (some d) v) h" % (lean, lean))
            wl("  | _, _ => .error (.ub \"null dereference (%s)\")" % cname)
            wl("")
            wl("theorem free%s_tab {h : Heap} {i : Nat} {v : %s} (e : h.%s i = some v) :" % (lean, lean, table))
            wl("    free%s (some (.tab i)) h = .ok ((), { h with %s := upd h.%s i none }) := by simp [free%s, e]" % (lean, table, table, lean))
            wl("")
    # opaque state pointer
    name, lean_state, kinds = OPAQUE
    w("/-! ## `struct internal_state *` and its casts -/")
    w("")
    for (ctor, target) in kinds:
        tl = S[target][2]
        w("/-- `(%s *) p` for `p` of type `struct internal_state *`: faults if `p` points to the other kind of state. -/" % target)
        w("def cast%s (p : Option %s) : M %sPtr := fun h =>" % (tl, lean_state, tl))
        w("  match p with")
        w("  | none => .ok (none, h)")
        w("  | some (.%s i) => .ok (some (.tab i), h)" % ctor)
        for (c2, t2) in kinds:
            if c2 != ctor:
                w("  | some (.%s _) => .error (.ub \"a %s is used as a %s\")" % (c2, t2, target))
        w("")
        w("theorem cast%s_ok {h : Heap} {i : Nat} : cast%s (some (.%s i)) h = .ok (some (.tab i), h) := rfl" % (tl, tl, ctor))
        w("")
        w("/-- `(struct internal_state *) p` for `p` of type `%s *`. -/" % target)
        w("def %s.of%s : %sPtr → Option %s" % (lean_state, tl, tl, lean_state))
        w("  | none => none")
        w("  | some (.tab i) => some (.%s i)" % ctor)
        if len(model.struct_ctors[target]) > 1:
            die("%s has embedded references: the cast to %s is not defined" % (target, lean_state))
        w("")
    w("end C")
    wl("end C")
    return "\n".join(L) + "\n", "\n".join(LC) + "\n"


# ------------------------------------------------------------------------------------------------------------
# documentation
# ------------------------------------------------------------------------------------------------------------

DOC_HEAD = """# Runtime schema: the structs of zlib on the object heap

This page is **generated** by `scripts/gen_schema.py` together with `ZlibF/Runtime/Schema.lean` and
`ZlibF/Runtime/Tables.lean` and `ZlibF/Runtime/LibcTables.lean`. Do not edit it by hand: change the script and run it again. The script reads the headers
`zlib.h`, `zutil.h`, `inftrees.h`, `inflate.h`, `deflate.h`, `trees.h`, `gzguts.h` and `crc32.h` of the verified source
(zlib commit `{commit}`) through clang's JSON AST dump, in the default x86_64 Linux build
(`./configure --static`, LP64, `-D_LARGEFILE64_SOURCE=1`).

## How the script decides

| C | Lean | Why |
| --- | --- | --- |
| `char`, `short`, `int`, `long` and the unsigned forms | `Int8`, `Int16`, `Int32`, `Int64`, `UInt8` .. `UInt64` | LP64: `long` and pointers are 64 bits; plain `char` is signed on x86_64 |
| `enum` type | `UInt32` (`Int32` if an enumerator is negative); the enumerators become constants `X` of that type, and `X_i` of type `Int32` | gcc picks `unsigned int` for the object of an enum type without negative values. The constant itself has type `int` in C: `X` is for a comparison with such an object, `X_i` where the constant meets an `int` |
| `T *` where `T` is a byte, `void` | `BPtr = Ptr BRef`: null, or an array and an offset | a byte buffer is a block of the `bytes` table; `void *` is only ever a byte buffer or opaque in zlib |
| `T *` where `T` is a wider scalar | `WPtr`, `IPtr`, ... (`Ptr` of the reference type of that element) | the same, for the `words` table or for an array inside a struct |
| `T *` where `T` is an array element struct (`ct_data`, `code`) | `CtDataPtr`, `CodePtr` | a pointer into an array of structs is the array and an index, never an address |
| `S *` where `S` is a single struct (`z_stream`, `gz_header`, `deflate_state`, ...) | `Option SRef`; `none` is null | `SRef` is a table entry or the struct inside its owner |
| `struct internal_state *` | `Option StateRef` (a deflate state or an inflate state) | `z_stream.state` is cast to both in the C |
| array field `T f[N]` | `Array T` field | an array that is part of a struct is copied with the struct, as in C; a pointer to it is a constructor of the reference type of `T` |
| struct field `S f` | a nested record `S` | value semantics; `&s->f` is the constructor `in_<owner>_<f>` of `SRef` |
| `union` whose members have one type | one field | `ct_data` is `ush` for both members: they are the same bits |
| function pointer | `FnPtr` (null or a name) | only the default allocator is modelled; any other function is a fault when called |
| static table or instance | a field of `Statics` in the heap, a reference constructor `st_<name>` | read-only: a store through it is a fault; its content is set by the translation |

## What the schema does not model

* **Pointer to pointer, and the address of a scalar field** (`&state->lenbits`, `&state->next` in the call of
  `inflate_table`). The translation passes such out-parameters as results. The script stops if a struct field has
  type pointer to pointer.
* **Bit-fields and unions with members of different types.** The script stops; there are none in the headers.
* **`opaque` pointers to caller data** (`z_stream.opaque`, `voidpf`) are `BPtr`; a caller object that is not a byte
  block is not representable. zlib never dereferences it.
* **Structs that are defined in `.c` files** (`struct config_s` in `deflate.c`, the `FILE` of the C library).
* **Uninitialised pointers.** A fresh record (`allocK`, `X.garbage`) has null pointers. In C a pointer read from
  uninitialised memory is indeterminate. In the model it is a valid NULL: using it is a null dereference, but
  `p == NULL`, `free(p)` and a copy of it succeed. A theorem about a function that reads a pointer field before the
  field is written must therefore establish that write; the runtime does not check it. See `trusted-base.md`, item 2.
  Integers are arbitrary (decision D5 of `overview.md`).
* **The lengths of array fields.** `Array` fields have any length. `X.WellFormed` says that every array has the
  declared length, and `Heap.RecordsWellFormed` that every record of the heap does; a theorem carries it as a
  hypothesis (`Heap.WellFormed` adds the static tables). `X.garbage` and `X.zeroed` are well-formed, and the lemmas
  `Heap.RecordsWellFormed.set_*`, `clear_*` and `*.put_*_wf` show that stores keep it.
* **The content of the static tables.** `Statics` holds the arrays; `Statics.WellFormed` says that each has the
  declared length. Their values are fixed by the translation of `trees.c`, `inffixed.h`, `crc32.c` (each from a
  generator that reads the C source) and are a hypothesis of a theorem until then. The script does not compare
  them with the C.
* **Tables.** The tables of the heap are `Tbl`s (an `Array` read as a function of the block number), so that the
  primitives that write can update in place; see `trusted-base.md`, item 2.
* **Macros that share a name with an enumerator.** `COPY` is both an enumerator of `inflate.h` (16195) and a macro of
  `gzguts.h` (1). The enumerator keeps the name `COPY`; the macro is the constant `GZ_COPY`.
* **Allocation.** `allocK` faults if the next block number is already in use, so the heap must be `Fresh`
  (`Fresh.slotUsed_next`; the tactic `fresh_slot` discharges the hypothesis of `allocK_some` from `Fresh h`).
  A direct store (`stK`) of a record whose arrays have the wrong length is not a fault.
* **A cast between the two kinds of state** is a fault at the cast; in C it is a fault only at the access.

The static objects that are not declared in a header are listed in the script
(`EXTRA_STATIC_ARRAYS`, `EXTRA_STATIC_INSTANCES`): {extras}.

## Fields

"""


def emit_doc(model, commit):
    S = model.struct_info
    L = [DOC_HEAD.format(commit=commit, extras=", ".join("`%s`" % e[0] for e in EXTRA_STATIC_ARRAYS + EXTRA_STATIC_INSTANCES))]
    w = L.append
    for s in STRUCTS:
        cname, aliases, lean, role, table, short = s
        w("### `%s` (Lean `%s`, %s)" % (cname, lean, {
            "table": "table `%s` of the heap" % table, "embedded": "only a field of another struct",
            "static": "static instances only", "elem": "element of arrays"}[role]))
        w("")
        w("| Field | C type | Lean type | Why |")
        w("| --- | --- | --- | --- |")
        for f in model.fields[cname]:
            w("| `%s` | `%s` | `%s` | %s |" % (f.name, f.ctype.replace("|", "\\|"), f.lean, f.why))
        w("")
        refs = model.struct_ctors.get(cname)
        if refs:
            w("Reference constructors (`%sRef`): %s." % (lean, ", ".join("`%s`" % c for c, _ in refs)))
            w("")
    w("### Reference types of arrays")
    w("")
    w("| Lean type | Elements | Constructors |")
    w("| --- | --- | --- |")
    for key in sorted(model.families, key=lambda k: (k not in FAMILY, k)):
        ref, ptr = model.fam_names(key)
        c = []
        if key in ("UInt8", "UInt16"):
            c.append("`blk` (table `%s`)" % ("bytes" if key == "UInt8" else "words"))
        c += ["`%s`" % x[0] for x in model.ref_ctors.get(key, [])]
        w("| `%s` / `%s` | `%s` | %s |" % (ref, ptr, key, ", ".join(c)))
    w("")
    w("### String literals")
    w("")
    w("`strTable` (in `Schema.lean`) lists the %d string literals of the library sources: the `*.c` and `*.h` files of the" % len(model.strs))
    w("top directory of the verified source, comments excluded, adjacent literals joined, plus the empty string. They are the")
    w("error messages (`zutil.c`, `inflate.c`, `inffast.c`, `inftrees.c`, `trees.c`, `deflate.c`, `gz*.c`), the `z_errmsg`")
    w("texts, `ZLIB_VERSION`, the copyright strings and the format strings. The set is closed: `strLitRef` of a text that is")
    w("not in the table is a fault. A literal is `BRef.str i`: read-only, always live, never freed, in no table of the heap.")
    w("")
    w("```")
    for b in model.strs:
        w(lean_string(b))
    w("```")
    w("")
    w("### Static objects")
    w("")
    w("| Field of `Statics` | C object | Elements | Source |")
    w("| --- | --- | --- | --- |")
    for (name, kind, lean, size, src, cname) in model.statics:
        w("| `%s` | `%s` | %s | %s |" % (name, cname, ("%d x `%s`" % (size, lean)) if kind == "array" else "`%s`" % lean, src))
    w("")
    w("The three descriptors are read from `trees.c` when the script runs (the declaration of their struct is compared with")
    w("the field list of the script). Their members `(static_tree, extra_bits, extra_base, elems, max_length)` are:")
    w("")
    for name in sorted(model.descs):
        d = model.descs[name]
        w("* `%s` = (`%s`, `%s`, %d, %d, %d)" % ((name,) + d))
    w("")
    w("`bl_order` (`local const uch bl_order[BL_CODES]` in `trees.c`) is not a field of `Statics`: it is only indexed, never")
    w("addressed, so the translation of `trees.c` holds it as a plain constant.")
    w("")
    return "\n".join(L)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--zlib", required=True, help="the verified source (zlib plus patches)")
    ap.add_argument("--out", default=ROOT, help="the workspace root")
    args = ap.parse_args()
    zdir = os.path.abspath(args.zlib)
    tu, pre = run_clang(zdir)
    ast = Ast(tu)
    macros = read_macros(pre, zdir)
    consts = compute_constants(ast, macros)
    ints = consts[0]
    model = Model(ast, ints)
    model.descs = read_trees_c(zdir, macros, ast)
    model.strs = read_string_table(zdir)
    commit = zlib_commit(zdir)
    tables_text, libc_tables_text = emit_tables(model)
    out = {
        "ZlibF/Runtime/Schema.lean": emit_schema(model, commit, consts),
        "ZlibF/Runtime/Tables.lean": tables_text,
        "ZlibF/Runtime/LibcTables.lean": libc_tables_text,
        "docs/runtime-schema.md": emit_doc(model, commit),
    }
    for rel, text in out.items():
        path = os.path.join(args.out, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(text)
        print("wrote", rel, file=sys.stderr)


if __name__ == "__main__":
    main()
