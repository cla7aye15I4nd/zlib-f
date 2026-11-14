#!/usr/bin/env python3
"""Every C string literal the translations pass to `strLit` / `strLitRef` is in the runtime table `strTable`.

`strLit s` is a fault when `s` is not in `strTable` (`ZlibF/Runtime/Schema.lean`), so a missing literal turns a
C path that returns into a model path that faults. This check reads the quoted literals passed to `strLit` or
`strLitRef` in `ZlibF/Zlib/*.lean`, plus `ZLIB_VERSION`, and fails on any literal not in the table. Arguments that
are variables (error-text tables) are covered by the proofs about those tables.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
STRING = r'"((?:[^"\\]|\\.)*)"'


def unescape(s: str) -> str:
    return bytes(s, "utf-8").decode("unicode_escape")


def table() -> list[str]:
    text = (ROOT / "ZlibF/Runtime/Schema.lean").read_text()
    start = text.index("def strTable : Array String := #[")
    end = text.index("\n]", start)
    return [unescape(m) for m in re.findall(STRING, text[start:end])]


def used() -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    for path in sorted((ROOT / "ZlibF/Zlib").glob("*.lean")):
        for n, line in enumerate(path.read_text().splitlines(), 1):
            code = line.split("--", 1)[0]
            for m in re.finditer(r"\bstrLit(?:Ref)?\s+" + STRING, code):
                found.setdefault(unescape(m.group(1)), []).append(f"{path.relative_to(ROOT)}:{n}")
    version = re.search(r"def ZLIB_VERSION\b[^\n]*?" + STRING, (ROOT / "ZlibF/Runtime/Schema.lean").read_text())
    if version:
        found.setdefault(unescape(version.group(1)), []).append("ZLIB_VERSION")
    return found


def main() -> int:
    tab = set(table())
    missing = {s: where for s, where in used().items() if s not in tab}
    for s, where in sorted(missing.items()):
        print(f"string literal not in strTable: {s!r} (used at {', '.join(where)})")
    if missing:
        return 1
    print(f"check-strlit: {len(used())} literals used, all in strTable ({len(tab)} entries)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
