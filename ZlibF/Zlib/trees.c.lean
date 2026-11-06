import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Tables

/-!
# trees.c — faithful translation (draft)

Source: `zlib/trees.c` and `zlib/trees.h`, default build (LP64; `ZLIB_DEBUG`, `GEN_TREES_H`, `LIT_MEM`,
`NO_INIT_GLOBAL_POINTERS`, `FORCE_STATIC`, `FORCE_STORED` undefined; `STDC` defined, so the tables come from
`trees.h`). Translated statement by statement. Macros are expanded in source order: `put_byte`, `put_short`,
`send_bits`, `send_code`, `pqremove`, `smaller`, `d_code`.

Conventions of this file:

* `deflate_state *s` is `DeflateStatePtr`. A scalar field is read with `rd s` (a load of the whole record) and
  written with `md s` (a load, a record update and a store). An array field decays to a pointer: `pLtree s`
  (`s->dyn_ltree`), `pDtree`, `pBltree`, `pHeap`, `pDepth`, `pBlCount`.
* `int` is `Int32` with checked arithmetic (`iadd`, `isub`, `shl1`, ...): an overflow is `Fault.ub`.
  `unsigned`, `ush`, `uch`, `ulg` wrap.
* `Assert` and `Trace*` are compiled out (no `ZLIB_DEBUG`); `tr_static_init` is an empty function.
* The static tables of `trees.h` and `trees.c` are `*_tab` constants below, installed in the heap by
  `install_trees` (they are `Statics` fields; a store through them is a fault).
* `ct_data`: `Freq`/`Code` is `fc`, `Dad`/`Len` is `dl`.
* Local `ush next_code[MAX_BITS+1]` of `gen_codes` is a Lean `Array UInt16`; its element 0 is never read
  (`len == 0` is skipped) and an index outside it is a fault.
-/

namespace Zlib.Trees
open C

/-! ## Constants -/

def MAX_BL_BITS : Int32 := 7
def END_BLOCK : Int32 := 256
def REP_3_6 : Int32 := 16
def REPZ_3_10 : Int32 := 17
def REPZ_11_138 : Int32 := 18

/-- `extra_lbits[LENGTH_CODES]` (trees.c). -/
def extra_lbits_tab : Array Int32 := #[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0]
/-- `extra_dbits[D_CODES]` (trees.c). -/
def extra_dbits_tab : Array Int32 := #[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13]
/-- `extra_blbits[BL_CODES]` (trees.c). -/
def extra_blbits_tab : Array Int32 := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,7]
/-- `local const uch bl_order[BL_CODES]` (trees.c). -/
def bl_order : Array UInt8 := #[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15]

/-! ## Tables of `trees.h` (verbatim) -/

/-- `static_ltree`: `trees.h`, verbatim (288 entries; `fc` = `Code`, `dl` = `Len`). -/
def static_ltree_tab : Array CtData := #[
  ⟨12, 8⟩, ⟨140, 8⟩, ⟨76, 8⟩, ⟨204, 8⟩, ⟨44, 8⟩, ⟨172, 8⟩,
  ⟨108, 8⟩, ⟨236, 8⟩, ⟨28, 8⟩, ⟨156, 8⟩, ⟨92, 8⟩, ⟨220, 8⟩,
  ⟨60, 8⟩, ⟨188, 8⟩, ⟨124, 8⟩, ⟨252, 8⟩, ⟨2, 8⟩, ⟨130, 8⟩,
  ⟨66, 8⟩, ⟨194, 8⟩, ⟨34, 8⟩, ⟨162, 8⟩, ⟨98, 8⟩, ⟨226, 8⟩,
  ⟨18, 8⟩, ⟨146, 8⟩, ⟨82, 8⟩, ⟨210, 8⟩, ⟨50, 8⟩, ⟨178, 8⟩,
  ⟨114, 8⟩, ⟨242, 8⟩, ⟨10, 8⟩, ⟨138, 8⟩, ⟨74, 8⟩, ⟨202, 8⟩,
  ⟨42, 8⟩, ⟨170, 8⟩, ⟨106, 8⟩, ⟨234, 8⟩, ⟨26, 8⟩, ⟨154, 8⟩,
  ⟨90, 8⟩, ⟨218, 8⟩, ⟨58, 8⟩, ⟨186, 8⟩, ⟨122, 8⟩, ⟨250, 8⟩,
  ⟨6, 8⟩, ⟨134, 8⟩, ⟨70, 8⟩, ⟨198, 8⟩, ⟨38, 8⟩, ⟨166, 8⟩,
  ⟨102, 8⟩, ⟨230, 8⟩, ⟨22, 8⟩, ⟨150, 8⟩, ⟨86, 8⟩, ⟨214, 8⟩,
  ⟨54, 8⟩, ⟨182, 8⟩, ⟨118, 8⟩, ⟨246, 8⟩, ⟨14, 8⟩, ⟨142, 8⟩,
  ⟨78, 8⟩, ⟨206, 8⟩, ⟨46, 8⟩, ⟨174, 8⟩, ⟨110, 8⟩, ⟨238, 8⟩,
  ⟨30, 8⟩, ⟨158, 8⟩, ⟨94, 8⟩, ⟨222, 8⟩, ⟨62, 8⟩, ⟨190, 8⟩,
  ⟨126, 8⟩, ⟨254, 8⟩, ⟨1, 8⟩, ⟨129, 8⟩, ⟨65, 8⟩, ⟨193, 8⟩,
  ⟨33, 8⟩, ⟨161, 8⟩, ⟨97, 8⟩, ⟨225, 8⟩, ⟨17, 8⟩, ⟨145, 8⟩,
  ⟨81, 8⟩, ⟨209, 8⟩, ⟨49, 8⟩, ⟨177, 8⟩, ⟨113, 8⟩, ⟨241, 8⟩,
  ⟨9, 8⟩, ⟨137, 8⟩, ⟨73, 8⟩, ⟨201, 8⟩, ⟨41, 8⟩, ⟨169, 8⟩,
  ⟨105, 8⟩, ⟨233, 8⟩, ⟨25, 8⟩, ⟨153, 8⟩, ⟨89, 8⟩, ⟨217, 8⟩,
  ⟨57, 8⟩, ⟨185, 8⟩, ⟨121, 8⟩, ⟨249, 8⟩, ⟨5, 8⟩, ⟨133, 8⟩,
  ⟨69, 8⟩, ⟨197, 8⟩, ⟨37, 8⟩, ⟨165, 8⟩, ⟨101, 8⟩, ⟨229, 8⟩,
  ⟨21, 8⟩, ⟨149, 8⟩, ⟨85, 8⟩, ⟨213, 8⟩, ⟨53, 8⟩, ⟨181, 8⟩,
  ⟨117, 8⟩, ⟨245, 8⟩, ⟨13, 8⟩, ⟨141, 8⟩, ⟨77, 8⟩, ⟨205, 8⟩,
  ⟨45, 8⟩, ⟨173, 8⟩, ⟨109, 8⟩, ⟨237, 8⟩, ⟨29, 8⟩, ⟨157, 8⟩,
  ⟨93, 8⟩, ⟨221, 8⟩, ⟨61, 8⟩, ⟨189, 8⟩, ⟨125, 8⟩, ⟨253, 8⟩,
  ⟨19, 9⟩, ⟨275, 9⟩, ⟨147, 9⟩, ⟨403, 9⟩, ⟨83, 9⟩, ⟨339, 9⟩,
  ⟨211, 9⟩, ⟨467, 9⟩, ⟨51, 9⟩, ⟨307, 9⟩, ⟨179, 9⟩, ⟨435, 9⟩,
  ⟨115, 9⟩, ⟨371, 9⟩, ⟨243, 9⟩, ⟨499, 9⟩, ⟨11, 9⟩, ⟨267, 9⟩,
  ⟨139, 9⟩, ⟨395, 9⟩, ⟨75, 9⟩, ⟨331, 9⟩, ⟨203, 9⟩, ⟨459, 9⟩,
  ⟨43, 9⟩, ⟨299, 9⟩, ⟨171, 9⟩, ⟨427, 9⟩, ⟨107, 9⟩, ⟨363, 9⟩,
  ⟨235, 9⟩, ⟨491, 9⟩, ⟨27, 9⟩, ⟨283, 9⟩, ⟨155, 9⟩, ⟨411, 9⟩,
  ⟨91, 9⟩, ⟨347, 9⟩, ⟨219, 9⟩, ⟨475, 9⟩, ⟨59, 9⟩, ⟨315, 9⟩,
  ⟨187, 9⟩, ⟨443, 9⟩, ⟨123, 9⟩, ⟨379, 9⟩, ⟨251, 9⟩, ⟨507, 9⟩,
  ⟨7, 9⟩, ⟨263, 9⟩, ⟨135, 9⟩, ⟨391, 9⟩, ⟨71, 9⟩, ⟨327, 9⟩,
  ⟨199, 9⟩, ⟨455, 9⟩, ⟨39, 9⟩, ⟨295, 9⟩, ⟨167, 9⟩, ⟨423, 9⟩,
  ⟨103, 9⟩, ⟨359, 9⟩, ⟨231, 9⟩, ⟨487, 9⟩, ⟨23, 9⟩, ⟨279, 9⟩,
  ⟨151, 9⟩, ⟨407, 9⟩, ⟨87, 9⟩, ⟨343, 9⟩, ⟨215, 9⟩, ⟨471, 9⟩,
  ⟨55, 9⟩, ⟨311, 9⟩, ⟨183, 9⟩, ⟨439, 9⟩, ⟨119, 9⟩, ⟨375, 9⟩,
  ⟨247, 9⟩, ⟨503, 9⟩, ⟨15, 9⟩, ⟨271, 9⟩, ⟨143, 9⟩, ⟨399, 9⟩,
  ⟨79, 9⟩, ⟨335, 9⟩, ⟨207, 9⟩, ⟨463, 9⟩, ⟨47, 9⟩, ⟨303, 9⟩,
  ⟨175, 9⟩, ⟨431, 9⟩, ⟨111, 9⟩, ⟨367, 9⟩, ⟨239, 9⟩, ⟨495, 9⟩,
  ⟨31, 9⟩, ⟨287, 9⟩, ⟨159, 9⟩, ⟨415, 9⟩, ⟨95, 9⟩, ⟨351, 9⟩,
  ⟨223, 9⟩, ⟨479, 9⟩, ⟨63, 9⟩, ⟨319, 9⟩, ⟨191, 9⟩, ⟨447, 9⟩,
  ⟨127, 9⟩, ⟨383, 9⟩, ⟨255, 9⟩, ⟨511, 9⟩, ⟨0, 7⟩, ⟨64, 7⟩,
  ⟨32, 7⟩, ⟨96, 7⟩, ⟨16, 7⟩, ⟨80, 7⟩, ⟨48, 7⟩, ⟨112, 7⟩,
  ⟨8, 7⟩, ⟨72, 7⟩, ⟨40, 7⟩, ⟨104, 7⟩, ⟨24, 7⟩, ⟨88, 7⟩,
  ⟨56, 7⟩, ⟨120, 7⟩, ⟨4, 7⟩, ⟨68, 7⟩, ⟨36, 7⟩, ⟨100, 7⟩,
  ⟨20, 7⟩, ⟨84, 7⟩, ⟨52, 7⟩, ⟨116, 7⟩, ⟨3, 8⟩, ⟨131, 8⟩,
  ⟨67, 8⟩, ⟨195, 8⟩, ⟨35, 8⟩, ⟨163, 8⟩, ⟨99, 8⟩, ⟨227, 8⟩
]

/-- `static_dtree`: `trees.h`, verbatim (30 entries; `fc` = `Code`, `dl` = `Len`). -/
def static_dtree_tab : Array CtData := #[
  ⟨0, 5⟩, ⟨16, 5⟩, ⟨8, 5⟩, ⟨24, 5⟩, ⟨4, 5⟩, ⟨20, 5⟩,
  ⟨12, 5⟩, ⟨28, 5⟩, ⟨2, 5⟩, ⟨18, 5⟩, ⟨10, 5⟩, ⟨26, 5⟩,
  ⟨6, 5⟩, ⟨22, 5⟩, ⟨14, 5⟩, ⟨30, 5⟩, ⟨1, 5⟩, ⟨17, 5⟩,
  ⟨9, 5⟩, ⟨25, 5⟩, ⟨5, 5⟩, ⟨21, 5⟩, ⟨13, 5⟩, ⟨29, 5⟩,
  ⟨3, 5⟩, ⟨19, 5⟩, ⟨11, 5⟩, ⟨27, 5⟩, ⟨7, 5⟩, ⟨23, 5⟩
]

/-- `_dist_code`: `trees.h`, verbatim (512 entries). -/
def dist_code_tab : Array UInt8 := #[
  0, 1, 2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8,
  8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10,
  10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
  11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
  12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13,
  13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
  13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14,
  14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14,
  14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14,
  14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15,
  15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
  15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
  15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 0, 0, 16, 17,
  18, 18, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22,
  23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25,
  26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26,
  26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27,
  27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
  27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
  28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
  28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
  28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29,
  29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29,
  29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29,
  29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29
]

/-- `_length_code`: `trees.h`, verbatim (256 entries). -/
def length_code_tab : Array UInt8 := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 12, 12,
  13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16,
  17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19,
  19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
  21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22,
  22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23,
  23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
  25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25,
  25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26,
  26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26,
  26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
  27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28
]

/-- `base_length`: `trees.h`, verbatim (29 entries). -/
def base_length_tab : Array Int32 := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48, 56,
  64, 80, 96, 112, 128, 160, 192, 224, 0
]

/-- `base_dist`: `trees.h`, verbatim (30 entries). -/
def base_dist_tab : Array Int32 := #[
  0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768,
  1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288, 16384, 24576
]

/-- The static tables and descriptors of `trees.c`, installed in the `Statics` of a heap:
`static_l_desc = {static_ltree, extra_lbits, LITERALS+1, L_CODES, MAX_BITS}`,
`static_d_desc = {static_dtree, extra_dbits, 0, D_CODES, MAX_BITS}`,
`static_bl_desc = {NULL, extra_blbits, 0, BL_CODES, MAX_BL_BITS}`. -/
def trees_statics (st : Statics) : Statics :=
  { st with
    dist_code := dist_code_tab
    length_code := length_code_tab
    base_dist := base_dist_tab
    base_length := base_length_tab
    static_dtree := static_dtree_tab
    static_ltree := static_ltree_tab
    extra_lbits := extra_lbits_tab
    extra_dbits := extra_dbits_tab
    extra_blbits := extra_blbits_tab
    static_l_desc := { static_tree := .ref .st_static_ltree 0, extra_bits := .ref .st_extra_lbits 0,
                       extra_base := LITERALS + 1, elems := L_CODES, max_length := MAX_BITS }
    static_d_desc := { static_tree := .ref .st_static_dtree 0, extra_bits := .ref .st_extra_dbits 0,
                       extra_base := 0, elems := D_CODES, max_length := MAX_BITS }
    static_bl_desc := { static_tree := .null, extra_bits := .ref .st_extra_blbits 0,
                        extra_base := 0, elems := BL_CODES, max_length := MAX_BL_BITS } }

/-- The heap with the static data of `trees.c` and `trees.h` in place. -/
def install_trees (h : Heap) : Heap := { h with static := trees_statics h.static }

/-! ## Helpers (not C functions): checked `int` arithmetic, record and array access -/

/-- A checked `int` result. -/
def ck (x : Int) : M Int32 :=
  if -2147483648 ≤ x ∧ x ≤ 2147483647 then pure (Int32.ofInt x) else ub "signed integer overflow"
def iadd (a b : Int32) : M Int32 := ck (a.toInt + b.toInt)
def isub (a b : Int32) : M Int32 := ck (a.toInt - b.toInt)
/-- `x << 1` for an `int`: undefined for a negative `x` or if the result does not fit. -/
def shl1 (x : Int32) : M Int32 := if x.toInt < 0 then ub "left shift of a negative value" else ck (x.toInt * 2)
/-- `ush` to `int`. -/
def u16i (x : UInt16) : Int32 := Int32.ofInt x.toNat
/-- `uch` to `int`. -/
def u8i (x : UInt8) : Int32 := Int32.ofInt x.toNat
/-- `int` to `unsigned` (modulo 2^32). -/
def i2u (x : Int32) : UInt32 := UInt32.ofNat (x.toInt % 4294967296).toNat
/-- `unsigned` to `int` (modulo 2^32, as gcc). -/
def u2i (x : UInt32) : Int32 := Int32.ofInt (if x.toNat ≥ 2147483648 then (x.toNat : Int) - 4294967296 else x.toNat)
/-- `int` to `unsigned long` (sign extension, modulo 2^64). -/
def i2ul (x : Int32) : UInt64 := UInt64.ofNat (x.toInt % 18446744073709551616).toNat
/-- `(ush)x` for an `int`. -/
def i2us (x : Int32) : UInt16 := UInt16.ofNat (x.toInt % 65536).toNat

/-- `for (init; cond; step) body` over the locals `σ`; `continue` is the end of `body`. -/
def cfor {σ : Type} (cond : σ → M Bool) (step : σ → M σ) (body : σ → M σ) (s : σ) : M σ :=
  cwhile (fun s => do pure (← cond s, s)) (fun s => do step (← body s)) s

/-- `s` is a live deflate state; its block number. -/
def sid (s : DeflateStatePtr) : M Nat := do
  let _ ← ldDeflateState s
  match s with
  | some (.tab i) => pure i
  | none => ub "null dereference (deflate_state)"

/-- `s->f` for a scalar field: the whole record. -/
def rd (s : DeflateStatePtr) : M DeflateState := ldDeflateState s
/-- `s->f = v`, as a load, a record update and a store. -/
def md (s : DeflateStatePtr) (f : DeflateState → DeflateState) : M Unit := do
  stDeflateState s (f (← ldDeflateState s))

/-- `s->dyn_ltree` -/
def pLtree (s : DeflateStatePtr) : M CtDataPtr := do pure (.ref (.dstate_dyn_ltree (← sid s)) 0)
/-- `s->dyn_dtree` -/
def pDtree (s : DeflateStatePtr) : M CtDataPtr := do pure (.ref (.dstate_dyn_dtree (← sid s)) 0)
/-- `s->bl_tree` -/
def pBltree (s : DeflateStatePtr) : M CtDataPtr := do pure (.ref (.dstate_bl_tree (← sid s)) 0)
/-- `s->heap` -/
def pHeap (s : DeflateStatePtr) : M IPtr := do pure (.ref (.dstate_heap (← sid s)) 0)
/-- `s->depth` -/
def pDepth (s : DeflateStatePtr) : M BPtr := do pure (.ref (.dstate_depth (← sid s)) 0)
/-- `s->bl_count` -/
def pBlCount (s : DeflateStatePtr) : M WPtr := do pure (.ref (.dstate_bl_count (← sid s)) 0)
/-- `&s->l_desc`, `&s->d_desc`, `&s->bl_desc` -/
def pLdesc (s : DeflateStatePtr) : M TreeDescPtr := do pure (some (.in_dstate_l_desc (← sid s)))
def pDdesc (s : DeflateStatePtr) : M TreeDescPtr := do pure (some (.in_dstate_d_desc (← sid s)))
def pBldesc (s : DeflateStatePtr) : M TreeDescPtr := do pure (some (.in_dstate_bl_desc (← sid s)))

/-- `p[i] = v` -/
def setAt {R T : Type} [Space Heap R T] (p : Ptr R) (i : Int) (v : T) : M Unit := do
  Ptr.store (← Ptr.add p i) v
/-- `s->heap[i]` -/
def heapAt (s : DeflateStatePtr) (i : Int32) : M Int32 := do Ptr.index (← pHeap s) i.toInt
/-- `s->heap[i] = v` -/
def heapSet (s : DeflateStatePtr) (i : Int32) (v : Int32) : M Unit := do setAt (← pHeap s) i.toInt v

/-- `tree[i].Freq` / `.Code` -/
def getFc (tree : CtDataPtr) (i : Int) : M UInt16 := do pure (← Ptr.index tree i).fc
/-- `tree[i].Dad` / `.Len` -/
def getDl (tree : CtDataPtr) (i : Int) : M UInt16 := do pure (← Ptr.index tree i).dl
/-- `tree[i].Freq = v` -/
def setFc (tree : CtDataPtr) (i : Int) (v : UInt16) : M Unit := do
  let p ← Ptr.add tree i
  let e ← Ptr.load p
  Ptr.store p { e with fc := v }
/-- `tree[i].Len = v` -/
def setDl (tree : CtDataPtr) (i : Int) (v : UInt16) : M Unit := do
  let p ← Ptr.add tree i
  let e ← Ptr.load p
  Ptr.store p { e with dl := v }

/-- `bl_order[i]` (a static array; an index outside it is undefined). -/
def blOrder (i : Int) : M UInt8 :=
  if 0 ≤ i ∧ i < 19 then pure bl_order[i.toNat]! else ub "bl_order index outside its array"

/-! ## Macros of `deflate.h` and `trees.c` -/

/-- `put_byte(s, c)`: `{s->pending_buf[s->pending++] = (Bytef)(c);}` -/
def put_byte (s : DeflateStatePtr) (c : UInt8) : M Unit := do
  let d ← rd s
  let p ← Ptr.add d.pending_buf (d.pending.toNat : Int)
  store8 p c
  md s fun d => { d with pending := d.pending + 1 }

/-- `put_short(s, w)`: `{ put_byte(s, (uch)((w) & 0xff)); put_byte(s, (uch)((ush)(w) >> 8)); }` -/
def put_short (s : DeflateStatePtr) (w : UInt16) : M Unit := do
  put_byte s (w &&& 0xff).toUInt8
  put_byte s (w >>> 8).toUInt8

/-- `(ush)val << s->bi_valid` (an `int` shift: the count must be in `0..31` and the result must fit). -/
def shlUs (val : Int32) (c : Int32) : M Nat :=
  if c.toInt < 0 ∨ 31 < c.toInt then ub "invalid shift count"
  else if (i2us val).toNat * 2 ^ c.toInt.toNat ≥ 2147483648 then ub "signed overflow in left shift"
  else pure ((i2us val).toNat * 2 ^ c.toInt.toNat)

/-- `(ush)val >> c` -/
def shrUs (val : Int32) (c : Int32) : M UInt16 :=
  if c.toInt < 0 ∨ 31 < c.toInt then ub "invalid shift count"
  else pure (UInt16.ofNat ((i2us val).toNat >>> c.toInt.toNat))

/-- `send_bits(s, value, length)` (the macro of `trees.c`, `Buf_size` = 16). -/
def send_bits (s : DeflateStatePtr) (value : Int32) (length : Int32) : M Unit := do
  -- int len = length;
  let len := length
  let d ← rd s
  if d.bi_valid > (← isub Buf_size len) then
    -- int val = (int)value;
    let val := value
    -- s->bi_buf |= (ush)val << s->bi_valid;
    let sh ← shlUs val d.bi_valid
    md s fun d => { d with bi_buf := UInt16.ofNat (d.bi_buf.toNat ||| sh) }
    -- put_short(s, s->bi_buf);
    put_short s (← rd s).bi_buf
    -- s->bi_buf = (ush)val >> (Buf_size - s->bi_valid);
    let c ← isub Buf_size (← rd s).bi_valid
    let r ← shrUs val c
    md s fun d => { d with bi_buf := r }
    -- s->bi_valid += len - Buf_size;
    let t ← isub len Buf_size
    let nv ← iadd (← rd s).bi_valid t
    md s fun d => { d with bi_valid := nv }
  else
    -- s->bi_buf |= (ush)(value) << s->bi_valid;
    let sh ← shlUs value d.bi_valid
    md s fun d => { d with bi_buf := UInt16.ofNat (d.bi_buf.toNat ||| sh) }
    -- s->bi_valid += len;
    let nv ← iadd (← rd s).bi_valid len
    md s fun d => { d with bi_valid := nv }

/-- `send_code(s, c, tree)`: `send_bits(s, tree[c].Code, tree[c].Len)`. -/
def send_code (s : DeflateStatePtr) (c : Int) (tree : CtDataPtr) : M Unit := do
  let len := u16i (← getDl tree c)
  let code := u16i (← getFc tree c)
  send_bits s code len

/-- `d_code(dist)`: `((dist) < 256 ? _dist_code[dist] : _dist_code[256+((dist)>>7)])`, `dist` unsigned. -/
def d_code (dist : UInt32) : M UInt8 :=
  if dist < 256 then Ptr.index (.ref .st_dist_code 0 : BPtr) (dist.toNat : Int)
  else Ptr.index (.ref .st_dist_code 0 : BPtr) (((256 : UInt32) + (dist >>> 7)).toNat : Int)

/-- `smaller(tree, n, m, depth)` -/
def smaller (tree : CtDataPtr) (n m : Int32) (depth : BPtr) : M Bool := do
  let fn ← getFc tree n.toInt
  let fm ← getFc tree m.toInt
  if fn < fm then return true
  if fn == fm then
    let dn ← Ptr.index depth n.toInt
    let dm ← Ptr.index depth m.toInt
    return decide (dn ≤ dm)
  return false

/-! ## Functions -/

/-- `local unsigned bi_reverse(unsigned code, int len)` -/
def bi_reverse (code : UInt32) (len : Int32) : M UInt32 := do
  -- unsigned res = 0;
  -- do { res |= code & 1; code >>= 1, res <<= 1; } while (--len > 0);
  let (_, res, _) ← cdoWhile (σ := UInt32 × UInt32 × Int32)
    (fun (code, res, len) => do
      let res := res ||| (code &&& 1)
      pure (code >>> 1, res <<< 1, len))
    (fun (code, res, len) => do
      let len ← isub len 1
      pure (decide (len.toInt > 0), (code, res, len)))
    (code, 0, len)
  return res >>> 1

/-- `local void bi_flush(deflate_state *s)` -/
def bi_flush (s : DeflateStatePtr) : M Unit := do
  let d ← rd s
  if d.bi_valid == 16 then
    put_short s (← rd s).bi_buf
    md s fun d => { d with bi_buf := 0 }
    md s fun d => { d with bi_valid := 0 }
  else if d.bi_valid ≥ 8 then
    put_byte s (← rd s).bi_buf.toUInt8
    md s fun d => { d with bi_buf := d.bi_buf >>> 8 }
    let nv ← isub (← rd s).bi_valid 8
    md s fun d => { d with bi_valid := nv }

/-- `local void bi_windup(deflate_state *s)` -/
def bi_windup (s : DeflateStatePtr) : M Unit := do
  let d ← rd s
  if d.bi_valid > 8 then
    put_short s (← rd s).bi_buf
  else if d.bi_valid > 0 then
    put_byte s (← rd s).bi_buf.toUInt8
  -- s->bi_used = ((s->bi_valid - 1) & 7) + 1;
  let t ← isub (← rd s).bi_valid 1
  let u ← iadd (t &&& 7) 1
  md s fun d => { d with bi_used := u }
  md s fun d => { d with bi_buf := 0 }
  md s fun d => { d with bi_valid := 0 }

/-- `local void gen_codes(ct_data *tree, int max_code, ushf *bl_count)` -/
def gen_codes (tree : CtDataPtr) (max_code : Int32) (bl_count : WPtr) : M Unit := do
  -- ush next_code[MAX_BITS+1]; unsigned code = 0;
  let next_code0 : Array UInt16 := Array.replicate 16 0
  -- for (bits = 1; bits <= MAX_BITS; bits++) { code = (code + bl_count[bits - 1]) << 1; next_code[bits] = (ush)code; }
  let (_, _, next_code) ← cfor (σ := Int32 × UInt32 × Array UInt16)
    (fun (bits, _, _) => pure (decide (bits.toInt ≤ MAX_BITS.toInt)))
    (fun (bits, code, nc) => do pure (← iadd bits 1, code, nc))
    (fun (bits, code, nc) => do
      let b ← Ptr.index bl_count (← isub bits 1).toInt
      let code := (code + b.toUInt32) <<< 1
      if bits.toInt < 0 ∨ nc.size ≤ bits.toInt.toNat then ub "next_code index outside its array"
      pure (bits, code, nc.set! bits.toInt.toNat code.toUInt16))
    (1, 0, next_code0)
  -- for (n = 0; n <= max_code; n++) { int len = tree[n].Len; if (len == 0) continue;
  --   tree[n].Code = (ush)bi_reverse(next_code[len]++, len); }
  let _ ← cfor (σ := Int32 × Array UInt16)
    (fun (n, _) => pure (decide (n.toInt ≤ max_code.toInt)))
    (fun (n, nc) => do pure (← iadd n 1, nc))
    (fun (n, nc) => do
      let len := u16i (← getDl tree n.toInt)
      if len == 0 then return (n, nc)
      let li := len.toInt.toNat
      if nc.size ≤ li then ub "next_code index outside its array"
      let old := nc[li]!
      let nc := nc.set! li (old + 1)
      let r ← bi_reverse old.toUInt32 len
      setFc tree n.toInt r.toUInt16
      pure (n, nc))
    (0, next_code)

/-- `local void tr_static_init(void)`: the body is inside `#if defined(GEN_TREES_H) || !defined(STDC)`, which is
false in the default build, so the function is empty. -/
def tr_static_init : M Unit := pure ()

/-- `local void init_block(deflate_state *s)` -/
def init_block (s : DeflateStatePtr) : M Unit := do
  -- for (n = 0; n < L_CODES; n++) s->dyn_ltree[n].Freq = 0;
  let _ ← cfor (σ := Int32) (fun n => pure (decide (n.toInt < L_CODES.toInt))) (fun n => iadd n 1)
    (fun n => do setFc (← pLtree s) n.toInt 0; pure n) 0
  let _ ← cfor (σ := Int32) (fun n => pure (decide (n.toInt < D_CODES.toInt))) (fun n => iadd n 1)
    (fun n => do setFc (← pDtree s) n.toInt 0; pure n) 0
  let _ ← cfor (σ := Int32) (fun n => pure (decide (n.toInt < BL_CODES.toInt))) (fun n => iadd n 1)
    (fun n => do setFc (← pBltree s) n.toInt 0; pure n) 0
  -- s->dyn_ltree[END_BLOCK].Freq = 1;
  setFc (← pLtree s) END_BLOCK.toInt 1
  -- s->opt_len = s->static_len = 0L;
  md s fun d => { d with static_len := 0 }
  md s fun d => { d with opt_len := 0 }
  -- s->sym_next = s->matches = 0;
  md s fun d => { d with «matches» := 0 }
  md s fun d => { d with sym_next := 0 }

/-- `void ZLIB_INTERNAL _tr_init(deflate_state *s)` -/
def «_tr_init» (s : DeflateStatePtr) : M Unit := do
  tr_static_init
  let id ← sid s
  md s fun d => { d with l_desc := { d.l_desc with dyn_tree := .ref (.dstate_dyn_ltree id) 0 } }
  md s fun d => { d with l_desc := { d.l_desc with stat_desc := some .st_static_l_desc } }
  md s fun d => { d with d_desc := { d.d_desc with dyn_tree := .ref (.dstate_dyn_dtree id) 0 } }
  md s fun d => { d with d_desc := { d.d_desc with stat_desc := some .st_static_d_desc } }
  md s fun d => { d with bl_desc := { d.bl_desc with dyn_tree := .ref (.dstate_bl_tree id) 0 } }
  md s fun d => { d with bl_desc := { d.bl_desc with stat_desc := some .st_static_bl_desc } }
  md s fun d => { d with bi_buf := 0 }
  md s fun d => { d with bi_valid := 0 }
  md s fun d => { d with bi_used := 0 }
  -- Initialize the first block of the first file:
  init_block s

/-- `local void pqdownheap(deflate_state *s, ct_data *tree, int k)` -/
def pqdownheap (s : DeflateStatePtr) (tree : CtDataPtr) (k : Int32) : M Unit := do
  -- int v = s->heap[k]; int j = k << 1;
  let v ← heapAt s k
  let j ← shl1 k
  -- while (j <= s->heap_len) { ... }   (the flag is the `break`)
  let (k, _, _) ← cwhile (σ := Int32 × Int32 × Bool)
    (fun (k, j, brk) => do
      if brk then return (false, (k, j, brk))
      pure (decide (j.toInt ≤ (← rd s).heap_len.toInt), (k, j, brk)))
    (fun (k, j, _) => do
      let mut jj := j
      -- if (j < s->heap_len && smaller(tree, s->heap[j + 1], s->heap[j], s->depth)) j++;
      if jj.toInt < (← rd s).heap_len.toInt then
        let a ← heapAt s (← iadd jj 1)
        let b ← heapAt s jj
        if ← smaller tree a b (← pDepth s) then jj ← iadd jj 1
      -- if (smaller(tree, v, s->heap[j], s->depth)) break;
      let hj ← heapAt s jj
      if ← smaller tree v hj (← pDepth s) then return (k, jj, true)
      -- s->heap[k] = s->heap[j];  k = j;
      heapSet s k hj
      -- j <<= 1;
      let j2 ← shl1 jj
      return (jj, j2, false))
    (k, j, false)
  -- s->heap[k] = v;
  heapSet s k v

/-- `pqremove(s, tree, top)`: `{ top = s->heap[SMALLEST]; s->heap[SMALLEST] = s->heap[s->heap_len--];
pqdownheap(s, tree, SMALLEST); }`; returns `top`. -/
def pqremove (s : DeflateStatePtr) (tree : CtDataPtr) : M Int32 := do
  let top ← heapAt s 1
  -- s->heap[SMALLEST] = s->heap[s->heap_len--];
  let hl := (← rd s).heap_len
  let v ← heapAt s hl
  let hl' ← isub hl 1
  md s fun d => { d with heap_len := hl' }
  heapSet s 1 v
  pqdownheap s tree 1
  return top

/-- `local void gen_bitlen(deflate_state *s, tree_desc *desc)` -/
def gen_bitlen (s : DeflateStatePtr) (desc : TreeDescPtr) : M Unit := do
  let dd ← ldTreeDesc desc
  let tree := dd.dyn_tree
  let max_code := dd.max_code
  let sd ← ldStaticTreeDesc dd.stat_desc
  let stree := sd.static_tree
  let extra := sd.extra_bits
  let base := sd.extra_base
  let max_length := sd.max_length
  -- for (bits = 0; bits <= MAX_BITS; bits++) s->bl_count[bits] = 0;
  let _ ← cfor (σ := Int32) (fun b => pure (decide (b.toInt ≤ MAX_BITS.toInt))) (fun b => iadd b 1)
    (fun b => do setAt (← pBlCount s) b.toInt 0; pure b) 0
  -- tree[s->heap[s->heap_max]].Len = 0;
  setDl tree (← heapAt s (← rd s).heap_max).toInt 0
  -- for (h = s->heap_max + 1; h < HEAP_SIZE; h++) { ... }     state (h, overflow)
  let h0 ← iadd (← rd s).heap_max 1
  let (h, overflow) ← cfor (σ := Int32 × Int32)
    (fun (h, _) => pure (decide (h.toInt < HEAP_SIZE.toInt)))
    (fun (h, o) => do pure (← iadd h 1, o))
    (fun (h, overflow) => do
      let n ← heapAt s h
      -- bits = tree[tree[n].Dad].Len + 1;
      let mut bits ← iadd (u16i (← getDl tree (u16i (← getDl tree n.toInt)).toInt)) 1
      let mut overflow := overflow
      -- if (bits > max_length) bits = max_length, overflow++;
      if bits.toInt > max_length.toInt then
        bits := max_length
        overflow ← iadd overflow 1
      -- tree[n].Len = (ush)bits;
      setDl tree n.toInt (i2us bits)
      -- if (n > max_code) continue;
      if n.toInt > max_code.toInt then return (h, overflow)
      -- s->bl_count[bits]++;
      let bc ← pBlCount s
      setAt bc bits.toInt ((← Ptr.index bc bits.toInt) + 1)
      -- xbits = 0; if (n >= base) xbits = extra[n - base];
      let mut xbits : Int32 := 0
      if n.toInt ≥ base.toInt then xbits ← Ptr.index extra (← isub n base).toInt
      -- f = tree[n].Freq;
      let f ← getFc tree n.toInt
      -- s->opt_len += (ulg)f * (unsigned)(bits + xbits);
      let t ← iadd bits xbits
      md s fun d => { d with opt_len := d.opt_len + f.toUInt64 * (i2u t).toUInt64 }
      -- if (stree) s->static_len += (ulg)f * (unsigned)(stree[n].Len + xbits);
      if stree != .null then
        let t2 ← iadd (u16i (← getDl stree n.toInt)) xbits
        md s fun d => { d with static_len := d.static_len + f.toUInt64 * (i2u t2).toUInt64 }
      return (h, overflow))
    (h0, 0)
  -- if (overflow == 0) return;
  if overflow == 0 then return
  -- do { bits = max_length-1; while (bl_count[bits]==0) bits--; ... overflow -= 2; } while (overflow > 0);
  let _ ← cdoWhile (σ := Int32)
    (fun overflow => do
      let bits ← isub max_length 1
      let bc ← pBlCount s
      let bits ← cwhile (σ := Int32)
        (fun b => do pure (decide ((← Ptr.index bc b.toInt) == 0), b))
        (fun b => isub b 1) bits
      setAt bc bits.toInt ((← Ptr.index bc bits.toInt) - 1)
      let b1 ← iadd bits 1
      setAt bc b1.toInt ((← Ptr.index bc b1.toInt) + 2)
      setAt bc max_length.toInt ((← Ptr.index bc max_length.toInt) - 1)
      isub overflow 2)
    (fun overflow => pure (decide (overflow.toInt > 0), overflow))
    overflow
  -- for (bits = max_length; bits != 0; bits--) { n = s->bl_count[bits]; while (n != 0) { ... } }
  let _ ← cfor (σ := Int32 × Int32)
    (fun (bits, _) => pure (bits != 0))
    (fun (bits, h) => do pure (← isub bits 1, h))
    (fun (bits, h) => do
      let n0 := u16i (← Ptr.index (← pBlCount s) bits.toInt)
      let (_, h) ← cwhile (σ := Int32 × Int32)
        (fun (n, h) => pure (n != 0, (n, h)))
        (fun (n, h) => do
          -- m = s->heap[--h];
          let h ← isub h 1
          let m ← heapAt s h
          -- if (m > max_code) continue;
          if m.toInt > max_code.toInt then return (n, h)
          -- if ((unsigned) tree[m].Len != (unsigned) bits) {...}
          let lm ← getDl tree m.toInt
          if lm.toUInt32 != i2u bits then
            -- s->opt_len += ((ulg)bits - tree[m].Len) * tree[m].Freq;
            let fm ← getFc tree m.toInt
            md s fun d => { d with opt_len := d.opt_len + (i2ul bits - lm.toUInt64) * fm.toUInt64 }
            setDl tree m.toInt (i2us bits)
          -- n--;
          pure (← isub n 1, h))
        (n0, h)
      pure (bits, h))
    (max_length, h)

/-- `local void build_tree(deflate_state *s, tree_desc *desc)` -/
def build_tree (s : DeflateStatePtr) (desc : TreeDescPtr) : M Unit := do
  let dd ← ldTreeDesc desc
  let tree := dd.dyn_tree
  let sd ← ldStaticTreeDesc dd.stat_desc
  let stree := sd.static_tree
  let elems := sd.elems
  -- int max_code = -1;
  -- s->heap_len = 0, s->heap_max = HEAP_SIZE;
  md s fun d => { d with heap_len := 0 }
  md s fun d => { d with heap_max := HEAP_SIZE }
  -- for (n = 0; n < elems; n++) { if (tree[n].Freq != 0) {...} else tree[n].Len = 0; }
  let max_code ← cfor (σ := Int32 × Int32)
    (fun (n, _) => pure (decide (n.toInt < elems.toInt)))
    (fun (n, mc) => do pure (← iadd n 1, mc))
    (fun (n, mc) => do
      if (← getFc tree n.toInt) != 0 then
        -- s->heap[++(s->heap_len)] = max_code = n;
        let hl ← iadd (← rd s).heap_len 1
        md s fun d => { d with heap_len := hl }
        heapSet s hl n
        -- s->depth[n] = 0;
        setAt (← pDepth s) n.toInt 0
        pure (n, n)
      else
        setDl tree n.toInt 0
        pure (n, mc))
    (0, -1)
  let mut max_code := max_code.2
  -- while (s->heap_len < 2) { ... }
  let mc ← cwhile (σ := Int32)
    (fun mc => do pure (decide ((← rd s).heap_len.toInt < 2), mc))
    (fun mc => do
      -- node = s->heap[++(s->heap_len)] = (max_code < 2 ? ++max_code : 0);
      let mut mc := mc
      let mut val : Int32 := 0
      if mc.toInt < 2 then
        mc ← iadd mc 1
        val := mc
      let hl ← iadd (← rd s).heap_len 1
      md s fun d => { d with heap_len := hl }
      heapSet s hl val
      let node := val
      -- tree[node].Freq = 1; s->depth[node] = 0;
      setFc tree node.toInt 1
      setAt (← pDepth s) node.toInt 0
      -- s->opt_len--; if (stree) s->static_len -= stree[node].Len;
      md s fun d => { d with opt_len := d.opt_len - 1 }
      if stree != .null then
        let l ← getDl stree node.toInt
        md s fun d => { d with static_len := d.static_len - l.toUInt64 }
      pure mc)
    max_code
  max_code := mc
  -- desc->max_code = max_code;
  stTreeDesc desc { (← ldTreeDesc desc) with max_code := max_code }
  -- for (n = s->heap_len/2; n >= 1; n--) pqdownheap(s, tree, n);
  let _ ← cfor (σ := Int32) (fun n => pure (decide (n.toInt ≥ 1))) (fun n => isub n 1)
    (fun n => do pqdownheap s tree n; pure n) ((← rd s).heap_len / 2)
  -- node = elems;
  -- do { ... } while (s->heap_len >= 2);
  let _ ← cdoWhile (σ := Int32)
    (fun node => do
      -- pqremove(s, tree, n);  m = s->heap[SMALLEST];
      let n ← pqremove s tree
      let m ← heapAt s 1
      -- s->heap[--(s->heap_max)] = n;  s->heap[--(s->heap_max)] = m;
      let hm ← isub (← rd s).heap_max 1
      md s fun d => { d with heap_max := hm }
      heapSet s hm n
      let hm ← isub (← rd s).heap_max 1
      md s fun d => { d with heap_max := hm }
      heapSet s hm m
      -- tree[node].Freq = tree[n].Freq + tree[m].Freq;
      let fn ← getFc tree n.toInt
      let fm ← getFc tree m.toInt
      setFc tree node.toInt (fn + fm)
      -- s->depth[node] = (uch)((s->depth[n] >= s->depth[m] ? s->depth[n] : s->depth[m]) + 1);
      let dp ← pDepth s
      let dn ← Ptr.index dp n.toInt
      let dm ← Ptr.index dp m.toInt
      let mx := if dn ≥ dm then dn else dm
      setAt dp node.toInt (mx + 1)
      -- tree[n].Dad = tree[m].Dad = (ush)node;
      setDl tree m.toInt (i2us node)
      setDl tree n.toInt (i2us node)
      -- s->heap[SMALLEST] = node++;
      heapSet s 1 node
      let node' ← iadd node 1
      pqdownheap s tree 1
      pure node')
    (fun node => do pure (decide ((← rd s).heap_len.toInt ≥ 2), node))
    elems
  -- s->heap[--(s->heap_max)] = s->heap[SMALLEST];
  let top ← heapAt s 1
  let hm ← isub (← rd s).heap_max 1
  md s fun d => { d with heap_max := hm }
  heapSet s hm top
  -- gen_bitlen(s, (tree_desc *)desc);
  gen_bitlen s desc
  -- gen_codes ((ct_data *)tree, max_code, s->bl_count);
  gen_codes tree max_code (← pBlCount s)

/-- `local void scan_tree(deflate_state *s, ct_data *tree, int max_code)` -/
def scan_tree (s : DeflateStatePtr) (tree : CtDataPtr) (max_code : Int32) : M Unit := do
  -- locals: n, prevlen, curlen, nextlen, count, max_count, min_count
  let nextlen0 := u16i (← getDl tree 0)
  let (mx0, mn0) : Int32 × Int32 := if nextlen0 == 0 then (138, 3) else (7, 4)
  -- tree[max_code + 1].Len = (ush)0xffff;
  setDl tree (← iadd max_code 1).toInt 0xffff
  let _ ← cfor (σ := Int32 × Int32 × Int32 × Int32 × Int32 × Int32 × Int32)
    (fun (n, _) => pure (decide (n.toInt ≤ max_code.toInt)))
    (fun (n, r) => do pure (← iadd n 1, r))
    (fun (n, prevlen, nextlen, count, max_count, min_count, _) => do
      -- curlen = nextlen; nextlen = tree[n + 1].Len;
      let curlen := nextlen
      let nextlen := u16i (← getDl tree (← iadd n 1).toInt)
      -- if (++count < max_count && curlen == nextlen) continue;
      let count ← iadd count 1
      if count.toInt < max_count.toInt ∧ curlen == nextlen then
        return (n, prevlen, nextlen, count, max_count, min_count, 0)
      let blt ← pBltree s
      if count.toInt < min_count.toInt then
        -- s->bl_tree[curlen].Freq += (ush)count;
        setFc blt curlen.toInt ((← getFc blt curlen.toInt) + i2us count)
      else if curlen != 0 then
        -- if (curlen != prevlen) s->bl_tree[curlen].Freq++;
        if curlen != prevlen then setFc blt curlen.toInt ((← getFc blt curlen.toInt) + 1)
        setFc blt REP_3_6.toInt ((← getFc blt REP_3_6.toInt) + 1)
      else if count.toInt ≤ 10 then
        setFc blt REPZ_3_10.toInt ((← getFc blt REPZ_3_10.toInt) + 1)
      else
        setFc blt REPZ_11_138.toInt ((← getFc blt REPZ_11_138.toInt) + 1)
      -- count = 0; prevlen = curlen;
      let count : Int32 := 0
      let prevlen := curlen
      let (max_count, min_count) : Int32 × Int32 :=
        if nextlen == 0 then (138, 3) else if curlen == nextlen then (6, 3) else (7, 4)
      return (n, prevlen, nextlen, count, max_count, min_count, 0))
    (0, -1, nextlen0, 0, mx0, mn0, 0)

/-- `local void send_tree(deflate_state *s, ct_data *tree, int max_code)` -/
def send_tree (s : DeflateStatePtr) (tree : CtDataPtr) (max_code : Int32) : M Unit := do
  let nextlen0 := u16i (← getDl tree 0)
  -- /* tree[max_code + 1].Len = -1; */  /* guard already set */
  let (mx0, mn0) : Int32 × Int32 := if nextlen0 == 0 then (138, 3) else (7, 4)
  let _ ← cfor (σ := Int32 × Int32 × Int32 × Int32 × Int32 × Int32 × Int32)
    (fun (n, _) => pure (decide (n.toInt ≤ max_code.toInt)))
    (fun (n, r) => do pure (← iadd n 1, r))
    (fun (n, prevlen, nextlen, count, max_count, min_count, _) => do
      let curlen := nextlen
      let nextlen := u16i (← getDl tree (← iadd n 1).toInt)
      let mut count ← iadd count 1
      if count.toInt < max_count.toInt ∧ curlen == nextlen then
        return (n, prevlen, nextlen, count, max_count, min_count, 0)
      if count.toInt < min_count.toInt then
        -- do { send_code(s, curlen, s->bl_tree); } while (--count != 0);
        count ← cdoWhile (σ := Int32)
          (fun c => do send_code s curlen.toInt (← pBltree s); pure c)
          (fun c => do let c ← isub c 1; pure (c != 0, c))
          count
      else if curlen != 0 then
        if curlen != prevlen then
          send_code s curlen.toInt (← pBltree s)
          count ← isub count 1
        send_code s REP_3_6.toInt (← pBltree s)
        send_bits s (← isub count 3) 2
      else if count.toInt ≤ 10 then
        send_code s REPZ_3_10.toInt (← pBltree s)
        send_bits s (← isub count 3) 3
      else
        send_code s REPZ_11_138.toInt (← pBltree s)
        send_bits s (← isub count 11) 7
      -- count = 0; prevlen = curlen;
      count := 0
      let prevlen := curlen
      let (max_count, min_count) : Int32 × Int32 :=
        if nextlen == 0 then (138, 3) else if curlen == nextlen then (6, 3) else (7, 4)
      return (n, prevlen, nextlen, count, max_count, min_count, 0))
    (0, -1, nextlen0, 0, mx0, mn0, 0)

/-- `local int build_bl_tree(deflate_state *s)` -/
def build_bl_tree (s : DeflateStatePtr) : M Int32 := do
  -- scan_tree(s, (ct_data *)s->dyn_ltree, s->l_desc.max_code);
  scan_tree s (← pLtree s) (← rd s).l_desc.max_code
  scan_tree s (← pDtree s) (← rd s).d_desc.max_code
  -- build_tree(s, (tree_desc *)(&(s->bl_desc)));
  build_tree s (← pBldesc s)
  -- for (max_blindex = BL_CODES-1; max_blindex >= 3; max_blindex--) { if (...Len != 0) break; }
  let (mb, _) ← cwhile (σ := Int32 × Bool)
    (fun (mb, brk) => pure (!brk && decide (mb.toInt ≥ 3), (mb, brk)))
    (fun (mb, _) => do
      if (← getDl (← pBltree s) (u8i (← blOrder mb.toInt)).toInt) != 0 then return (mb, true)
      pure (← isub mb 1, false))
    (BL_CODES - 1, false)
  -- s->opt_len += 3*((ulg)max_blindex + 1) + 5 + 5 + 4;
  md s fun d => { d with opt_len := d.opt_len + (3 * (i2ul mb + 1) + 5 + 5 + 4) }
  return mb

/-- `local void send_all_trees(deflate_state *s, int lcodes, int dcodes, int blcodes)` -/
def send_all_trees (s : DeflateStatePtr) (lcodes dcodes blcodes : Int32) : M Unit := do
  send_bits s (← isub lcodes 257) 5
  send_bits s (← isub dcodes 1) 5
  send_bits s (← isub blcodes 4) 4
  -- for (rank = 0; rank < blcodes; rank++) send_bits(s, s->bl_tree[bl_order[rank]].Len, 3);
  let _ ← cfor (σ := Int32) (fun r => pure (decide (r.toInt < blcodes.toInt))) (fun r => iadd r 1)
    (fun r => do
      let l ← getDl (← pBltree s) (u8i (← blOrder r.toInt)).toInt
      send_bits s (u16i l) 3
      pure r) 0
  send_tree s (← pLtree s) (← isub lcodes 1)
  send_tree s (← pDtree s) (← isub dcodes 1)

/-- `void ZLIB_INTERNAL _tr_stored_block(deflate_state *s, charf *buf, ulg stored_len, int last)` -/
def «_tr_stored_block» (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) : M Unit := do
  -- send_bits(s, (STORED_BLOCK<<1) + last, 3);
  send_bits s (← iadd (STORED_BLOCK <<< 1) last) 3
  bi_windup s
  put_short s stored_len.toUInt16
  put_short s (~~~stored_len).toUInt16
  -- if (stored_len) zmemcpy(s->pending_buf + s->pending, (Bytef *)buf, stored_len);
  if stored_len != 0 then
    let d ← rd s
    let dst ← Ptr.add d.pending_buf (d.pending.toNat : Int)
    memcpyB dst buf stored_len.toNat
  md s fun d => { d with pending := d.pending + stored_len }

/-- `void ZLIB_INTERNAL _tr_flush_bits(deflate_state *s)` -/
def «_tr_flush_bits» (s : DeflateStatePtr) : M Unit := bi_flush s

/-- `void ZLIB_INTERNAL _tr_align(deflate_state *s)` -/
def «_tr_align» (s : DeflateStatePtr) : M Unit := do
  send_bits s (STATIC_TREES <<< 1) 3
  send_code s END_BLOCK.toInt (.ref .st_static_ltree 0)
  bi_flush s

/-- `local void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)` -/
def compress_block (s : DeflateStatePtr) (ltree dtree : CtDataPtr) : M Unit := do
  let lcp : BPtr := .ref .st_length_code 0
  -- if (s->sym_next != 0) do { ... } while (sx < s->sym_next);
  if (← rd s).sym_next != 0 then
    let _ ← cdoWhile (σ := UInt32)
      (fun sx => do
        -- dist = s->sym_buf[sx++] & 0xff;
        let sb := (← rd s).sym_buf
        let b0 ← Ptr.index sb sx.toNat
        let sx := sx + 1
        let dist : UInt32 := b0.toUInt32 &&& 0xff
        -- dist += (unsigned)(s->sym_buf[sx++] & 0xff) << 8;
        let b1 ← Ptr.index sb sx.toNat
        let sx := sx + 1
        let dist := dist + ((b1.toUInt32 &&& 0xff) <<< 8)
        -- lc = s->sym_buf[sx++];
        let b2 ← Ptr.index sb sx.toNat
        let sx := sx + 1
        let lc := u8i b2
        if dist == 0 then
          send_code s lc.toInt ltree
        else
          -- code = _length_code[lc];
          let code := (← Ptr.index lcp lc.toInt).toUInt32
          -- send_code(s, code + LITERALS + 1, ltree);
          send_code s (code + (i2u LITERALS) + 1).toNat ltree
          -- extra = extra_lbits[code];
          let extra ← Ptr.index (.ref .st_extra_lbits 0 : IPtr) code.toNat
          let mut lc := lc
          if extra != 0 then
            lc ← isub lc (← Ptr.index (.ref .st_base_length 0 : IPtr) code.toNat)
            send_bits s lc extra
          -- dist--; code = d_code(dist);
          let dist := dist - 1
          let code := (← d_code dist).toUInt32
          send_code s code.toNat dtree
          let extra ← Ptr.index (.ref .st_extra_dbits 0 : IPtr) code.toNat
          if extra != 0 then
            let dist := dist - (i2u (← Ptr.index (.ref .st_base_dist 0 : IPtr) code.toNat))
            send_bits s (u2i dist) extra
        pure sx)
      (fun sx => do pure (decide (sx < (← rd s).sym_next), sx))
      0
  -- send_code(s, END_BLOCK, ltree);
  send_code s END_BLOCK.toInt ltree

/-- `local int detect_data_type(deflate_state *s)` -/
def detect_data_type (s : DeflateStatePtr) : M Int32 := do
  -- unsigned long block_mask = 0xf3ffc07fUL;
  -- for (n = 0; n <= 31; n++, block_mask >>= 1) if ((block_mask & 1) && ...Freq != 0) return Z_BINARY;
  let (_, _, r) ← cwhile (σ := Int32 × UInt64 × Option Int32)
    (fun (n, bm, r) => pure (r.isNone && decide (n.toInt ≤ 31), (n, bm, r)))
    (fun (n, bm, _) => do
      if (bm &&& 1) != 0 ∧ (← getFc (← pLtree s) n.toInt) != 0 then return (n, bm, some Z_BINARY)
      pure (← iadd n 1, bm >>> 1, none))
    (0, 0xf3ffc07f, none)
  if let some v := r then return v
  -- if (dyn_ltree[9].Freq != 0 || dyn_ltree[10].Freq != 0 || dyn_ltree[13].Freq != 0) return Z_TEXT;
  if (← getFc (← pLtree s) 9) != 0 ∨ (← getFc (← pLtree s) 10) != 0 ∨ (← getFc (← pLtree s) 13) != 0 then
    return Z_TEXT
  -- for (n = 32; n < LITERALS; n++) if (s->dyn_ltree[n].Freq != 0) return Z_TEXT;
  let (_, r) ← cwhile (σ := Int32 × Option Int32)
    (fun (n, r) => pure (r.isNone && decide (n.toInt < LITERALS.toInt), (n, r)))
    (fun (n, _) => do
      if (← getFc (← pLtree s) n.toInt) != 0 then return (n, some Z_TEXT)
      pure (← iadd n 1, none))
    (32, none)
  if let some v := r then return v
  return Z_BINARY

/-- `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf, ulg stored_len, int last)` -/
def «_tr_flush_block» (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) : M Unit := do
  -- int max_blindex = 0;
  let mut max_blindex : Int32 := 0
  let mut opt_lenb : UInt64 := 0
  let mut static_lenb : UInt64 := 0
  if (← rd s).level.toInt > 0 then
    -- if (s->strm->data_type == Z_UNKNOWN) s->strm->data_type = detect_data_type(s);
    let strm := (← rd s).strm
    if (← ldZStream strm).data_type == Z_UNKNOWN then
      let t ← detect_data_type s
      stZStream strm { (← ldZStream strm) with data_type := t }
    build_tree s (← pLdesc s)
    build_tree s (← pDdesc s)
    max_blindex ← build_bl_tree s
    -- opt_lenb = (s->opt_len + 3 + 7) >> 3; static_lenb = (s->static_len + 3 + 7) >> 3;
    opt_lenb := ((← rd s).opt_len + 3 + 7) >>> 3
    static_lenb := ((← rd s).static_len + 3 + 7) >>> 3
    -- if (static_lenb <= opt_lenb || s->strategy == Z_FIXED) opt_lenb = static_lenb;
    if static_lenb ≤ opt_lenb ∨ (← rd s).strategy == Z_FIXED then opt_lenb := static_lenb
  else
    -- opt_lenb = static_lenb = stored_len + 5;
    opt_lenb := stored_len + 5
    static_lenb := stored_len + 5
  if stored_len + 4 ≤ opt_lenb ∧ buf != .null then
    «_tr_stored_block» s buf stored_len last
  else if static_lenb == opt_lenb then
    send_bits s (← iadd (STATIC_TREES <<< 1) last) 3
    compress_block s (.ref .st_static_ltree 0) (.ref .st_static_dtree 0)
  else
    send_bits s (← iadd (DYN_TREES <<< 1) last) 3
    send_all_trees s (← iadd (← rd s).l_desc.max_code 1) (← iadd (← rd s).d_desc.max_code 1)
      (← iadd max_blindex 1)
    compress_block s (← pLtree s) (← pDtree s)
  init_block s
  -- if (last) bi_windup(s);
  if last != 0 then bi_windup s

/-- `int ZLIB_INTERNAL _tr_tally(deflate_state *s, unsigned dist, unsigned lc)` -/
def «_tr_tally» (s : DeflateStatePtr) (dist lc : UInt32) : M Int32 := do
  -- s->sym_buf[s->sym_next++] = (uch)dist;  (uch)(dist >> 8);  (uch)lc;
  let put (v : UInt8) : M Unit := do
    let d ← rd s
    setAt d.sym_buf d.sym_next.toNat v
    md s fun d => { d with sym_next := d.sym_next + 1 }
  put dist.toUInt8
  put (dist >>> 8).toUInt8
  put lc.toUInt8
  if dist == 0 then
    -- s->dyn_ltree[lc].Freq++;
    let lt ← pLtree s
    setFc lt lc.toNat ((← getFc lt lc.toNat) + 1)
  else
    md s fun d => { d with «matches» := d.«matches» + 1 }
    let dist := dist - 1
    -- s->dyn_ltree[_length_code[lc] + LITERALS + 1].Freq++;
    let lcode ← Ptr.index (.ref .st_length_code 0 : BPtr) lc.toNat
    let idx := (u8i lcode).toInt + LITERALS.toInt + 1
    let lt ← pLtree s
    setFc lt idx ((← getFc lt idx) + 1)
    -- s->dyn_dtree[d_code(dist)].Freq++;
    let dc ← d_code dist
    let dt ← pDtree s
    setFc dt dc.toNat ((← getFc dt dc.toNat) + 1)
  -- return (s->sym_next == s->sym_end);
  let d ← rd s
  return (if d.sym_next == d.sym_end then 1 else 0)

end Zlib.Trees
