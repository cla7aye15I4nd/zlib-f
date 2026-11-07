import ZlibF.Proof.«trees.c.send-support»
import ZlibF.Math.DeflateHeader

/-! # trees.c: complete actual dynamic-header output -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out

/-- A count field's actual checked subtraction and bit write. -/
def atField (s : DeflateStatePtr) (count off width : Int32) : M Unit := do
  send_bits s (← isub count off) width

/-- The actual count-field prefix. -/
def atCounts (s : DeflateStatePtr) (lcodes dcodes blcodes : Int32) : M Unit := do
  atField s lcodes 257 5
  atField s dcodes 1 5
  atField s blcodes 4 4

/-- One actual rank iteration, including both table reads. -/
def atLengthBody (s : DeflateStatePtr) (r : Int32) : M Int32 := do
  let l ← getDl (← pBltree s) (u8i (← blOrder r.toInt)).toInt
  send_bits s (u16i l) 3
  pure r

def atLengthLoop (s : DeflateStatePtr) (blcodes : Int32) : M Int32 :=
  cfor (fun r => pure (decide (r.toInt < blcodes.toInt))) (fun r => iadd r 1) (atLengthBody s) 0

/-- The actual source-tree pointer selected for a call. -/
def atSourcePtr (s : DeflateStatePtr) : TK → M CtDataPtr
  | .lit => pLtree s
  | .dist => pDtree s
  | .bl => pBltree s

/-- A source-tree call with its actual pointer read and checked maximum. -/
def atTree (s : DeflateStatePtr) (tk : TK) (count : Int32) : M Unit := do
  let tree ← atSourcePtr s tk
  let mc ← isub count 1
  send_tree s tree mc

/-- The actual pair of final source-tree calls. -/
def atTrees (s : DeflateStatePtr) (lcodes dcodes : Int32) : M Unit := do
  atTree s .lit lcodes
  atTree s .dist dcodes

/-- Complete source equality, independent of all execution proofs below. -/
theorem send_all_trees_eq (s : DeflateStatePtr) (lcodes dcodes blcodes : Int32) :
    send_all_trees s lcodes dcodes blcodes = (do
      atCounts s lcodes dcodes blcodes
      let _ ← atLengthLoop s blcodes
      atTrees s lcodes dcodes) := by
  unfold send_all_trees atCounts atField atLengthLoop atLengthBody atTrees atTree atSourcePtr
  simp only [M_bind_assoc]

/-- A count field emits its exact low-to-high bits; no arithmetic fault
or output write is abstracted away. -/
theorem atField_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (count off width : Int32) (N O W total : Nat)
    (hn : count.toInt = N) (ho : off.toInt = O) (hw : width.toInt = W)
    (hO : O ≤ N) (hN : N < 65536) (hW : W ≤ 15) (hfit : N - O < 2 ^ W)
    (hp : w.length + W ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (atField (Sp id) count off width) h (fun _ H => ∃ D B,
      EmitState id b h0 d0 buf0 (w ++ natBits (N - O) W) H D B) := by
  unfold atField
  rw [st_isub count off (by omega) (by omega), M_pure_bind]
  have hv : (Int32.ofInt (count.toInt - off.toInt)).toInt = (N - O : Nat) := by
    rw [ofInt_toInt' _ (by omega) (by omega)]
    omega
  exact ht.extra_bits _ width (N - O) W (st_v16 _ _ hv (by omega)) (by rw [hw]; simp)
    (by omega) (by omega) hfit (ht.room W total hp hr)

/-- Data carried by send_tree is preserved by actual bit-output writes. -/
theorem SendTreeData.bitsDiff {d e : DeflateState} (tk : TK) (hd : SendTreeData d tk)
    (he : BitsDiff d e) : SendTreeData e tk := by
  obtain ⟨p, a, v, u, rfl⟩ := he
  cases tk <;> exact ⟨hd.nonneg, hd.max285, hd.capacity, hd.lengths, hd.codes⟩

/-- The current descriptor remains that of the source state. -/
theorem Out.EmitState.desc {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (tk : TK) : tk.getDesc d = tk.getDesc d0 := by
  obtain ⟨p, a, v, u, he⟩ := ht.fields
  rw [he]
  cases tk <;> rfl

theorem Out.EmitState.words {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) : blWords d = blWords d0 := by
  funext k
  unfold blWords
  rw [ht.tree_arrays.2.2]

theorem Out.EmitState.lengths {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (tk : TK) : sendLengths d tk = sendLengths d0 tk := by
  funext i
  unfold sendLengths
  rw [emitState_tk_arr ht tk]

/-- The three actual count fields execute in their original order. -/
theorem atCounts_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (lc dc bc : Int32) (L D B total : Nat)
    (hl : lc.toInt = L) (hd : dc.toInt = D) (hb : bc.toInt = B)
    (hl0 : 257 ≤ L) (hl1 : L ≤ 286) (hd0 : 1 ≤ D) (hd1 : D ≤ 30) (hb0 : 4 ≤ B) (hb1 : B ≤ 19)
    (hp : w.length + 14 ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (atCounts (Sp id) lc dc bc) h (fun _ H => ∃ de bu,
      EmitState id b h0 d0 buf0 (w ++ natBits (L - 257) 5 ++ natBits (D - 1) 5 ++ natBits (B - 4) 4) H de bu) := by
  unfold atCounts
  refine EWP.bind (atField_run ht lc 257 5 L 257 5 total hl rfl rfl hl0 (by omega) (by omega)
    (by change _ < 32; omega) (by omega) hr) ?_
  rintro _ H1 ⟨d1, b1, ht1⟩
  refine EWP.bind (atField_run ht1 dc 1 5 D 1 5 total hd rfl rfl hd0 (by omega) (by omega)
    (by change _ < 32; omega) (by simp only [List.length_append, natBits, List.length_map, List.length_range]; omega) hr) ?_
  rintro _ H2 ⟨d2, b2, ht2⟩
  exact atField_run ht2 bc 4 4 B 4 4 total hb rfl rfl hb0 (by omega) (by omega)
    (by change _ < 16; omega) (by simp only [List.length_append, natBits, List.length_map, List.length_range]; omega) hr

/-- One actual rank reads the permutation and tree length, then emits
exactly three bits and returns the unchanged loop index. -/
theorem atLengthBody_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (r : Int32) (R total : Nat) (hrank : r.toInt = R) (hR : R < 19)
    (hlens : ∀ k < 19, d0.bl_tree[k]!.dl.toNat ≤ 7) (hp : w.length + 3 ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (atLengthBody (Sp id) r) h (fun r' H => r' = r ∧ ∃ D B,
      EmitState id b h0 d0 buf0 (w ++ natBits (blWords d0 bl_order[R]!.toNat).2.toNat 3) H D B) := by
  have hindex : r.toInt.toNat = R := by omega
  have hord : blOrder r.toInt h = .ok (bl_order[R]!, h) := by
    unfold blOrder
    rw [ite_eq_left (show 0 ≤ r.toInt ∧ r.toInt < 19 by omega), hindex]
    rfl
  have hk := bl_order_bound R hR
  have hsize : 19 ≤ d.bl_tree.size := by have := ht.inv.base.wf.2.2.1; omega
  have hload := getDl_sel ht.inv.base.dstate .bl (i := bl_order[R]!.toNat) (by change bl_order[R]!.toNat < d.bl_tree.size; omega)
  change getDl (.ref (.dstate_bl_tree id) 0) (bl_order[R]!.toNat : Int) h = .ok (d.bl_tree[bl_order[R]!.toNat]!.dl, h) at hload
  rw [ht.tree_arrays.2.2] at hload
  have hread : getDl (.ref (.dstate_bl_tree id) 0) (u8i bl_order[R]!).toInt h =
      .ok (d0.bl_tree[bl_order[R]!.toNat]!.dl, h) := by
    rw [Out.u8i_toInt]
    exact hload
  unfold atLengthBody
  refine EWP.read (pBltree_run ht.inv.base.dstate) ?_
  refine EWP.read hord ?_
  refine EWP.read hread ?_
  refine EWP.bind (ht.extra_bits _ 3 (blWords d0 bl_order[R]!.toNat).2.toNat 3
    (v16_u16i _) rfl (by decide +kernel) (by decide +kernel)
    (by have := hlens _ hk; change _ < 8; exact Nat.lt_succ_of_le this)
    (ht.room 3 total hp hr)) ?_
  rintro _ H ⟨D, B, htrace⟩
  exact EWP.pure ⟨rfl, D, B, htrace⟩

/-- One complete rank iteration includes the actual signed increment. -/
theorem atLengthIteration_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (r : Int32) (R total : Nat) (hrank : r.toInt = R) (hR : R < 19)
    (hlens : ∀ k < 19, d0.bl_tree[k]!.dl.toNat ≤ 7) (hp : w.length + 3 ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (do let r' ← atLengthBody (Sp id) r; iadd r' 1) h (fun r' H => r'.toInt = (R + 1 : Nat) ∧ ∃ D B,
      EmitState id b h0 d0 buf0 (w ++ natBits (blWords d0 bl_order[R]!.toNat).2.toNat 3) H D B) := by
  refine EWP.bind (atLengthBody_run ht r R total hrank hR hlens hp hr) ?_
  rintro rr H ⟨he, D, B, htrace⟩
  subst rr
  have hone : (1 : Int32).toInt = 1 := rfl
  rw [st_iadd r 1 (by omega) (by omega)]
  refine EWP.pure ⟨?_, D, B, htrace⟩
  rw [ofInt_toInt' _ (by omega) (by omega)]
  omega

/-- All transmitted BL lengths are read and emitted in the actual
permutation. The loop terminates before any out-of-range rank. -/
theorem atLengthLoop_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (bc : Int32) (N total : Nat) (hbc : bc.toInt = N) (hN : N ≤ 19)
    (hlens : ∀ k < 19, d0.bl_tree[k]!.dl.toNat ≤ 7) (hp : w.length + 3 * N ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (atLengthLoop (Sp id) bc) h (fun r H => r.toInt = N ∧ ∃ D B,
      EmitState id b h0 d0 buf0 (w ++ blLensBits (blWords d0) N) H D B) := by
  let cond := fun r : Int32 => do pure (← (pure (decide (r.toInt < bc.toInt)) : _root_.C.M Bool), r)
  let body := fun r : Int32 => do let r' ← atLengthBody (Sp id) r; iadd r' 1
  let P := fun k (r : Int32) H => k ≤ N ∧ r.toInt = (N - k : Nat) ∧ ∃ D B,
    EmitState id b h0 d0 buf0 (w ++ blLensBits (blWords d0) (N - k)) H D B
  let Q := fun (r : Int32) H => r.toInt = N ∧ ∃ D B,
    EmitState id b h0 d0 buf0 (w ++ blLensBits (blWords d0) N) H D B
  have step : ∀ k r H, P (k + 1) r H → ∃ r1 H1 r2 H2,
      cond r H = .ok ((true, r1), H1) ∧ body r1 H1 = .ok (r2, H2) ∧ P k r2 H2 := by
    rintro k r H ⟨hk, hrank, D, B, htrace⟩
    have hlt : r.toInt < bc.toInt := by omega
    have hroom : (w ++ blLensBits (blWords d0) (N - (k + 1))).length + 3 ≤ total := by
      rw [List.length_append, blLensBits_length]
      omega
    obtain ⟨r2, H2, hbody, hr2, D2, B2, htrace2⟩ :=
      atLengthIteration_run htrace r (N - (k + 1)) total hrank (by omega) hlens hroom hr
    refine ⟨r, H, r2, H2, ?_, hbody, by omega, by omega, D2, B2, ?_⟩
    · simp only [cond, bind_app, pure_app, hlt, decide_true]
    · have he : N - k = N - (k + 1) + 1 := by omega
      rw [he, blLensBits_succ]
      simpa only [List.append_assoc] using htrace2
  have stop : ∀ r H, P 0 r H → ∃ r1 H1, cond r H = .ok ((false, r1), H1) ∧ Q r1 H1 := by
    rintro r H ⟨hk, hrank, D, B, htrace⟩
    have hno : ¬ r.toInt < bc.toInt := by omega
    refine ⟨r, H, ?_, by omega, D, B, ?_⟩
    · simp only [cond, bind_app, pure_app, hno, decide_false]
    · simpa only [Nat.sub_zero] using htrace
  have hstart : P N 0 h := by
    refine ⟨Nat.le_refl _, by simp, d, buf, ?_⟩
    simpa only [Nat.sub_self, blLensBits, List.range_zero, List.flatMap_nil, List.append_nil] using ht
  obtain ⟨r, H, hrun, hQ⟩ := _root_.C.cwhile_run P Q step stop hstart (by unfold fuel; omega)
  exact ⟨r, H, hrun, hQ⟩

/-- One actual source-tree pointer/subtraction/send call. Its data come
from the baseline record and are preserved by every earlier bit write. -/
theorem atTree_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (tk : TK) (count : Int32) (N total : Nat) (hN : count.toInt = N)
    (hlink : (tk.getDesc d0).max_code.toInt + 1 = N) (hdata : SendTreeData d0 tk)
    (hp : w.length + (sendTreeBits (blWords d0) (sendLengths d0 tk) (tk.getDesc d0).max_code.toInt.toNat).length ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (atTree (Sp id) tk count) h (fun _ H => ∃ D B,
      EmitState id b h0 d0 buf0 (w ++ sendTreeBits (blWords d0) (sendLengths d0 tk) (tk.getDesc d0).max_code.toInt.toNat) H D B) := by
  have hptr : atSourcePtr (Sp id) tk h =
      .ok (.ref (tk.ref id) 0, h) := by
    cases tk
    · exact pLtree_run ht.inv.base.dstate
    · exact pDtree_run ht.inv.base.dstate
    · exact pBltree_run ht.inv.base.dstate
  have hnc0 := hdata.nonneg
  have hnc1 := hdata.max285
  have hone : (1 : Int32).toInt = 1 := rfl
  have hmc : Int32.ofInt (count.toInt - (1 : Int32).toInt) = (tk.getDesc d0).max_code := by
    apply Int32.toInt_inj.mp
    rw [ofInt_toInt' _ (by omega) (by omega)]
    omega
  have hroom := ht.room (sendTreeBits (blWords d0) (sendLengths d0 tk) (tk.getDesc d0).max_code.toInt.toNat).length total hp hr
  have hd := hdata.bitsDiff tk ht.fields
  have hemit := hd.emit ht.inv tk (by rwa [ht.words, ht.lengths tk, ht.desc tk])
  rw [ht.words, ht.lengths tk, ht.desc tk] at hemit
  obtain ⟨H, D, B, hsend, htrace⟩ := ht.step hemit
  unfold atTree
  refine EWP.read hptr ?_
  rw [st_isub count 1 (by omega) (by omega), M_pure_bind, hmc]
  exact ⟨(), H, hsend, D, B, htrace⟩

/-- Both actual source-tree calls compose after any earlier header bits. -/
theorem atTrees_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (lc dc : Int32) (L D total : Nat) (hl : lc.toInt = L) (hd : dc.toInt = D)
    (hlinkL : d0.l_desc.max_code.toInt + 1 = L) (hlinkD : d0.d_desc.max_code.toInt + 1 = D)
    (hdataL : SendTreeData d0 .lit) (hdataD : SendTreeData d0 .dist)
    (hp : w.length + (sendTreeBits (blWords d0) (sendLengths d0 .lit) (L - 1)).length +
      (sendTreeBits (blWords d0) (sendLengths d0 .dist) (D - 1)).length ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    EWP (atTrees (Sp id) lc dc) h (fun _ H => ∃ De Bu,
      EmitState id b h0 d0 buf0 (w ++ sendTreeBits (blWords d0) (sendLengths d0 .lit) (L - 1) ++
        sendTreeBits (blWords d0) (sendLengths d0 .dist) (D - 1)) H De Bu) := by
  have hLM : (TK.lit.getDesc d0).max_code.toInt.toNat = L - 1 := by
    have := hdataL.nonneg
    change 0 ≤ d0.l_desc.max_code.toInt at this
    change d0.l_desc.max_code.toInt.toNat = L - 1
    omega
  have hDM : (TK.dist.getDesc d0).max_code.toInt.toNat = D - 1 := by
    have := hdataD.nonneg
    change 0 ≤ d0.d_desc.max_code.toInt at this
    change d0.d_desc.max_code.toInt.toNat = D - 1
    omega
  unfold atTrees
  refine EWP.bind (atTree_run ht .lit lc L total hl hlinkL hdataL (by rw [hLM]; omega) hr) ?_
  rintro _ H1 ⟨D1, B1, ht1⟩
  have he := atTree_run ht1 .dist dc D total hd hlinkD hdataD
    (by simp only [List.length_append]; rw [hLM, hDM]; exact hp) hr
  refine EWP.mono he ?_
  rintro _ H2 ⟨D2, B2, ht2⟩
  refine ⟨D2, B2, ?_⟩
  simpa only [hLM, hDM] using ht2

/-- Internal count/storage/code data established by actual construction.
No called-function contract or output-room premise is a field. -/
structure AllTreeData (d : DeflateState) (L D B : Nat) : Prop where
  lit_min : 257 ≤ L
  lit_max : L ≤ 286
  dist_min : 1 ≤ D
  dist_max : D ≤ 30
  bl_min : 4 ≤ B
  bl_max : B ≤ 19
  lit_count : d.l_desc.max_code.toInt + 1 = L
  dist_count : d.d_desc.max_code.toInt + 1 = D
  lit_data : SendTreeData d .lit
  dist_data : SendTreeData d .dist
  bl_lengths : ∀ k < 19, d.bl_tree[k]!.dl.toNat ≤ 7

/-- `local void send_all_trees(deflate_state *s, int lcodes, int dcodes, int blcodes)`.
Under explicit internal construction data and exact total bit room, the
complete actual routine terminates and emits the modeled dynamic header.
This statement does not yet identify the whole output with the independent
format grammar or derive room from the output/symbol overlay bound. -/
theorem send_all_trees_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (lc dc bc : Int32) (L D B : Nat)
    (hl : lc.toInt = L) (hd : dc.toInt = D) (hb : bc.toInt = B) (hdata : AllTreeData d L D B)
    (hr : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
      (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B).length ≤ 8 * buf.size) :
    Emit id b (send_all_trees (Sp id) lc dc bc) h d buf
      (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B)
      (d.bi_valid.toInt.toNat + (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B).length) := by
  let total := (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B).length
  have hlen : total = 14 + 3 * B + (sendTreeBits (blWords d) (sendLengths d .lit) (L - 1)).length +
      (sendTreeBits (blWords d) (sendLengths d .dist) (D - 1)).length := allTreesBits_length _ _ _ _ _ _
  have hrun : EWP (do atCounts (Sp id) lc dc bc
                       let _ ← atLengthLoop (Sp id) bc
                       atTrees (Sp id) lc dc) h (fun _ H => ∃ De Bu,
      EmitState id b h d buf (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B) H De Bu) := by
    refine EWP.bind (atCounts_run (EmitState.start hI) lc dc bc L D B total hl hd hb
      hdata.lit_min hdata.lit_max hdata.dist_min hdata.dist_max hdata.bl_min hdata.bl_max
      (by simp only [List.length_nil]; omega) hr) ?_
    rintro _ H1 ⟨D1, B1, ht1⟩
    refine EWP.bind (atLengthLoop_run ht1 bc B total hb hdata.bl_max hdata.bl_lengths
      (by simp only [List.length_append, List.length_nil, natBits, List.length_map, List.length_range]; omega) hr) ?_
    rintro _ H2 ⟨hindex, D2, B2, ht2⟩
    refine EWP.mono (atTrees_run ht2 lc dc L D total hl hd hdata.lit_count hdata.dist_count hdata.lit_data hdata.dist_data
      (by simp only [List.length_append, List.length_nil, natBits, List.length_map, List.length_range, blLensBits_length]; omega) hr) ?_
    rintro _ H3 ⟨D3, B3, ht3⟩
    refine ⟨D3, B3, ?_⟩
    simpa only [List.nil_append, List.append_assoc, allTreesBits] using ht3
  obtain ⟨a, H, hcall, De, Bu, htrace⟩ := hrun
  have ha : a = () := Subsingleton.elim _ _
  subst a
  rw [send_all_trees_eq]
  exact htrace.emit hcall

/-- Construction facts from the two checked views of the same actual run
hold on the same returned record. No callee specification is assumed. -/
theorem init_tallies_all_tree_data {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (symbols : List (UInt32 × UInt32))
    (hlegal : ∀ t ∈ symbols, t.2.toNat < 256 ∧ t.1.toNat ≤ 32768)
    (hroom : 3 * symbols.length ≤ d.sym_end.toNat) :
    ∃ (mb : Int32) (e : DeflateState) (buf' : Array UInt8),
      (do init_block (Sp id); tallyCalls (Sp id) symbols
          blPrepare (Sp id); build_bl_tree (Sp id)) h =
        .ok (mb, Out.setD (Out.setB h b buf') id e) ∧
      TreesInvAt (Out.setD (Out.setB h b buf') id e) id e b buf' ∧
      AllTreeData e (e.l_desc.max_code.toInt.toNat + 1) (e.d_desc.max_code.toInt.toNat + 1) (mb.toInt.toNat + 1) ∧
      3 ≤ mb.toInt ∧ mb.toInt ≤ 18 := by
  obtain ⟨mb, e, buf', hr, hIe, hsend⟩ := init_tallies_ready_to_send hI symbols hlegal hroom
  obtain ⟨mb2, e2, buf2, hr2, hlo, hhi, hlL, hlH, hdL, hdH, hlen, hupper, hI2⟩ :=
    init_tallies_prepare_bl_fields hI symbols hlegal hroom
  have heq := Prod.mk.inj (Except.ok.inj (hr.symm.trans hr2))
  have hrecord := congrArg (fun H : Heap => H.dstates id) heq.2
  simp only [Out.setD_dstates_same] at hrecord
  have he : e = e2 := Option.some.inj hrecord
  have hm : mb = mb2 := heq.1
  subst e2
  subst mb2
  have hL := hsend .lit (by decide +kernel)
  have hD := hsend .dist (by decide +kernel)
  have hL0 := hL.nonneg
  have hD0 := hD.nonneg
  change 0 ≤ e.l_desc.max_code.toInt at hL0
  change 0 ≤ e.d_desc.max_code.toInt at hD0
  refine ⟨mb, e, buf', hr, hIe, ?_, hlo, hhi⟩
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, hL, hD, hlen⟩

/-- The actual count-argument expression in the dynamic flush branch.
This fragment alone does not constitute a whole flush-block proof. -/
def atCall (s : DeflateStatePtr) (mb : Int32) : M Unit := do
  send_all_trees s (← iadd (← rd s).l_desc.max_code 1) (← iadd (← rd s).d_desc.max_code 1)
    (← iadd mb 1)

/-- Actual descriptor reads and all three checked argument increments
connect constructed data to the complete actual header writer. -/
theorem atCall_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (mb : Int32) (L D B : Nat)
    (hdata : AllTreeData d L D B) (hmb : mb.toInt + 1 = B)
    (hr : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
      (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B).length ≤ 8 * buf.size) :
    Emit id b (atCall (Sp id) mb) h d buf
      (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B)
      (d.bi_valid.toInt.toNat + (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B).length) := by
  have hl := hdata.lit_count
  have hd := hdata.dist_count
  have hl0 := hdata.lit_min
  have hl1 := hdata.lit_max
  have hd0 := hdata.dist_min
  have hd1 := hdata.dist_max
  have hb0 := hdata.bl_min
  have hb1 := hdata.bl_max
  have hone : (1 : Int32).toInt = 1 := rfl
  let lc := Int32.ofInt (d.l_desc.max_code.toInt + (1 : Int32).toInt)
  let dc := Int32.ofInt (d.d_desc.max_code.toInt + (1 : Int32).toInt)
  let bc := Int32.ofInt (mb.toInt + (1 : Int32).toInt)
  have hLC : lc.toInt = L := by
    dsimp [lc]
    rw [ofInt_toInt' _ (by omega) (by omega)]
    omega
  have hDC : dc.toInt = D := by
    dsimp [dc]
    rw [ofInt_toInt' _ (by omega) (by omega)]
    omega
  have hBC : bc.toInt = B := by
    dsimp [bc]
    rw [ofInt_toInt' _ (by omega) (by omega)]
    omega
  have hcall : atCall (Sp id) mb h = send_all_trees (Sp id) lc dc bc h := by
    unfold atCall
    simp only [bind_app, rd_run hI.base.dstate]
    rw [st_iadd d.l_desc.max_code 1 (by omega) (by omega)]
    simp only [pure_app, rd_run hI.base.dstate]
    rw [st_iadd d.d_desc.max_code 1 (by omega) (by omega)]
    simp only [pure_app]
    rw [st_iadd mb 1 (by omega) (by omega)]
    rfl
  obtain ⟨bu, de, hrun, hInv, hbits, hsize, hframe, hlo, hhi, hdiff⟩ :=
    send_all_trees_emit hI lc dc bc L D B hLC hDC hBC hdata hr
  exact ⟨bu, de, hcall.trans hrun, hInv, hbits, hsize, hframe, hlo, hhi, hdiff⟩

/-- A proof harness composing the actual block/tree/header calls. It is
not a replacement translation of the flush or strategy functions. -/
def atPrepared (s : DeflateStatePtr) (symbols : List (UInt32 × UInt32)) : M Unit := do
  let mb ← do
    init_block s
    tallyCalls s symbols
    blPrepare s
    build_bl_tree s
  atCall s mb

/-- Grouping the actual construction calls does not change their order. -/
theorem atPrepared_eq (s : DeflateStatePtr) (symbols : List (UInt32 × UInt32)) :
    atPrepared s symbols = ((do init_block s; tallyCalls s symbols; blPrepare s; build_bl_tree s) >>= fun mb => atCall s mb) := by
  unfold atPrepared
  simp only [M_bind_assoc]

/-- Actual construction establishes the writer data, and the actual
computed-argument call emits the full modeled header when its exact bit
room holds. Room is tested on the returned constructed state; it is still
to be derived from block/overlay bounds. No output-prefix claim is made
across the earlier symbol-buffer tally stores. -/
theorem atPrepared_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (symbols : List (UInt32 × UInt32))
    (hlegal : ∀ t ∈ symbols, t.2.toNat < 256 ∧ t.1.toNat ≤ 32768)
    (hcapacity : 3 * symbols.length ≤ d.sym_end.toNat) :
    ∃ (mb : Int32) (built : DeflateState) (prepared : Array UInt8),
      (do init_block (Sp id); tallyCalls (Sp id) symbols
          blPrepare (Sp id); build_bl_tree (Sp id)) h =
        .ok (mb, Out.setD (Out.setB h b prepared) id built) ∧
      (let L := built.l_desc.max_code.toInt.toNat + 1
       let D := built.d_desc.max_code.toInt.toNat + 1
       let B := mb.toInt.toNat + 1
       let bits := allTreesBits (blWords built) (sendLengths built .lit) (sendLengths built .dist) L D B
       8 * built.pending.toNat + built.bi_valid.toInt.toNat + bits.length ≤ 8 * prepared.size →
         ∃ (e : DeflateState) (buf' : Array UInt8),
           atPrepared (Sp id) symbols h = .ok ((), Out.setD (Out.setB h b buf') id e) ∧
           TreesInvAt (Out.setD (Out.setB h b buf') id e) id e b buf' ∧
           outBits buf' e = outBits prepared built ++ bits ∧ BitsDiff built e) := by
  obtain ⟨mb, built, prepared, hbuild, hIb, hdata, hlo, hhi⟩ :=
    init_tallies_all_tree_data hI symbols hlegal hcapacity
  refine ⟨mb, built, prepared, hbuild, ?_⟩
  dsimp only
  intro hroom
  obtain ⟨buf', e, hcall, hIe, hbits, hsize, hframe, hplo, hphi, hdiff⟩ :=
    atCall_emit hIb mb _ _ _ hdata (by omega) hroom
  refine ⟨e, buf', ?_, ?_, hbits, hdiff⟩
  · rw [atPrepared_eq, bind_app, hbuild]
    simpa only [Out.setB_setD, Out.setB_setB, Out.setD_setD] using hcall
  · simpa only [Out.setB_setD, Out.setB_setB, Out.setD_setD] using hIe

end Zlib.Trees.Proofs
