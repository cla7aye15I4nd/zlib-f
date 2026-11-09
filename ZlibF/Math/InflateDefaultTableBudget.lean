import ZlibF.Math.InflateTableCoverage

namespace Zlib.Inftrees.Proofs.DefaultBudget
open Zlib.Inftrees.Canon
set_option autoImplicit false

/-- A complete alphabet cannot have too few leaves for its shortest depth. -/
theorem kraft_prefix_min_bound (ls : List Nat) (j : Nat)
    (inside : j ≤ nz ls) : K ls j ≤ j * 2 ^ (15 - L ls 0) := by
  induction j with
  | zero => simp [K_zero]
  | succ j ih =>
    have previous := ih (by omega)
    have ordered := L_mono ls (show 0 ≤ j by omega) (show j < nz ls by omega)
    have power : 2 ^ (15 - L ls j) ≤ 2 ^ (15 - L ls 0) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [K_succ, Nat.succ_mul]
    omega

/-- For a complete alphabet with fewer than 2^r leaves, the shortest code
is no longer than r. This rules out the upward root adjustment. -/
theorem complete_min_le_requested {ls : List Nat} {requested : Nat}
    (complete : K ls (nz ls) = 2 ^ 15) (small : nz ls < 2 ^ requested)
    (requested_le : requested ≤ 15) : L ls 0 ≤ requested := by
  by_cases shorter : L ls 0 ≤ requested
  · exact shorter
  apply False.elim
  have bound := kraft_prefix_min_bound ls (nz ls) (Nat.le_refl _)
  have factor : 2 ^ (15 - L ls 0) ≤ 2 ^ (15 - requested) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have multiplied := Nat.mul_le_mul_left (nz ls) factor
  have strict := Nat.mul_lt_mul_of_pos_right small (Nat.two_pow_pos (15 - requested))
  have total : 2 ^ requested * 2 ^ (15 - requested) = 2 ^ 15 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [complete] at bound
  rw [total] at strict
  omega

/-- Root nine never increases for a complete alphabet with at most 286 codes. -/
theorem lens_root_not_increased {ls : List Nat}
    (complete : K ls (nz ls) = 2 ^ 15) (count : nz ls ≤ 286) : L ls 0 ≤ 9 :=
  complete_min_le_requested complete (by omega) (by omega)

/-- If all lengths fit in the requested root, only the root table exists. -/
theorem desc_requested_short {ls : List Nat} {requested mx i : Nat}
    (code : CompleteCode ls requested mx) (inside : i < nz ls) (short : mx ≤ requested) :
    (desc ls requested mx i).used = 2 ^ requested := by
  have length := code.L_le_mx inside
  rw [desc_short ls inside (by omega)]
  rfl

/-- The exponential potential grows at least linearly. -/
theorem power_linear_growth {a b : Nat} (ordered : a ≤ b) :
    2 ^ a + b ≤ 2 ^ b + a := by
  induction b with
  | zero => have : a = 0 := by omega
            subst a
            decide
  | succ b ih =>
    by_cases same : a = b + 1
    · subst a
      omega
    have previous := ih (by omega)
    have positive := Nat.two_pow_pos b
    rw [Nat.pow_succ]
    omega

/-- A canonical sequence of complete subtrees has ordered depth intervals.
Each subtree has at least 2^a + (b-a) leaves if its shortest and longest
relative depths are a and b. The resulting replication overhead telescopes. -/
theorem ordered_subtable_budget (groups : List (Nat × Nat × Nat)) (lower upper : Nat)
    (overall : lower ≤ upper)
    (bounds : ∀ g ∈ groups, lower ≤ g.1 ∧ g.1 ≤ g.2.1 ∧ g.2.1 ≤ upper)
    (ordered : groups.Pairwise (fun g h => g.2.1 ≤ h.1))
    (leaves : ∀ g ∈ groups, 2 ^ g.1 + g.2.1 ≤ g.2.2 + g.1) :
    (groups.map fun g => 2 ^ g.2.1).sum + 2 ^ lower + upper ≤
      (groups.map fun g => g.2.2).sum + 2 ^ upper + lower := by
  induction groups generalizing lower with
  | nil => simpa using power_linear_growth overall
  | cons g gs ih =>
    obtain ⟨low, interval, high⟩ := bounds g (by simp)
    obtain ⟨next, tailOrdered⟩ := List.pairwise_cons.mp ordered
    have tailBounds : ∀ h ∈ gs, g.2.1 ≤ h.1 ∧ h.1 ≤ h.2.1 ∧ h.2.1 ≤ upper := by
      intro h mem
      exact ⟨next h mem, (bounds h (by simp [mem])).2⟩
    have tailLeaves : ∀ h ∈ gs, 2 ^ h.1 + h.2.1 ≤ h.2.2 + h.1 := by
      intro h mem
      exact leaves h (by simp [mem])
    have tail := ih g.2.1 high tailBounds tailOrdered tailLeaves
    have group := leaves g (by simp)
    have gap := power_linear_growth low
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The generic canonical-overhead bound specializes to 57 entries when
relative depths lie in 1..6, as for root-nine LENS tables. -/
theorem ordered_lens_subtables_budget (groups : List (Nat × Nat × Nat))
    (bounds : ∀ g ∈ groups, 1 ≤ g.1 ∧ g.1 ≤ g.2.1 ∧ g.2.1 ≤ 6)
    (ordered : groups.Pairwise (fun g h => g.2.1 ≤ h.1))
    (leaves : ∀ g ∈ groups, 2 ^ g.1 + g.2.1 ≤ g.2.2 + g.1) :
    (groups.map fun g => 2 ^ g.2.1).sum ≤ (groups.map fun g => g.2.2).sum + 57 := by
  have result := ordered_subtable_budget groups 1 6 (by omega) bounds ordered leaves
  simp only [Nat.reducePow] at result
  omega

#print axioms kraft_prefix_min_bound
#print axioms complete_min_le_requested
#print axioms lens_root_not_increased
#print axioms desc_requested_short
#print axioms power_linear_growth
#print axioms ordered_subtable_budget
#print axioms ordered_lens_subtables_budget

/-- A complete binary-forest histogram, with its last occupied level retained.
The input is the number of available positions at its first level. -/
inductive CompleteFrontier : Nat → List Nat → Prop where
  | last (slots : Nat) : CompleteFrontier slots [slots]
  | next {slots used : Nat} {tail : List Nat} (remaining : used < slots)
      (complete : CompleteFrontier (2 * (slots - used)) tail) :
      CompleteFrontier slots (used :: tail)

/-- Extending a complete forest by one occupied depth costs at least one leaf. -/
theorem complete_frontier_leaf_count {slots : Nat} {histogram : List Nat}
    (complete : CompleteFrontier slots histogram) :
    slots + histogram.length ≤ histogram.sum + 1 := by
  induction complete with
  | last slots => simp
  | @next slots used tail remaining complete ih =>
    simp only [List.length_cons, List.sum_cons]
    omega

/-- The leaf-count condition used by the telescoping table bound follows
from a complete histogram whose first and last depths are a and b. -/
theorem complete_frontier_depth_budget {a b : Nat} {histogram : List Nat}
    (interval : a ≤ b) (levels : histogram.length = b - a + 1)
    (complete : CompleteFrontier (2 ^ a) histogram) :
    2 ^ a + b ≤ histogram.sum + a := by
  have leaves := complete_frontier_leaf_count complete
  omega

/-- For six-bit secondary tables the sum of complete histogram costs is
at most the number of symbols plus 57 replicated cells. -/
theorem complete_lens_forest_budget
    (groups : List (Nat × Nat × List Nat))
    (bounds : ∀ g ∈ groups, 1 ≤ g.1 ∧ g.1 ≤ g.2.1 ∧ g.2.1 ≤ 6)
    (ordered : groups.Pairwise (fun g h => g.2.1 ≤ h.1))
    (levels : ∀ g ∈ groups, g.2.2.length = g.2.1 - g.1 + 1)
    (complete : ∀ g ∈ groups, CompleteFrontier (2 ^ g.1) g.2.2) :
    (groups.map fun g => 2 ^ g.2.1).sum ≤
      (groups.map fun g => g.2.2.sum).sum + 57 := by
  let numerical := groups.map fun g => (g.1, g.2.1, g.2.2.sum)
  have membership : ∀ g ∈ numerical, 1 ≤ g.1 ∧ g.1 ≤ g.2.1 ∧ g.2.1 ≤ 6 := by
    intro g mem
    obtain ⟨actual, actualMem, equal⟩ := List.mem_map.mp mem
    subst g
    exact bounds actual actualMem
  have sorting : numerical.Pairwise (fun g h => g.2.1 ≤ h.1) := by
    apply List.pairwise_map.mpr
    exact ordered
  have leaves : ∀ g ∈ numerical, 2 ^ g.1 + g.2.1 ≤ g.2.2 + g.1 := by
    intro g mem
    obtain ⟨actual, actualMem, equal⟩ := List.mem_map.mp mem
    subst g
    exact complete_frontier_depth_budget (bounds actual actualMem).2.1
      (levels actual actualMem) (complete actual actualMem)
  have total := ordered_lens_subtables_budget numerical membership sorting leaves
  simpa [numerical, List.map_map, Function.comp_def] using total

#print axioms complete_frontier_leaf_count
#print axioms complete_frontier_depth_budget
#print axioms complete_lens_forest_budget


/-- Integer Kraft mass of a histogram, in units of its deepest level. -/
def histogramMass : List Nat → Nat
  | [] => 0
  | used :: tail => used * 2 ^ tail.length + histogramMass tail

theorem histogram_mass_positive {histogram : List Nat} {last : Nat}
    (terminal : histogram.getLast? = some last) (positive : 0 < last) :
    0 < histogramMass histogram := by
  induction histogram with
  | nil => simp at terminal
  | cons used tail ih =>
    cases tail with
    | nil =>
      have same : used = last := by simpa using terminal
      subst last
      simpa [histogramMass] using positive
    | cons next rest =>
      have actual : (next :: rest).getLast? = some last := by
        simpa only [List.getLast?_cons, Option.getD_some] using terminal
      have remains := ih actual
      change 0 < used * 2 ^ (next :: rest).length + histogramMass (next :: rest)
      omega

/-- Exact integer Kraft equality and an occupied last level reconstruct
the complete frontier; no table-capacity hypothesis is used. -/
theorem complete_frontier_of_mass {histogram : List Nat} {slots last : Nat}
    (terminal : histogram.getLast? = some last) (positive : 0 < last)
    (mass : histogramMass histogram = slots * 2 ^ (histogram.length - 1)) :
    CompleteFrontier slots histogram := by
  induction histogram generalizing slots with
  | nil => simp at terminal
  | cons used tail ih =>
    cases tail with
    | nil =>
      have same : used = slots := by simpa [histogramMass] using mass
      subst used
      exact CompleteFrontier.last slots
    | cons next rest =>
      have actual : (next :: rest).getLast? = some last := by
        simpa only [List.getLast?_cons, Option.getD_some] using terminal
      have remains := histogram_mass_positive actual positive
      have enough : used < slots := by
        by_cases order : used < slots
        · exact order
        have product := Nat.mul_le_mul_right (2 ^ (next :: rest).length) (show slots ≤ used by omega)
        change used * 2 ^ (next :: rest).length + histogramMass (next :: rest) =
          slots * 2 ^ (next :: rest).length at mass
        omega
      apply CompleteFrontier.next enough
      apply ih actual
      have equal : histogramMass (next :: rest) = (slots - used) * 2 ^ (next :: rest).length := by
        rw [Nat.sub_mul]
        simp only [histogramMass, List.length_cons, Nat.add_sub_cancel] at mass ⊢
        omega
      rw [equal, List.length_cons, Nat.add_sub_cancel, Nat.pow_succ]
      rw [Nat.mul_comm (2 ^ rest.length) 2, ← Nat.mul_assoc, Nat.mul_comm (slots - used) 2]

#print axioms histogram_mass_positive
#print axioms complete_frontier_of_mass


/-- A lower bound on remaining code lengths bounds their integer Kraft mass. -/
theorem kraft_suffix_length_bound (ls : List Nat) (a b lower : Nat)
    (order : a ≤ b) (lengths : ∀ i, a ≤ i → i < b → lower ≤ L ls i) :
    K ls b ≤ K ls a + (b - a) * 2 ^ (15 - lower) := by
  induction b with
  | zero => have : a = 0 := by omega
            subst a
            simp
  | succ b ih =>
    by_cases same : a = b + 1
    · subst a
      simp
    have previous := ih (by omega) (by intro i ha hi; exact lengths i ha (by omega))
    have last := lengths b (by omega) (by omega)
    have power : 2 ^ (15 - L ls b) ≤ 2 ^ (15 - lower) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [K_succ, show b + 1 - a = (b - a) + 1 by omega, Nat.succ_mul]
    omega

/-- A complete LENS alphabet with at most 286 used symbols has at least
two codes in the root table; a single short leaf cannot supply enough mass. -/
theorem lens_at_least_two_short {ls : List Nat}
    (positive : 0 < nz ls) (complete : K ls (nz ls) = 2 ^ 15)
    (count : nz ls ≤ 286) : 2 ≤ offL ls 10 := by
  by_cases two : 2 ≤ offL ls 10
  · exact two
  apply False.elim
  have firstLength := (L_interval ls positive).1
  have firstPower : 2 ^ (15 - L ls 0) ≤ 2 ^ 14 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have first : K ls 1 ≤ 2 ^ 14 := by
    simpa [K_succ, K_zero] using firstPower
  have remaining : ∀ i, 1 ≤ i → i < nz ls → 10 ≤ L ls i := by
    intro i after inside
    have classify := lt_offL_iff ls inside (l := 9)
    change i < offL ls 10 ↔ L ls i ≤ 9 at classify
    omega
  have tail := kraft_suffix_length_bound ls 1 (nz ls) 10 (by omega) remaining
  rw [complete] at tail
  simp only [Nat.reducePow, Nat.reduceSub] at first tail
  omega

/-- Combining the canonical-forest overhead, two short LENS leaves and
parity gives precisely the default ENOUGH_LENS value. -/
theorem lens_default_capacity_from_forest (groups : List (Nat × Nat × List Nat))
    (bounds : ∀ g ∈ groups, 1 ≤ g.1 ∧ g.1 ≤ g.2.1 ∧ g.2.1 ≤ 6)
    (ordered : groups.Pairwise (fun g h => g.2.1 ≤ h.1))
    (levels : ∀ g ∈ groups, g.2.2.length = g.2.1 - g.1 + 1)
    (complete : ∀ g ∈ groups, CompleteFrontier (2 ^ g.1) g.2.2)
    (longCount : (groups.map fun g => g.2.2.sum).sum ≤ 284) :
    512 + (groups.map fun g => 2 ^ g.2.1).sum ≤ 852 := by
  have overhead := complete_lens_forest_budget groups bounds ordered levels complete
  have sumEven : ∀ xs : List (Nat × Nat × List Nat),
      (∀ g ∈ xs, 1 ≤ g.2.1) → 2 ∣ (xs.map fun g => 2 ^ g.2.1).sum := by
    intro xs
    induction xs with
    | nil => intro _; exact Nat.dvd_zero 2
    | cons g gs ih =>
      intro positive
      simp only [List.map_cons, List.sum_cons]
      apply Nat.dvd_add
      · exact Nat.dvd_trans (show 2 ∣ 2 ^ 1 by decide)
          (Nat.pow_dvd_pow 2 (positive g (by simp)))
      · exact ih (by intro h mem; exact positive h (by simp [mem]))
  have parity := sumEven groups (by
    intro g mem
    have interval := bounds g mem
    omega)
  obtain ⟨half, even⟩ := parity
  omega

#print axioms kraft_suffix_length_bound
#print axioms lens_at_least_two_short
#print axioms lens_default_capacity_from_forest


/-- The actual descriptor budget is exactly the root allocation plus the
allocations at the translated constructor's real startsAt transitions. -/
theorem desc_used_allocation_sum (ls : List Nat) (root mx i : Nat) :
    (desc ls root mx i).used = 2 ^ root +
      ((List.range i).map fun j => if startsAt ls root j then
        2 ^ width ls (j + 1) root mx else 0).sum := by
  induction i with
  | zero => simp [desc]
  | succ i ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases start : startsAt ls root i
    · rw [desc_succ_of_starts ls root mx i start]
      simp only [List.map_singleton, List.sum_singleton, ite_eq_left start]
      rw [ih]
      omega
    · rw [desc_succ_of_not ls root mx i start]
      simpa only [List.map_singleton, List.sum_singleton, ite_eq_right start, Nat.add_zero] using ih

/-- The requested root can decrease for short codes, but never increases
for the complete default LENS alphabet. -/
theorem lens_root_clamp_eq {ls : List Nat}
    (positive : 0 < nz ls) (complete : K ls (nz ls) = 2 ^ 15)
    (count : nz ls ≤ 286) :
    max (L ls 0) (min 9 (L ls (nz ls - 1))) = min 9 (L ls (nz ls - 1)) := by
  have shortest := lens_root_not_increased complete count
  have last := L_mono ls (show 0 ≤ nz ls - 1 by omega) (show nz ls - 1 < nz ls by omega)
  omega

/-- Long-table cases use exactly root nine after the real min/max clamp. -/
theorem lens_root_clamp_long {ls : List Nat}
    (positive : 0 < nz ls) (complete : K ls (nz ls) = 2 ^ 15)
    (count : nz ls ≤ 286) (long : 9 < L ls (nz ls - 1)) :
    max (L ls 0) (min 9 (L ls (nz ls - 1))) = 9 := by
  rw [lens_root_clamp_eq positive complete count]
  omega

#print axioms desc_used_allocation_sum
#print axioms lens_root_clamp_eq
#print axioms lens_root_clamp_long


/-- Once the real canonical root group has been delimited by its Kraft
end point, the translated count lookahead chooses its actual longest code.
The interval and endpoint premises describe the group, not a capacity bound. -/
theorem width_eq_group_last {ls : List Nat} {root mx first finish : Nat}
    (code : CompleteCode ls root mx) (firstPositive : 1 ≤ first)
    (nonempty : first < finish) (inside : finish ≤ nz ls)
    (start : startsAt ls root (first - 1))
    (same : grp ls root (finish - 1) = grp ls root first)
    (endPoint : K ls finish = K ls first + 2 ^ (15 - root)) :
    width ls first root mx = L ls (finish - 1) - root := by
  have firstInside : first < nz ls := by omega
  have lastInside : finish - 1 < nz ls := by omega
  have startIndex : first - 1 + 1 = first := by omega
  have long : root < L ls first := by simpa only [startIndex] using start.1
  have covers := look_covers code (a := first - 1) (by omega) start
    (i := finish - 1) (by omega) lastInside (by simpa only [startIndex] using same)
  rw [startIndex] at covers
  have information := width_spec ls firstInside code.mx_le long (code.L_le_mx firstInside)
  have increasing := L_mono ls (show first ≤ finish - 1 by omega) lastInside
  by_cases equal : width ls first root mx = L ls (finish - 1) - root
  · exact equal
  apply False.elim
  have strict : L ls (finish - 1) < root + width ls first root mx := by omega
  have boundary : finish ≤ offL ls (root + width ls first root mx) := by
    have classify := lt_offL_iff ls lastInside (l := root + width ls first root mx - 1)
    have positiveWidth : 1 ≤ root + width ls first root mx := by omega
    rw [show root + width ls first root mx - 1 + 1 = root + width ls first root mx by omega] at classify
    omega
  have mass := K_mono ls (Nat.le_trans boundary (Nat.le_max_right first _))
  have minimal := information.2.2.2 (show L ls first - root < width ls first root mx by omega)
  unfold cov at minimal
  omega

#print axioms width_eq_group_last


/-- A positive step of at most one block ending on a block boundary
finishes precisely the block containing its initial point. -/
theorem adjacent_block_endpoint {x step block : Nat}
    (blockPositive : 0 < block) (stepPositive : 0 < step) (stepFits : step ≤ block)
    (aligned : block ∣ x + step) :
    x + step = (x / block + 1) * block := by
  obtain ⟨q, quotient⟩ := aligned
  have lower : x / block * block ≤ x := Nat.div_mul_le_self _ _
  have upper : x < (x / block + 1) * block := by
    exact (Nat.div_lt_iff_lt_mul blockPositive).mp (show x / block < x / block + 1 by omega)
  have afterLower : x / block < q := by
    apply Nat.lt_of_mul_lt_mul_right (a := block)
    rw [Nat.mul_comm q block, ← quotient]
    omega
  have afterUpper : q < x / block + 2 := by
    apply Nat.lt_of_mul_lt_mul_right (a := block)
    rw [Nat.mul_comm q block, ← quotient]
    rw [Nat.add_mul, Nat.two_mul]
    rw [Nat.add_mul, Nat.one_mul] at upper
    omega
  have exactQuotient : q = x / block + 1 := by omega
  rw [quotient, exactQuotient, Nat.mul_comm]

/-- A real root group's terminal aligned code step fills one whole root
slot. This supplies the endpoint needed by lookahead minimality. -/
theorem canonical_group_endpoint {ls : List Nat} {root mx first finish : Nat}
    (code : CompleteCode ls root mx) (firstPositive : 1 ≤ first)
    (nonempty : first < finish) (inside : finish ≤ nz ls)
    (start : startsAt ls root (first - 1))
    (same : grp ls root (finish - 1) = grp ls root first)
    (terminalAligned : 2 ^ (15 - root) ∣ K ls finish) :
    K ls finish = K ls first + 2 ^ (15 - root) := by
  have firstInside : first < nz ls := by omega
  have lastInside : finish - 1 < nz ls := by omega
  have startIndex : first - 1 + 1 = first := by omega
  have long : root < L ls first := by simpa only [startIndex] using start.1
  have ordered := L_mono ls (show first ≤ finish - 1 by omega) lastInside
  have stepFits : 2 ^ (15 - L ls (finish - 1)) ≤ 2 ^ (15 - root) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have finalStep : K ls finish = K ls (finish - 1) + 2 ^ (15 - L ls (finish - 1)) := by
    simpa only [show finish - 1 + 1 = finish by omega] using K_succ ls (finish - 1)
  have boundary := adjacent_block_endpoint (Nat.two_pow_pos (15 - root))
    (Nat.two_pow_pos (15 - L ls (finish - 1))) stepFits (by rw [← finalStep]; exact terminalAligned)
  have initial := start_aligned code (i := first - 1) (by omega) start
  rw [startIndex] at initial
  rw [finalStep, boundary]
  change (grp ls root (finish - 1) + 1) * 2 ^ (15 - root) = _
  rw [same, Nat.add_mul, Nat.one_mul, ← initial]

#print axioms adjacent_block_endpoint
#print axioms canonical_group_endpoint


/-- Integer histogram mass is additive in its per-level counts. -/
theorem histogram_mass_map_add (indices : List Nat) (f g : Nat → Nat) :
    histogramMass (indices.map fun k => f k + g k) =
      histogramMass (indices.map f) + histogramMass (indices.map g) := by
  induction indices with
  | nil => rfl
  | cons k tail ih =>
    simp only [List.map_cons, histogramMass, List.length_map, Nat.add_mul, ih]
    omega

/-- One code at depth d contributes its dyadic weight to the histogram. -/
theorem histogram_mass_impulse (start count depth : Nat) :
    histogramMass ((List.range' start count).map fun k => if depth = k then 1 else 0) =
      if start ≤ depth ∧ depth < start + count then 2 ^ (start + count - 1 - depth) else 0 := by
  induction count generalizing start with
  | zero =>
    simp only [List.range'_zero, List.map_nil, histogramMass]
    rw [ite_eq_right (by omega)]
  | succ count ih =>
    rw [List.range'_succ]
    simp only [List.map_cons, histogramMass, List.length_map, List.length_range', ih]
    by_cases same : depth = start
    · subst depth
      simp only [ite_true, Nat.one_mul]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      rw [show start + (count + 1) - 1 - start = count by omega, Nat.add_zero]
    · rw [ite_eq_right same, Nat.zero_mul, Nat.zero_add]
      by_cases inside : start + 1 ≤ depth ∧ depth < start + 1 + count
      · rw [ite_eq_left inside, ite_eq_left (by omega)]
        congr 1
        omega
      · rw [ite_eq_right inside, ite_eq_right (by omega)]

/-- Histogram mass equals the sum of the individual canonical weights. -/
theorem histogram_mass_counts (depths : List Nat) (start count : Nat) :
    histogramMass ((List.range' start count).map fun k => depths.count k) =
      (depths.map fun depth => if start ≤ depth ∧ depth < start + count then
        2 ^ (start + count - 1 - depth) else 0).sum := by
  induction depths with
  | nil =>
    have zero : ∀ indices : List Nat, histogramMass (indices.map fun _ => 0) = 0 := by
      intro indices
      induction indices with
      | nil => rfl
      | cons k ks ih => simpa [histogramMass] using ih
    simpa only [List.count_nil, List.map_nil, List.sum_nil] using zero (List.range' start count)
  | cons depth tail ih =>
    have expression : ((List.range' start count).map fun k => (depth :: tail).count k) =
        ((List.range' start count).map fun k => tail.count k + if depth = k then 1 else 0) := by
      apply List.map_congr_left
      intro k _
      simp [List.count_cons]
    rw [expression, histogram_mass_map_add, ih, histogram_mass_impulse]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Real canonical K differences are sums over the same consecutive code
indices that delimit each constructor root group. -/
theorem canonical_interval_mass (ls : List Nat) (first finish : Nat) (order : first ≤ finish) :
    K ls finish = K ls first +
      ((List.range (finish - first)).map fun k => 2 ^ (15 - L ls (first + k))).sum := by
  induction finish with
  | zero => have : first = 0 := by omega
            subst first
            simp
  | succ finish ih =>
    by_cases same : first = finish + 1
    · subst first
      simp
    have previous := ih (by omega)
    rw [K_succ, previous, show finish + 1 - first = (finish - first) + 1 by omega,
      List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    rw [show first + (finish - first) = finish by omega]
    omega

#print axioms histogram_mass_map_add
#print axioms histogram_mass_impulse
#print axioms histogram_mass_counts
#print axioms canonical_interval_mass


/-- Summing a histogram over a range counts exactly the symbols in that range. -/
theorem histogram_count_sum (depths : List Nat) (start count : Nat) :
    ((List.range' start count).map fun k => depths.count k).sum =
      (depths.map fun depth => if start ≤ depth ∧ depth < start + count then 1 else 0).sum := by
  have additive : ∀ indices : List Nat, ∀ f g : Nat → Nat,
      (indices.map fun k => f k + g k).sum = (indices.map f).sum + (indices.map g).sum := by
    intro indices f g
    induction indices with
    | nil => rfl
    | cons k ks ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  have impulse : ∀ count start depth : Nat,
      ((List.range' start count).map fun k => if depth = k then 1 else 0).sum =
        if start ≤ depth ∧ depth < start + count then 1 else 0 := by
    intro count
    induction count with
    | zero => intro start depth; simp only [List.range'_zero, List.map_nil, List.sum_nil]; rw [ite_eq_right (by omega)]
    | succ count ih =>
      intro start depth
      rw [List.range'_succ]
      simp only [List.map_cons, List.sum_cons, ih]
      by_cases same : depth = start
      · subst depth
        rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_zero]
      · rw [ite_eq_right same, Nat.zero_add]
        by_cases inside : start + 1 ≤ depth ∧ depth < start + 1 + count
        · rw [ite_eq_left inside, ite_eq_left (by omega)]
        · rw [ite_eq_right inside, ite_eq_right (by omega)]
  induction depths with
  | nil =>
    have zero : ∀ indices : List Nat, (indices.map fun _ => (0 : Nat)).sum = 0 := by
      intro indices
      induction indices with
      | nil => rfl
      | cons k ks ih => simpa using ih
    simpa only [List.count_nil, List.map_nil, List.sum_nil] using zero (List.range' start count)
  | cons depth tail ih =>
    have expression : ((List.range' start count).map fun k => (depth :: tail).count k) =
        ((List.range' start count).map fun k => tail.count k + if depth = k then 1 else 0) := by
      apply List.map_congr_left
      intro k _
      simp [List.count_cons]
    rw [expression, additive, ih, impulse]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A complete set of subtree code depths needs at least 2^a+(b-a)
leaves when its shortest possible depth is a and longest attained depth b. -/
theorem complete_depths_leaf_lower_bound {depths : List Nat} {a b : Nat}
    (interval : a ≤ b) (bounds : ∀ d ∈ depths, a ≤ d ∧ d ≤ b)
    (last : b ∈ depths) (kraft : (depths.map fun d => 2 ^ (b - d)).sum = 2 ^ b) :
    2 ^ a + b ≤ depths.length + a := by
  let histogram := (List.range' a (b - a + 1)).map fun k => depths.count k
  have countLevels : histogram.length = b - a + 1 := by simp [histogram]
  have lastHistogram : histogram.getLast? = some (depths.count b) := by
    simp only [histogram, List.getLast?_map, List.getLast?_range']
    rw [ite_eq_right (by omega)]
    simp only [Option.map_some]
    congr 2
    omega
  have occupied : 0 < depths.count b := List.count_pos_iff.mpr last
  have mass : histogramMass histogram = 2 ^ a * 2 ^ (histogram.length - 1) := by
    rw [histogram_mass_counts]
    have mapped : (depths.map fun depth => if a ≤ depth ∧ depth < a + (b - a + 1) then
        2 ^ (a + (b - a + 1) - 1 - depth) else 0) = depths.map (fun depth => 2 ^ (b - depth)) := by
      apply List.map_congr_left
      intro d mem
      have bound := bounds d mem
      rw [ite_eq_left (by omega)]
      congr 1
      omega
    rw [mapped, kraft, countLevels, Nat.add_sub_cancel, ← Nat.pow_add]
    congr 1
    omega
  have complete := complete_frontier_of_mass lastHistogram occupied mass
  have minimum := complete_frontier_depth_budget interval countLevels complete
  have total := histogram_count_sum depths a (b - a + 1)
  have allOnes : ∀ xs : List Nat, (∀ d ∈ xs, a ≤ d ∧ d ≤ b) →
      (xs.map fun depth => if a ≤ depth ∧ depth < a + (b - a + 1) then 1 else 0).sum = xs.length := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons d ds ih =>
      intro limits
      have first := limits d (by simp)
      have tailBounds : ∀ e ∈ ds, a ≤ e ∧ e ≤ b := by intro e mem; exact limits e (by simp [mem])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ite_eq_left (by omega), ih tailBounds]
      omega
  have ones := allOnes depths bounds
  rw [ones] at total
  change 2 ^ a + b ≤ depths.length + a
  change 2 ^ a + b ≤ histogram.sum + a at minimum
  rw [show histogram.sum = depths.length from total] at minimum
  exact minimum

#print axioms histogram_count_sum
#print axioms complete_depths_leaf_lower_bound


/-- A real complete canonical root group has the leaf-count lower bound
needed by the analytic ENOUGH argument. All inputs refer to its actual
allocation interval and its Kraft endpoint. -/
theorem canonical_group_leaf_budget {ls : List Nat} {root mx first finish : Nat}
    (code : CompleteCode ls root mx) (firstPositive : 1 ≤ first)
    (nonempty : first < finish) (inside : finish ≤ nz ls)
    (start : startsAt ls root (first - 1))
    (same : grp ls root (finish - 1) = grp ls root first)
    (terminalAligned : 2 ^ (15 - root) ∣ K ls finish) :
    2 ^ (L ls first - root) + (L ls (finish - 1) - root) ≤
      (finish - first) + (L ls first - root) := by
  let a := L ls first - root
  let b := L ls (finish - 1) - root
  let factor := 2 ^ (15 - L ls (finish - 1))
  let depths := (List.range (finish - first)).map fun k => L ls (first + k) - root
  have firstInside : first < nz ls := by omega
  have lastInside : finish - 1 < nz ls := by omega
  have startIndex : first - 1 + 1 = first := by omega
  have long : root < L ls first := by simpa only [startIndex] using start.1
  have monotone := L_mono ls (show first ≤ finish - 1 by omega) lastInside
  have limits : ∀ k, k < finish - first →
      root < L ls (first + k) ∧ L ls first ≤ L ls (first + k) ∧
      L ls (first + k) ≤ L ls (finish - 1) := by
    intro k member
    have indexInside : first + k < nz ls := by omega
    have left := L_mono ls (show first ≤ first + k by omega) indexInside
    have right := L_mono ls (show first + k ≤ finish - 1 by omega) lastInside
    omega
  have bounds : ∀ d ∈ depths, a ≤ d ∧ d ≤ b := by
    intro d member
    obtain ⟨k, mem, equal⟩ := List.mem_map.mp member
    have info := limits k (List.mem_range.mp mem)
    subst d
    dsimp only [a, b]
    omega
  have lastDepth : b ∈ depths := by
    apply List.mem_map.mpr
    refine ⟨finish - first - 1, List.mem_range.mpr (by omega), ?_⟩
    dsimp only [b]
    rw [show first + (finish - first - 1) = finish - 1 by omega]
  have source := canonical_interval_mass ls first finish (by omega)
  have endpoint := canonical_group_endpoint code firstPositive nonempty inside start same terminalAligned
  have sumSource : ((List.range (finish - first)).map fun k => 2 ^ (15 - L ls (first + k))).sum =
      2 ^ (15 - root) := by omega
  have powerMap : ((List.range (finish - first)).map fun k => 2 ^ (15 - L ls (first + k))) =
      ((List.range (finish - first)).map fun k => 2 ^ (b - (L ls (first + k) - root)) * factor) := by
    apply List.map_congr_left
    intro k member
    have info := limits k (List.mem_range.mp member)
    have length15 := (L_interval ls lastInside).2.1
    dsimp only [b, factor]
    rw [← Nat.pow_add]
    congr 1
    omega
  have factorSum : ∀ xs : List Nat,
      (xs.map fun d => 2 ^ (b - d) * factor).sum = (xs.map fun d => 2 ^ (b - d)).sum * factor := by
    intro xs
    induction xs with
    | nil => simp
    | cons d ds ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]
  have scaled : (depths.map fun d => 2 ^ (b - d)).sum * factor = 2 ^ (15 - root) := by
    rw [powerMap] at sumSource
    rw [← factorSum]
    simpa only [depths, List.map_map, Function.comp_def] using sumSource
  have totalFactor : 2 ^ (15 - root) = 2 ^ b * factor := by
    dsimp only [b, factor]
    rw [← Nat.pow_add]
    congr 1
    have bound := (L_interval ls lastInside).2.1
    omega
  rw [totalFactor] at scaled
  have kraft := Nat.mul_right_cancel (show 0 < factor from Nat.two_pow_pos _) scaled
  have result := complete_depths_leaf_lower_bound (by dsimp only [a, b]; omega) bounds lastDepth kraft
  simpa only [depths, List.length_map, List.length_range, a, b] using result

#print axioms canonical_group_leaf_budget


/-- A finite scan either finds the next marked index or reaches its end. -/
theorem finite_next_boundary (marked : Nat → Prop) [DecidablePred marked]
    (first distance : Nat) :
    ∃ finish, first < finish ∧ finish ≤ first + distance + 1 ∧
      (finish = first + distance + 1 ∨ marked finish) ∧
      (∀ k, first < k → k < finish → ¬ marked k) := by
  induction distance generalizing first with
  | zero => exact ⟨first + 1, by omega, by omega, Or.inl (by omega), by intro k lower upper; omega⟩
  | succ distance ih =>
    by_cases next : marked (first + 1)
    · exact ⟨first + 1, by omega, by omega, Or.inr next, by intro k lower upper; omega⟩
    obtain ⟨finish, lower, upper, boundary, minimal⟩ := ih (first + 1)
    refine ⟨finish, by omega, by omega, ?_, ?_⟩
    · rcases boundary with last | found
      · exact Or.inl (by omega)
      · exact Or.inr found
    · intro k after before
      by_cases immediate : k = first + 1
      · simpa only [immediate] using next
      · exact minimal k (by omega) before

/-- With no real startsAt transition, all long codes remain in one root group. -/
theorem no_starts_same_group {ls : List Nat} {root first finish : Nat}
    (firstInside : first < nz ls) (lastInside : finish < nz ls) (order : first ≤ finish)
    (long : root < L ls first)
    (noStart : ∀ k, first < k → k ≤ finish → ¬ startsAt ls root (k - 1)) :
    grp ls root finish = grp ls root first := by
  induction finish with
  | zero => have : first = 0 := by omega
            subst first
            rfl
  | succ finish ih =>
    by_cases same : first = finish + 1
    · subst first
      rfl
    have previous := ih (by omega) (by omega) (by intro k lower upper; exact noStart k lower (by omega))
    have ordered := L_mono ls (show first ≤ finish + 1 by omega) lastInside
    have no := noStart (finish + 1) (by omega) (by omega)
    have equal : grp ls root (finish + 1) = grp ls root finish := by
      by_cases equal : grp ls root (finish + 1) = grp ls root finish
      · exact equal
      · apply False.elim
        apply no
        simp only [Nat.add_sub_cancel, startsAt]
        exact ⟨by omega, Or.inr equal⟩
    exact equal.trans previous

/-- Every actual next-group boundary, including the complete final
boundary, is aligned to a root-slot Kraft unit. -/
theorem canonical_boundary_aligned {ls : List Nat} {root mx finish : Nat}
    (code : CompleteCode ls root mx) (positive : 1 ≤ finish)
    (inside : finish ≤ nz ls) (boundary : finish = nz ls ∨ startsAt ls root (finish - 1)) :
    2 ^ (15 - root) ∣ K ls finish := by
  rcases boundary with final | next
  · rw [final, code.complete]
    exact Nat.pow_dvd_pow 2 (by omega)
  · by_cases final : finish = nz ls
    · rw [final, code.complete]
      exact Nat.pow_dvd_pow 2 (by omega)
    have aligned := start_aligned code (i := finish - 1) (by omega) next
    rw [show finish - 1 + 1 = finish by omega] at aligned
    rw [aligned]
    exact Nat.dvd_mul_left _ _

#print axioms finite_next_boundary
#print axioms no_starts_same_group
#print axioms canonical_boundary_aligned


/-- The true constructor allocations telescope over consecutive canonical
root groups. No ENOUGH condition or constructor success is a premise. -/
theorem desc_long_tail_amortized {ls : List Nat} {root mx first : Nat}
    (code : CompleteCode ls root mx) (positive : 1 ≤ first)
    (inside : first < nz ls) (start : startsAt ls root (first - 1)) :
    (desc ls root mx (nz ls - 1)).used + 2 ^ (L ls first - root) + (mx - root) ≤
      (desc ls root mx (first - 1)).used + (nz ls - first) +
        2 ^ (mx - root) + (L ls first - root) := by
  suffices all : ∀ remaining first, nz ls - first = remaining →
      1 ≤ first → first < nz ls → startsAt ls root (first - 1) →
      (desc ls root mx (nz ls - 1)).used + 2 ^ (L ls first - root) + (mx - root) ≤
        (desc ls root mx (first - 1)).used + (nz ls - first) +
          2 ^ (mx - root) + (L ls first - root) by
    exact all (nz ls - first) first rfl positive inside start
  intro remaining
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    intro first difference positive inside start
    obtain ⟨finish, after, before, found, noStart⟩ :=
      finite_next_boundary (fun k => startsAt ls root (k - 1)) first (nz ls - first - 1)
    have endpoint : first + (nz ls - first - 1) + 1 = nz ls := by omega
    rw [endpoint] at before found
    have boundary : finish = nz ls ∨ startsAt ls root (finish - 1) := found
    have firstIndex : first - 1 + 1 = first := by omega
    have long : root < L ls first := by simpa only [firstIndex] using start.1
    have lastInside : finish - 1 < nz ls := by omega
    have order := L_mono ls (show first ≤ finish - 1 by omega) lastInside
    have same := no_starts_same_group inside lastInside (by omega) long
      (by intro k lower upper; exact noStart k lower (by omega))
    have aligned := canonical_boundary_aligned code (by omega) before boundary
    have filled := canonical_group_endpoint code positive after before start same aligned
    have width := width_eq_group_last code positive after before start same filled
    have leaves := canonical_group_leaf_budget code positive after before start same aligned
    have sameDesc := desc_same_group (mx := mx) inside lastInside long (by omega) same.symm
    have allocation := desc_succ_of_starts ls root mx (first - 1) start
    rw [firstIndex] at allocation
    have current : (desc ls root mx (finish - 1)).used =
        (desc ls root mx (first - 1)).used + 2 ^ (L ls (finish - 1) - root) := by
      rw [← sameDesc, allocation]
      simp only [width]
    have maxLength := code.L_le_mx lastInside
    have topGap := power_linear_growth (show L ls (finish - 1) - root ≤ mx - root by omega)
    by_cases final : finish = nz ls
    · rw [final] at current leaves topGap
      omega
    · have nextStart : startsAt ls root (finish - 1) := by
        rcases boundary with equal | next
        · contradiction
        · exact next
      have tail := ih (nz ls - finish) (by omega) finish rfl (by omega) (by omega) nextStart
      have nextOrder := L_mono ls (show finish - 1 ≤ finish by omega) (show finish < nz ls by omega)
      have gap := power_linear_growth (show L ls (finish - 1) - root ≤ L ls finish - root by omega)
      omega

#print axioms desc_long_tail_amortized


/-- Every allocation in a real nonempty complete constructor has even
size, because root and secondary-table widths are positive. -/
theorem desc_used_even {ls : List Nat} {root mx i : Nat}
    (code : CompleteCode ls root mx) (inside : i < nz ls) :
    2 ∣ (desc ls root mx i).used := by
  induction i with
  | zero =>
    change 2 ∣ 2 ^ root
    exact Nat.dvd_trans (show 2 ∣ 2 ^ 1 by decide) (Nat.pow_dvd_pow 2 code.root_pos)
  | succ i ih =>
    have previous := ih (by omega)
    by_cases start : startsAt ls root i
    · have width := width_spec ls inside code.mx_le start.1 (code.L_le_mx inside)
      have long := start.1
      have positiveWidth : 1 ≤ Canon.width ls (i + 1) root mx := by omega
      rw [desc_succ_of_starts ls root mx i start]
      exact Nat.dvd_add previous (Nat.dvd_trans (show 2 ∣ 2 ^ 1 by decide)
        (Nat.pow_dvd_pow 2 positiveWidth))
    · rw [desc_succ_of_not ls root mx i start]
      exact previous

/-- Exact ENOUGH_LENS bound for the real descriptor, for complete codes
using the default nine-bit root. There is no capacity precondition. -/
theorem lens_desc_used_le_852 {ls : List Nat} {mx : Nat}
    (code : CompleteCode ls 9 mx) (count : nz ls ≤ 286) :
    (desc ls 9 mx (nz ls - 1)).used ≤ 852 := by
  have lastInside : nz ls - 1 < nz ls := by have := code.pos; omega
  by_cases short : L ls (nz ls - 1) ≤ 9
  · rw [desc_short ls lastInside short]
    simp only [desc]
    decide
  let first := offL ls 10
  have enoughShort := lens_at_least_two_short code.pos code.complete count
  have firstInside : first < nz ls := by
    have classify := lt_offL_iff ls lastInside (l := 9)
    change nz ls - 1 < first ↔ L ls (nz ls - 1) ≤ 9 at classify
    omega
  have positive : 1 ≤ first := by dsimp only [first]; omega
  have beforeInside : first - 1 < nz ls := by omega
  have previousShort : L ls (first - 1) ≤ 9 := by
    apply (lt_offL_iff ls beforeInside (l := 9)).mp
    change first - 1 < first
    omega
  have firstLong : 9 < L ls first := by
    have classify := lt_offL_iff ls firstInside (l := 9)
    change first < first ↔ L ls first ≤ 9 at classify
    omega
  have start : startsAt ls 9 (first - 1) := by
    unfold startsAt
    rw [show first - 1 + 1 = first by omega]
    exact ⟨firstLong, Or.inl previousShort⟩
  have tail := desc_long_tail_amortized code positive firstInside start
  rw [desc_short ls beforeInside previousShort] at tail
  simp only [desc, Nat.reducePow] at tail
  have smallDepth : L ls first - 9 ≤ mx - 9 := by
    have := code.L_le_mx firstInside
    omega
  have six : mx - 9 ≤ 6 := by have := code.mx_le; omega
  have rootPotential := power_linear_growth six
  have firstPotential := power_linear_growth (show 1 ≤ L ls first - 9 by omega)
  simp only [Nat.reducePow] at rootPotential firstPotential
  have shortCount : 2 ≤ first := enoughShort
  have rough : (desc ls 9 mx (nz ls - 1)).used ≤ 853 := by omega
  obtain ⟨half, even⟩ := desc_used_even code lastInside
  omega

/-- The actual min/max clamp is included: short complete alphabets use
only their smaller root table; long ones satisfy the nine-bit bound. -/
theorem lens_default_desc_budget {ls : List Nat} {root mx : Nat}
    (code : CompleteCode ls root mx) (count : nz ls ≤ 286)
    (clamped : root = max (L ls 0) (min 9 mx)) :
    (desc ls root mx (nz ls - 1)).used ≤ 852 := by
  have firstLength := code.L_le_mx (show 0 < nz ls from code.pos)
  by_cases short : mx ≤ 9
  · have same : root = mx := by omega
    have single := desc_requested_short code (show nz ls - 1 < nz ls by have := code.pos; omega)
      (show mx ≤ root by omega)
    rw [single]
    have power := Nat.pow_le_pow_right (n := 2) (by omega) (show root ≤ 9 by omega)
    have small : 2 ^ 9 ≤ 852 := by decide
    omega
  · have shortest := lens_root_not_increased code.complete count
    have same : root = 9 := by omega
    rw [same] at code ⊢
    exact lens_desc_used_le_852 code count

#print axioms desc_used_even
#print axioms lens_desc_used_le_852
#print axioms lens_default_desc_budget


/-- A complete distance alphabet that needs secondary tables has at least
three short codes when it contains at most 30 used symbols. -/
theorem dist_at_least_three_short {ls : List Nat} {mx : Nat}
    (code : CompleteCode ls 6 mx) (count : nz ls ≤ 30) (long : 6 < mx) :
    3 ≤ offL ls 7 := by
  have lastInside : nz ls - 1 < nz ls := by have := code.pos; omega
  have lastLong : 6 < L ls (nz ls - 1) := by rw [← code.mx_eq]; exact long
  have firstLength := (L_interval ls code.pos).1
  have firstPower : 2 ^ (15 - L ls 0) ≤ 2 ^ 14 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have firstMass : K ls 1 ≤ 16384 := by simpa [K_succ, K_zero] using firstPower
  have atLeastThree : 3 ≤ nz ls := by
    by_cases many : 3 ≤ nz ls
    · exact many
    have cases : nz ls = 1 ∨ nz ls = 2 := by have := code.pos; omega
    have complete := code.complete
    rcases cases with one | two
    · have oneLong : 6 < L ls 0 := by simpa [one] using lastLong
      have power : 2 ^ (15 - L ls 0) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
      rw [one, K_succ, K_zero] at complete
      simp only [Nat.zero_add, Nat.reducePow] at complete power
      omega
    · have secondLong : 6 < L ls 1 := by simpa [two] using lastLong
      have power : 2 ^ (15 - L ls 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
      rw [two, K_succ] at complete
      simp only [Nat.reducePow] at complete power
      omega
  have secondInside : 1 < nz ls := by omega
  have secondPositive := (L_interval ls secondInside).1
  have ordered := L_mono ls (show 0 ≤ 1 by omega) secondInside
  have secondTwo : 2 ≤ L ls 1 := by
    by_cases wide : 2 ≤ L ls 1
    · exact wide
    have one : L ls 1 = 1 := by omega
    have firstOne : L ls 0 = 1 := by omega
    have full : K ls 2 = 2 ^ 15 := by simp [K_succ, K_zero, one, firstOne]
    have after := K_strict ls (show 2 < nz ls by omega)
    rw [full, code.complete] at after
    omega
  have secondPower : 2 ^ (15 - L ls 1) ≤ 2 ^ 13 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have twoMass : K ls 2 ≤ 24576 := by
    rw [K_succ]
    simp only [Nat.reducePow] at secondPower
    omega
  by_cases enough : 3 ≤ offL ls 7
  · exact enough
  have remaining : ∀ i, 2 ≤ i → i < nz ls → 7 ≤ L ls i := by
    intro i after inside
    have classify := lt_offL_iff ls inside (l := 6)
    change i < offL ls 7 ↔ L ls i ≤ 6 at classify
    omega
  have tail := kraft_suffix_length_bound ls 2 (nz ls) 7 (by omega) remaining
  rw [code.complete] at tail
  simp only [Nat.reducePow, Nat.reduceSub] at tail
  omega

/-- Real default six-bit distance descriptors use at most 592 slots. -/
theorem dist_desc_used_le_592 {ls : List Nat} {mx : Nat}
    (code : CompleteCode ls 6 mx) (count : nz ls ≤ 30) :
    (desc ls 6 mx (nz ls - 1)).used ≤ 592 := by
  have lastInside : nz ls - 1 < nz ls := by have := code.pos; omega
  by_cases short : L ls (nz ls - 1) ≤ 6
  · rw [desc_short ls lastInside short]
    simp only [desc]
    decide
  let first := offL ls 7
  have maxLong : 6 < mx := by rw [code.mx_eq]; omega
  have enoughShort := dist_at_least_three_short code count maxLong
  have firstInside : first < nz ls := by
    have classify := lt_offL_iff ls lastInside (l := 6)
    change nz ls - 1 < first ↔ L ls (nz ls - 1) ≤ 6 at classify
    omega
  have positive : 1 ≤ first := by dsimp only [first]; omega
  have beforeInside : first - 1 < nz ls := by omega
  have previousShort : L ls (first - 1) ≤ 6 := by
    apply (lt_offL_iff ls beforeInside (l := 6)).mp
    change first - 1 < first
    omega
  have firstLong : 6 < L ls first := by
    have classify := lt_offL_iff ls firstInside (l := 6)
    change first < first ↔ L ls first ≤ 6 at classify
    omega
  have start : startsAt ls 6 (first - 1) := by
    unfold startsAt
    rw [show first - 1 + 1 = first by omega]
    exact ⟨firstLong, Or.inl previousShort⟩
  have tail := desc_long_tail_amortized code positive firstInside start
  rw [desc_short ls beforeInside previousShort] at tail
  simp only [desc, Nat.reducePow] at tail
  have nine : mx - 6 ≤ 9 := by have := code.mx_le; omega
  have rootPotential := power_linear_growth nine
  have firstPotential := power_linear_growth (show 1 ≤ L ls first - 6 by omega)
  simp only [Nat.reducePow] at rootPotential firstPotential
  have shortCount : 3 ≤ first := enoughShort
  have rough : (desc ls 6 mx (nz ls - 1)).used ≤ 593 := by omega
  obtain ⟨half, even⟩ := desc_used_even code lastInside
  omega

/-- The default distance bound includes the real min/max root adjustment. -/
theorem dist_default_desc_budget {ls : List Nat} {root mx : Nat}
    (code : CompleteCode ls root mx) (count : nz ls ≤ 30)
    (clamped : root = max (L ls 0) (min 6 mx)) :
    (desc ls root mx (nz ls - 1)).used ≤ 592 := by
  have firstLength := code.L_le_mx (show 0 < nz ls from code.pos)
  by_cases short : mx ≤ 6
  · have same : root = mx := by omega
    have single := desc_requested_short code (show nz ls - 1 < nz ls by have := code.pos; omega)
      (show mx ≤ root by omega)
    rw [single]
    have power := Nat.pow_le_pow_right (n := 2) (by omega) (show root ≤ 6 by omega)
    have small : 2 ^ 6 ≤ 592 := by decide
    omega
  · have shortest := complete_min_le_requested code.complete
        (show nz ls < 2 ^ 6 by omega) (show 6 ≤ 15 by omega)
    have same : root = 6 := by omega
    rw [same] at code ⊢
    exact dist_desc_used_le_592 code count

/-- Accepted empty and single-symbol alphabets have no repeated descriptor
allocation; their actual one-bit representation uses two slots. -/
theorem small_alphabet_desc_budget {ls : List Nat} {root mx : Nat}
    (small : nz ls ≤ 1) (oneBit : root = 1) :
    (desc ls root mx (nz ls - 1)).used = 2 := by
  rw [show nz ls - 1 = 0 by omega, oneBit]
  rfl

#print axioms dist_at_least_three_short
#print axioms dist_desc_used_le_592
#print axioms dist_default_desc_budget
#print axioms small_alphabet_desc_budget

end Zlib.Inftrees.Proofs.DefaultBudget
