import ImbalancedChen.P4AOriginalFull87FourHistoryPhysicalTuple
import ImbalancedChen.P4AOriginalFull87OddCeilingEightWord
import ImbalancedChen.P4AOriginalFull87RankNineHistoryRisk
import ImbalancedChen.P4AOriginalFull87ActualEighthCarrier
import ImbalancedChen.PrimeHistoryLogCoordinates
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: connect the ACTUAL eight-prime reverse-stored selectedPrefix to
the original four physical inherited odd-square gates. The source
history is recovered from primeHistoryTuple_reverse_ofFn, not a new
synthetic prime population. The exact original 87-domain owner/trim
source and actual finite cap are kept.

The resulting strict J < cap is only for the CAP side. In particular
this file does NOT claim J < actualParent, no historical charge at
parent, asymptotic estimate, or reserve payment.
-/

namespace ImbalancedChen.P4AOriginalFull87CapHistoricalCeiling
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87FourHistoryPhysicalTuple
  (owned_four_physical_tuple_gates_below_actual_cap)
open P4AOriginalFull87OddCeilingEightWord
  (actual_eight_odd_square_ceiling_lt)
open P4AOriginalFull87RankNineHistoryRisk
  (historyOddSquareCeiling rankNineInheritedAt
   rankNineInheritedReciprocalCost
   actual_inherited_nil_of_history_ceiling
   actual_inherited_cost_zero_of_history_ceiling)
open P4AOriginalFull87Post8GuardExtraction
  (actualFrozenPost8Level)

/-- A finite suffix is setified only to evaluate the ORIGINAL
historical Rosser test. Under literal strict order, no prime can
disappear from its product through duplicate removal. -/
private theorem nodup_toFinset_prod (xs : List ℕ) (hxs : xs.Nodup) :
    xs.toFinset.prod id = xs.prod := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
      have hp : p ∉ ps.toFinset := by
        simpa using (List.nodup_cons.mp hxs).1
      have hps : ps.Nodup := (List.nodup_cons.mp hxs).2
      simp [List.toFinset_cons, Finset.prod_insert hp, ih hps]

/-- The four EXACT tuple-prefix gates imply the actual eight-word
Rosser ceiling. The proof keeps all four distinct suffixes and their
original strict cardinality/parity test; it does not weaken the
historical gate to the ordinary prefix-square test. -/
theorem ordered_tuple_gates_imply_eight_ceiling
    (P : Fin 8 → ℕ) (hanti : StrictAnti P) (R : ℝ)
    (hgates : ∀ j : Fin 4,
      (∏ i ∈ Finset.univ.filter
        (fun i : Fin 8 => i.val ≤ 2 * j.val), (P i : ℝ)) *
      (P ⟨2 * j.val, by omega⟩ : ℝ) ^ 2 < R) :
    historyOddSquareCeiling
      [P ⟨7, by decide⟩, P ⟨6, by decide⟩,
       P ⟨5, by decide⟩, P ⟨4, by decide⟩,
       P ⟨3, by decide⟩, P ⟨2, by decide⟩,
       P ⟨1, by decide⟩, P ⟨0, by decide⟩] < R := by
  let p0 : ℕ := P ⟨0, by decide⟩
  let p1 : ℕ := P ⟨1, by decide⟩
  let p2 : ℕ := P ⟨2, by decide⟩
  let p3 : ℕ := P ⟨3, by decide⟩
  let p4 : ℕ := P ⟨4, by decide⟩
  let p5 : ℕ := P ⟨5, by decide⟩
  let p6 : ℕ := P ⟨6, by decide⟩
  let p7 : ℕ := P ⟨7, by decide⟩
  have h01 : p1 < p0 := hanti (by decide)
  have h12 : p2 < p1 := hanti (by decide)
  have h23 : p3 < p2 := hanti (by decide)
  have h34 : p4 < p3 := hanti (by decide)
  have h45 : p5 < p4 := hanti (by decide)
  have h56 : p6 < p5 := hanti (by decide)
  have h67 : p7 < p6 := hanti (by decide)
  have hn0 : ([p0] : List ℕ).Nodup := by simp
  have hn2 : ([p2,p1,p0] : List ℕ).Nodup := by
    simp [List.nodup_cons]
    omega
  have hn4 : ([p4,p3,p2,p1,p0] : List ℕ).Nodup := by
    simp [List.nodup_cons]
    omega
  have hn6 : ([p6,p5,p4,p3,p2,p1,p0] : List ℕ).Nodup := by
    simp [List.nodup_cons]
    omega
  have h0 :
      ((([p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) *
        (p0 : ℝ) ^ 2 < R := by
    convert hgates ⟨0, by decide⟩ using 1
    rw [nodup_toFinset_prod _ hn0]
    norm_num [Finset.prod_filter, Fin.prod_univ_succ,
      List.prod_cons, p0]
    ring
  have h2 :
      ((([p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) *
        (p2 : ℝ) ^ 2 < R := by
    convert hgates ⟨1, by decide⟩ using 1
    rw [nodup_toFinset_prod _ hn2]
    norm_num [Finset.prod_filter, Fin.prod_univ_succ,
      List.prod_cons, p0, p1, p2]
    ring
  have h4 :
      ((([p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) *
        (p4 : ℝ) ^ 2 < R := by
    convert hgates ⟨2, by decide⟩ using 1
    rw [nodup_toFinset_prod _ hn4]
    norm_num [Finset.prod_filter, Fin.prod_univ_succ,
      List.prod_cons, p0, p1, p2, p3, p4]
    ring
  have h6 :
      ((([p6,p5,p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) *
        (p6 : ℝ) ^ 2 < R := by
    convert hgates ⟨3, by decide⟩ using 1
    rw [nodup_toFinset_prod _ hn6]
    norm_num [Finset.prod_filter, Fin.prod_univ_succ,
      List.prod_cons, p0, p1, p2, p3, p4, p5, p6]
    ring
  change historyOddSquareCeiling
    [p7,p6,p5,p4,p3,p2,p1,p0] < R
  exact actual_eight_odd_square_ceiling_lt
    p0 p1 p2 p3 p4 p5 p6 p7
    h01 h12 h23 h34 h45 h56 h67 R h6 h4 h2 h0

/-- This is the missing physical bridge on EVERY genuine original
87-domain owned eighth occurrence. The original reverse-stored history
word, its strict order and all four primitive historical gates come
from the SAME original carrier and finiteCap. No hypothetical history
licence, synthetic tuple or archived numerical assumption is supplied. -/
theorem owned_actual_history_ceiling_below_cap
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hn : 4 * width n < width r)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    historyOddSquareCeiling s.selectedPrefix <
      actualFrozenPost8Level n e q om N c s false := by
  obtain ⟨hlen, hsort, _hrem, _hboundary, _hcut⟩ :=
    owned87_eighth_state_exact_carrier
      (width r) n e q om N cap w z c s hs
  let P : Fin 8 → ℕ := primeHistoryTuple 8 s.selectedPrefix
  have hanti : StrictAnti P :=
    primeHistoryTuple_strictAnti hlen hsort
  have hword :
      s.selectedPrefix =
        [P ⟨7, by decide⟩, P ⟨6, by decide⟩,
         P ⟨5, by decide⟩, P ⟨4, by decide⟩,
         P ⟨3, by decide⟩, P ⟨2, by decide⟩,
         P ⟨1, by decide⟩, P ⟨0, by decide⟩] := by
    have hreverse := primeHistoryTuple_reverse_ofFn
      (k := 8) (history := s.selectedPrefix) hlen
    simpa [P, List.ofFn] using hreverse.symm
  have hgates : ∀ j : Fin 4,
      (∏ i ∈ Finset.univ.filter
        (fun i : Fin 8 => i.val ≤ 2 * j.val), (P i : ℝ)) *
      (P ⟨2 * j.val, by omega⟩ : ℝ) ^ 2 <
        actualFrozenPost8Level n e q om N c s false := by
    simpa only [P] using
      owned_four_physical_tuple_gates_below_actual_cap
        r n e q om N cap hN w z c s hn hs
  rw [hword]
  exact ordered_tuple_gates_imply_eight_ceiling P hanti
    (actualFrozenPost8Level n e q om N c s false) hgates

/-- As a consequence, the actual cap policy has NO ninth-rank
INHERITED historical-square rejected occurrence. This is a literal
list equality, not an absolute bound, and makes no assertion about
parent-side inheritance, full rank-nine corrections, or signed gain. -/
theorem owned_cap_rankNine_inherited_nil
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hn : 4 * width n < width r)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    rankNineInheritedAt n e q om N c s false = [] :=
  actual_inherited_nil_of_history_ceiling
    (width r) n e q om N cap w z c s hs false
    (owned_actual_history_ceiling_below_cap
      r n e q om N cap hN w z c s hn hs)

/-- The cap-side inherited reciprocal invoice is exactly zero,
rather than merely bounded by its generic risk support. Other
rank-nine modes and all parent-side expenses remain unaltered. -/
theorem owned_cap_rankNine_inherited_cost_zero
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hn : 4 * width n < width r)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    rankNineInheritedReciprocalCost n e q om N c s false = 0 :=
  actual_inherited_cost_zero_of_history_ceiling
    (width r) n e q om N cap w z c s hs false
    (owned_actual_history_ceiling_below_cap
      r n e q om N cap hN w z c s hn hs)

end
end ImbalancedChen.P4AOriginalFull87CapHistoricalCeiling
