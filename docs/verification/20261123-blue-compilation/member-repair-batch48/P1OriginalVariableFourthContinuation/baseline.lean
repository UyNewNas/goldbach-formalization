import ImbalancedChen.P1CoarseFirstCubeFallbackMargin
import ImbalancedChen.FirstExitHistoricalLevels
import ImbalancedChen.P2OriginalFourthCapProducerInterface
import Mathlib.Data.Finset.Max

/-!
The original variable fourth profile retains its inherited original rawQ3
floor, then takes the maximum of EVERY eligible pointwise row candidate.
Overlapping rows all participate; no first-match lookup or constant midpoint
is used. Row eligibility/licensing remains explicit data and is not certified
by the max algebra. A single candidate may lie below the inherited floor.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope

namespace P1OriginalVariableFourthContinuation

def finiteValues {ι : Type*} (rows : Finset ι) (eligible : ι → Prop)
    (profile : ι → ℝ) (seed : ℝ) : Finset ℝ :=
  insert seed ((rows.filter eligible).image profile)

theorem finiteValues_nonempty {ι : Type*} (rows : Finset ι) (eligible : ι → Prop)
    (profile : ι → ℝ) (seed : ℝ) : (finiteValues rows eligible profile seed).Nonempty := by
  exact ⟨seed, Finset.mem_insert_self _ _⟩

def finiteMax {ι : Type*} (rows : Finset ι) (eligible : ι → Prop)
    (profile : ι → ℝ) (seed : ℝ) : ℝ :=
  (finiteValues rows eligible profile seed).max' (finiteValues_nonempty rows eligible profile seed)

theorem finiteMax_seed_le {ι : Type*} (rows : Finset ι) (eligible : ι → Prop)
    (profile : ι → ℝ) (seed : ℝ) : seed ≤ finiteMax rows eligible profile seed := by
  exact Finset.le_max' _ seed (Finset.mem_insert_self _ _)

theorem finiteMax_row_le {ι : Type*} (rows : Finset ι) (eligible : ι → Prop)
    (profile : ι → ℝ) (seed : ℝ) (r : ι) (hr : r ∈ rows) (he : eligible r) :
    profile r ≤ finiteMax rows eligible profile seed := by
  exact Finset.le_max' _ (profile r) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, he⟩, rfl⟩))

theorem finiteMax_le {ι : Type*} (rows : Finset ι) (eligible : ι → Prop)
    (profile : ι → ℝ) (seed upper : ℝ) (hseed : seed ≤ upper)
    (hrow : ∀ r ∈ rows, eligible r → profile r ≤ upper) :
    finiteMax rows eligible profile seed ≤ upper := by
  apply Finset.max'_le
  intro value hv
  rcases Finset.mem_insert.mp hv with h | h
  · simpa only [h] using hseed
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h
    exact hrow r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2

theorem finiteMax_le_iff {ι : Type*} (rows : Finset ι) (eligible : ι → Prop)
    (profile : ι → ℝ) (seed upper : ℝ) :
    finiteMax rows eligible profile seed ≤ upper ↔
      seed ≤ upper ∧ ∀ r ∈ rows, eligible r → profile r ≤ upper := by
  constructor
  · intro h
    exact ⟨(finiteMax_seed_le rows eligible profile seed).trans h,
      fun r hr he => (finiteMax_row_le rows eligible profile seed r hr he).trans h⟩
  · rintro ⟨hseed, hrow⟩
    exact finiteMax_le rows eligible profile seed upper hseed hrow

theorem finiteMax_eq_seed_of_outside {ι : Type*} (rows : Finset ι) (eligible : ι → Prop)
    (profile : ι → ℝ) (seed : ℝ) (hout : ∀ r ∈ rows, ¬eligible r) :
    finiteMax rows eligible profile seed = seed := by
  apply le_antisymm
  · exact finiteMax_le rows eligible profile seed seed le_rfl
      (fun r hr he => False.elim (hout r hr he))
  · exact finiteMax_seed_le rows eligible profile seed

theorem finiteMax_eq_seed_of_dominated {ι : Type*} (rows : Finset ι) (eligible : ι → Prop)
    (profile : ι → ℝ) (seed : ℝ) (hrow : ∀ r ∈ rows, eligible r → profile r ≤ seed) :
    finiteMax rows eligible profile seed = seed := by
  exact le_antisymm (finiteMax_le rows eligible profile seed seed le_rfl hrow)
    (finiteMax_seed_le rows eligible profile seed)

def profile4 {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (profile : ι → (Fin 4 → ℝ) → ℝ)
    (t : Fin 4 → ℝ) : ℝ :=
  finiteMax rows (fun r => eligible r t) (fun r => profile r t) seed

theorem profile4_seed_le {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (profile : ι → (Fin 4 → ℝ) → ℝ)
    (t : Fin 4 → ℝ) : seed ≤ profile4 seed rows eligible profile t := by
  exact finiteMax_seed_le rows _ _ seed

theorem profile4_row_le {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (profile : ι → (Fin 4 → ℝ) → ℝ)
    (t : Fin 4 → ℝ) (r : ι) (hr : r ∈ rows) (he : eligible r t) :
    profile r t ≤ profile4 seed rows eligible profile t := by
  exact finiteMax_row_le rows _ _ seed r hr he

theorem profile4_eq_seed_of_outside {ι : Type*} (seed : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (profile : ι → (Fin 4 → ℝ) → ℝ)
    (t : Fin 4 → ℝ) (hout : ∀ r ∈ rows, ¬eligible r t) :
    profile4 seed rows eligible profile t = seed := by
  exact finiteMax_eq_seed_of_outside rows _ _ seed hout

/-- This is the pointwise tent M(t), with its explicit buffer loss. -/
def candidateExponent (loss : ℝ) (I : Finset (Fin 4)) (t : Fin 4 → ℝ) : ℝ :=
  v (∑ i ∈ I, t i) - loss

theorem candidateExponent_eq_min (loss : ℝ) (I : Finset (Fin 4)) (t : Fin 4 → ℝ) :
    candidateExponent loss I t =
      min ((1 + ∑ i ∈ I, t i) / 2) (57 / 64 - (3 / 2 : ℝ) * ∑ i ∈ I, t i) - loss := by
  rw [candidateExponent, v_eq_min]
  rfl

theorem overlapping_candidates_le_profile4 {ι : Type*} (seed loss : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (mask : ι → Finset (Fin 4))
    (t : Fin 4 → ℝ) (r s : ι) (hr : r ∈ rows) (hs : s ∈ rows)
    (her : eligible r t) (hes : eligible s t) :
    max (candidateExponent loss (mask r) t) (candidateExponent loss (mask s) t) ≤
      profile4 seed rows eligible (fun row => candidateExponent loss (mask row)) t := by
  exact max_le (profile4_row_le seed rows eligible _ t r hr her)
    (profile4_row_le seed rows eligible _ t s hs hes)

def seedExponent (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) : ℝ :=
  P1CoarseFirstCubeFallbackMargin.effectiveExponent e chi m omega N (rosserAncestor 3 history)

theorem frozenLevel_eq_rpow_seed (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) :
    frozenLevel e chi m omega N history = N ^ seedExponent e chi m omega N history := by
  exact P1CoarseFirstCubeFallbackMargin.rawLevel_eq_rpow_effectiveExponent
    e chi m omega N (rosserAncestor 3 history)

theorem seedExponent_ancestor_four (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    seedExponent e chi m omega N (rosserAncestor 4 history) =
      seedExponent e chi m omega N history := by
  unfold seedExponent
  rw [rosserAncestor_nested 3 4 (by omega)]

def exponent4 {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (profile : ι → (Fin 4 → ℝ) → ℝ)
    (history : List ℕ) : ℝ :=
  if history.length = 4 then
    profile4 (seedExponent e chi m omega N history) rows eligible profile
      (primeHistoryLogCoordinates N 4 history)
  else seedExponent e chi m omega N history

def level4 {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (profile : ι → (Fin 4 → ℝ) → ℝ)
    (history : List ℕ) : ℝ :=
  N ^ exponent4 e chi m omega N rows eligible profile history

def frozenLevel4 {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (profile : ι → (Fin 4 → ℝ) → ℝ)
    (history : List ℕ) : ℝ :=
  level4 e chi m omega N rows eligible profile (rosserAncestor 4 history)

def policy4 {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (profile : ι → (Fin 4 → ℝ) → ℝ) :
    Bool → List ℕ → Bool :=
  fourthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N)
    (level4 e chi m omega N rows eligible profile)

theorem seedExponent_le_exponent4 {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ι) (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (history : List ℕ) :
    seedExponent e chi m omega N history ≤ exponent4 e chi m omega N rows eligible profile history := by
  unfold exponent4
  split_ifs
  · exact profile4_seed_le _ rows eligible profile _
  · exact le_rfl

theorem exponent4_outside {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ι) (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (history : List ℕ)
    (hout : ∀ r ∈ rows, ¬eligible r (primeHistoryLogCoordinates N 4 history)) :
    exponent4 e chi m omega N rows eligible profile history = seedExponent e chi m omega N history := by
  unfold exponent4
  split_ifs
  · exact profile4_eq_seed_of_outside _ rows eligible profile _ hout
  · rfl

theorem level4_outside {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ι) (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (history : List ℕ)
    (hout : ∀ r ∈ rows, ¬eligible r (primeHistoryLogCoordinates N 4 history)) :
    level4 e chi m omega N rows eligible profile history = frozenLevel e chi m omega N history := by
  rw [level4, exponent4_outside e chi m omega N rows eligible profile history hout]
  exact (frozenLevel_eq_rpow_seed e chi m omega N history).symm

/-- h34 follows from the retained floor, even if every individual row loses. -/
theorem frozenThird_le_level4 {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ) (hN : 1 ≤ N)
    (rows : Finset ι) (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (history : List ℕ) :
    frozenLevel e chi m omega N history ≤ level4 e chi m omega N rows eligible profile history := by
  rw [frozenLevel_eq_rpow_seed, level4]
  exact Real.rpow_le_rpow_of_exponent_le hN
    (seedExponent_le_exponent4 e chi m omega N rows eligible profile history)

theorem frozenLevel4_append {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ι) (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (later history : List ℕ) (hlen : 4 ≤ history.length) :
    frozenLevel4 e chi m omega N rows eligible profile (later ++ history) =
      frozenLevel4 e chi m omega N rows eligible profile history := by
  unfold frozenLevel4
  rw [rosserAncestor_append 4 later history hlen]

theorem frozenLevel4_outside {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ι) (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (history : List ℕ)
    (hout : ∀ r ∈ rows, ¬eligible r (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history))) :
    frozenLevel4 e chi m omega N rows eligible profile history = frozenLevel e chi m omega N history := by
  unfold frozenLevel4
  rw [level4_outside e chi m omega N rows eligible profile (rosserAncestor 4 history) hout]
  unfold frozenLevel
  rw [rosserAncestor_nested 3 4 (by omega)]

/-- The fourth coordinate dictionary projects to the SAME actual third ancestor. -/
theorem original_third_coordinates_project_fourth (N : ℝ) (history : List ℕ)
    (hlen : 4 ≤ history.length) :
    primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) =
      historicalPrefixProject (by omega : 3 ≤ 4)
        (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history)) := by
  have hlen4 : (rosserAncestor 4 history).length = 4 := by
    rw [rosserAncestor_length]
    omega
  have h := primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 4) hlen4
  simpa only [rosserAncestor_nested 3 4 (by omega)] using h

theorem policy4_through_four {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ι) (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (positive : Bool) (history : List ℕ)
    (hlen : history.length ≤ 4) :
    policy4 e chi m omega N rows eligible profile positive history =
      HistoricalThirdCoarse.policy e chi m omega N positive history := by
  simp only [policy4, fourthCappedUpperPolicy, firstExitDepthSplicePolicy, if_pos hlen,
    HistoricalThirdCoarse.policy]

/-- Outside all ancestor-four row regions the actual POLICY also inherits T3. -/
theorem policy4_outside {ι : Type*} (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ι) (eligible : ι → (Fin 4 → ℝ) → Prop)
    (profile : ι → (Fin 4 → ℝ) → ℝ) (positive : Bool) (history : List ℕ)
    (hout : ∀ r ∈ rows, ¬eligible r (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history))) :
    policy4 e chi m omega N rows eligible profile positive history =
      HistoricalThirdCoarse.policy e chi m omega N positive history := by
  by_cases hlen : history.length ≤ 4
  · exact policy4_through_four e chi m omega N rows eligible profile positive history hlen
  · have hdeep : ¬history.length ≤ 2 := by omega
    have hlevel := frozenLevel4_outside e chi m omega N rows eligible profile history hout
    change level4 e chi m omega N rows eligible profile (rosserAncestor 4 history) =
      rawLevel e chi m omega N (rosserAncestor 3 history) at hlevel
    simp only [policy4, fourthCappedUpperPolicy, firstExitDepthSplicePolicy, if_neg hlen,
      frozenParityRosserPolicy, ancestorFrozenPolicy]
    rw [hlevel]
    simp only [HistoricalThirdCoarse.policy, thirdCappedUpperPolicy,
      firstExitDepthSplicePolicy, if_neg hdeep, frozenParityRosserPolicy, ancestorFrozenPolicy]

theorem actual_h34 {ι : Type*} (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ) (rows : Finset ι)
    (eligible : ι → (Fin 4 → ℝ) → Prop) (profile : ι → (Fin 4 → ℝ) → ℝ)
    (state : FirstExitDepthState ℕ)
    (_hstate : state ∈ firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)) :
    rawLevel e chi m omega (N : ℝ) (rosserAncestor 3 state.selectedPrefix) ≤
      level4 e chi m omega (N : ℝ) rows eligible profile state.selectedPrefix := by
  exact frozenThird_le_level4 e chi m omega (N : ℝ) hN rows eligible profile state.selectedPrefix

section ActualProducerRows

open P2OriginalFourthCapProducerInterface

/-- Whole-box buffer/distribution licensing remains an independent row input.
The producer's stronger Geometry predicate includes an improvement gap, so it
is NOT forced here: losing candidates must still be admissible to the max. -/
def producerEligible (licensed : ProducerRow → Prop) (r : ProducerRow) (t : Point) : Prop :=
  licensed r ∧ t ∈ r.box

theorem producerEligible_license (licensed : ProducerRow → Prop) (r : ProducerRow)
    (t : Point) (ht : producerEligible licensed r t) : licensed r := by
  exact ht.1

theorem producerEligible_mem_box (licensed : ProducerRow → Prop) (r : ProducerRow)
    (t : Point) (ht : producerEligible licensed r t) : t ∈ r.box := by
  exact ht.2

def producerProfile4 (e : ℝ) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (seed : ℝ) (t : Point) : ℝ :=
  profile4 seed rows (producerEligible licensed) (fun r => r.bufferedCandidate e) t

def producerLevel4 (e chi : ℝ) (m : ℕ) (omega N : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (history : List ℕ) : ℝ :=
  level4 e chi m omega N rows (producerEligible licensed) (fun r => r.bufferedCandidate e) history

def producerFrozenLevel4 (e chi : ℝ) (m : ℕ) (omega N : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (history : List ℕ) : ℝ :=
  frozenLevel4 e chi m omega N rows (producerEligible licensed) (fun r => r.bufferedCandidate e) history

def producerPolicy4 (e chi : ℝ) (m : ℕ) (omega N : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) : Bool → List ℕ → Bool :=
  policy4 e chi m omega N rows (producerEligible licensed) (fun r => r.bufferedCandidate e)

theorem producer_bufferedCandidate_is_actual (r : ProducerRow) (e : ℝ) (t : Point) :
    r.bufferedCandidate e t = candidateExponent (2 * e) r.selected t := by
  exact r.bufferedCandidate_eq e t

/-- All simultaneously eligible producer rows are maximized at their REAL M(t). -/
theorem producerProfile4_row_le (e : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (seed : ℝ) (t : Point)
    (r : ProducerRow) (hr : r ∈ rows) (he : producerEligible licensed r t) :
    v (∑ i ∈ r.selected, t i) - 2 * e ≤ producerProfile4 e rows licensed seed t := by
  rw [← r.bufferedCandidate_eq e t]
  exact profile4_row_le seed rows (producerEligible licensed) _ t r hr he

theorem producerProfile4_seed_le (e : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (seed : ℝ) (t : Point) :
    seed ≤ producerProfile4 e rows licensed seed t := by
  exact profile4_seed_le seed rows (producerEligible licensed) _ t

/-- Raw single-row gaps may be negative without lowering the inherited floor. -/
theorem producerProfile4_eq_seed_of_dominated (e : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (seed : ℝ) (t : Point)
    (hrow : ∀ r ∈ rows, producerEligible licensed r t → r.bufferedCandidate e t ≤ seed) :
    producerProfile4 e rows licensed seed t = seed := by
  exact finiteMax_eq_seed_of_dominated rows _ _ seed hrow

theorem producerProfile4_overlap (e : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (seed : ℝ) (t : Point)
    (r s : ProducerRow) (hr : r ∈ rows) (hs : s ∈ rows)
    (her : producerEligible licensed r t) (hes : producerEligible licensed s t) :
    max (r.bufferedCandidate e t) (s.bufferedCandidate e t) ≤
      producerProfile4 e rows licensed seed t := by
  exact max_le (profile4_row_le seed rows (producerEligible licensed) _ t r hr her)
    (profile4_row_le seed rows (producerEligible licensed) _ t s hs hes)

theorem producerLevel4_outside_rows (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (history : List ℕ)
    (hout : ∀ r ∈ rows, primeHistoryLogCoordinates N 4 history ∉ r.box) :
    producerLevel4 e chi m omega N rows licensed history = frozenLevel e chi m omega N history := by
  apply level4_outside
  intro r hr he
  exact hout r hr he.2

theorem producer_frozenThird_le_level4 (e chi : ℝ) (m : ℕ) (omega N : ℝ) (hN : 1 ≤ N)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (history : List ℕ) :
    frozenLevel e chi m omega N history ≤ producerLevel4 e chi m omega N rows licensed history := by
  exact frozenThird_le_level4 e chi m omega N hN rows (producerEligible licensed) _ history

theorem producer_actual_h34 (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)) :
    rawLevel e chi m omega (N : ℝ) (rosserAncestor 3 state.selectedPrefix) ≤
      producerLevel4 e chi m omega (N : ℝ) rows licensed state.selectedPrefix := by
  exact actual_h34 e chi m omega N cap hN z rows (producerEligible licensed) _ state hstate

theorem producerFrozenLevel4_append (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (later history : List ℕ) (hlen : 4 ≤ history.length) :
    producerFrozenLevel4 e chi m omega N rows licensed (later ++ history) =
      producerFrozenLevel4 e chi m omega N rows licensed history := by
  exact frozenLevel4_append e chi m omega N rows (producerEligible licensed) _ later history hlen

theorem producerPolicy4_outside_rows (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (positive : Bool) (history : List ℕ)
    (hout : ∀ r ∈ rows, primeHistoryLogCoordinates N 4 (rosserAncestor 4 history) ∉ r.box) :
    producerPolicy4 e chi m omega N rows licensed positive history =
      HistoricalThirdCoarse.policy e chi m omega N positive history := by
  apply policy4_outside
  intro r hr he
  exact hout r hr he.2

end ActualProducerRows

end P1OriginalVariableFourthContinuation
end
end ImbalancedChen
