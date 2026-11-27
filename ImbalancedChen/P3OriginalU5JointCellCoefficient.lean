import ImbalancedChen.P3OriginalU5CommonPhysicalRoot
import ImbalancedChen.P3OriginalU5WarmMixedReusedCore
import ImbalancedChen.P3OriginalU5RoundedCountInsertion

/-! Whole-cell lower rounding for the common physical U5 policy. Each
fibre includes the physical owner and logarithmic labels of both marked
primes and the complete ordered rough word. Positive words use the inner
test, and negative words use the outer test on this same finite carrier. -/

namespace ImbalancedChen.P3OriginalU5JointCellCoefficient

noncomputable section
open scoped Classical BigOperators List
open P2LowerCanonicalRetainedTrace (canonical_subword_of_universe)
open P2LowerFiniteCellRounding (primeLabel label rawSupport raw raw_value)
open P2OriginalLowerSelectedCapConstructor (Code)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalPairSourceReceiver (PairRange)
open P3OriginalU5CommonPhysicalRoot (rowAddress rowOwner policy)
open P5OriginalU5CausalFinite (pairSupport smallCutoff cutoff coordinates_mem_triangle)
open P5OriginalU5PlateauPrimeBV (fullModulus)

abbrev Point := (ℕ × ℕ) × ℕ

abbrev roughCarrier (N : ℕ) (epsilon : ℝ) : Finset ℕ :=
  P2LowerFiniteCellRounding.«universe» N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N)

def carrier (N : ℕ) (epsilon : ℝ) : Finset Point := pairSupport N ×ˢ roughCarrier N epsilon

def jointLabel (R : PairRange) (m N : ℕ) (tau : ℝ) (x : Point) : Code m × List ℤ :=
  (rowAddress R m N x.1,
    primeLabel N tau x.1.2 :: primeLabel N tau x.1.1 :: label N tau x.2)

def cell (R : PairRange) (m N : ℕ) (epsilon tau : ℝ) (x : Point) : Finset Point :=
  (carrier N epsilon).filter (fun y => jointLabel R m N tau y = jointLabel R m N tau x)

theorem self_mem_cell (R : PairRange) (m N : ℕ) (epsilon tau : ℝ) {x : Point}
    (hx : x ∈ carrier N epsilon) : x ∈ cell R m N epsilon tau x :=
  Finset.mem_filter.mpr ⟨hx, rfl⟩

theorem same_owner (R : PairRange) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {tau : ℝ} {x y : Point}
    (hx : x.1 ∈ pairSupport N) (hy : y.1 ∈ pairSupport N)
    (h : jointLabel R m N tau x = jointLabel R m N tau y) :
    rowOwner R m hN hx = rowOwner R m hN hy :=
  Subtype.ext (congrArg Prod.fst h)

theorem same_fine_word (R : PairRange) (m N : ℕ) (tau : ℝ) {x y : Point}
    (h : jointLabel R m N tau x = jointLabel R m N tau y) :
    (x.1.2 :: x.1.1 :: x.2.primeFactorsList.reverse).map (primeLabel N tau) =
      (y.1.2 :: y.1.1 :: y.2.primeFactorsList.reverse).map (primeLabel N tau) :=
  congrArg Prod.snd h

theorem same_rough_length (R : PairRange) (m N : ℕ) (tau : ℝ) {x y : Point}
    (h : jointLabel R m N tau x = jointLabel R m N tau y) :
    x.2.primeFactorsList.length = y.2.primeFactorsList.length := by
  have hword := congrArg List.length (same_fine_word R m N tau h)
  simp only [List.length_map, List.length_cons, List.length_reverse] at hword
  omega

theorem moebius_eq_rank_sign (N : ℕ) (epsilon : ℝ) {d : ℕ} (hd : d ∈ roughCarrier N epsilon) :
    ArithmeticFunction.moebius d = (-1 : ℤ) ^ d.primeFactorsList.length := by
  obtain ⟨hsub, hprod⟩ := canonical_subword_of_universe _ _ _ _ hd
  have h := moebius_list_prod_eq_negOnePow_length d.primeFactorsList.reverse
    ((roughPrimeUniverse_nodup _ _ _ _).sublist hsub)
    (fun _ hp => mem_roughPrimeUniverse_prime (hsub.subset hp))
  simpa only [hprod, List.length_reverse] using h

variable (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ) (m N : ℕ) (epsilon tau : ℝ)

def retained (x : Point) : Prop :=
  x.2 ∈ rawSupport (policy R bank b m N x.1) N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N)

abbrev rawCoefficient (x : Point) : ℝ :=
  raw (policy R bank b m N x.1) N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N) x.2

def inner (x : Point) : Prop := ∀ y ∈ cell R m N epsilon tau x, retained R bank b m N epsilon y
def outer (x : Point) : Prop := ∃ y ∈ cell R m N epsilon tau x, retained R bank b m N epsilon y

def coefficient (x : Point) : ℝ :=
  if x ∈ carrier N epsilon then
    if 0 ≤ (ArithmeticFunction.moebius x.2 : ℝ) then
      if inner R bank b m N epsilon tau x then (ArithmeticFunction.moebius x.2 : ℝ) else 0
    else if outer R bank b m N epsilon tau x then (ArithmeticFunction.moebius x.2 : ℝ) else 0
  else 0

theorem rawCoefficient_value (x : Point) : rawCoefficient R bank b m N epsilon x =
    if retained R bank b m N epsilon x then (ArithmeticFunction.moebius x.2 : ℝ) else 0 := by
  by_cases h : x.2 ∈ rawSupport (policy R bank b m N x.1) N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N)
  all_goals simp [rawCoefficient, raw_value, retained, h]

/-- A positive word can only be removed; an omitted negative word can
only be added. Comparisons use each original external pair's actual policy. -/
theorem coefficient_le_raw {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (d : ℕ) :
    coefficient R bank b m N epsilon tau (t,d) ≤ rawCoefficient R bank b m N epsilon (t,d) := by
  let x : Point := (t,d)
  change coefficient R bank b m N epsilon tau x ≤ rawCoefficient R bank b m N epsilon x
  rw [rawCoefficient_value]
  by_cases hx : x ∈ carrier N epsilon
  · have hs := self_mem_cell R m N epsilon tau hx
    by_cases hsign : 0 ≤ (ArithmeticFunction.moebius x.2 : ℝ)
    · by_cases hi : inner R bank b m N epsilon tau x
      · have hr := hi x hs
        simp only [coefficient, hx, hsign, hi, hr, if_true, le_refl]
      · simp only [coefficient, hx, hsign, hi, if_true, if_false]
        split_ifs <;> linarith only [hsign]
    · by_cases ho : outer R bank b m N epsilon tau x
      · simp only [coefficient, hx, hsign, ho, if_true, if_false]
        split_ifs <;> linarith only [hsign]
      · have hr : ¬retained R bank b m N epsilon x := fun h => ho ⟨x, hs, h⟩
        simp only [coefficient, hx, hsign, ho, hr, if_true, if_false, le_refl]
  · have hr : ¬retained R bank b m N epsilon x := by
      intro h
      exact hx (Finset.mem_product.mpr ⟨ht, P2LowerFiniteCellRounding.rawSupport_subset_universe _ _ _ _ _ h⟩)
    simp only [coefficient, hx, hr, if_false, le_refl]

theorem coefficient_abs_le_one (x : Point) : |coefficient R bank b m N epsilon tau x| ≤ 1 := by
  unfold coefficient
  split_ifs <;> try norm_num
  all_goals exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := x.2))

/-- The sign follows from the squarefree divisor's actual number of prime
factors. Equal labels give one coefficient throughout the whole fibre. -/
theorem coefficient_eq_of_same_label {x y : Point} (hx : x ∈ carrier N epsilon) (hy : y ∈ carrier N epsilon)
    (h : jointLabel R m N tau x = jointLabel R m N tau y) :
    coefficient R bank b m N epsilon tau x = coefficient R bank b m N epsilon tau y := by
  have hc : cell R m N epsilon tau x = cell R m N epsilon tau y := by simp only [cell, h]
  have hi : inner R bank b m N epsilon tau x ↔ inner R bank b m N epsilon tau y := by
    unfold inner
    rw [hc]
  have ho : outer R bank b m N epsilon tau x ↔ outer R bank b m N epsilon tau y := by
    unfold outer
    rw [hc]
  have hmu : ArithmeticFunction.moebius x.2 = ArithmeticFunction.moebius y.2 := by
    rw [moebius_eq_rank_sign N epsilon (Finset.mem_product.mp hx).2,
      moebius_eq_rank_sign N epsilon (Finset.mem_product.mp hy).2, same_rough_length R m N tau h]
  simp only [coefficient, hx, hy, if_true, hmu, hi, ho]

/-- A nonzero joint atom has a genuinely retained representative. -/
theorem retained_witness_of_ne_zero {x : Point} (hne : coefficient R bank b m N epsilon tau x ≠ 0) :
    x ∈ carrier N epsilon ∧ ∃ y ∈ cell R m N epsilon tau x, retained R bank b m N epsilon y := by
  by_cases hx : x ∈ carrier N epsilon
  · refine ⟨hx, ?_⟩
    by_cases hs : 0 ≤ (ArithmeticFunction.moebius x.2 : ℝ)
    · by_cases hi : inner R bank b m N epsilon tau x
      · have hself := self_mem_cell R m N epsilon tau hx
        exact ⟨x, hself, hi x hself⟩
      · exact (hne (by simp [coefficient, hx, hs, hi])).elim
    · by_contra ho
      exact hne (by simp [coefficient, hx, hs, show ¬outer R bank b m N epsilon tau x from ho])
  · exact (hne (by simp [coefficient, hx])).elim

theorem retained_difference_of_coefficient_ne_raw {x : Point} (hx : x ∈ carrier N epsilon)
    (hne : coefficient R bank b m N epsilon tau x ≠ rawCoefficient R bank b m N epsilon x) :
    ∃ y ∈ cell R m N epsilon tau x, ¬(retained R bank b m N epsilon x ↔ retained R bank b m N epsilon y) := by
  by_contra hn
  have he (y : Point) (hy : y ∈ cell R m N epsilon tau x) :
      retained R bank b m N epsilon x ↔ retained R bank b m N epsilon y := by
    by_contra h
    exact hn ⟨y, hy, h⟩
  have hself := self_mem_cell R m N epsilon tau hx
  apply hne
  rw [rawCoefficient_value]
  by_cases hr : retained R bank b m N epsilon x
  · have hi : inner R bank b m N epsilon tau x := fun y hy => (he y hy).mp hr
    have ho : outer R bank b m N epsilon tau x := ⟨x, hself, hr⟩
    simp [coefficient, hx, hi, ho, hr]
  · have hi : ¬inner R bank b m N epsilon tau x := fun h => hr (h x hself)
    have ho : ¬outer R bank b m N epsilon tau x := by
      rintro ⟨y, hy, h⟩
      exact hr ((he y hy).mpr h)
    simp [coefficient, hx, hi, ho, hr]

theorem retained_iff_canonical_gate {N : ℕ} (hN : 2 ≤ N) (epsilon : ℝ)
    {x : Point} (hx : x ∈ carrier N epsilon) :
    retained R bank b m N epsilon x ↔ policy R bank b m N x.1 x.2.primeFactorsList = true := by
  obtain ⟨ht, hd⟩ := Finset.mem_product.mp hx
  have ht' := coordinates_mem_triangle hN ht
  unfold retained
  simp only [policy, dif_pos ht', P2ActualPairPlanRawSupport.pair_raw_iff_canonical_warm, hd, true_and]

theorem gate_difference_of_coefficient_ne_raw {N : ℕ} (hN : 2 ≤ N) (epsilon tau : ℝ)
    {x : Point} (hx : x ∈ carrier N epsilon)
    (hne : coefficient R bank b m N epsilon tau x ≠ rawCoefficient R bank b m N epsilon x) :
    ∃ y ∈ cell R m N epsilon tau x, ¬(policy R bank b m N x.1 x.2.primeFactorsList = true ↔
      policy R bank b m N y.1 y.2.primeFactorsList = true) := by
  obtain ⟨y, hy, hd⟩ := retained_difference_of_coefficient_ne_raw R bank b m N epsilon tau hx hne
  refine ⟨y, hy, ?_⟩
  rwa [← retained_iff_canonical_gate R bank b m hN epsilon hx,
    ← retained_iff_canonical_gate R bank b m hN epsilon (Finset.mem_filter.mp hy).1]

/-- Exact pre-attachment loss with the external marks in each totient. -/
def roundingLoss : ℝ :=
  ∑ t ∈ pairSupport N, ∑ d ∈ roughCarrier N epsilon,
    |coefficient R bank b m N epsilon tau (t,d) - rawCoefficient R bank b m N epsilon (t,d)| /
      (Nat.totient (fullModulus t d) : ℝ)

theorem roundingLoss_exact :
    (∑ t ∈ pairSupport N, ∑ d ∈ roughCarrier N epsilon,
      rawCoefficient R bank b m N epsilon (t,d) / (Nat.totient (fullModulus t d) : ℝ)) -
    (∑ t ∈ pairSupport N, ∑ d ∈ roughCarrier N epsilon,
      coefficient R bank b m N epsilon tau (t,d) / (Nat.totient (fullModulus t d) : ℝ)) =
      roundingLoss R bank b m N epsilon tau := by
  unfold roundingLoss
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [abs_of_nonpos (sub_nonpos.mpr (coefficient_le_raw R bank b m N epsilon tau ht d))]
  ring

end
end ImbalancedChen.P3OriginalU5JointCellCoefficient
