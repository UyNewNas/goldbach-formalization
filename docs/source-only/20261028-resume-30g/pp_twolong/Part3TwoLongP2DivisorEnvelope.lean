import Mathlib
import ImbalancedChen.Part3TwoLongFilteredIntegerFrequency

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual divisor-filtered majorants on Z x Z. This is the missing finite
divisor/absolutely convergent frequency assembly, consuming frozen D/E
budgets rather than assuming their desired P2 output.
-/
namespace ImbalancedChen.Part3.TwoLongP2DivisorEnvelope
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.Part3.TwoLongInternalP2FrequencySums
open ImbalancedChen.Part3.TwoLongFilteredIntegerFrequency
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode

def filteredProduct (H K : ℝ) (d : ℕ) (p : ℤ × ℤ) : ℝ :=
  filteredDecay H d p.1 * filteredDecay K d p.2

theorem filteredProduct_nonneg (H K : ℝ) (d : ℕ) (p : ℤ × ℤ) :
    0 ≤ filteredProduct H K d p :=
  mul_nonneg (filtered_nonneg H d p.1) (filtered_nonneg K d p.2)

private theorem summable_separated {A B : ℤ → ℝ}
    (hA : Summable A) (hB : Summable B) (hA0 : ∀ j, 0 ≤ A j) (hB0 : ∀ k, 0 ≤ B k) :
    Summable (fun p : ℤ × ℤ => A p.1*B p.2) := by
  apply (summable_prod_of_nonneg (fun p => mul_nonneg (hA0 p.1) (hB0 p.2))).mpr
  constructor
  · intro j
    exact hB.mul_left _
  · simp_rw [tsum_mul_left]
    exact hA.mul_right _

theorem filteredProduct_summable {H K : ℝ} (hH : 0 < H) (hK : 0 < K) (d : ℕ) :
    Summable (filteredProduct H K d) :=
  summable_separated (filtered_summable hH d) (filtered_summable hK d)
    (filtered_nonneg H d) (filtered_nonneg K d)

def weilEnvelope (H K : ℝ) (q : ℕ) (p : ℤ × ℤ) : ℝ :=
  ∑ d ∈ q.divisors, Real.sqrt (d : ℝ)*filteredProduct H K d p

def ramanujanEnvelope (H : ℝ) (q : ℕ) (j : ℤ) : ℝ :=
  ∑ d ∈ q.divisors, (Nat.totient d : ℝ)*filteredDecay H d j

theorem weilEnvelope_nonneg (H K : ℝ) (q : ℕ) (p : ℤ × ℤ) :
    0 ≤ weilEnvelope H K q p := by
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (Real.sqrt_nonneg _) (filteredProduct_nonneg H K d p)

theorem ramanujanEnvelope_nonneg (H : ℝ) (q : ℕ) (j : ℤ) :
    0 ≤ ramanujanEnvelope H q j := by
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (by positivity) (filtered_nonneg H d j)

theorem weilEnvelope_summable {H K : ℝ} (hH : 0 < H) (hK : 0 < K) (q : ℕ) :
    Summable (weilEnvelope H K q) :=
  summable_sum (fun d hd => (filteredProduct_summable hH hK d).mul_left _)

theorem ramanujanEnvelope_summable {H : ℝ} (hH : 0 < H) (q : ℕ) :
    Summable (ramanujanEnvelope H q) :=
  summable_sum (fun d hd => (filtered_summable hH d).mul_left _)

/-- The actual complete integer divisor filters have D's uniform Weil
moment, after the justified finite divisor/product-frequency interchange. -/
theorem weilEnvelope_tsum_le {H K : ℝ} (hH : 0 < H) (hK : 0 < K) (q : ℕ) :
    (∑' p : ℤ × ℤ, weilEnvelope H K q p) ≤ (4*H*K)*weilConstant := by
  calc
    _ = ∑ d ∈ q.divisors, Real.sqrt (d : ℝ)*
        (∑' j : ℤ, ∑' k : ℤ, filteredDecay H d j*filteredDecay K d k) := by
      rw [weilEnvelope,Summable.tsum_finsetSum
        (fun d hd => (filteredProduct_summable hH hK d).mul_left _)]
      apply Finset.sum_congr rfl
      intro d hd
      rw [tsum_mul_left,(filteredProduct_summable hH hK d).tsum_prod]
    _ ≤ ∑ d ∈ q.divisors, Real.sqrt (d : ℝ)*(4*H*K/(d : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (filtered_double_sum_le hH hK (Nat.pos_of_mem_divisors hd)) (Real.sqrt_nonneg _)
    _ = (4*H*K)*weilDivisorMoment q := by
      unfold weilDivisorMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weilDivisorMoment_le_constant q) (by positivity)

theorem ramanujanEnvelope_tsum_eq {H : ℝ} (hH : 0 < H) (q : ℕ) :
    (∑' j : ℤ, ramanujanEnvelope H q j) = ramanujanFrequencyMass H q := by
  rw [ramanujanEnvelope,Summable.tsum_finsetSum
    (fun d hd => (filtered_summable hH d).mul_left _)]
  unfold ramanujanFrequencyMass
  apply Finset.sum_congr rfl
  intro d hd
  rw [tsum_mul_left,filtered_tsum_eq_multiple (Nat.pos_of_mem_divisors hd)]

/-- Ramanujan's gcd bound is charged on the actual nonzero j filter. -/
theorem weighted_ramanujan_le (H : ℝ) (q : ℕ) (hq : 0 < q) (j : ℤ) :
    baseDecay H j*‖ramanujan q j‖ ≤ ramanujanEnvelope H q j := by
  have h := mul_le_mul_of_nonneg_left (ramanujan_norm_le_totient_filter q hq j)
    (multipleDecay_nonneg H 1 j)
  apply h.trans_eq
  rw [Finset.sum_filter,Finset.mul_sum]
  unfold ramanujanEnvelope
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hj : (d : ℤ) ∣ j <;> simp [filteredDecay,hj] <;> ring

/-- The common-divisor sqrt(gcd) expansion is paid by both ACTUAL
integer filters. No d*k candidate sum replaces the original Z x Z sum. -/
theorem weighted_sqrt_gcd_le (H K : ℝ) (q : ℕ) (hq : 0 < q) (j k : ℤ) :
    baseDecay H j*baseDecay K k*
      Real.sqrt (Nat.gcd (Nat.gcd j.natAbs k.natAbs) q : ℝ) ≤ weilEnvelope H K q (j,k) := by
  have h := mul_le_mul_of_nonneg_left (sqrt_gcd_le_divisor_sum q hq j k)
    (mul_nonneg (multipleDecay_nonneg H 1 j) (multipleDecay_nonneg K 1 k))
  apply h.trans_eq
  rw [Finset.sum_filter,Finset.mul_sum]
  unfold weilEnvelope filteredProduct
  apply Finset.sum_congr rfl
  intro d hd
  have hj : d ∣ j.natAbs ↔ (d : ℤ) ∣ j := by
    symm
    rw [← Int.dvd_natAbs,Int.natCast_dvd_natCast]
  have hk : d ∣ k.natAbs ↔ (d : ℤ) ∣ k := by
    symm
    rw [← Int.dvd_natAbs,Int.natCast_dvd_natCast]
  rw [hj,hk]
  by_cases hdj : (d : ℤ) ∣ j <;> by_cases hdk : (d : ℤ) ∣ k <;>
    simp [filteredDecay,hdj,hdk] <;> ring

def centeredEnvelope (H K : ℝ) (q : ℕ) (p : ℤ × ℤ) : ℝ :=
  (q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilEnvelope H K q p +
    (Nat.totient q : ℝ)⁻¹*(ramanujanEnvelope H q p.1*ramanujanEnvelope K q p.2)

theorem centeredEnvelope_nonneg (H K : ℝ) (q : ℕ) (p : ℤ × ℤ) :
    0 ≤ centeredEnvelope H K q p := by
  unfold centeredEnvelope
  exact add_nonneg (mul_nonneg (by positivity) (weilEnvelope_nonneg H K q p))
    (mul_nonneg (by positivity)
      (mul_nonneg (ramanujanEnvelope_nonneg H q p.1) (ramanujanEnvelope_nonneg K q p.2)))

theorem centeredEnvelope_summable {H K : ℝ} (hH : 0 < H) (hK : 0 < K) (q : ℕ) :
    Summable (centeredEnvelope H K q) :=
  ((weilEnvelope_summable hH hK q).mul_left _).add
    ((summable_separated (ramanujanEnvelope_summable hH q) (ramanujanEnvelope_summable hK q)
      (ramanujanEnvelope_nonneg H q) (ramanujanEnvelope_nonneg K q)).mul_left _)

/-- This is the actual centered frequency majorant, with the separate
Weil and exact-Ramanujan mean terms and their original totient factor. -/
theorem centeredEnvelope_tsum_le {H K : ℝ} (hH : 0 < H) (hK : 0 < K) (q : ℕ) :
    (∑' p : ℤ × ℤ, centeredEnvelope H K q p) ≤ 4*H*K*
      ((q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilConstant +
        (q.divisors.card : ℝ)^2/(Nat.totient q : ℝ)) := by
  have hprod := summable_separated (ramanujanEnvelope_summable hH q)
    (ramanujanEnvelope_summable hK q)
    (ramanujanEnvelope_nonneg H q) (ramanujanEnvelope_nonneg K q)
  have he : (∑' p : ℤ × ℤ, ramanujanEnvelope H q p.1*ramanujanEnvelope K q p.2) =
      ramanujanFrequencyMass H q*ramanujanFrequencyMass K q := by
    rw [hprod.tsum_prod]
    simp_rw [tsum_mul_left]
    rw [tsum_mul_right,ramanujanEnvelope_tsum_eq hH,ramanujanEnvelope_tsum_eq hK]
  rw [centeredEnvelope,tsum_add ((weilEnvelope_summable hH hK q).mul_left _)
    (hprod.mul_left _),tsum_mul_left,tsum_mul_left,he]
  calc
    _ ≤ (q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*((4*H*K)*weilConstant) +
        (Nat.totient q : ℝ)⁻¹*(4*H*K*(q.divisors.card : ℝ)^2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (weilEnvelope_tsum_le hH hK q) (by positivity))
        (mul_le_mul_of_nonneg_left (double_ramanujan_mass_le hH hK q) (by positivity))
    _ = _ := by ring

end
end ImbalancedChen.Part3.TwoLongP2DivisorEnvelope
