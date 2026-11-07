import ImbalancedChen.Part3RoughFiniteEulerBounds
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Scalar payment for the actual finite boundary Euler envelopes. The pinned
primary `primeProduct_asymptotic_order` proves a positive lower bound for
the ordinary inclusive Mertens product at every natural cutoff >=2.
Its reciprocal therefore pays both actual envelopes with ONE logarithm.
The empty range z<2 and the p=2 factor are retained exactly. Constants
precede every real z. No envelope estimate is assumed, and no contour,
L-function, SW, Mellin-profile, or original currentK claim is made.
-/

namespace ImbalancedChen.Part3.RoughEulerEnvelopePayment20261026b
noncomputable section
open Classical Finset Real
open RoughSlotCharacterLift20261026b RoughFiniteEulerBounds20261026b
open scoped BigOperators

/-- The inverse envelope has exactly the primary inclusive floor carrier. -/
theorem inverseEnvelope_eq_inverse_primeProduct (z : ℝ) :
    inverseEnvelope z =
      (MathlibNt.SieveTheory.MertensTheorem.primeProduct (Nat.floor z))⁻¹ := by
  unfold inverseEnvelope smallPrimes MathlibNt.SieveTheory.MertensTheorem.primeProduct
  rw [Finset.prod_inv_distrib]

private theorem prime_factor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_one₀ (by linarith : (0 : ℝ) < p)).mpr hp1)

/-- The plus factor is bounded by the reciprocal minus factor even at p=2. -/
theorem plusEnvelope_le_inverseEnvelope (z : ℝ) :
    plusEnvelope z ≤ inverseEnvelope z := by
  unfold plusEnvelope inverseEnvelope
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hpPrime := smallPrimes_prime hp
    have hfactor := prime_factor_pos hpPrime
    rw [← one_div]
    apply (le_div_iff₀ hfactor).mpr
    nlinarith [sq_nonneg (1 / (p : ℝ))]

/-- There is no prime in the actual inclusive carrier when z<2,
including negative cutoffs whose natural floor is zero. -/
theorem smallPrimes_eq_empty_of_lt_two {z : ℝ} (hz : z < 2) :
    smallPrimes z = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  have hp2 := (smallPrimes_prime hp).two_le
  have hpFloor : p < Nat.floor z + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  have hfloor : Nat.floor z < 2 := (Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).mpr hz
  omega

theorem envelopes_eq_one_of_lt_two {z : ℝ} (hz : z < 2) :
    plusEnvelope z = 1 ∧ inverseEnvelope z = 1 := by
  simp [plusEnvelope, inverseEnvelope, smallPrimes_eq_empty_of_lt_two hz]

/-- A genuine primary Mertens lower bound pays the literal reciprocal
product uniformly, with the real inclusive endpoint preserved. -/
theorem exists_inverseEnvelope_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ,
      inverseEnvelope z ≤ C * (1 + log (max 2 z)) := by
  obtain ⟨c, cUpper, hc, hMertens⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.primeProduct_asymptotic_order
  let C : ℝ := 1 + c⁻¹
  have hinv : 0 < c⁻¹ := inv_pos.mpr hc
  have hC : 0 < C := by dsimp [C]; positivity
  have hCOne : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro z
  have hlogmax : 0 ≤ log (max 2 z) := Real.log_nonneg (by
    exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _))
  by_cases hz : 2 ≤ z
  · have hn : 2 ≤ Nat.floor z := Nat.le_floor hz
    have hn1 : (1 : ℝ) < Nat.floor z := by exact_mod_cast (by omega : 1 < Nat.floor z)
    have hlogn : 0 < log (Nat.floor z : ℝ) := Real.log_pos hn1
    have hLower := (hMertens (Nat.floor z) hn).1
    have hinverse :
        (MathlibNt.SieveTheory.MertensTheorem.primeProduct (Nat.floor z))⁻¹ ≤
          log (Nat.floor z : ℝ) / c := by
      simpa only [one_div, inv_div] using
        one_div_le_one_div_of_le (div_pos hc hlogn) hLower
    have hlogFloor : log (Nat.floor z : ℝ) ≤ log (max 2 z) := by
      exact Real.log_le_log (by linarith)
        ((Nat.floor_le (by linarith : 0 ≤ z)).trans (le_max_right _ _))
    rw [inverseEnvelope_eq_inverse_primeProduct]
    calc
      _ ≤ log (Nat.floor z : ℝ) / c := hinverse
      _ ≤ log (max 2 z) / c := div_le_div_of_nonneg_right hlogFloor hc.le
      _ ≤ C * (1 + log (max 2 z)) := by
        dsimp [C]
        rw [div_eq_mul_inv]
        nlinarith
  · have hz2 : z < 2 := lt_of_not_ge hz
    rw [(envelopes_eq_one_of_lt_two hz2).2]
    calc
      (1 : ℝ) ≤ C := hCOne
      _ ≤ C * (1 + log (max 2 z)) := by
        nlinarith [mul_nonneg hC.le hlogmax]

/-- One positive scalar constant pays BOTH actual boundary products,
for every real cutoff. Thus exponent K=1 suffices in the polylog payment. -/
theorem exists_euler_envelopes_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ,
      plusEnvelope z ≤ C * (1 + log (max 2 z)) ∧
      inverseEnvelope z ≤ C * (1 + log (max 2 z)) := by
  obtain ⟨C, hC, hInverse⟩ := exists_inverseEnvelope_le_log
  exact ⟨C, hC, fun z =>
    ⟨(plusEnvelope_le_inverseEnvelope z).trans (hInverse z), hInverse z⟩⟩

end
end ImbalancedChen.Part3.RoughEulerEnvelopePayment20261026b
