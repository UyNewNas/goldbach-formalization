import ImbalancedChen.P5OriginalOneLongLiteralBrunDictionary
import ImbalancedChen.Part3RoughSlotCharacterLift

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Shared owner for the six existing generic Brun-support declarations.
The source interval, declaration docs, and unchanged proof bodies are bound
in EXTRACTION_BINDING.json alongside the complementary provider postimage.
-/
namespace ImbalancedChen.Part3.TwoLongActualLowerBrunMoment
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.OriginalOneLongLiteralBrunDictionary
open ImbalancedChen.Part3.RoughSlotCharacterLift20261026b (smallPrimes smallPrimes_prime mem_smallPrimes)
open ImbalancedChen.Part3.TwoLongDivisorAxisClosure (chartDivisor)

def brunSupport (Z : ℝ) (r : ℕ) : Finset ℕ := divisorSupport (smallPrimes Z) r

theorem brunSupport_bounds {Z : ℝ} (hZ : 1 ≤ Z) (r : ℕ)
    {d : ℕ} (hd : d ∈ brunSupport Z r) : 0 < d ∧ (d : ℝ) ≤ Z^r := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hd
  have hAP := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  have hAr := (Finset.mem_filter.mp hA).2
  refine ⟨chartDivisor_positive A (fun p hp => smallPrimes_prime (hAP hp)), ?_⟩
  calc
    (chartDivisor A : ℝ) = ∏ p ∈ A, (p : ℝ) := by simp [chartDivisor]
    _ ≤ ∏ _p ∈ A, Z := by
      apply Finset.prod_le_prod (fun p hp => Nat.cast_nonneg _)
      intro p hp
      exact ((mem_smallPrimes (by linarith)).mp (hAP hp)).2
    _ = Z^A.card := by simp
    _ ≤ Z^r := pow_le_pow_right₀ hZ hAr

/-- The actual image carrier has at most floor(Z^r) positive integers.
Thus the growing Brun order appears only in the power support, never
in a divisor-moment exponent or in a factorial restoring scalar. -/
theorem brunSupport_card {Z : ℝ} (hZ : 1 ≤ Z) (r : ℕ) :
    ((brunSupport Z r).card : ℝ) ≤ Z^r := by
  have hsub : brunSupport Z r ⊆ Finset.Icc 1 ⌊Z^r⌋₊ := by
    intro d hd
    obtain ⟨hpos, hbound⟩ := brunSupport_bounds hZ r hd
    exact Finset.mem_Icc.mpr ⟨hpos, Nat.le_floor hbound⟩
  have hc : (brunSupport Z r).card ≤ ⌊Z^r⌋₊ := by
    simpa using Finset.card_le_card hsub
  have hcR : ((brunSupport Z r).card : ℝ) ≤ (⌊Z^r⌋₊ : ℝ) := by exact_mod_cast hc
  exact hcR.trans (Nat.floor_le (pow_nonneg (by linarith) _))

def brunPairCoefficient (Z : ℝ) (j : ℕ) (b₁ b₂ : Bool) (d : ℕ × ℕ) : ℂ :=
  ((if b₁ then gapCoefficient (smallPrimes Z) (2*j+1) d.1
    else upperCoefficient (smallPrimes Z) (2*j) d.1) : ℂ) *
  ((if b₂ then gapCoefficient (smallPrimes Z) (2*j+1) d.2
    else upperCoefficient (smallPrimes Z) (2*j) d.2) : ℂ)

theorem brunPairCoefficient_norm (Z : ℝ) (j : ℕ) (b₁ b₂ : Bool) (d : ℕ × ℕ) :
    ‖brunPairCoefficient Z j b₁ b₂ d‖ ≤ 1 := by
  have hb (b : Bool) (e : ℕ) :
      ‖((if b then gapCoefficient (smallPrimes Z) (2*j+1) e
        else upperCoefficient (smallPrimes Z) (2*j) e) : ℂ)‖ ≤ 1 := by
    have h := coefficient_bounds (smallPrimes Z) (2*j) (2*j+1) e
    cases b
    · simpa only [Bool.false_eq_true, if_false, Complex.norm_real, Real.norm_eq_abs] using h.1
    · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.2.1] using h.2.2
  rw [brunPairCoefficient, norm_mul]
  exact (mul_le_mul (hb b₁ d.1) (hb b₂ d.2) (norm_nonneg _) zero_le_one).trans_eq (by ring)

/-- The four Boolean coefficient pairs are bounded. E3 needs only the
upper/upper, gap/upper and upper/gap three. Transition-profile labels are
independent; confusing a smoothing strip with a Brun gap is avoided. -/
theorem brunPair_mass {Z : ℝ} (hZ : 1 ≤ Z) (j : ℕ) (b₁ b₂ : Bool) (alpha : ℂ) :
    (∑ d ∈ (brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1)),
      ‖brunPairCoefficient Z j b₁ b₂ d‖ * ‖alpha‖) ≤ (Z^(2*j+1))^2 * ‖alpha‖ := by
  calc
    _ ≤ ∑ _d ∈ (brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1)), ‖alpha‖ := by
      apply Finset.sum_le_sum
      intro d hd
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (brunPairCoefficient_norm Z j b₁ b₂ d) (norm_nonneg alpha)
    _ = ((brunSupport Z (2*j+1)).card : ℝ)^2 * ‖alpha‖ := by
      simp [Finset.card_product, Nat.cast_mul, pow_two]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (brunSupport_card hZ _) 2) (norm_nonneg alpha)

end
end ImbalancedChen.Part3.TwoLongActualLowerBrunMoment
