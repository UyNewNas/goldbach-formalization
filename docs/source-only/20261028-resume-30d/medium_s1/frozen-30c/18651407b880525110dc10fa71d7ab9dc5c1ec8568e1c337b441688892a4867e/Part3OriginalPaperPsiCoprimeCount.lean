import ImbalancedChen.Part3OriginalGevreyPoissonPacket
import ImbalancedChen.Part3SmoothCoprimeError
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Uniform finite progression and coprime counting for the actual constructed
Gevrey paperPsi. No identification with the older dyadic bump is made.
The only analytic ingredients are the existing actual-profile Poisson
packet and the generic Schwartz rapid-decay theorem. The elementary
nonzero-frequency telescoping majorant is reused unchanged.
-/

namespace ImbalancedChen.Part3.OriginalPaperPsiCoprimeCount

noncomputable section

open Classical MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform
open OriginalGevreyFinalPsi20261028 OriginalGevreyActualPsiFourierIBP20261028
open OriginalGevreyPoissonPacket20261028 CommonSmoothCutoff

/-- Exactly the h0=integral psi appearing in the original S1 principal. -/
def paperMass : ℝ := ∫ x : ℝ, paperPsi x

/-- Mathlib's Fourier convention has no missing normalizing factor at zero. -/
theorem paperPsi_fourier_zero : (𝓕 paperPsiComplex) 0 = (paperMass : ℂ) := by
  rw [Real.fourier_real_eq]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  change (∫ x : ℝ, (paperPsi x : ℂ)) = (paperMass : ℂ)
  exact integral_complex_ofReal

def paperWeight (M : ℝ) (m : ℕ) : ℝ := paperPsi ((m : ℝ) / M)

/-- The same fixed absolute constant works for all positive frequency
mesh sizes, including modulus larger than the smoothing scale. -/
theorem paperPsi_nonzero_frequency_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      ‖∑' h : ℤ, paperPsiNonzeroMode t x h‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 paperPsiSchwartz) 2
  have hdecay' (y : ℝ) : ‖𝓕 paperPsiComplex y‖ ≤ C / (1 + |y|) ^ 2 := by
    simpa only [SchwartzMap.fourier_coe] using hdecay y
  refine ⟨2 * C, by positivity, ?_⟩
  intro t ht x
  obtain ⟨hmajor, hsum⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hpoint (h : ℤ) :
      ‖paperPsiNonzeroMode t x h‖ ≤ C * poissonNonzeroDecay t h := by
    by_cases hh : h = 0
    · simp [paperPsiNonzeroMode, poissonNonzeroDecay, hh]
    · simp only [paperPsiNonzeroMode, poissonNonzeroDecay, if_neg hh,
        norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        fourier_apply, Circle.norm_coe, mul_one]
      calc
        _ ≤ t * (C / (1 + |t * h|) ^ 2) :=
          mul_le_mul_of_nonneg_left (hdecay' (t * h)) ht.le
        _ = _ := by ring
  have hnorm := paperPsiNonzeroMode_summable_norm ht x
  apply (norm_tsum_le_tsum_norm hnorm).trans
  calc
    _ ≤ ∑' h : ℤ, C * poissonNonzeroDecay t h :=
      hnorm.tsum_le_tsum hpoint (hmajor.mul_left C)
    _ = C * ∑' h : ℤ, poissonNonzeroDecay t h := tsum_mul_left
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hsum hC.le
    _ = _ := by ring

/-- The exact actual-profile packet is valid on every support-containing
finite carrier, not only the profile's canonical enclosing interval. -/
theorem paperPsi_finset_progression_packet {M : ℝ} (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ m, paperWeight M m ≠ 0 → m ∈ S)
    {q : ℕ} (hq : 0 < q) (b : ℤ) :
    (∑ m ∈ S, if Int.ModEq q (m : ℤ) b then scaledPaperPsi M m else 0) =
      (M / (q : ℝ)) • (𝓕 paperPsiComplex) 0 +
        ∑' h : ℤ, paperPsiNonzeroMode (M / (q : ℝ)) ((b : ℝ) / q) h := by
  let f : ℕ → ℂ := fun m =>
    if Int.ModEq q (m : ℤ) b then scaledPaperPsi M m else 0
  have hzero (m : ℕ) (hm : m ∉ S) : f m = 0 := by
    have hw : paperWeight M m = 0 := by
      by_contra hn
      exact hm (hS m hn)
    have hwc : scaledPaperPsi M m = 0 := by
      change (paperWeight M m : ℂ) = 0
      rw [hw]
      norm_num
    simp [f, hwc]
  have hzero' (m : ℕ) (hm : m ∉ paperPsiNaturalCarrier M) : f m = 0 := by
    have hw : scaledPaperPsi M m = 0 := by
      by_contra hn
      exact hm (paperPsiNaturalCarrier_support hM hn)
    simp [f, hw]
  have heq : (∑ m ∈ S, f m) = ∑ m ∈ paperPsiNaturalCarrier M, f m := by
    calc
      _ = ∑' m : ℕ, f m := by symm; exact tsum_eq_sum hzero
      _ = _ := tsum_eq_sum hzero'
  calc
    _ = ∑ m ∈ paperPsiNaturalCarrier M,
        if Int.ModEq q (m : ℤ) b then scaledPaperPsi M m else 0 := heq
    _ = _ := paperPsi_finite_residue_poisson_packet hM hq b

theorem paperPsi_finset_progression_eq_main_add_fourier
    {M : ℝ} (hM : 0 < M) (S : Finset ℕ)
    (hS : ∀ m, paperWeight M m ≠ 0 → m ∈ S)
    {q : ℕ} (hq : 0 < q) (b : ℤ) :
    (∑ m ∈ S, if Int.ModEq q (m : ℤ) b then paperWeight M m else 0) =
      (M / (q : ℝ)) * paperMass +
        (∑' h : ℤ, paperPsiNonzeroMode (M / (q : ℝ)) ((b : ℝ) / q) h).re := by
  have he := paperPsi_finset_progression_packet hM S hS hq b
  rw [paperPsi_fourier_zero] at he
  change (∑ m ∈ S,
      if Int.ModEq q (m : ℤ) b then (paperWeight M m : ℂ) else 0) = _ at he
  have hre := congrArg Complex.re he
  simpa only [Complex.re_sum, apply_ite, Complex.zero_re, Complex.ofReal_re,
    Complex.add_re, Complex.real_smul] using hre

theorem paperPsi_finset_progression_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m, paperWeight M m ≠ 0 → m ∈ S) →
      ∀ q : ℕ, 0 < q → ∀ b : ℤ,
        |(∑ m ∈ S, if Int.ModEq q (m : ℤ) b then paperWeight M m else 0) -
          (M / (q : ℝ)) * paperMass| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := paperPsi_nonzero_frequency_uniform
  refine ⟨C, hC, ?_⟩
  intro M hM S hS q hq b
  rw [paperPsi_finset_progression_eq_main_add_fourier hM S hS hq b,
    add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans
    (hbound (M / (q : ℝ)) (div_pos hM (by exact_mod_cast hq)) ((b : ℝ) / q))

theorem paperPsi_finset_multiples_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m, paperWeight M m ≠ 0 → m ∈ S) →
      ∀ q : ℕ, 0 < q →
        |(∑ m ∈ S, if q ∣ m then paperWeight M m else 0) -
          (M / (q : ℝ)) * paperMass| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := paperPsi_finset_progression_uniform_error
  refine ⟨C, hC, ?_⟩
  intro M hM S hS q hq
  simpa only [Int.modEq_zero_iff_dvd, Int.natCast_dvd_natCast]
    using hbound M hM S hS q hq 0

/-- The actual same-paperPsi common-m coprime counting theorem. The
single constant is chosen before M, carrier, and physical modulus. -/
theorem paperPsi_finset_coprime_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m, paperWeight M m ≠ 0 → m ∈ S) →
      ∀ q : ℕ, q ≠ 0 →
        |(∑ m ∈ S, if m.Coprime q then paperWeight M m else 0) -
          (M * paperMass) * (q.totient : ℝ) / (q : ℝ)| ≤
            C * (q.divisors.card : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := paperPsi_finset_multiples_uniform_error
  refine ⟨C, hC, ?_⟩
  intro M hM S hS q hq
  calc
    _ = |∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ((∑ m ∈ S, if d ∣ m then paperWeight M m else 0) -
          (M / (d : ℝ)) * paperMass)| := by
      rw [coprime_weight_eq_moebius S _ hq, mul_div_assoc, ← moebius_density hq,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius d : ℝ) *
        ((∑ m ∈ S, if d ∣ m then paperWeight M m else 0) -
          (M / (d : ℝ)) * paperMass)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ q.divisors, C := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      simpa using mul_le_mul hmu
        (hbound M hM S hS d (Nat.pos_of_mem_divisors hd))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp [mul_comm]

def paperCommonMCount (S : Finset ℕ) (M : ℝ) (ell r s : ℕ) : ℝ :=
  ∑ m ∈ S, if m.Coprime (ell * r * s) then paperWeight M m else 0

theorem paperCommonMCount_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m, paperWeight M m ≠ 0 → m ∈ S) →
      ∀ ell r s : ℕ, 0 < ell → 0 < r → 0 < s →
        |paperCommonMCount S M ell r s -
          (M * paperMass) * ((ell * r * s).totient : ℝ) / (ell * r * s : ℕ)| ≤
            C * ((ell * r * s).divisors.card : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := paperPsi_finset_coprime_uniform_error
  refine ⟨C, hC, ?_⟩
  intro M hM S hS ell r s hell hr hs
  exact hbound M hM S hS (ell * r * s) (mul_pos (mul_pos hell hr) hs).ne'

end

end ImbalancedChen.Part3.OriginalPaperPsiCoprimeCount
