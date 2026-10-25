import ImbalancedChen.Part3ActualComplexEisensteinCanonicalFourier
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
Absolute summability and signed reconstruction of the actual canonical
Eisenstein Fourier coefficients. The only analytic convergence input is the
already proved actual Fourier-Bessel norm series; no reconstruction identity
or coefficient summability is a premise.
SOURCE_WRITTEN_UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3ActualCanonicalEisensteinFourierSeries

noncomputable section

open Set Filter
open scoped Topology BigOperators
open Part3.ActualComplexEisensteinCanonicalFourier
open Part3ActualRamanujanBesselNormalConvergence

/-- Common factor of every nonzero actual canonical Fourier term. -/
def nonzeroNormalization (s : ℂ) (y : ℝ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) ^ s) /
    (Complex.Gamma s * riemannZeta (2 * s)) * (Real.sqrt y : ℂ)

private theorem fourier_positive_phase (k : ℕ) (x : ℝ) :
    AddCircle.fourier (((k + 1 : ℕ) : ℤ)) (x : AddCircle (1 : ℝ)) = phase (k + 1) x := by
  rw [AddCircle.fourier_coe_apply]
  unfold phase
  simp only [div_one]
  push_cast
  congr 1
  ring

private theorem fourier_negative_phase (k : ℕ) (x : ℝ) :
    AddCircle.fourier (-((k + 1 : ℕ) : ℤ)) (x : AddCircle (1 : ℝ)) = phase (k + 1) (-x) := by
  rw [AddCircle.fourier_coe_apply]
  unfold phase
  simp only [div_one]
  push_cast
  congr 1
  ring

/-- Literal positive Fourier term equals the normally convergent actual
Bessel term with precisely the original common normalization. -/
theorem canonical_positive_term (s : ℂ) (y x : ℝ) (k : ℕ) :
    complexCanonicalCoefficient s y ((k + 1 : ℕ) : ℤ) *
      AddCircle.fourier (((k + 1 : ℕ) : ℤ)) (x : AddCircle (1 : ℝ)) =
        nonzeroNormalization s y * fourierBesselTerm k s y x := by
  have hk : ((k + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hkr : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg _
  rw [complexCanonicalCoefficient, if_neg hk, fourier_positive_phase]
  unfold complexNonzeroCoefficient nonzeroNormalization fourierBesselTerm
  simp only [Int.cast_natCast, abs_of_nonneg hkr, Int.natAbs_natCast, Complex.ofReal_natCast]
  ring

theorem canonical_negative_term (s : ℂ) (y x : ℝ) (k : ℕ) :
    complexCanonicalCoefficient s y (-((k + 1 : ℕ) : ℤ)) *
      AddCircle.fourier (-((k + 1 : ℕ) : ℤ)) (x : AddCircle (1 : ℝ)) =
        nonzeroNormalization s y * fourierBesselTerm k s y (-x) := by
  have hk : -((k + 1 : ℕ) : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast (Nat.succ_ne_zero k))
  have hkr : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg _
  rw [complexCanonicalCoefficient, if_neg hk, fourier_negative_phase]
  unfold complexNonzeroCoefficient nonzeroNormalization fourierBesselTerm
  simp only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg hkr,
    Int.natAbs_neg, Int.natAbs_natCast, Complex.ofReal_natCast]
  ring

private theorem canonical_positive_value (s : ℂ) (y : ℝ) (k : ℕ) :
    complexCanonicalCoefficient s y ((k + 1 : ℕ) : ℤ) =
      nonzeroNormalization s y * fourierBesselTerm k s y 0 := by
  simpa using canonical_positive_term s y 0 k

private theorem canonical_negative_value (s : ℂ) (y : ℝ) (k : ℕ) :
    complexCanonicalCoefficient s y (-((k + 1 : ℕ) : ℤ)) =
      nonzeroNormalization s y * fourierBesselTerm k s y 0 := by
  simpa using canonical_negative_term s y 0 k

/-- The true canonical coefficients are absolutely summable at every
complex s and every positive height, before imposing Re(s)>1 to identify
them with the physical Eisenstein coefficients. -/
theorem canonicalCoefficient_norm_summable (s : ℂ) {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℤ => ‖complexCanonicalCoefficient s y n‖) := by
  have hp : Summable (fun k : ℕ => ‖complexCanonicalCoefficient s y ((k + 1 : ℕ) : ℤ)‖) := by
    have h := (fourierBessel_norm_summable s hy 0).const_mul ‖nonzeroNormalization s y‖
    simpa only [canonical_positive_value, norm_mul] using h
  have hn : Summable (fun k : ℕ => ‖complexCanonicalCoefficient s y (-((k + 1 : ℕ) : ℤ))‖) := by
    have h := (fourierBessel_norm_summable s hy 0).const_mul ‖nonzeroNormalization s y‖
    simpa only [canonical_negative_value, norm_mul] using h
  have hp0 : Summable (fun k : ℕ => ‖complexCanonicalCoefficient s y (k : ℤ)‖) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  exact Summable.of_nat_of_neg_add_one hp0 (by
    simpa only [Nat.cast_add, Nat.cast_one] using hn)

theorem canonicalCoefficient_summable (s : ℂ) {y : ℝ} (hy : 0 < y) :
    Summable (complexCanonicalCoefficient s y) :=
  (canonicalCoefficient_norm_summable s hy).of_norm

/-- The actual signed Fourier series is summable at each horizontal point. -/
theorem canonicalFourierTerm_summable (s : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℤ => complexCanonicalCoefficient s y n *
      AddCircle.fourier n (x : AddCircle (1 : ℝ))) := by
  apply Summable.of_norm_bounded (canonicalCoefficient_norm_summable s hy)
  intro n
  simp only [norm_mul, AddCircle.fourier_apply, Circle.norm_coe, mul_one, le_refl]

/-- Exact regrouping of all integer Fourier frequencies into the original
constant and one positive/negative pair for each positive natural integer. -/
theorem canonicalFourierSeries_eq (s : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    (∑' n : ℤ, complexCanonicalCoefficient s y n *
      AddCircle.fourier n (x : AddCircle (1 : ℝ))) =
        (y : ℂ) ^ s + complexScattering s * (y : ℂ) ^ (1 - s) +
          nonzeroNormalization s y * ∑' k : ℕ, nonzeroFrequencyPair k s y x := by
  let f : ℤ → ℂ := fun n => complexCanonicalCoefficient s y n *
    AddCircle.fourier n (x : AddCircle (1 : ℝ))
  have hf : Summable f := canonicalFourierTerm_summable s hy x
  have hp : Summable (fun k : ℕ => f ((k + 1 : ℕ) : ℤ)) :=
    hf.comp_injective (by intro i j hij; exact Nat.succ_injective (Int.ofNat_injective hij))
  have hn : Summable (fun k : ℕ => f (-((k + 1 : ℕ) : ℤ))) :=
    hf.comp_injective (by
      intro i j hij
      exact Nat.succ_injective (Int.ofNat_injective (neg_injective hij)))
  have hp0 : Summable (fun k : ℕ => f (k : ℤ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  calc
    _ = (∑' k : ℕ, f (k : ℤ)) + ∑' k : ℕ, f (-((k + 1 : ℕ) : ℤ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using tsum_of_nat_of_neg_add_one hp0
        (by simpa only [Nat.cast_add, Nat.cast_one] using hn)
    _ = f 0 + ((∑' k : ℕ, f ((k + 1 : ℕ) : ℤ)) +
        ∑' k : ℕ, f (-((k + 1 : ℕ) : ℤ))) := by
      rw [hp0.tsum_eq_zero_add]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ = f 0 + ∑' k : ℕ, (f ((k + 1 : ℕ) : ℤ) + f (-((k + 1 : ℕ) : ℤ))) := by
      rw [tsum_add hp hn]
    _ = _ := by
      have hpair : ∀ k : ℕ, f ((k + 1 : ℕ) : ℤ) + f (-((k + 1 : ℕ) : ℤ)) =
          nonzeroNormalization s y * nonzeroFrequencyPair k s y x := by
        intro k
        dsimp [f]
        rw [canonical_positive_term, canonical_negative_term]
        unfold nonzeroFrequencyPair
        ring
      simp_rw [hpair]
      rw [tsum_mul_left]
      simp only [f, complexCanonicalCoefficient, if_true, AddCircle.fourier_zero, mul_one]

end

end ImbalancedChen.Part3ActualCanonicalEisensteinFourierSeries
