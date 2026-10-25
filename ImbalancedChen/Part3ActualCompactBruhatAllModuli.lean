import ImbalancedChen.Part3ActualCompactBruhatKernel
import Mathlib.Data.PNat.Interval

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

A positive lower radial support height gives a uniform cutoff in the
actual lower-left modulus, simultaneously for every horizontal x.
The level-gated all-positive-modulus canonical-section sum is therefore a
finite sum, with proved absolute/norm summability and exact Fourier
integral interchange. Actual matrices with a larger lower-left entry
have zero transformed seed as well. The complete GammaInfinity coset to
signed-row/residue/translation reindexing, its c=0 contribution, and the
Bessel/spectral steps are not supplied by this module.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.ActualCompactBruhatAllModuli20261025a

open Set MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators FourierTransform
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail

/-- A genuine positive lower radial support bound forces the entire
actual x-kernel to vanish for sufficiently large modulus, uniformly in x. -/
theorem actualKernel_zero_of_large_modulus (c : ℝ) (hc : c ≠ 0)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (a : ℝ) (ha : 0 < a)
    (hfloor : ∀ t : ℝ, ψ t ≠ 0 → a ≤ t)
    (hlarge : 1 < a * c ^ 2 * y) (x : ℝ) :
    actualKernel c hc y hy m ψ x = 0 := by
  by_contra hne
  rw [actualKernel_formula] at hne
  have hψ : ψ (y / (c ^ 2 * (x ^ 2 + y ^ 2))) ≠ 0 := right_ne_zero_of_mul hne
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hden : 0 < c ^ 2 * (x ^ 2 + y ^ 2) :=
    mul_pos hc2 (by nlinarith [sq_nonneg x, sq_pos_of_pos hy])
  have hmass := (le_div_iff₀ hden).mp (hfloor _ hψ)
  have hlargey := mul_lt_mul_of_pos_right hlarge hy
  nlinarith [hmass, mul_nonneg (mul_pos ha hc2).le (sq_nonneg x)]

/-- The cutoff concerns the actual group action, not merely a rewritten
kernel: every actual SL2 matrix beyond it has zero transformed seed. -/
theorem actual_seed_zero_of_large_lowerLeft (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (z : UpperHalfPlane) (m : ℤ) (ψ : ℝ → ℂ) (a : ℝ) (ha : 0 < a)
    (hfloor : ∀ t : ℝ, ψ t ≠ 0 → a ≤ t)
    (hlarge : 1 < a * (g 1 0 : ℝ) ^ 2 * z.im) :
    fourierRadialSeed m ψ (g • z) = 0 := by
  have hc : (g 1 0 : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul] at hlarge
    linarith
  have hpoint : ((g 1 1 : ℝ) / (g 1 0 : ℝ)) +ᵥ z =
      horizontalPoint z.im z.im_pos (((g 1 1 : ℝ) / (g 1 0 : ℝ)) + z.re) := by
    apply UpperHalfPlane.ext
    ext <;> simp [horizontalPoint, UpperHalfPlane.coe_vadd]
  rw [fourierRadialSeed_actual_bruhat m ψ g hc z, hpoint]
  change _ * actualKernel (g 1 0 : ℝ) hc z.im z.im_pos m ψ _ = 0
  rw [actualKernel_zero_of_large_modulus _ hc _ z.im_pos m ψ a ha hfloor hlarge, mul_zero]

/-- A natural positive cutoff exists by the Archimedean property. -/
theorem exists_positive_modulus_cutoff (a y : ℝ) (ha : 0 < a) (hy : 0 < y) :
    ∃ C : ℕ+, 1 / (a * y) < (C : ℝ) := by
  obtain ⟨C, hC⟩ := exists_nat_gt (1 / (a * y))
  have hposR : (0 : ℝ) < C := lt_trans (div_pos zero_lt_one (mul_pos ha hy)) hC
  have hpos : 0 < C := by exact_mod_cast hposR
  exact ⟨⟨C, hpos⟩, hC⟩

/-- This explicit arithmetic cutoff guarantees the actual squared-modulus
support inequality. No summability input is hidden in the cutoff. -/
theorem large_modulus_of_cutoff (a y : ℝ) (ha : 0 < a) (hy : 0 < y)
    (C c : ℕ+) (hC : 1 / (a * y) < (C : ℝ)) (hc : C < c) :
    1 < a * (c : ℝ) ^ 2 * y := by
  have hcc : (C : ℝ) < (c : ℝ) := by
    have hnat : (C : ℕ) < (c : ℕ) := hc
    exact_mod_cast hnat
  have hprod := (div_lt_iff₀ (mul_pos ha hy)).mp (lt_trans hC hcc)
  have hcone : (1 : ℝ) ≤ c := by
    have hnat : 1 ≤ (c : ℕ) := c.property
    exact_mod_cast hnat
  have hsq : (c : ℝ) ≤ (c : ℝ) ^ 2 := by
    simpa only [mul_one, pow_two] using
      mul_le_mul_of_nonneg_left hcone (le_trans zero_le_one hcone)
  calc
    1 < (a * y) * (c : ℝ) := by nlinarith only [hprod]
    _ ≤ (a * y) * (c : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq (mul_pos ha hy).le
    _ = a * (c : ℝ) ^ 2 * y := by ring

/-- Uniform vanishing descends to the actual circle periodization after
its actual translate summability has been proved. -/
theorem periodizedKernelCircle_zero_of_large (c : ℝ) (hc : c ≠ 0)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ))
    (a : ℝ) (ha : 0 < a) (hfloor : ∀ t : ℝ, ψ t ≠ 0 → a ≤ t)
    (hlarge : 1 < a * c ^ 2 * y) :
    periodizedKernelCircle c hc y hy m ψ hψ = 0 := by
  funext z
  refine Quotient.inductionOn z ?_
  intro x
  rw [periodizedKernelCircle_coe c hc y hy m ψ hψ hcompact hpositive x]
  simp only [actualKernel_zero_of_large_modulus c hc y hy m ψ a ha hfloor hlarge,
    tsum_zero, Pi.zero_apply]

/-- Integrability of the actual finite canonical section follows from
the proved common-kernel integrability and its actual finite translations. -/
theorem canonicalFiniteSection_integrable (c : ℕ) [NeZero c] (m : ℤ)
    (F : UnitAddCircle → ℂ) (hF : Integrable F AddCircle.haarAddCircle) :
    Integrable (canonicalFiniteSection c m F) AddCircle.haarAddCircle := by
  unfold canonicalFiniteSection
  apply integrable_finsetSum'
  intro u hu
  exact (P3CuspTranslationFourierPhaseSourceOnly.integrable_translated F hF _).const_mul _

/-- The correct actual level gate is N|c for infinity-to-infinity. -/
def positiveModulusSection (N : ℕ) (c : ℕ+) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) : UnitAddCircle → ℂ :=
  letI : NeZero (c : ℕ) := ⟨Nat.ne_of_gt c.property⟩
  if N ∣ (c : ℕ) then
    canonicalFiniteSection (c : ℕ) m
      (periodizedKernelCircle (c : ℝ) (by exact_mod_cast (Nat.ne_of_gt c.property))
        y hy m ψ hψ)
  else 0

theorem positiveModulusSection_zero_of_large (N : ℕ) (c : ℕ+)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ))
    (a : ℝ) (ha : 0 < a) (hfloor : ∀ t : ℝ, ψ t ≠ 0 → a ≤ t)
    (hlarge : 1 < a * (c : ℝ) ^ 2 * y) :
    positiveModulusSection N c y hy m ψ hψ = 0 := by
  unfold positiveModulusSection
  split_ifs
  · rw [periodizedKernelCircle_zero_of_large _ _ y hy m ψ hψ hcompact hpositive a ha hfloor hlarge]
    simp [canonicalFiniteSection, P3CuspTranslationFourierPhaseSourceOnly.translated]
  · rfl

theorem positiveModulusSection_integrable (N : ℕ) (c : ℕ+)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Integrable (positiveModulusSection N c y hy m ψ hψ) AddCircle.haarAddCircle := by
  unfold positiveModulusSection
  split_ifs
  · exact canonicalFiniteSection_integrable _ m _
      (periodizedKernelCircle_integrable _ _ y hy m ψ hψ)
  · exact integrable_zero _ _ _

/-- Literal all-positive-modulus section series, with its actual Gamma0
level divisibility gate. -/
def allPositiveModulusSections (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (x : UnitAddCircle) : ℂ :=
  ∑' c : ℕ+, positiveModulusSection N c y hy m ψ hψ x

/-- The entire positive-modulus series is a genuine finite sum,
simultaneously for every circle coordinate x. -/
theorem allPositiveModulusSections_eq_finite (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ))
    (a : ℝ) (ha : 0 < a) (hfloor : ∀ t : ℝ, ψ t ≠ 0 → a ≤ t)
    (C : ℕ+) (hC : 1 / (a * y) < (C : ℝ)) :
    allPositiveModulusSections N y hy m ψ hψ =
      ∑ c ∈ Finset.Icc (1 : ℕ+) C, positiveModulusSection N c y hy m ψ hψ := by
  funext x
  simp only [allPositiveModulusSections, Finset.sum_apply]
  apply tsum_eq_sum
  intro c hc
  have hcone : (1 : ℕ+) ≤ c := by
    change 1 ≤ (c : ℕ)
    exact c.property
  have hcc : C < c := lt_of_not_ge (fun hle => hc (Finset.mem_Icc.mpr ⟨hcone, hle⟩))
  have hz := positiveModulusSection_zero_of_large N c y hy m ψ hψ hcompact hpositive
    a ha hfloor (large_modulus_of_cutoff a y ha hy C c hC hcc)
  exact congrFun hz x

/-- This is genuine norm summability from a proved common finite cutoff,
not a generic absolute-summability supplier. -/
theorem allPositiveModulusSections_norm_summable (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ))
    (x : UnitAddCircle) :
    Summable (fun c : ℕ+ => ‖positiveModulusSection N c y hy m ψ hψ x‖) := by
  obtain ⟨a, ha, hfloor⟩ := radial_support_positive_floor ψ hcompact hpositive
  obtain ⟨C, hC⟩ := exists_positive_modulus_cutoff a y ha hy
  apply summable_of_ne_finset_zero (s := Finset.Icc (1 : ℕ+) C)
  intro c hc
  have hcone : (1 : ℕ+) ≤ c := by
    change 1 ≤ (c : ℕ)
    exact c.property
  have hcc : C < c := lt_of_not_ge (fun hle => hc (Finset.mem_Icc.mpr ⟨hcone, hle⟩))
  have hz := positiveModulusSection_zero_of_large N c y hy m ψ hψ hcompact hpositive
    a ha hfloor (large_modulus_of_cutoff a y ha hy C c hC hcc)
  simp only [hz, Pi.zero_apply, norm_zero]

/-- The all-positive-c series is genuinely integrable because its proved
uniform cutoff reduces it to finitely many integrable actual sections. -/
theorem allPositiveModulusSections_integrable (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Integrable (allPositiveModulusSections N y hy m ψ hψ) AddCircle.haarAddCircle := by
  obtain ⟨a, ha, hfloor⟩ := radial_support_positive_floor ψ hcompact hpositive
  obtain ⟨C, hC⟩ := exists_positive_modulus_cutoff a y ha hy
  rw [allPositiveModulusSections_eq_finite N y hy m ψ hψ hcompact hpositive a ha hfloor C hC]
  exact integrable_finsetSum' _ (fun c hc => positiveModulusSection_integrable N c y hy m ψ hψ)

/-- Even the L1 norms of the actual modulus sections are summable from
the same concrete cutoff, with no external absolute-sum hypothesis. -/
theorem allPositiveModulusSections_integral_norm_summable (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Summable (fun c : ℕ+ =>
      ∫ x : UnitAddCircle, ‖positiveModulusSection N c y hy m ψ hψ x‖
        ∂AddCircle.haarAddCircle) := by
  obtain ⟨a, ha, hfloor⟩ := radial_support_positive_floor ψ hcompact hpositive
  obtain ⟨C, hC⟩ := exists_positive_modulus_cutoff a y ha hy
  apply summable_of_ne_finset_zero (s := Finset.Icc (1 : ℕ+) C)
  intro c hc
  have hcone : (1 : ℕ+) ≤ c := by
    change 1 ≤ (c : ℕ)
    exact c.property
  have hcc : C < c := lt_of_not_ge (fun hle => hc (Finset.mem_Icc.mpr ⟨hcone, hle⟩))
  have hz := positiveModulusSection_zero_of_large N c y hy m ψ hψ hcompact hpositive
    a ha hfloor (large_modulus_of_cutoff a y ha hy C c hC hcc)
  simp only [hz, Pi.zero_apply, norm_zero, integral_zero]
/-- The true all-positive-c Fourier coefficient has an exact finite
Kloosterman/actual-Fourier-kernel formula. Integral interchange follows
from the proved uniform finite cutoff and integrable actual sections. -/
theorem allPositiveModulusSections_fourierCoeff (N : ℕ) (y : ℝ) (hy : 0 < y)
    (m n : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ))
    (a : ℝ) (ha : 0 < a) (hfloor : ∀ t : ℝ, ψ t ≠ 0 → a ≤ t)
    (C : ℕ+) (hC : 1 / (a * y) < (C : ℝ)) :
    AddCircle.fourierCoeff (allPositiveModulusSections N y hy m ψ hψ) n =
      ∑ c ∈ Finset.Icc (1 : ℕ+) C,
        if N ∣ (c : ℕ) then
          kloosterman (c : ℕ) n m *
            𝓕 (actualKernel (c : ℝ) (by exact_mod_cast (Nat.ne_of_gt c.property))
              y hy m ψ) (n : ℝ)
        else 0 := by
  rw [allPositiveModulusSections_eq_finite N y hy m ψ hψ hcompact hpositive a ha hfloor C hC]
  have hsum := congrFun (AddCircle.fourierCoeff.sum (Finset.Icc (1 : ℕ+) C)
    (fun c => positiveModulusSection N c y hy m ψ hψ)
    (fun c hc => positiveModulusSection_integrable N c y hy m ψ hψ)) n
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c hc
  unfold positiveModulusSection
  split_ifs with hNc
  · exact compactSeed_canonicalSection_fourierCoeff (c : ℕ) y hy m n ψ hψ hcompact hpositive
  · simp [AddCircle.fourierCoeff]

end ImbalancedChen.Part3.ActualCompactBruhatAllModuli20261025a

