import ImbalancedChen.Part3InfinityZeroActualAllDenominatorAssembly
import ImbalancedChen.Part3InfinityZeroActualFiberGeometricPair
import ImbalancedChen.Part3CompactCuspFiniteGeometricIntegral
import ImbalancedChen.Part3FrickeNormalizer

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The full ORIGINAL infinity Poincare series in the literal normalized
zero chart, paired against an actual compact radial seed, has a FINITE
all-denominator geometric formula. All signed original cosets occur
once. The d=0 term is a single diagonal at N=1. The positive terms have
the actual S_d(-m*N^-1,-n) and N*d^2 kernel, with no infinite Fubini.
This module proves the complete strip slice formula; the quotient
unfolding is a separate next module.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.InfinityZeroActualFiniteGeometricAssembly20261026b

open Set MeasureTheory Matrix Matrix.SpecialLinearGroup
open scoped UpperHalfPlane BigOperators FourierTransform
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.InfinityZeroActualDenominatorFiber20261026a
open ImbalancedChen.Part3.InfinityZeroActualAllDenominatorAssembly20261026b
open ImbalancedChen.Part3.InfinityZeroActualFiberFourier20261026a
open ImbalancedChen.Part3.InfinityZeroActualFiberGeometricPair20261026a
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.ActualCompactBruhatAllModuli20261025a
open ImbalancedChen.Part3.ActualCompactPoincareFourier20261025a
open ImbalancedChen.Part3.CompactParabolicNormalIndex20261025a
open ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a
open ImbalancedChen.Part3.CompactCuspFiniteGeometricIntegral20261025a
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.OriginalSmoothPoissonTail

theorem zeroSL_eq_frickeSL (N : ℕ) (hN : 0 < N) : zeroSL N hN = frickeSL N hN := rfl

theorem actualZeroFiber_zero_denominator (N : ℕ) (hN : 0 < N)
    (m : ℤ) (ψ : ℝ → ℂ) (z : UpperHalfPlane) :
    actualZeroFiber N hN 0 m ψ z = if N = 1 then fourierRadialSeed m ψ z else 0 := by
  by_cases hN1 : N = 1
  · subst N
    letI : Unique (ZeroDenominatorCosets 1 0) :=
      ⟨exceptionalWeylCoset, zero_denominator_class_unique⟩
    have hS : SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S = zeroSL 1 hN := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [zeroSL, zeroScaling, ModularGroup.S]
    simp only [actualZeroFiber, tsum_unique, zeroFiberSeed]
    change fourierRadialSeed m ψ
      (ModularGroup.S • (zeroSL 1 hN • z)) = _
    have haction : ModularGroup.S • (zeroSL 1 hN • z) = z := by
      change (SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S) • (zeroSL 1 hN • z) = z
      rw [hS, zeroSL_eq_frickeSL]
      exact frickeSL_action_involutive 1 hN z
    simp only [haction, if_pos rfl]
  · letI := zero_denominator_isEmpty N hN hN1
    simp [actualZeroFiber, hN1]

/-- A single positive cutoff is valid with the physical mixed level
factor N*d^2. It follows from N>=1, rather than a changed modulus. -/
theorem mixed_large_of_cutoff (N : ℕ) (hN : 0 < N) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (C d : ℕ+)
    (hC : 1 / (a * b) < (C : ℝ)) (hd : C < d) :
    1 < a * ((N : ℝ) * (d : ℝ) ^ 2) * b := by
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlevel : (d : ℝ) ^ 2 ≤ (N : ℝ) * (d : ℝ) ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hNone (sq_nonneg (d : ℝ))
  exact (large_modulus_of_cutoff a b ha hb C d hC hd).trans_le
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlevel ha.le) hb.le)

private theorem positiveFiber_continuous (N : ℕ) (hN : 0 < N)
    (d : ℕ) [NeZero d] (y : ℝ) (hy : 0 < y) (n : ℤ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Continuous (fun x : ℝ => actualZeroFiber N hN d n φ (horizontalPoint y hy x)) := by
  have heq := funext (actualZeroFiber_eq_section N hN d y hy n φ hφ hcφ hposφ)
  rw [heq]
  unfold zeroFiniteSection P3CuspTranslationFourierPhaseSourceOnly.translated
  simp only [Finset.sum_apply]
  apply continuous_finsetSum
  intro r _
  exact continuous_const.mul ((periodizedKernelCircle_continuous _ _ y hy n φ hφ).comp
    (AddCircle.continuous_mk'.add continuous_const))

/-- The actual paired full Poincare slice, with its canonical density. -/
def mixedActualPairSlice (N : ℕ) (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  if hy : 0 < y then
    ∫ x in (0 : ℝ)..1, ((y⁻¹ ^ 2 : ℝ) : ℂ) *
      star (fourierRadialSeed m ψ (horizontalPoint y hy x)) *
        actualCompactPoincare N n φ (zeroSL N hN • horizontalPoint y hy x)
  else 0

private theorem zeroFiberPairSlice (N : ℕ) (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, ((y⁻¹ ^ 2 : ℝ) : ℂ) *
      star (fourierRadialSeed m ψ (horizontalPoint y hy x)) *
        actualZeroFiber N hN 0 n φ (horizontalPoint y hy x)) =
      if N = 1 ∧ m = n then radialWeight ψ y * φ y else 0 := by
  simp_rw [actualZeroFiber_zero_denominator]
  by_cases hN1 : N = 1
  · simp only [if_pos hN1]
    have hseed (x : ℝ) : ((y⁻¹ ^ 2 : ℝ) : ℂ) *
        star (fourierRadialSeed m ψ (horizontalPoint y hy x)) *
          fourierRadialSeed n φ (horizontalPoint y hy x) =
        (radialWeight ψ y * φ y) *
          (AddCircle.fourier (-m) (x : UnitAddCircle) * AddCircle.fourier n (x : UnitAddCircle)) := by
      simp only [fourierRadialSeed, horizontalPoint, star_mul', Complex.star_def,
        ← AddCircle.fourier_neg, radialWeight]
      ring
    simp_rw [hseed]
    rw [intervalIntegral.integral_const_mul]
    have hc := AddCircle.fourierCoeff_fourier (T := (1 : ℝ)) n m
    rw [AddCircle.fourierCoeff_eq_intervalIntegral _ m 0] at hc
    simpa [hN1, Pi.single_apply, eq_comm] using congrArg (fun t : ℂ => (radialWeight ψ y * φ y) * t) hc
  · simp [hN1]

/-- Uniform finite all-d assembly of the actual paired slice. Only a
FINITE x-integral exchange is made, after actual coset grouping. -/
theorem mixedActualPairSlice_eq_finite (N : ℕ) (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfloorφ : ∀ t, φ t ≠ 0 → a ≤ t) (hfloorψ : ∀ t, ψ t ≠ 0 → b ≤ t)
    (C : ℕ+) (hC : 1 / (a * b) < (C : ℝ)) (y : ℝ) :
    mixedActualPairSlice N hN m n ψ φ y =
      (if N = 1 ∧ m = n then radialWeight ψ y * φ y else 0) +
      ∑ d ∈ Finset.Icc (1 : ℕ+) C, mixedFiberPairSlice N hN (d : ℕ) m n ψ φ y := by
  by_cases hzero : ψ y = 0
  · simp [mixedActualPairSlice, mixedFiberPairSlice, fourierRadialSeed, horizontalPoint,
      radialWeight, hzero]
  · have hy : 0 < y := hposψ (subset_tsupport ψ hzero)
    have hby := hfloorψ y hzero
    let S : Finset ℕ := insert 0 ((Finset.Icc (1 : ℕ+) C).image PNat.val)
    have hsum (x : ℝ) : actualCompactPoincare N n φ (zeroSL N hN • horizontalPoint y hy x) =
        ∑ d ∈ S, actualZeroFiber N hN d n φ (horizontalPoint y hy x) := by
      rw [actualPoincare_zeroChart_eq_all_fibers N hN n φ hφ hcφ hposφ]
      apply tsum_eq_sum
      intro d hd
      have hd0 : d ≠ 0 := by intro h; subst d; exact hd (Finset.mem_insert_self _ _)
      let dp : ℕ+ := ⟨d, Nat.pos_of_ne_zero hd0⟩
      have hCd : C < dp := by
        by_contra h
        have hm : dp ∈ Finset.Icc (1 : ℕ+) C := Finset.mem_Icc.mpr ⟨by exact dp.property, le_of_not_gt h⟩
        exact hd (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨dp, hm, rfl⟩))
      letI : NeZero d := ⟨hd0⟩
      apply actualZeroFiber_zero_of_large N hN d y hy n φ x a ha hfloorφ
      exact (mixed_large_of_cutoff N hN a b ha hb C dp hC hCd).trans_le
        (mul_le_mul_of_nonneg_left hby (by positivity))
    have hint (d : ℕ) : IntervalIntegrable (fun x : ℝ => ((y⁻¹ ^ 2 : ℝ) : ℂ) *
        star (fourierRadialSeed m ψ (horizontalPoint y hy x)) *
          actualZeroFiber N hN d n φ (horizontalPoint y hy x)) volume 0 1 := by
      have hf : Continuous (fun x : ℝ => actualZeroFiber N hN d n φ (horizontalPoint y hy x)) := by
        by_cases hd : d = 0
        · subst d
          simp_rw [actualZeroFiber_zero_denominator]
          by_cases hN1 : N = 1
          · simp only [if_pos hN1, fourierRadialSeed, horizontalPoint]
            fun_prop
          · simp only [if_neg hN1]
            exact continuous_const
        · letI : NeZero d := ⟨hd⟩
          exact positiveFiber_continuous N hN d y hy n φ hφ hcφ hposφ
      exact (continuous_const.mul ((by
        simp only [fourierRadialSeed, horizontalPoint]
        fun_prop : Continuous (fun x : ℝ => fourierRadialSeed m ψ (horizontalPoint y hy x))).star)
          |>.mul hf).intervalIntegrable 0 1
    rw [mixedActualPairSlice, dif_pos hy]
    simp_rw [hsum, Finset.mul_sum]
    rw [intervalIntegral.integral_finset_sum (fun d _ => hint d)]
    have hz : (0 : ℕ) ∉ (Finset.Icc (1 : ℕ+) C).image PNat.val := by simp
    rw [Finset.sum_insert hz, zeroFiberPairSlice N hN m n ψ φ y hy]
    congr 1
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [mixedFiberPairSlice, dif_pos hy]
    · intro d hd e he h
      exact Subtype.ext h

/-- Full finite mixed-cusp geometric formula for the ORIGINAL scaled
Poincare strip slices, retaining the exact physical mixed phase. -/
theorem integrated_mixedActualPairSlice_eq_finite_geometric (N : ℕ) (hN : 0 < N)
    (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℕ+,
      (∫ y : ℝ, mixedActualPairSlice N hN m n ψ φ y) =
        (if N = 1 ∧ m = n then ∫ y : ℝ, radialWeight ψ y * φ y else 0) +
        ∑ d ∈ Finset.Icc (1 : ℕ+) C,
          (if N.Coprime (d : ℕ) then
            kloosterman (d : ℕ) (-m * inverseResidue (d : ℕ) (N : ℤ)) (-n) else 0) *
              ∫ x : ℝ, ∫ y : ℝ, mixedOrbitKernel N (d : ℕ) m n ψ φ (x, y) := by
  obtain ⟨a, ha, hfloorφ⟩ := radial_support_positive_floor φ hcφ hposφ
  obtain ⟨b, hb, hfloorψ⟩ := radial_support_positive_floor ψ hcψ hposψ
  obtain ⟨C, hC⟩ := exists_positive_modulus_cutoff a b ha hb
  refine ⟨C, ?_⟩
  have heq := funext (mixedActualPairSlice_eq_finite N hN m n ψ φ hposψ hφ hcφ hposφ
    a b ha hb hfloorφ hfloorψ C hC)
  have hd : Integrable (fun y => if N = 1 ∧ m = n then radialWeight ψ y * φ y else 0) := by
    by_cases h : N = 1 ∧ m = n
    · simpa only [if_pos h] using radial_diagonal_integrable ψ φ hψ hcψ hposψ hφ
    · simp only [if_neg h]
      exact integrable_zero _ _ _
  have ht (d : ℕ+) := mixedFiberPairSlice_integrable N hN (d : ℕ) m n ψ φ
    hψ hcψ hposψ hφ hcφ hposφ
  rw [heq, integral_add hd (integrable_finsetSum _ (fun d _ => ht d)),
    integral_finsetSum _ (fun d _ => ht d)]
  congr 1
  · by_cases h : N = 1 ∧ m = n <;> simp [h]
  · apply Finset.sum_congr rfl
    intro d hd
    exact integrated_actualMixedFiber_eq_geometric N hN (d : ℕ) m n ψ φ
      hψ hcψ hposψ hφ hcφ hposφ

end ImbalancedChen.Part3.InfinityZeroActualFiniteGeometricAssembly20261026b
