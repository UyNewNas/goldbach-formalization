import ImbalancedChen.Part3InfinityZeroActualDenominatorFiber
import ImbalancedChen.Part3ActualCompactPoincareFourier

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The ORIGINAL GammaInfinity-left-coset d-fiber evaluated at sigma0*z has
absolute convergence proved from a genuine continuous compact positive
radial profile. Its period-one normalized Fourier integral is the literal
physical Kloosterman factor times the actual real Fourier transform with
C=sqrt(N)*d. The right translations are the actual zero-cusp stabilizer.
No summability, assumed zero-cusp periodicity, coefficient identity or
abstract arithmetic supplier is a hypothesis.

This is a fixed positive denominator contribution. Assembling the full
mixed-cusp quotient pairing, the exceptional d=0 class at N=1, and the
all-denominator index decomposition is explicitly not asserted here.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.InfinityZeroActualFiberFourier20261026a

open Set MeasureTheory Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane BigOperators FourierTransform
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.InfinityZeroPhysicalKloosterman20261025a
open ImbalancedChen.Part3.InfinityZeroBruhatSeed20261025a
open ImbalancedChen.Part3.InfinityZeroActualDenominatorFiber20261026a
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.ActualCompactBruhatAllModuli20261025a
open ImbalancedChen.Part3.ActualCompactPoincareFourier20261025a
open ImbalancedChen.Part3.CompactParabolicNormalIndex20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail

def zeroModulus (N d : ℕ) : ℝ := Real.sqrt (N : ℝ) * (d : ℝ)

theorem zeroModulus_ne_zero (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d] :
    zeroModulus N d ≠ 0 :=
  mul_ne_zero (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
    (by exact_mod_cast NeZero.ne d)

theorem zeroModulus_sq (N d : ℕ) : (zeroModulus N d) ^ 2 = (N : ℝ) * (d : ℝ) ^ 2 := by
  rw [zeroModulus, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The actual original coset summand, evaluated in the normalized zero chart. -/
def zeroFiberSeed (N : ℕ) (hN : 0 < N) (d : ℕ) (m : ℤ)
    (ψ : ℝ → ℂ) (z : UpperHalfPlane) (q : ZeroDenominatorCosets N d) : ℂ :=
  compactCosetSeed N m ψ (zeroSL N hN • z) q.1

/-- Integral right-parabolic motion is precisely unit translation in the
normalized chart. This is derived from the actual width-N conjugation. -/
theorem zeroParabolic_normalized_action (N : ℕ) (hN : 0 < N) (v : ℤ)
    (z : UpperHalfPlane) :
    zeroParabolic N v • (zeroSL N hN • z) = zeroSL N hN • ((v : ℝ) +ᵥ z) := by
  have hmatrix := zeroSL_conj_translation N hN v
  have hmul :
      SpecialLinearGroup.map (Int.castRingHom ℝ) (zeroParabolic N v) * zeroSL N hN =
      zeroSL N hN * SpecialLinearGroup.map (Int.castRingHom ℝ) (ModularGroup.T ^ v) := by
    rw [← hmatrix]
    group
  have h := congrArg (fun G : SL(2, ℝ) => G • z) hmul
  simp only [mul_smul] at h
  change zeroParabolic N v • (zeroSL N hN • z) =
    zeroSL N hN • ((ModularGroup.T ^ v) • z) at h
  simpa only [UpperHalfPlane.modular_T_zpow_smul] using h

/-- Exact original summand: the sign of v and the residue shift both
follow from k=val(r)-d*v in the actual matrix, rather than a sum licence. -/
theorem zeroFiberSeed_pair (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ)
    (r : ZeroResidue N d) (v : ℤ) :
    zeroFiberSeed N hN d m ψ (horizontalPoint y hy x) (zeroPairCoset N d (r, v)) =
      AddCircle.fourier m (((canonicalB N d r.1 : ℤ) : ℝ) / (d : ℝ) : UnitAddCircle) *
        actualKernel (zeroModulus N d) (zeroModulus_ne_zero N hN d) y hy m ψ
          ((x - (r.1.val : ℝ) / (d : ℝ)) + (v : ℝ)) := by
  change fourierRadialSeed m ψ
    (zeroPairMatrix N d (r, v) • (zeroSL N hN • horizontalPoint y hy x)) = _
  have hd : zeroPairMatrix N d (r, v) 1 1 ≠ 0 := by
    rw [(zeroPairMatrix_entries N d (r, v)).2.1]
    exact_mod_cast NeZero.ne d
  have h := gamma_zeroScaling_fourierRadialSeed N hN (zeroPairMatrix N d (r, v))
    ((r.1.val : ℤ) - (d : ℤ) * v) (zeroPairMatrix_entries N d (r, v)).1 hd y hy m ψ x
  have harg : x - (((r.1.val : ℤ) - (d : ℤ) * v : ℤ) : ℝ) / (d : ℝ) =
      (x - (r.1.val : ℝ) / (d : ℝ)) + (v : ℝ) := by
    push_cast
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast NeZero.ne d]
    <;> ring
  simpa only [(zeroPairMatrix_entries N d (r, v)).2.1,
    (zeroPairMatrix_entries N d (r, v)).2.2, zeroModulus, harg] using h

/-- Absolute convergence of the original coset fiber is a theorem. -/
theorem zeroFiberSeed_norm_summable (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    Summable (fun q : ZeroDenominatorCosets N d =>
      ‖zeroFiberSeed N hN d m ψ (horizontalPoint y hy x) q‖) := by
  apply (zeroDenominatorCosetEquiv N hN d).summable_iff.mp
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_, summable_fintype _⟩
  intro r
  simp_rw [show ∀ v : ℤ, zeroDenominatorCosetEquiv N hN d (r, v) =
    zeroPairCoset N d (r, v) from fun _ => rfl, zeroFiberSeed_pair, norm_mul]
  exact (kernel_translates_summable (zeroModulus N d) (zeroModulus_ne_zero N hN d)
    y hy m ψ hψ hcψ hposψ (x - (r.1.val : ℝ) / (d : ℝ))).norm.mul_left _

/-- A uniform d cutoff for EVERY original coset in the fiber, independent
of the horizontal point and its integer translate. -/
theorem zeroFiberSeed_zero_of_large (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ)
    (a : ℝ) (ha : 0 < a) (hfloor : ∀ t, ψ t ≠ 0 → a ≤ t)
    (hlarge : 1 < a * ((N : ℝ) * (d : ℝ) ^ 2) * y)
    (q : ZeroDenominatorCosets N d) :
    zeroFiberSeed N hN d m ψ (horizontalPoint y hy x) q = 0 := by
  obtain ⟨⟨r, v⟩, rfl⟩ := (zeroDenominatorCosetEquiv N hN d).surjective q
  change zeroFiberSeed N hN d m ψ (horizontalPoint y hy x) (zeroPairCoset N d (r, v)) = 0
  rw [zeroFiberSeed_pair, actualKernel_zero_of_large_modulus _ _ y hy m ψ a ha hfloor
    (by simpa only [zeroModulus_sq] using hlarge), mul_zero]

def zeroFiniteSection (N d : ℕ) [NeZero d] (m : ℤ)
    (F : UnitAddCircle → ℂ) : UnitAddCircle → ℂ :=
  ∑ r : ZeroResidue N d, fun x =>
    AddCircle.fourier m (((canonicalB N d r.1 : ℤ) : ℝ) / (d : ℝ) : UnitAddCircle) *
      P3CuspTranslationFourierPhaseSourceOnly.translated F
        ((-((r.1.val : ℝ) / (d : ℝ)) : ℝ) : UnitAddCircle) x

def actualZeroFiber (N : ℕ) (hN : 0 < N) (d : ℕ) (m : ℤ)
    (ψ : ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑' q : ZeroDenominatorCosets N d, zeroFiberSeed N hN d m ψ z q

theorem actualZeroFiber_zero_of_large (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ)
    (a : ℝ) (ha : 0 < a) (hfloor : ∀ t, ψ t ≠ 0 → a ≤ t)
    (hlarge : 1 < a * ((N : ℝ) * (d : ℝ) ^ 2) * y) :
    actualZeroFiber N hN d m ψ (horizontalPoint y hy x) = 0 := by
  apply tsum_eq_zero
  intro q
  exact zeroFiberSeed_zero_of_large N hN d y hy m ψ x a ha hfloor hlarge q

/-- Reindexing the ORIGINAL fiber is licensed by proved norm summability.
The circle function is obtained by actual compact-kernel periodization. -/
theorem actualZeroFiber_eq_section (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    actualZeroFiber N hN d m ψ (horizontalPoint y hy x) =
      zeroFiniteSection N d m (periodizedKernelCircle (zeroModulus N d)
        (zeroModulus_ne_zero N hN d) y hy m ψ hψ) (x : UnitAddCircle) := by
  have hs := (zeroFiberSeed_norm_summable N hN d y hy m ψ hψ hcψ hposψ x).of_norm
  have hp := (zeroDenominatorCosetEquiv N hN d).summable_iff.mpr hs
  rw [actualZeroFiber, ← (zeroDenominatorCosetEquiv N hN d).tsum_eq, hp.tsum_prod, tsum_fintype]
  simp only [zeroFiniteSection, Finset.sum_apply,
    P3CuspTranslationFourierPhaseSourceOnly.translated, ← AddCircle.coe_add]
  apply Finset.sum_congr rfl
  intro r hr
  change (∑' v : ℤ, zeroFiberSeed N hN d m ψ (horizontalPoint y hy x)
      (zeroPairCoset N d (r, v))) = _
  simp_rw [zeroFiberSeed_pair, tsum_mul_left]
  rw [periodizedKernelCircle_coe _ _ y hy m ψ hψ hcψ hposψ]
  simp only [sub_eq_add_neg]

/-- Period one of the original actual fiber is a consequence, not an input. -/
theorem actualZeroFiber_periodic (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Function.Periodic (fun x => actualZeroFiber N hN d m ψ (horizontalPoint y hy x)) 1 := by
  intro x
  rw [actualZeroFiber_eq_section N hN d y hy m ψ hψ hcψ hposψ (x + 1),
    actualZeroFiber_eq_section N hN d y hy m ψ hψ hcψ hposψ x]
  simp

private theorem phase_product (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (m n : ℤ) (r : ZeroResidue N d) :
    AddCircle.fourier m (((canonicalB N d r.1 : ℤ) : ℝ) / (d : ℝ) : UnitAddCircle) *
      AddCircle.fourier n ((-((r.1.val : ℝ) / (d : ℝ)) : ℝ) : UnitAddCircle) =
        zeroNormalizedPhase N hN d m n r := by
  have hd : zeroCanonicalMatrix N d r 1 1 ≠ 0 := by
    change (d : ℤ) ≠ 0
    exact_mod_cast NeZero.ne d
  have hcoords := zero_normalized_coordinates N hN (zeroCanonicalMatrix N d r)
    (r.1.val : ℤ) rfl hd
  dsimp only [zeroNormalizedPhase]
  rw [hcoords.1, hcoords.2]
  simp only [zeroCanonicalMatrix, Int.cast_natCast, AddCircle.fourier_coe_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem zeroFiniteSection_fourierCoeff (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (m n : ℤ) (F : UnitAddCircle → ℂ) (hF : Integrable F AddCircle.haarAddCircle) :
    AddCircle.fourierCoeff (zeroFiniteSection N d m F) n =
      zeroGeneralizedKloosterman N d m n * AddCircle.fourierCoeff F n := by
  let sections : ZeroResidue N d → UnitAddCircle → ℂ := fun r x =>
    AddCircle.fourier m (((canonicalB N d r.1 : ℤ) : ℝ) / (d : ℝ) : UnitAddCircle) *
      P3CuspTranslationFourierPhaseSourceOnly.translated F
        ((-((r.1.val : ℝ) / (d : ℝ)) : ℝ) : UnitAddCircle) x
  have hsections (r : ZeroResidue N d) : Integrable (sections r) AddCircle.haarAddCircle :=
    (P3CuspTranslationFourierPhaseSourceOnly.integrable_translated F hF _).const_mul _
  have hsum : AddCircle.fourierCoeff (zeroFiniteSection N d m F) n =
      ∑ r : ZeroResidue N d, AddCircle.fourierCoeff (sections r) n := by
    simpa only [Finset.sum_apply] using congrFun (AddCircle.fourierCoeff.sum
      (Finset.univ : Finset (ZeroResidue N d)) sections (fun r hr => hsections r)) n
  rw [hsum]
  calc
    _ = ∑ r : ZeroResidue N d,
        zeroNormalizedPhase N hN d m n r * AddCircle.fourierCoeff F n := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [sections, AddCircle.fourierCoeff.const_mul,
        P3CuspTranslationFourierPhaseSourceOnly.fourierCoeff_translated,
        ← mul_assoc, phase_product N hN]
    _ = (∑ r : ZeroResidue N d, zeroNormalizedPhase N hN d m n r) *
        AddCircle.fourierCoeff F n := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [sum_zeroNormalizedPhase_eq_generalized]

/-- Literal normalized Fourier integral of the ORIGINAL actual mixed
fiber. The arithmetic factor and the sqrt(N)*d kernel are both derived. -/
theorem actualZeroFiber_fourierIntegral (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (y : ℝ) (hy : 0 < y) (m n : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    (∫ x in (0 : ℝ)..1, AddCircle.fourier (-n) (x : UnitAddCircle) *
      actualZeroFiber N hN d m ψ (horizontalPoint y hy x)) =
      (if N.Coprime d then kloosterman d (-n * inverseResidue d (N : ℤ)) (-m) else 0) *
        𝓕 (actualKernel (zeroModulus N d) (zeroModulus_ne_zero N hN d) y hy m ψ) (n : ℝ) := by
  let F := periodizedKernelCircle (zeroModulus N d) (zeroModulus_ne_zero N hN d) y hy m ψ hψ
  have hcoeff := zeroFiniteSection_fourierCoeff N hN d m n F
    (periodizedKernelCircle_integrable _ _ y hy m ψ hψ)
  dsimp only [F] at hcoeff
  rw [periodizedKernelCircle_fourierCoeff _ _ y hy m n ψ hψ hcψ hposψ,
    zeroGeneralized_eq_physical_or_zero] at hcoeff
  rw [AddCircle.fourierCoeff_eq_intervalIntegral _ n 0] at hcoeff
  simpa only [zero_add, one_div_one, one_smul, smul_eq_mul,
    actualZeroFiber_eq_section N hN d y hy m ψ hψ hcψ hposψ] using hcoeff

/-- The orbit kernel has the exact N*d^2 denominator after substitution.
This is the kernel entering the preceding actual Fourier integral. -/
theorem zeroKernel_explicit (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ) :
    actualKernel (zeroModulus N d) (zeroModulus_ne_zero N hN d) y hy m ψ x =
      AddCircle.fourier m
        ((-x / ((N : ℝ) * (d : ℝ) ^ 2 * (x ^ 2 + y ^ 2)) : ℝ) : UnitAddCircle) *
      ψ (y / ((N : ℝ) * (d : ℝ) ^ 2 * (x ^ 2 + y ^ 2))) := by
  rw [actualKernel_formula, zeroModulus_sq]

end ImbalancedChen.Part3.InfinityZeroActualFiberFourier20261026a
