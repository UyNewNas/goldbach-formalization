import ImbalancedChen.Part3ActualInfinityKloostermanSeed
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.Compact

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

At infinity-to-infinity, a continuous radial seed with genuine compact
support in positive height gives an actual continuous compactly supported
Bruhat x-kernel. Its integrability and local summability of integer
translates are proved; native periodization then supplies its actual
Fourier integral and removes the prior common-kernel integrability input.
The infinite modulus sum, Bessel evaluation and spectral formula remain
separate OPEN steps.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a

open Set MeasureTheory Filter Asymptotics
open scoped MatrixGroups UpperHalfPlane BigOperators FourierTransform
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail

/-- The actual point of height y and real coordinate x. -/
def horizontalPoint (y : ℝ) (hy : 0 < y) (x : ℝ) : UpperHalfPlane :=
  ⟨⟨x, y⟩, hy⟩

/-- The actual Fourier-radial seed after the Bruhat Weyl action. -/
def actualKernel (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  fourierRadialSeed m ψ (scaledWeyl c hc • horizontalPoint y hy x)

/-- The imaginary part in the actual SL2 action has the exact geometric
denominator required for the compact-support argument. -/
theorem scaledWeyl_horizontal_im (c : ℝ) (hc : c ≠ 0)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    (scaledWeyl c hc • horizontalPoint y hy x).im =
      y / (c ^ 2 * (x ^ 2 + y ^ 2)) := by
  have hxy : x ^ 2 + y ^ 2 ≠ 0 := by nlinarith [sq_pos_of_pos hy, sq_nonneg x]
  have hden : c ^ 2 * (x ^ 2 + y ^ 2) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc) hxy
  have hnorm : (c * x) ^ 2 + (c * y) ^ 2 ≠ 0 := by
    have heq : (c * x) ^ 2 + (c * y) ^ 2 = c ^ 2 * (x ^ 2 + y ^ 2) := by ring
    rwa [heq]
  have hnorm' : (c * x) * (c * x) + (c * y) * (c * y) ≠ 0 := by
    simpa only [pow_two] using hnorm
  change (((scaledWeyl c hc • horizontalPoint y hy x : UpperHalfPlane) : ℂ)).im = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [scaledWeyl, horizontalPoint, Complex.div_im, Complex.normSq] <;>
    field_simp [hc, hxy, hden, hnorm, hnorm'] <;> ring

theorem scaledWeyl_horizontal_re (c : ℝ) (hc : c ≠ 0)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    (scaledWeyl c hc • horizontalPoint y hy x).re =
      -x / (c ^ 2 * (x ^ 2 + y ^ 2)) := by
  have hxy : x ^ 2 + y ^ 2 ≠ 0 := by nlinarith [sq_pos_of_pos hy, sq_nonneg x]
  have hden : c ^ 2 * (x ^ 2 + y ^ 2) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc) hxy
  have hnorm : (c * x) ^ 2 + (c * y) ^ 2 ≠ 0 := by
    have heq : (c * x) ^ 2 + (c * y) ^ 2 = c ^ 2 * (x ^ 2 + y ^ 2) := by ring
    rwa [heq]
  have hnorm' : (c * x) * (c * x) + (c * y) * (c * y) ≠ 0 := by
    simpa only [pow_two] using hnorm
  change (((scaledWeyl c hc • horizontalPoint y hy x : UpperHalfPlane) : ℂ)).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [scaledWeyl, horizontalPoint, Complex.div_re, Complex.normSq] <;>
    field_simp [hc, hxy, hden, hnorm, hnorm'] <;> ring

/-- This is a theorem identifying the rational formula with the actual
transformed cusp seed, rather than a substitute formal kernel. -/
theorem actualKernel_formula (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ) :
    actualKernel c hc y hy m ψ x =
      AddCircle.fourier m
        ((-x / (c ^ 2 * (x ^ 2 + y ^ 2)) : ℝ) : UnitAddCircle) *
        ψ (y / (c ^ 2 * (x ^ 2 + y ^ 2))) := by
  unfold actualKernel fourierRadialSeed
  rw [scaledWeyl_horizontal_re, scaledWeyl_horizontal_im]

/-- Genuine compact support inside positive height supplies a strictly
positive lower support bound. The identically zero profile is included. -/
theorem radial_support_positive_floor (ψ : ℝ → ℂ) (hcompact : HasCompactSupport ψ)
    (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, ψ t ≠ 0 → a ≤ t := by
  by_cases hne : (tsupport ψ).Nonempty
  · obtain ⟨a, ha⟩ := hcompact.isCompact.exists_isLeast hne
    exact ⟨a, hpositive ha.1, fun t ht => ha.2 (subset_tsupport ψ ht)⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    exact (hne ⟨t, subset_tsupport ψ ht⟩).elim

/-- Nonzero values of the actual kernel force a quantitative bounded
horizontal coordinate, using the actual transformed imaginary part. -/
theorem actualKernel_support_bound (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (a : ℝ) (ha : 0 < a)
    (hfloor : ∀ t : ℝ, ψ t ≠ 0 → a ≤ t) :
    Function.support (actualKernel c hc y hy m ψ) ⊆
      Icc (-(y / (a * c ^ 2) + 1)) (y / (a * c ^ 2) + 1) := by
  intro x hx
  have hxne : actualKernel c hc y hy m ψ x ≠ 0 := hx
  rw [actualKernel_formula] at hxne
  have hψ : ψ (y / (c ^ 2 * (x ^ 2 + y ^ 2))) ≠ 0 := right_ne_zero_of_mul hxne
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hden : 0 < c ^ 2 * (x ^ 2 + y ^ 2) :=
    mul_pos hc2 (by nlinarith [sq_nonneg x, sq_pos_of_pos hy])
  have hac : 0 < a * c ^ 2 := mul_pos ha hc2
  have hmass := (le_div_iff₀ hden).mp (hfloor _ hψ)
  have hx2 : x ^ 2 ≤ y / (a * c ^ 2) := by
    apply (le_div_iff₀ hac).mpr
    nlinarith [hmass, mul_nonneg hac.le (sq_nonneg y)]
  have hratio : 0 < y / (a * c ^ 2) := div_pos hy hac
  constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]

/-- The actual x-kernel is compactly supported, without an assumed
integrability or decay certificate. -/
theorem actualKernel_hasCompactSupport (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hcompact : HasCompactSupport ψ)
    (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    HasCompactSupport (actualKernel c hc y hy m ψ) := by
  obtain ⟨a, ha, hfloor⟩ := radial_support_positive_floor ψ hcompact hpositive
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  by_contra hne
  exact hx (actualKernel_support_bound c hc y hy m ψ a ha hfloor hne)

/-- Ordinary continuity of the genuine kernel follows from its actual
rational coordinates and the radial profile's continuity. -/
theorem actualKernel_continuous (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Continuous (actualKernel c hc y hy m ψ) := by
  have hden (x : ℝ) : c ^ 2 * (x ^ 2 + y ^ 2) ≠ 0 := by
    exact ne_of_gt (mul_pos (sq_pos_of_ne_zero hc)
      (by nlinarith [sq_nonneg x, sq_pos_of_pos hy]))
  have hre : Continuous (fun x : ℝ => -x / (c ^ 2 * (x ^ 2 + y ^ 2))) := by
    fun_prop (disch := exact hden _)
  have him : Continuous (fun x : ℝ => y / (c ^ 2 * (x ^ 2 + y ^ 2))) := by
    fun_prop (disch := exact hden _)
  have hcircle : Continuous (fun x : ℝ =>
      ((-x / (c ^ 2 * (x ^ 2 + y ^ 2)) : ℝ) : UnitAddCircle)) :=
    continuous_quotient_mk'.comp hre
  have heq : actualKernel c hc y hy m ψ = fun x =>
      AddCircle.fourier m
        ((-x / (c ^ 2 * (x ^ 2 + y ^ 2)) : ℝ) : UnitAddCircle) *
        ψ (y / (c ^ 2 * (x ^ 2 + y ^ 2))) := by
    funext x
    exact actualKernel_formula c hc y hy m ψ x
  rw [heq]
  exact ((map_continuous (AddCircle.fourier m)).comp hcircle).mul (hψ.comp him)

/-- L1 of the actual Bruhat kernel is now a consequence of the genuine
compact radial seed inputs. -/
theorem actualKernel_integrable (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ)
    (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Integrable (actualKernel c hc y hy m ψ) :=
  (actualKernel_continuous c hc y hy m ψ hψ).integrable_of_hasCompactSupport
    (actualKernel_hasCompactSupport c hc y hy m ψ hcompact hpositive)

def actualKernelMap (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) : C(ℝ, ℂ) :=
  ⟨actualKernel c hc y hy m ψ, actualKernel_continuous c hc y hy m ψ hψ⟩

/-- Compact support supplies actual decay at infinity; no asymptotic
kernel estimate is inserted as a premise. -/
theorem actualKernelMap_decay (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ)
    (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    (actualKernelMap c hc y hy m ψ hψ : ℝ → ℂ) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  apply IsBigO.of_bound 1
  filter_upwards [(actualKernel_hasCompactSupport c hc y hy m ψ hcompact hpositive).isCompact.compl_mem_cocompact]
    with x hx
  have hzero : actualKernel c hc y hy m ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp only [actualKernelMap, ContinuousMap.coe_mk, hzero, norm_zero, one_mul]
  exact norm_nonneg _

/-- Actual local summability of every integer translate family, proved
from compact support before the periodization theorem is invoked. -/
theorem actualKernel_translates_locally_summable (c : ℝ) (hc : c ≠ 0)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ))
    (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun k : ℤ =>
      ‖((actualKernelMap c hc y hy m ψ hψ).comp (ContinuousMap.addRight (k : ℝ))).restrict K‖) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((isBigO_norm_restrict_cocompact (actualKernelMap c hc y hy m ψ hψ)
      (by norm_num : (0 : ℝ) < 2)
      (actualKernelMap_decay c hc y hy m ψ hψ hcompact hpositive) K).comp_tendsto
        Int.tendsto_coe_cofinite)

/-- The concrete circle kernel is the native lift of the actual
continuous integer periodization, rather than an assumed coefficient. -/
def periodizedKernelCircle (c : ℝ) (hc : c ≠ 0) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) : UnitAddCircle → ℂ :=
  Function.Periodic.lift ((actualKernelMap c hc y hy m ψ hψ).periodic_tsum_comp_add_zsmul 1)

/-- The concrete circle lift evaluates to the genuine pointwise integer
sum, after actual local summability has already been established. -/
theorem periodizedKernelCircle_coe (c : ℝ) (hc : c ≠ 0)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) (x : ℝ) :
    periodizedKernelCircle c hc y hy m ψ hψ (x : UnitAddCircle) =
      ∑' k : ℤ, actualKernel c hc y hy m ψ (x + (k : ℝ)) := by
  simp only [periodizedKernelCircle, Function.Periodic.lift_coe, zsmul_one]
  rw [← ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
    (actualKernel_translates_locally_summable c hc y hy m ψ hψ hcompact hpositive))]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    actualKernelMap, ContinuousMap.coe_mk]
/-- Native interval tiling gives the actual Fourier integral of this
concrete periodization. -/
theorem periodizedKernelCircle_fourierCoeff (c : ℝ) (hc : c ≠ 0)
    (y : ℝ) (hy : 0 < y) (m n : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    AddCircle.fourierCoeff (periodizedKernelCircle c hc y hy m ψ hψ) n =
      𝓕 (actualKernel c hc y hy m ψ) (n : ℝ) := by
  exact Real.fourierCoeff_tsum_comp_add
    (actualKernel_translates_locally_summable c hc y hy m ψ hψ hcompact hpositive) n

/-- The lifted continuous periodization is itself continuous on the
actual quotient circle. -/
theorem periodizedKernelCircle_continuous (c : ℝ) (hc : c ≠ 0)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Continuous (periodizedKernelCircle c hc y hy m ψ hψ) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (fun x : ℝ => periodizedKernelCircle c hc y hy m ψ hψ (x : UnitAddCircle))
  simpa only [periodizedKernelCircle, Function.Periodic.lift_coe, zsmul_one] using
    (map_continuous (∑' k : ℤ,
      (actualKernelMap c hc y hy m ψ hψ).comp (ContinuousMap.addRight (k : ℝ))))

/-- Thus the common circle kernel integrability input of the preceding
finite-modulus coefficient lemma is proved for this genuine compact seed. -/
theorem periodizedKernelCircle_integrable (c : ℝ) (hc : c ≠ 0)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Integrable (periodizedKernelCircle c hc y hy m ψ hψ) AddCircle.haarAddCircle :=
  (periodizedKernelCircle_continuous c hc y hy m ψ hψ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Genuine compact-seed finite-modulus folding: no `Integrable F`
assumption remains. The remaining transform is the actual real Fourier
integral of the actual Bruhat kernel. -/
theorem compactSeed_canonicalSection_fourierCoeff (c : ℕ) [NeZero c]
    (y : ℝ) (hy : 0 < y) (m n : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hpositive : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    AddCircle.fourierCoeff
      (canonicalFiniteSection c m (periodizedKernelCircle (c : ℝ)
        (by exact_mod_cast (NeZero.ne c)) y hy m ψ hψ)) n =
      kloosterman c n m *
        𝓕 (actualKernel (c : ℝ) (by exact_mod_cast (NeZero.ne c)) y hy m ψ) (n : ℝ) := by
  rw [canonicalFiniteSection_fourierCoeff c m n _
    (periodizedKernelCircle_integrable _ _ y hy m ψ hψ)]
  rw [periodizedKernelCircle_fourierCoeff _ _ y hy m n ψ hψ hcompact hpositive]

end ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a

