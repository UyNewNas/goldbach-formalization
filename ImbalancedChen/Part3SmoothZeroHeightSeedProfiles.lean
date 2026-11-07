import ImbalancedChen.Part3SmoothIntegerUnitPartition
import ImbalancedChen.Part3ActualInfinityCuspAnnihilator
import ImbalancedChen.Part3Gamma0SmoothCompactTensorCore
import Mathlib.Analysis.Complex.RealDeriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual smooth compact positive-height zero-frequency profiles, their
literal negative-Maass profile -y^2 psi'', and a genuine compact smooth
horizontal tensor. Its integer periodization is psi(y), and the integer
periodization of its actual tensor Laplacian is exactly -y^2 psi''(y).
Both horizontal derivative contributions are computed before summing.
-/
namespace ImbalancedChen.Part3.SmoothZeroHeightSeedProfiles20261026b

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open SmoothIntegerUnitPartition20261026b
open ActualInfinityCuspAnnihilator20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z
open Gamma0SmoothCompactTensorCore20261025a
open GammaInfinityTranslationStrip20261025a

structure SmoothHeightSeed extends HeightSeed where
  cinfty : ContDiff ℝ ∞ toFun

def SmoothHeightSeed.maass (s : SmoothHeightSeed) : SmoothHeightSeed where
  toFun := fun y => (-((y : ℂ)^2)) * deriv (deriv s.toFun) y
  continuous := by
    have hd := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp s.cinfty).2).2
    exact ((Complex.continuous_ofReal.pow 2).neg.mul hd.continuous)
  compact := s.compact.deriv.deriv.mul_left
  positive := tsupport_mul_subset_right.trans
    (tsupport_deriv_subset.trans (tsupport_deriv_subset.trans s.positive))
  cinfty := by
    have hd := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp s.cinfty).2).2
    exact ((Complex.ofRealCLM.contDiff.pow 2).neg.mul hd)

def complexHorizontalPartition (x : ℝ) : ℂ := (horizontalUnitPartition x : ℂ)

theorem complexHorizontalPartition_cinfty : ContDiff ℝ ∞ complexHorizontalPartition :=
  Complex.ofRealCLM.contDiff.comp horizontalUnitPartition_cinfty

theorem complexHorizontalPartition_compact : HasCompactSupport complexHorizontalPartition :=
  horizontalUnitPartition_compact.comp_left (by simp)

theorem complexHorizontalPartition_deriv (x : ℝ) :
    deriv complexHorizontalPartition x = (deriv horizontalUnitPartition x : ℂ) :=
  ((horizontalUnitPartition_cinfty.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv

theorem complexHorizontalPartition_second (x : ℝ) :
    deriv (deriv complexHorizontalPartition) x = (deriv (deriv horizontalUnitPartition) x : ℂ) := by
  rw [show deriv complexHorizontalPartition = (fun y => (deriv horizontalUnitPartition y : ℂ)) from
    funext complexHorizontalPartition_deriv]
  exact (((contDiff_infty_iff_deriv.mp horizontalUnitPartition_cinfty).2.differentiable
    (by simp) x).hasDerivAt.ofReal_comp).deriv

theorem complexHorizontalPartition_integer_sum (x : ℝ) :
    (∑' k : ℤ, complexHorizontalPartition (x + (k : ℝ))) = 1 := by
  rw [complexHorizontalPartition, ← Complex.ofReal_tsum, horizontalUnitPartition_integer_sum,
    Complex.ofReal_one]

theorem complexHorizontalPartition_second_integer_sum (x : ℝ) :
    (∑' k : ℤ, deriv (deriv complexHorizontalPartition) (x + (k : ℝ))) = 0 := by
  simp_rw [complexHorizontalPartition_second]
  rw [← Complex.ofReal_tsum, horizontalUnitPartition_second_integer_sum, Complex.ofReal_zero]

/-- Compact horizontal support supplies actual summability of the integer
trace; no complex tsum additivity is used without this supplier. -/
theorem compact_integer_translate_summable (f : ℝ → ℂ) (hc : HasCompactSupport f) (x : ℝ) :
    Summable (fun k : ℤ => f (x + (k : ℝ))) := by
  classical
  obtain ⟨a, ha⟩ := hc.bddBelow
  obtain ⟨b, hb⟩ := hc.bddAbove
  let S : Finset ℤ := (Set.finite_Icc (Int.ceil (a - x)) (Int.floor (b - x))).toFinset
  apply summable_of_ne_finset_zero (s := S)
  intro k hk
  by_contra hnonzero
  have ht : x + (k : ℝ) ∈ tsupport f := subset_closure hnonzero
  have hlo : Int.ceil (a - x) ≤ k := Int.ceil_le.mpr (by linarith [ha ht])
  have hhi : k ≤ Int.floor (b - x) := Int.le_floor.mpr (by linarith [hb ht])
  exact hk ((Set.finite_Icc _ _).mem_toFinset.mpr ⟨hlo, hhi⟩)

def profileTensor (s : SmoothHeightSeed) : SmoothCompactTensor where
  horizontal := complexHorizontalPartition
  vertical := s.toFun
  horizontal_smooth := complexHorizontalPartition_cinfty.of_le (by simp)
  vertical_smooth := s.cinfty.of_le (by simp)
  horizontal_compact := complexHorizontalPartition_compact
  vertical_compact := s.compact
  vertical_positive := s.positive
  horizontal_cinfty := complexHorizontalPartition_cinfty
  vertical_cinfty := s.cinfty

def profileTensorSeed (s : SmoothHeightSeed) : UpperHalfPlane → ℂ :=
  tensorFunctionH complexHorizontalPartition s.toFun

def profileTensorLaplacianSeed (s : SmoothHeightSeed) : UpperHalfPlane → ℂ :=
  tensorHyperbolicLaplacianH complexHorizontalPartition s.toFun

private theorem translate_height (k : ℤ) (z : UpperHalfPlane) : (translate k z).im = z.im := by
  rw [translate_eq_vadd, UpperHalfPlane.vadd_im]

theorem profileTensorSeed_integer_sum (s : SmoothHeightSeed) (z : UpperHalfPlane) :
    (∑' k : ℤ, profileTensorSeed s (translate k z)) = s.toFun z.im := by
  simp only [profileTensorSeed, tensorFunctionH_eq, translate_re, translate_height]
  rw [tsum_mul_right, complexHorizontalPartition_integer_sum, one_mul]

/-- The negative height-square operator is the original hyperbolic
Laplacian convention; no first-height-derivative term is introduced. -/
theorem profileTensorLaplacianSeed_integer_sum (s : SmoothHeightSeed) (z : UpperHalfPlane) :
    (∑' k : ℤ, profileTensorLaplacianSeed s (translate k z)) = s.maass.toFun z.im := by
  have hsecond := (compact_integer_translate_summable (deriv (deriv complexHorizontalPartition))
    complexHorizontalPartition_compact.deriv.deriv z.re).mul_right (s.toFun z.im)
  have hvalue := (compact_integer_translate_summable complexHorizontalPartition
    complexHorizontalPartition_compact z.re).mul_right (deriv (deriv s.toFun) z.im)
  have heq : (fun k : ℤ => profileTensorLaplacianSeed s (translate k z)) =
      fun k => (-((z.im : ℂ)^2)) *
        (deriv (deriv complexHorizontalPartition) (z.re + (k : ℝ)) * s.toFun z.im +
          complexHorizontalPartition (z.re + (k : ℝ)) * deriv (deriv s.toFun) z.im) := by
    funext k
    change -(((translate k z).im : ℂ)^2 *
      (deriv (deriv complexHorizontalPartition) (translate k z).re * s.toFun (translate k z).im +
        complexHorizontalPartition (translate k z).re * deriv (deriv s.toFun) (translate k z).im)) = _
    rw [translate_re, translate_height]
    ring
  rw [heq, tsum_mul_left, hsecond.tsum_add hvalue, tsum_mul_right, tsum_mul_right,
    complexHorizontalPartition_second_integer_sum, complexHorizontalPartition_integer_sum]
  simp only [zero_mul, one_mul, zero_add, SmoothHeightSeed.maass]

end
end ImbalancedChen.Part3.SmoothZeroHeightSeedProfiles20261026b
