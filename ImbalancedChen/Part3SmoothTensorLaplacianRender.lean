import ImbalancedChen.Part3Gamma0SmoothCompactTensorCore
import ImbalancedChen.Part3ActualTensorPoincareMaassJoin
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Logic.Equiv.Fin.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual Laplacian of a smooth compact positive-height tensor is the
sum of TWO explicitly constructed smooth compact positive-height tensors.
The construction uses the genuine real second derivatives and the actual
y^2 coefficient. It applies to the C-infinity subfamily, not to arbitrary
C2 tensors. No rendering or differential-commutation premise is supplied.

The finite rendering is transported through the already proved actual
Maass--Poincare identity, so its output is again an actual smooth compact
tensor Poincare function. No closure or spectral-domain assertion is used.
-/

namespace ImbalancedChen.Part3.SmoothTensorLaplacianRender20261025a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.ActualTensorPoincareMaassJoin20261025a

private theorem secondDeriv_cinfty {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deriv (deriv f)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2

private theorem heightSquare_cinfty :
    ContDiff ℝ ∞ (fun y : ℝ => (y : ℂ)^2) := by fun_prop

/-- The horizontal-second-derivative summand: (-h'', y^2 v). -/
def horizontalLaplacianTensor (T : SmoothCompactTensor) : SmoothCompactTensor :=
  let hh := (secondDeriv_cinfty T.horizontal_cinfty).neg
  let hv := heightSquare_cinfty.mul T.vertical_cinfty
  { horizontal := fun x => -(deriv (deriv T.horizontal) x)
    vertical := fun y => (y : ℂ)^2 * T.vertical y
    horizontal_smooth := hh.of_le (by simp)
    vertical_smooth := hv.of_le (by simp)
    horizontal_compact :=
      T.horizontal_compact.deriv.deriv.comp_left (g := fun z : ℂ => -z) (by simp)
    vertical_compact := T.vertical_compact.mul_left
    vertical_positive := tsupport_mul_subset_right.trans T.vertical_positive
    horizontal_cinfty := hh
    vertical_cinfty := hv }

/-- The vertical-second-derivative summand: (-h, y^2 v''). -/
def verticalLaplacianTensor (T : SmoothCompactTensor) : SmoothCompactTensor :=
  let hh := T.horizontal_cinfty.neg
  let hv := heightSquare_cinfty.mul (secondDeriv_cinfty T.vertical_cinfty)
  { horizontal := fun x => -(T.horizontal x)
    vertical := fun y => (y : ℂ)^2 * deriv (deriv T.vertical) y
    horizontal_smooth := hh.of_le (by simp)
    vertical_smooth := hv.of_le (by simp)
    horizontal_compact :=
      T.horizontal_compact.comp_left (g := fun z : ℂ => -z) (by simp)
    vertical_compact := T.vertical_compact.deriv.deriv.mul_left
    vertical_positive := tsupport_mul_subset_right.trans
      (tsupport_deriv_subset.trans (tsupport_deriv_subset.trans T.vertical_positive))
    horizontal_cinfty := hh
    vertical_cinfty := hv }

/-- Literal two-term smooth tensor rendering. -/
def laplacianPair (T : SmoothCompactTensor) : Fin 2 → SmoothCompactTensor :=
  ![horizontalLaplacianTensor T, verticalLaplacianTensor T]

theorem tensorLaplacian_eq_rendered_pair (T : SmoothCompactTensor) (z : UpperHalfPlane) :
    tensorHyperbolicLaplacianH T.horizontal T.vertical z =
      ∑ k : Fin 2, tensorFunctionH (laplacianPair T k).horizontal
        (laplacianPair T k).vertical z := by
  simp only [Fin.sum_univ_two, laplacianPair, Matrix.cons_val_zero, Matrix.cons_val_one]
  change -((z.im : ℂ)^2 *
      (deriv (deriv T.horizontal) z.re * T.vertical z.im +
        T.horizontal z.re * deriv (deriv T.vertical) z.im)) =
    (-deriv (deriv T.horizontal) z.re) * ((z.im : ℂ)^2 * T.vertical z.im) +
      (-T.horizontal z.re) * ((z.im : ℂ)^2 * deriv (deriv T.vertical) z.im)
  ring

def renderedFamily {ι : Type*} (T : ι → SmoothCompactTensor) :
    ι × Fin 2 → SmoothCompactTensor := fun ik => laplacianPair (T ik.1) ik.2

def renderedIndices {ι : Type*} (s : Finset ι) : Finset (ι × Fin 2) :=
  s.product Finset.univ

/-- Exact genuine finite Laplacian seed equality, including an empty family. -/
theorem finiteCoreLaplacian_eq_rendered {ι : Type*} (s : Finset ι)
    (T : ι → SmoothCompactTensor) :
    finiteCoreLaplacian s (fun i => (T i).toCompactTensor) =
      finiteCoreFunction (renderedIndices s)
        (fun ik => (renderedFamily T ik).toCompactTensor) := by
  funext z
  simp only [finiteCoreLaplacian, finiteCoreFunction, renderedIndices, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  exact tensorLaplacian_eq_rendered_pair (T i) z

/-- Genuine geometric Maass differentiation preserves this actual smooth
Poincare family, with its rendered output explicitly specified. -/
theorem upperMaass_smoothFinitePoincare_eq_rendered (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → SmoothCompactTensor) :
    upperMaass (smoothFinitePoincare N s T) =
      smoothFinitePoincare N (renderedIndices s) (renderedFamily T) := by
  rw [smoothFinitePoincare, upperMaass_finiteCompactTensorPoincare_eq_trace,
    finiteCoreLaplacian_eq_rendered]
  rfl

/-- A finite ordinal presentation of the same literal rendered family. -/
def ordinalRenderedFamily (n : ℕ) (T : Fin n → SmoothCompactTensor) :
    Fin (n * 2) → SmoothCompactTensor :=
  fun k => renderedFamily T (finProdFinEquiv.symm k)

theorem finiteCoreFunction_ordinal_render {n : ℕ} (T : Fin n → SmoothCompactTensor) :
    finiteCoreFunction (renderedIndices Finset.univ)
      (fun ik => (renderedFamily T ik).toCompactTensor) =
    finiteCoreFunction Finset.univ
      (fun k => (ordinalRenderedFamily n T k).toCompactTensor) := by
  funext z
  change (∑ ik ∈ (Finset.univ : Finset (Fin n)).product Finset.univ,
      tensorFunctionH (renderedFamily T ik).horizontal (renderedFamily T ik).vertical z) =
    ∑ k : Fin (n * 2), tensorFunctionH
      (renderedFamily T (finProdFinEquiv.symm k)).horizontal
      (renderedFamily T (finProdFinEquiv.symm k)).vertical z
  simpa only [Finset.univ_product_univ] using
    (Equiv.sum_comp (finProdFinEquiv.symm : Fin (n * 2) ≃ Fin n × Fin 2)
      (fun ik => tensorFunctionH (renderedFamily T ik).horizontal
        (renderedFamily T ik).vertical z)).symm

theorem upperMaass_smoothFinitePoincare_eq_ordinal_render (N n : ℕ)
    (T : Fin n → SmoothCompactTensor) :
    upperMaass (smoothFinitePoincare N Finset.univ T) =
      smoothFinitePoincare N Finset.univ (ordinalRenderedFamily n T) := by
  rw [upperMaass_smoothFinitePoincare_eq_rendered]
  unfold smoothFinitePoincare finiteCompactTensorPoincare
  rw [finiteCoreFunction_ordinal_render]

end
end ImbalancedChen.Part3.SmoothTensorLaplacianRender20261025a
