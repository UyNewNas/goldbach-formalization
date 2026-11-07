import ImbalancedChen.Part3GammaSmoothMultiplierPeriodization
import ImbalancedChen.Part3Gamma0CompactGreenProductL1
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Literal native Maass Leibniz formulas on the positive H chart. The mixed
first-derivative term is derived from genuine one-variable product rules;
there is no assumed weak-product, differential, commutator or graph identity.
In particular the cutoff-squared formula retains BOTH gradient-square and
cross-gradient terms, with the actual hyperbolic height-square factor.
-/

namespace ImbalancedChen.Part3.GammaNativeMaassLeibniz20261026a

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a ActualGamma0MaassDescent20261025a
open GammaSmoothMultiplierPeriodization20261026a

/-- Genuine second-order scalar product rule at a C2 germ. -/
theorem second_deriv_mul_at (f g : ℝ → ℂ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t * g t)) x =
      deriv (deriv f) x * g x + 2 * deriv f x * deriv g x +
        f x * deriv (deriv g) x := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hfdd : DifferentiableAt ℝ (deriv f) x :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgdd : DifferentiableAt ℝ (deriv g) x :=
    (hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hlocalf : ∀ᶠ t in 𝓝 x, ContDiffAt ℝ 2 f t := hf.eventually (by norm_num)
  have hlocalg : ∀ᶠ t in 𝓝 x, ContDiffAt ℝ 2 g t := hg.eventually (by norm_num)
  have hfirst : deriv (fun t => f t * g t) =ᶠ[𝓝 x]
      (fun t => deriv f t * g t + f t * deriv g t) := by
    filter_upwards [hlocalf, hlocalg] with t hft hgt
    exact deriv_fun_mul (hft.differentiableAt (by norm_num)) (hgt.differentiableAt (by norm_num))
  have hd := (hfdd.hasDerivAt.mul hgd.hasDerivAt).add
    (hfd.hasDerivAt.mul hgdd.hasDerivAt)
  calc
    _ = deriv (fun t => deriv f t * g t + f t * deriv g t) x := hfirst.deriv_eq
    _ = _ := by rw [hd.deriv]; ring

private theorem sliceX_C2 (F : (ℝ × ℝ) → ℂ)
    (hF : ContDiffOn ℝ 2 F positiveChart) (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ 2 (fun x => F (x,p.2)) p.1 :=
  ((hF p hp).contDiffAt (positiveChart_isOpen.mem_nhds hp)).comp p.1
    (contDiffAt_id.prodMk contDiffAt_const)

private theorem sliceY_C2 (F : (ℝ × ℝ) → ℂ)
    (hF : ContDiffOn ℝ 2 F positiveChart) (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ 2 (fun y => F (p.1,y)) p.2 :=
  ((hF p hp).contDiffAt (positiveChart_isOpen.mem_nhds hp)).comp p.2
    (contDiffAt_const.prodMk contDiffAt_id)

def chartCross (F G : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) : ℂ :=
  -(2 : ℂ) * (p.2 : ℂ)^2 *
    (sliceDx F p * sliceDx G p + sliceDy F p * sliceDy G p)

/-- Pointwise chart identity with the true native coordinate derivatives. -/
theorem chartMaass_mul (F G : (ℝ × ℝ) → ℂ)
    (hF : ContDiffOn ℝ 2 F positiveChart) (hG : ContDiffOn ℝ 2 G positiveChart)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    chartMaass (F*G) p =
      F p * chartMaass G p + G p * chartMaass F p + chartCross F G p := by
  have hx := second_deriv_mul_at (fun x => F (x,p.2)) (fun x => G (x,p.2)) p.1
    (sliceX_C2 F hF p hp) (sliceX_C2 G hG p hp)
  have hy := second_deriv_mul_at (fun y => F (p.1,y)) (fun y => G (p.1,y)) p.2
    (sliceY_C2 F hF p hp) (sliceY_C2 G hG p hp)
  simp only [chartMaass, Pi.mul_apply, chartCross, sliceDx, sliceDy]
  rw [hx, hy]
  ring

/-- Actual native first partials on H, with the original zero extension. -/
def nativeDx (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  sliceDx (extendUpper F) (z.re,z.im)

def nativeDy (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  sliceDy (extendUpper F) (z.re,z.im)

def maassCross (F G : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  -(2 : ℂ) * (z.im : ℂ)^2 *
    (nativeDx F z * nativeDx G z + nativeDy F z * nativeDy G z)

theorem nativeDx_mul (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart) (z : UpperHalfPlane) :
    nativeDx (F*G) z = nativeDx F z * G z + F z * nativeDx G z := by
  unfold nativeDx sliceDx
  rw [extendUpper_mul]
  have h := deriv_fun_mul
    ((sliceX_C2 (extendUpper F) hF (z.re,z.im) z.im_pos).differentiableAt (by norm_num))
    ((sliceX_C2 (extendUpper G) hG (z.re,z.im) z.im_pos).differentiableAt (by norm_num))
  simpa only [Pi.mul_apply, extendUpper_pair] using h

theorem nativeDy_mul (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart) (z : UpperHalfPlane) :
    nativeDy (F*G) z = nativeDy F z * G z + F z * nativeDy G z := by
  unfold nativeDy sliceDy
  rw [extendUpper_mul]
  have h := deriv_fun_mul
    ((sliceY_C2 (extendUpper F) hF (z.re,z.im) z.im_pos).differentiableAt (by norm_num))
    ((sliceY_C2 (extendUpper G) hG (z.re,z.im) z.im_pos).differentiableAt (by norm_num))
  simpa only [Pi.mul_apply, extendUpper_pair] using h

/-- Exact Maass Leibniz rule for arbitrary native C2 H functions. -/
theorem upperMaass_mul (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart) (z : UpperHalfPlane) :
    upperMaass (F*G) z =
      F z * upperMaass G z + G z * upperMaass F z + maassCross F G z := by
  unfold upperMaass
  rw [extendUpper_mul]
  simpa only [Complex.measurableEquivRealProd_apply, chartCross, maassCross,
    nativeDx, nativeDy, extendUpper_pair] using
    chartMaass_mul (extendUpper F) (extendUpper G) hF hG (z.re,z.im) z.im_pos

/-- The actual commutator includes the mixed gradient term. -/
theorem upperMaass_multiplier_commutator (chi F : UpperHalfPlane → ℂ)
    (hchi : ContDiffOn ℝ 2 (extendUpper chi) positiveChart)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) (z : UpperHalfPlane) :
    upperMaass (chi*F) z - chi z * upperMaass F z =
      F z * upperMaass chi z + maassCross chi F z := by
  rw [upperMaass_mul chi F hchi hF z]
  ring

/-- Literal cutoff-squared test, retaining both gradient-square and mixed
first-derivative terms. The formula is valid for complex C2 multipliers as
well; real compact cutoffs are a direct specialization. -/
theorem upperMaass_cutoff_square (chi F : UpperHalfPlane → ℂ)
    (hchi : ContDiffOn ℝ 2 (extendUpper chi) positiveChart)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) (z : UpperHalfPlane) :
    upperMaass ((chi*chi)*F) z =
      chi z^2 * upperMaass F z + 2 * chi z * F z * upperMaass chi z -
        2 * (z.im : ℂ)^2 * F z * ((nativeDx chi z)^2 + (nativeDy chi z)^2) -
        4 * (z.im : ℂ)^2 * chi z *
          (nativeDx chi z * nativeDx F z + nativeDy chi z * nativeDy F z) := by
  have hchisq : ContDiffOn ℝ 2 (extendUpper (chi*chi)) positiveChart := by
    rw [extendUpper_mul]
    exact hchi.mul hchi
  rw [upperMaass_mul (chi*chi) F hchisq hF z,
    upperMaass_mul chi chi hchi hchi z]
  simp only [maassCross, nativeDx_mul chi chi hchi hchi z,
    nativeDy_mul chi chi hchi hchi z, Pi.mul_apply]
  ring

end
end ImbalancedChen.Part3.GammaNativeMaassLeibniz20261026a
