import ImbalancedChen.Part3ActualCuspStripCutoffGraph
import ImbalancedChen.Part3Gamma0CompactGreenProductL1

/-!
# Actual height-cutoff Maass commutator

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

A genuine one-dimensional second product rule gives the actual native
upperMaass commutator for an arbitrary C2 positive-chart test function.
The cutoff factor is the same fixed native chi(y/Y). Every coefficient
is its proved first or second derivative; no operator-commutation or
error estimate is an input. The commutator vanishes off Y<=y<=2Y.
This is a local gluing primitive, not a global Gamma0 or graph-domain claim.
-/

namespace ImbalancedChen.Part3.ActualHeightCutoffMaassCommutator20261025a

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a
open ActualGamma0MaassDescent20261025a
open ActualCuspStripCutoff20261025a
open ActualCuspStripCutoffGraph20261025a

/-- Only the second factor needs C2 on positive heights. Its first
derivative product formula holds on a genuine neighborhood before being
differentiated, rather than being inferred from one pointwise equality. -/
theorem second_deriv_height_product (b g : ℝ → ℂ)
    (hb : ContDiff ℝ 2 b) (hg : ContDiffOn ℝ 2 g (Ioi (0 : ℝ)))
    {y : ℝ} (hy : 0 < y) :
    deriv (deriv (fun t => b t*g t)) y =
      deriv (deriv b) y*g y + 2*deriv b y*deriv g y + b y*deriv (deriv g) y := by
  have hfirst : deriv (fun t => b t*g t) =ᶠ[𝓝 y]
      (fun t => deriv b t*g t+b t*deriv g t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact deriv_mul (hb.differentiable (by norm_num) t)
      (((hg t ht).contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by norm_num))
  have hga : ContDiffAt ℝ 2 g y := (hg y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)
  have hgb : DifferentiableAt ℝ g y := hga.differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ (deriv g) y :=
    (hga.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hba : DifferentiableAt ℝ b y := hb.differentiable (by norm_num) y
  have hbd : DifferentiableAt ℝ (deriv b) y :=
    (hb.contDiffAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hfirst.deriv_eq,deriv_add (hbd.mul hgb) (hba.mul hgd),
    deriv_mul hbd hgb,deriv_mul hba hgd]
  ring

/-- Actual coordinate Maass commutator for any global C2 height factor
and an arbitrary positive-chart C2 function. -/
theorem chartMaass_height_commutator (b : ℝ → ℂ) (hb : ContDiff ℝ 2 b)
    (F : ℝ × ℝ → ℂ) (hF : ContDiffOn ℝ 2 F positiveChart)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    chartMaass (fun q => b q.2*F q) p - b p.2*chartMaass F p =
      -((p.2 : ℂ)^2 *
        (2*deriv b p.2*sliceDy F p + deriv (deriv b) p.2*F p)) := by
  have hg : ContDiffOn ℝ 2 (fun y : ℝ => F (p.1,y)) (Ioi (0 : ℝ)) :=
    hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => hy)
  have hxx : deriv (deriv (fun x : ℝ => b p.2*F (x,p.2))) p.1 =
      b p.2*deriv (deriv (fun x : ℝ => F (x,p.2))) p.1 := by
    simp only [deriv_const_mul_field',deriv_const_mul_field]
  have hyy := second_deriv_height_product b (fun y : ℝ => F (p.1,y)) hb hg hp
  unfold chartMaass
  rw [hxx,hyy]
  unfold sliceDy
  ring

theorem extendUpper_height_mul (b : ℝ → ℂ) (F : UpperHalfPlane → ℂ) :
    extendUpper (fun z => b z.im*F z) = fun p => b p.2*extendUpper F p := by
  funext p
  by_cases hp : 0 < p.2 <;> simp only [extendUpper,hp,dif_pos,dif_neg,mul_zero]

/-- Native H operator product rule, with the true first vertical
derivative of the existing zero-extension representative at positive height. -/
theorem upperMaass_height_commutator (b : ℝ → ℂ) (hb : ContDiff ℝ 2 b)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) (z : UpperHalfPlane) :
    upperMaass (fun w => b w.im*F w) z - b z.im*upperMaass F z =
      -((z.im : ℂ)^2 *
        (2*deriv b z.im*sliceDy (extendUpper F) (z.re,z.im) +
          deriv (deriv b) z.im*F z)) := by
  change chartMaass (extendUpper (fun w => b w.im*F w)) (z.re,z.im) -
    b z.im*chartMaass (extendUpper F) (z.re,z.im) = _
  rw [extendUpper_height_mul]
  simpa only [extendUpper_pair] using
    chartMaass_height_commutator b hb (extendUpper F) hF (z.re,z.im) z.im_pos

private theorem complex_cutoff_deriv (Y y : ℝ) :
    deriv (fun t : ℝ => (heightCutoff Y t : ℂ)) y =
      ((deriv chi (y/Y)/Y : ℝ) : ℂ) := by
  rw [← deriv_heightCutoff]
  exact ((heightCutoff_cinfty Y).differentiable (by simp) y).hasDerivAt.ofReal_comp.deriv

private theorem complex_cutoff_second_deriv (Y y : ℝ) :
    deriv (deriv (fun t : ℝ => (heightCutoff Y t : ℂ))) y =
      ((deriv (deriv chi) (y/Y)/Y^2 : ℝ) : ℂ) := by
  have hfirst : deriv (fun t : ℝ => (heightCutoff Y t : ℂ)) =
      fun t => ((deriv chi (t/Y)/Y : ℝ) : ℂ) := funext (complex_cutoff_deriv Y)
  rw [hfirst]
  have hr := (((deriv_chi_cinfty.differentiable (by simp) (y/Y)).hasDerivAt).comp y
    ((hasDerivAt_id y).div_const Y)).div_const Y
  have h := hr.ofReal_comp
  simpa only [div_eq_mul_inv,one_mul,inv_pow,pow_two,mul_assoc] using h.deriv

/-- Exact fixed native cutoff formula. No commutator premise or bound
on F is used, only the actual C2 chart regularity needed to differentiate it. -/
theorem upperMaass_fixed_cutoff_commutator (Y : ℝ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) (z : UpperHalfPlane) :
    upperMaass (fun w => complexCutoffH Y w*F w) z - complexCutoffH Y z*upperMaass F z =
      -((z.im : ℂ)^2 *
        (2*((deriv chi (z.im/Y)/Y : ℝ) : ℂ)*sliceDy (extendUpper F) (z.re,z.im) +
          ((deriv (deriv chi) (z.im/Y)/Y^2 : ℝ) : ℂ)*F z)) := by
  have hb : ContDiff ℝ 2 (fun t : ℝ => (heightCutoff Y t : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (heightCutoff_cinfty Y)).of_le (by simp)
  simpa only [complexCutoffH,cutoffH,complex_cutoff_deriv,complex_cutoff_second_deriv] using
    upperMaass_height_commutator (fun t : ℝ => (heightCutoff Y t : ℂ)) hb F hF z

/-- Both actual derivative coefficients vanish outside the SAME actual
height annulus. This can be used in a later, separately licensed gluing proof. -/
theorem upperMaass_fixed_cutoff_commutator_zero {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ) (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (z : UpperHalfPlane) (hz : z.im < Y ∨ 2*Y < z.im) :
    upperMaass (fun w => complexCutoffH Y w*F w) z - complexCutoffH Y z*upperMaass F z = 0 := by
  rw [upperMaass_fixed_cutoff_commutator Y F hF]
  rcases hz with hlow | hhigh
  · rw [deriv_chi_zero_below (div_pos z.im_pos hY) ((div_lt_one hY).mpr hlow),
      second_deriv_chi_zero_below (div_pos z.im_pos hY) ((div_lt_one hY).mpr hlow)]
    simp
  · rw [deriv_chi_zero_above ((lt_div_iff₀ hY).mpr hhigh),
      second_deriv_chi_zero_above ((lt_div_iff₀ hY).mpr hhigh)]
    simp

end
end ImbalancedChen.Part3.ActualHeightCutoffMaassCommutator20261025a
