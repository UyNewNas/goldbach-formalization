import ImbalancedChen.Part3GammaRawQuotientCutoffH1
import ImbalancedChen.Part3GammaRawCutoffLeibnizFiber

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The literal weak-product coordinate derivatives of the RAW actual
quotient cutoff field have exactly the native weighted Leibniz fibre.
The real directional derivatives are identified with the existing native
slice derivatives; canonical chart value identities are pointwise.
No form membership or desired gradient identity is assumed. The native
carrier L2 Leibniz supplier and its exact cutoffEnergyH error then apply
to these actual raw weak derivatives, including arbitrary non-form inputs.
-/

namespace ImbalancedChen.Part3.GammaRawCutoffDerivativeFiberIdentity20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a Gamma0QuotientCellPushforward20261025a
open MaassWeakOperatorCore20261024zz Gamma0CompactGreenProductL120261025a
open CompactC2ProductMollifier20261026a LocalWeakH1CutoffProduct20261026b
open ActualPullbackLocalH1Transfer20261026b CanonicalPlanarL2UnitarySourceOnly
open ActualModularCutoffMaassBudget20261025a GammaSmoothMultiplierLegalTests20261026a
open ActualGamma0MaassDescent20261025a GammaNativeMaassLeibniz20261026a
open GammaCoreMultiplierGradientProduct20261026b GammaRawQuotientCutoffH120261026b
open GammaRawWeightedFiberL220261026b GammaRawCutoffLeibnizFiber20261026b
open Gamma0WeightedCutoffDefectLimit20261026a Gamma0CarrierGradientHilbertMap20261026b
open ActualModularCutoffGradient20261025a

theorem rawCutoffPlane_directional_at_upper (Y : ℝ) (hY : 0 < Y) (z : UpperHalfPlane) :
    directional ex (rawCutoffPlane Y) (chartMap z) = nativeDx (complexGlobalH Y) z ∧
    directional ey (rawCutoffPlane Y) (chartMap z) = nativeDy (complexGlobalH Y) z := by
  have hd := (actualCutoff_cinfty Y hY).differentiableOn (by simp)
  constructor
  · change fderiv ℝ (extendUpper (complexGlobalH Y)) (z.re,z.im) (1,0) =
      sliceDx (extendUpper (complexGlobalH Y)) (z.re,z.im)
    exact (sliceDx_eq_fderiv _ hd z.im_pos).symm
  · change fderiv ℝ (extendUpper (complexGlobalH Y)) (z.re,z.im) (0,1) =
      sliceDy (extendUpper (complexGlobalH Y)) (z.re,z.im)
    exact (sliceDy_eq_fderiv _ hd z.im_pos).symm

/-- Exact derivative-fibre join for ANY raw coordinate fields. Their
weak-H1 legality is separately derived by the native quotient H1 packet. -/
theorem raw_cutoff_weighted_fiber_identity (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (Gx Gy : Plane → ℂ) (Y : ℝ) (hY : 0 < Y) (z : UpperHalfPlane) :
    rawWeightedFiber (rawCutoffDx Y (actualPlanePullback N f) Gx)
      (rawCutoffDy Y (actualPlanePullback N f) Gy) z =
      complexGlobalH Y z • rawWeightedFiber Gx Gy z +
        f (orbitProjection N z) • nativeWeightedGradient (complexGlobalH Y) z := by
  obtain ⟨hx,hy⟩ := rawCutoffPlane_directional_at_upper Y hY z
  have hv : rawCutoffPlane Y (chartMap z) = complexGlobalH Y z := extendUpper_pair _ z
  have hf : actualPlanePullback N f (chartMap z) = f (orbitProjection N z) :=
    actualPlanePullback_at_upper N f z
  ext i
  fin_cases i <;>
    simp only [rawWeightedFiber,rawCutoffDx,rawCutoffDy,productDerivative,nativeWeightedGradient,
      PiLp.smul_apply,PiLp.add_apply,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
      smul_eq_mul,hx,hy,hv,hf] <;> ring

/-- The EXACT raw derivative fields used by the H1 packet are the raw
Leibniz fibres whose native carrier L2 convergence was proved separately. -/
theorem raw_cutoff_weighted_fiber_eq_Leibniz (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (Gx Gy : Plane → ℂ) (n : ℕ) :
    rawWeightedFiber (rawCutoffDx (cutoffHeight n) (actualPlanePullback N f) Gx)
      (rawCutoffDy (cutoffHeight n) (actualPlanePullback N f) Gy) =
      rawLeibnizFiber N f (rawWeightedFiber Gx Gy) n := by
  funext z
  exact raw_cutoff_weighted_fiber_identity N f Gx Gy (cutoffHeight n) (cutoffHeight_pos n) z

theorem raw_cutoff_derivative_fiber_carrier_memLp (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (Gx Gy : Plane → ℂ) (hW : MemLp (rawWeightedFiber Gx Gy) 2 (carrierVolume N)) (n : ℕ) :
    MemLp (rawWeightedFiber (rawCutoffDx (cutoffHeight n) (actualPlanePullback N f) Gx)
      (rawCutoffDy (cutoffHeight n) (actualPlanePullback N f) Gy)) 2 (carrierVolume N) := by
  rw [raw_cutoff_weighted_fiber_eq_Leibniz]
  exact rawLeibnizFiber_memLp N f hW n

/-- The error term is the actual scalar cutoff energy times the actual
raw physical mass. There is no spurious global boundedness premise on f. -/
theorem raw_cutoff_derivative_fiber_error_norm_sq (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (Gx Gy : Plane → ℂ) (Y : ℝ) (hY : 0 < Y) (z : UpperHalfPlane) :
    ‖rawWeightedFiber (rawCutoffDx Y (actualPlanePullback N f) Gx)
      (rawCutoffDy Y (actualPlanePullback N f) Gy) z-
        complexGlobalH Y z • rawWeightedFiber Gx Gy z‖^2 =
      cutoffEnergyH Y z*‖f (orbitProjection N z)‖^2 := by
  have he : rawWeightedFiber (rawCutoffDx Y (actualPlanePullback N f) Gx)
      (rawCutoffDy Y (actualPlanePullback N f) Gy) z-
        complexGlobalH Y z • rawWeightedFiber Gx Gy z = cutoffErrorFiber N f Y z := by
    rw [raw_cutoff_weighted_fiber_identity N f Gx Gy Y hY z]
    unfold cutoffErrorFiber
    abel
  rw [he]
  exact cutoffErrorFiber_norm_sq N f Y z

end
end ImbalancedChen.Part3.GammaRawCutoffDerivativeFiberIdentity20261026b
