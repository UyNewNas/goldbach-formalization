import ImbalancedChen.Part3SLRealGreenCurrentCovariance
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Actual Gamma0 side transport and reverse orientation for the Green
one-form. The paired edge is literally t |-> gamma*c(1-t). Its ordinary
derivative is computed by the true SL(2,R) derivative and the affine
reverse map. Actual Gamma0 invariance gives a local function identity,
so both real derivatives are transported without assuming current
invariance or endpoint cancellation. Native affine substitution then
proves that the two oriented integrals cancel. No Stokes premise occurs.
-/

noncomputable section
open Set Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.FrickeNormalizer

namespace ImbalancedChen.Part3.Gamma0PairedEdgeGreen20261026b

theorem realSL_action_int (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    realSL g • z = g • z := by
  apply UpperHalfPlane.ext
  simp [realSL, UpperHalfPlane.coe_specialLinearGroup_apply]

theorem greenOneForm_congr_of_eventuallyEq (F F' G G' : ℂ → ℂ) (z v : ℂ)
    (hF : F =ᶠ[𝓝 z] F') (hG : G =ᶠ[𝓝 z] G') :
    greenOneForm F G z v = greenOneForm F' G' z v := by
  unfold greenOneForm
  rw [hF.eq_of_nhds, hG.eq_of_nhds, hF.fderiv_eq, hG.fderiv_eq]

theorem greenOneForm_neg_tangent (F G : ℂ → ℂ) (z v : ℂ) :
    greenOneForm F G z (-v) = -greenOneForm F G z v := by
  unfold greenOneForm
  simp only [mul_neg, map_neg]
  ring

theorem gamma0_slMap_eventually (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N)
    (F : ℂ → ℂ)
    (hInv : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z) (z : UpperHalfPlane) :
    (fun w => F (slMap (realSL (γ : SL(2, ℤ))) w)) =ᶠ[𝓝 (z : ℂ)] F := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  have h := hInv γ (⟨w, hw⟩ : UpperHalfPlane)
  have hm : slMap (realSL (γ : SL(2, ℤ))) w =
      ((γ • (⟨w, hw⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) := by
    change slMap (realSL (γ : SL(2, ℤ))) ((⟨w, hw⟩ : UpperHalfPlane) : ℂ) = _
    rw [slMap_eq_action, realSL_action_int]
  rw [hm]
  exact h

/-- Current invariance is a conclusion from actual function invariance
and the produced Mobius chain rule. -/
theorem greenOneForm_gamma0_transport (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N)
    (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, DifferentiableAt ℝ G (z : ℂ))
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z)
    (hGI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      G ((δ • z : UpperHalfPlane) : ℂ) = G z)
    (z : UpperHalfPlane) (v : ℂ) :
    greenOneForm F G ((γ • z : UpperHalfPlane) : ℂ)
      (slFactor (realSL (γ : SL(2, ℤ))) z * v) = greenOneForm F G z v := by
  have hFm : DifferentiableAt ℝ F (slMap (realSL (γ : SL(2, ℤ))) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using hF (γ • z)
  have hGm : DifferentiableAt ℝ G (slMap (realSL (γ : SL(2, ℤ))) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using hG (γ • z)
  have h := greenOneForm_slMap_pullback (realSL (γ : SL(2, ℤ))) z F G hFm hGm v
  have hc := greenOneForm_congr_of_eventuallyEq _ F _ G (z : ℂ) v
    (gamma0_slMap_eventually N γ F hFI z) (gamma0_slMap_eventually N γ G hGI z)
  rw [hc] at h
  simpa only [slMap_eq_action, realSL_action_int] using h.symm

def pairedEdge (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N)
    (c : ℝ → UpperHalfPlane) (t : ℝ) : UpperHalfPlane := γ • c (1 - t)

/-- The sign and Mobius tangent factor of the paired path are computed,
not supplied as an orientation or derivative premise. -/
theorem pairedEdge_hasDerivAt (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N)
    (c : ℝ → UpperHalfPlane) (v : ℝ → ℂ)
    (hc : ∀ t, HasDerivAt (fun r : ℝ => (c r : ℂ)) (v t) t) (t : ℝ) :
    HasDerivAt (fun r : ℝ => (pairedEdge N γ c r : ℂ))
      (-(slFactor (realSL (γ : SL(2, ℤ))) (c (1 - t)) * v (1 - t))) t := by
  have hr := HasDerivAt.comp_const_sub (1 : ℝ) t (hc (1 - t))
  have h := (slMap_hasFDerivAt (realSL (γ : SL(2, ℤ))) (c (1 - t))).comp_hasDerivAt t hr
  have heq : (fun r : ℝ => slMap (realSL (γ : SL(2, ℤ))) (c (1 - r))) =
      (fun r : ℝ => (pairedEdge N γ c r : ℂ)) := by
    funext r
    simp only [pairedEdge, slMap_eq_action, realSL_action_int]
  rw [heq] at h
  convert h using 1 <;> simp <;> ring

def edgeGreenIntegral (F G : ℂ → ℂ) (c : ℝ → UpperHalfPlane) : ℂ :=
  ∫ t in (0 : ℝ)..1, greenOneForm F G (c t) (deriv (fun r : ℝ => (c r : ℂ)) t)

/-- Paired actual Gamma0 side integrals cancel by produced covariance,
the literal reverse path and native affine substitution. This identity
does not presume a fundamental polygon or a quotient Stokes formula. -/
theorem gamma0_paired_edge_integral_cancel (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N)
    (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, DifferentiableAt ℝ G (z : ℂ))
    (hFI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((δ • z : UpperHalfPlane) : ℂ) = F z)
    (hGI : ∀ δ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      G ((δ • z : UpperHalfPlane) : ℂ) = G z)
    (c : ℝ → UpperHalfPlane) (v : ℝ → ℂ)
    (hc : ∀ t, HasDerivAt (fun r : ℝ => (c r : ℂ)) (v t) t) :
    edgeGreenIntegral F G c + edgeGreenIntegral F G (pairedEdge N γ c) = 0 := by
  let H : ℝ → ℂ := fun t => greenOneForm F G (c t) (v t)
  have hbase : edgeGreenIntegral F G c = ∫ t in (0 : ℝ)..1, H t := by
    unfold edgeGreenIntegral
    simp_rw [(hc _).deriv]
    rfl
  have hp (t : ℝ) : greenOneForm F G (pairedEdge N γ c t)
      (deriv (fun r : ℝ => (pairedEdge N γ c r : ℂ)) t) = -H (1 - t) := by
    rw [(pairedEdge_hasDerivAt N γ c v hc t).deriv, greenOneForm_neg_tangent]
    change -greenOneForm F G ((γ • c (1 - t) : UpperHalfPlane) : ℂ)
      (slFactor (realSL (γ : SL(2, ℤ))) (c (1 - t)) * v (1 - t)) = -H (1 - t)
    rw [greenOneForm_gamma0_transport N γ F G hF hG hFI hGI]
    rfl
  have hreverse : (∫ t in (0 : ℝ)..1, H (1 - t)) = ∫ t in (0 : ℝ)..1, H t := by
    simpa using intervalIntegral.integral_comp_sub_left H (1 : ℝ) (a := 0) (b := 1)
  rw [hbase, edgeGreenIntegral]
  simp_rw [hp]
  rw [intervalIntegral.integral_neg, hreverse]
  exact add_neg_cancel _

end ImbalancedChen.Part3.Gamma0PairedEdgeGreen20261026b
