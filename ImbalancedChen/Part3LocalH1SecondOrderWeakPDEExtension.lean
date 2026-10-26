import ImbalancedChen.Part3LocalH1WeakPDEExtension

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine distributional weak-gradient input converts the local
TRANSPOSED second-order finite-test PDE into its first-order equation,
which then extends by constructed support-preserving H1 jet density.
The finite PDE is required ONLY for factors inside the same rectangle.
The actual Gamma defect's weak gradients and coordinate second-order PDE
are independent primitive inputs; neither is asserted here or encoded as
a target-density/join premise.
-/
namespace ImbalancedChen.Part3.LocalH1SecondOrderWeakPDEExtension20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology UpperHalfPlane
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open SupportedH1FiniteTensorDensity20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open LocalH1Tests20261026b LocalH1WeakPDEExtension20261026b

/-- Literal Euclidean transpose of (-Delta + potential)f=0. The mass
coefficient m retains the original height weight when m=y^-2 f. -/
def secondOrderEquation (f m F : Plane → ℂ) : Prop :=
  (∫ p, star (directional ex (directional ex F) p) * f p) +
    (∫ p, star (directional ey (directional ey F) p) * f p) =
      ∫ p, star (F p) * m p

/-- Distributional integration by parts in the correct sesquilinear
convention. A compact derivative of the test is a legitimate weak test. -/
theorem weak_second_pairing {f g F : Plane → ℂ} (v : Plane)
    (hweak : HasWeakDirectionalDerivative f g v)
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) :
    (∫ p, star (directional v (directional v F) p) * f p) =
      -(∫ p, star (directional v F p) * g p) := by
  have hstar : directional v (fun p => star (directional v F p)) =
      fun p => star (directional v (directional v F) p) := by
    funext p
    simp [directional, fderiv_star]
  have h := hweak (fun p => star (directional v F p))
    (directional_smooth v hF).star
    ((directional_compact v hFc).comp_left (g := star) (by simp))
  simpa only [hstar] using h

/-- The first-order finite equation is DERIVED from weak derivatives and
the explicit transposed PDE, rather than supplied as a Green/join premise. -/
theorem secondOrderEquation_firstOrder {f gx gy m F : Plane → ℂ}
    (hDx : HasWeakDirectionalDerivative f gx ex)
    (hDy : HasWeakDirectionalDerivative f gy ey)
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hPDE : secondOrderEquation f m F) :
    smoothFirstOrderResidual ![m,gx,gy] F = 0 := by
  have hxx := weak_second_pairing ex hDx hF hFc
  have hyy := weak_second_pairing ey hDy hF hFc
  have hx : (fun p => partialJet (firstIndex 1) F p) = directional ex F := by
    funext p
    rw [partialJet_eq_mixedJet hF]
    rfl
  have hy : (fun p => partialJet (firstIndex 2) F p) = directional ey F := by
    funext p
    rw [partialJet_eq_mixedJet hF]
    rfl
  have hzero : (fun p => partialJet (firstIndex 0) F p) = F := by rfl
  change (∫ p, star (partialJet (firstIndex 1) F p) * gx p) +
    (∫ p, star (partialJet (firstIndex 2) F p) * gy p) +
    (∫ p, star (partialJet (firstIndex 0) F p) * m p) = 0
  simp_rw [congrFun hx, congrFun hy, congrFun hzero]
  change (∫ p, star (directional ex (directional ex F) p) * f p) +
    (∫ p, star (directional ey (directional ey F) p) * f p) = _ at hPDE
  rw [hxx,hyy] at hPDE
  calc
    _ = (∫ p, star (directional ex F p) * gx p) +
        (∫ p, star (directional ey F p) * gy p) +
        (-(∫ p, star (directional ex F p) * gx p) +
          -(∫ p, star (directional ey F p) * gy p)) := by rw [hPDE]
    _ = 0 := by ring

/-- LOCAL finite-test extension. The hfinite premise is restricted to the
same allowed rectangle, which is essential for compact localizations. -/
theorem local_finite_weakPDE_extends_to_H1
    (N : ℕ) (c : Fin 3 → Plane → ℂ) (hc : ∀ i, MemLp (c i) 2 volume)
    (uL uR vL vR : ℝ) (hvL : 0 < vL) (hu : uL < uR) (hv : vL < vR)
    (hU : ∀ z : UpperHalfPlane, z.re ∈ Ioo uL uR → z.im ∈ Ioo vL vR →
      z ∈ reducedCarrier N)
    (hfinite : ∀ (ι : Type) (s : Finset ι) (T : ι → SmoothCompactTensor),
      (∀ t, tsupport (T t).horizontal ⊆ Ioo uL uR ∧
        tsupport (T t).vertical ⊆ Ioo vL vR) →
      finiteCompactTensorSupportK s (fun t => (T t).toCompactTensor) ⊆ reducedCarrier N →
      smoothFirstOrderResidual c
        (finiteChartFunction s (fun t => (T t).toCompactTensor)) = 0)
    (J : CompactH1Jet) (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (hs : tsupport J.value ⊆ openRect uL uR vL vR) :
    H1FirstOrderResidual c J = 0 := by
  have hdense := compactH1_mem_localFiniteTensorJets_closure J hx hy
    uL uR vL vR hvL hu hv hs
  have hclosed : IsClosed {v : Fin 3 → PlaneL2 |
      weakResidual (coefficientClass c hc) v = 0} :=
    isClosed_eq (weakResidual_continuous _) continuous_const
  have hsub : localFiniteTensorJets uL uR vL vR ⊆
      {v : Fin 3 → PlaneL2 | weakResidual (coefficientClass c hc) v = 0} := by
    rintro v ⟨ι,s,T,hTc,hTs,rfl⟩
    rw [smoothResidual_eq]
    exact hfinite ι s T hTs (finiteTensorSupportK_subset_reducedCarrier N s T
      uL uR vL vR hU hTs)
  have hz := (closure_minimal hsub hclosed) hdense
  exact (H1Residual_eq c hc J) ▸ hz

/-- Explicit transposed finite PDE plus actual weak derivatives is enough
for every genuine compact H1 test in the original allowed carrier chart.
No smoothness of f, finite-span membership of J, test density, or Green
identity is assumed. The three ordinary L2 coefficients are explicit. -/
theorem local_secondOrder_weakPDE_extends_to_H1
    (N : ℕ) (f gx gy m : Plane → ℂ)
    (hf : MemLp f 2 volume)
    (hm : MemLp m 2 volume) (hgx : MemLp gx 2 volume) (hgy : MemLp gy 2 volume)
    (hDx : HasWeakDirectionalDerivative f gx ex)
    (hDy : HasWeakDirectionalDerivative f gy ey)
    (uL uR vL vR : ℝ) (hvL : 0 < vL) (hu : uL < uR) (hv : vL < vR)
    (hU : ∀ z : UpperHalfPlane, z.re ∈ Ioo uL uR → z.im ∈ Ioo vL vR →
      z ∈ reducedCarrier N)
    (hsecond : ∀ (ι : Type) (s : Finset ι) (T : ι → SmoothCompactTensor),
      (∀ t, tsupport (T t).horizontal ⊆ Ioo uL uR ∧
        tsupport (T t).vertical ⊆ Ioo vL vR) →
      finiteCompactTensorSupportK s (fun t => (T t).toCompactTensor) ⊆ reducedCarrier N →
      secondOrderEquation f m (finiteChartFunction s (fun t => (T t).toCompactTensor)))
    (J : CompactH1Jet) (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (hs : tsupport J.value ⊆ openRect uL uR vL vR) :
    (∫ p, star (J.dx p) * gx p) + (∫ p, star (J.dy p) * gy p) +
      (∫ p, star (J.value p) * m p) = 0 := by
  have hc : ∀ i : Fin 3, MemLp (![m,gx,gy] i) 2 volume := by
    intro i
    fin_cases i
    · exact hm
    · exact hgx
    · exact hgy
  apply local_finite_weakPDE_extends_to_H1 N ![m,gx,gy] hc
    uL uR vL vR hvL hu hv hU ?_ J hx hy hs
  intro ι s T hTs hK
  have hTc : HasCompactSupport (finiteChartFunction s (fun t => (T t).toCompactTensor)) := by
    have hsupport := finiteTensor_tsupport_rect s T uL uR vL vR (fun t =>
      ⟨(hTs t).1.trans Ioo_subset_Icc_self, (hTs t).2.trans Ioo_subset_Icc_self⟩)
    exact HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
      (subset_closure.trans hsupport)
  exact secondOrderEquation_firstOrder hDx hDy (finiteSmoothChart_contDiff s T) hTc
    (hsecond ι s T hTs hK)

end
end ImbalancedChen.Part3.LocalH1SecondOrderWeakPDEExtension20261026b

