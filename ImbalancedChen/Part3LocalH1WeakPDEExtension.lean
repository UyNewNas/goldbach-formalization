import ImbalancedChen.Part3LocalH1FiniteTensorDensity

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The literal first-order weak PDE with three actual planar L2 coefficients
extends from the original carrier-legal finite smooth tensor tests to
compact H1 jets. This supplies the TEST extension only. It does not assert
that an actual Gamma defect has a weak L2 gradient. The first-order finite
PDE is explicit input until that separate regularity/Green step is proved;
no density, approximation, or generic continuity/join input is assumed.
-/
namespace ImbalancedChen.Part3.LocalH1WeakPDEExtension20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology UpperHalfPlane
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open SupportedH1FiniteTensorDensity20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open LocalH1Tests20261026b

def coefficientClass (c : Fin 3 → Plane → ℂ)
    (hc : ∀ i, MemLp (c i) 2 volume) (i : Fin 3) : PlaneL2 := (hc i).toLp (c i)

/-- Derivative terms first, followed by the mass term; conjugation is on
THE TEST, exactly as in the original Gamma adjoint equation. -/
def weakResidual (a : Fin 3 → PlaneL2) (v : Fin 3 → PlaneL2) : ℂ :=
  inner ℂ (v 1) (a 1) + inner ℂ (v 2) (a 2) + inner ℂ (v 0) (a 0)

theorem weakResidual_continuous (a : Fin 3 → PlaneL2) : Continuous (weakResidual a) :=
  (((continuous_apply 1).inner continuous_const).add
    ((continuous_apply 2).inner continuous_const)).add
      ((continuous_apply 0).inner continuous_const)

theorem inner_toLp_eq_integral {f g : Plane → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ p, star (f p) * g p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with p hp hq
  simp only [RCLike.inner_apply', Complex.star_def, hp, hq]

/-- All products in the weak equation are genuinely integrable; the
Bochner integral never acquires meaning merely through its zero default. -/
theorem H1_test_products_integrable (J : CompactH1Jet)
    (c : Fin 3 → Plane → ℂ) (hc : ∀ i, MemLp (c i) 2 volume) :
    Integrable (fun p => star (J.dx p) * c 1 p) volume ∧
    Integrable (fun p => star (J.dy p) * c 2 p) volume ∧
    Integrable (fun p => star (J.value p) * c 0 p) volume :=
  ⟨MemLp.integrable_mul (p := 2) (q := 2) J.dx_memLp.star (hc 1),
    MemLp.integrable_mul (p := 2) (q := 2) J.dy_memLp.star (hc 2),
    MemLp.integrable_mul (p := 2) (q := 2) J.value_memLp.star (hc 0)⟩

def smoothFirstOrderResidual (c : Fin 3 → Plane → ℂ) (F : Plane → ℂ) : ℂ :=
  (∫ p, star (partialJet (firstIndex 1) F p) * c 1 p) +
  (∫ p, star (partialJet (firstIndex 2) F p) * c 2 p) +
  (∫ p, star (partialJet (firstIndex 0) F p) * c 0 p)

def H1FirstOrderResidual (c : Fin 3 → Plane → ℂ) (J : CompactH1Jet) : ℂ :=
  (∫ p, star (J.dx p) * c 1 p) + (∫ p, star (J.dy p) * c 2 p) +
    (∫ p, star (J.value p) * c 0 p)

theorem smoothResidual_eq (c : Fin 3 → Plane → ℂ)
    (hc : ∀ i, MemLp (c i) 2 volume) {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) :
    weakResidual (coefficientClass c hc) (smoothJetClass hF hFc) =
      smoothFirstOrderResidual c F := by
  unfold weakResidual coefficientClass smoothJetClass smoothFirstOrderResidual
  rw [inner_toLp_eq_integral, inner_toLp_eq_integral, inner_toLp_eq_integral]

theorem H1Residual_eq (c : Fin 3 → Plane → ℂ)
    (hc : ∀ i, MemLp (c i) 2 volume) (J : CompactH1Jet) :
    weakResidual (coefficientClass c hc) (h1JetClass J) = H1FirstOrderResidual c J := by
  change inner ℂ (J.dx_memLp.toLp J.dx) ((hc 1).toLp (c 1)) +
    inner ℂ (J.dy_memLp.toLp J.dy) ((hc 2).toLp (c 2)) +
    inner ℂ (J.value_memLp.toLp J.value) ((hc 0).toLp (c 0)) = _
  rw [inner_toLp_eq_integral, inner_toLp_eq_integral, inner_toLp_eq_integral]
  rfl

/-- The original finite test equation extends to a GENUINE H1 test.
Only the original finite test equation is assumed. In particular the
full carrier-legal support container is proved from each factor support,
and the H1 approximation is the constructed theorem, not an input. -/
theorem finite_carrier_weakPDE_extends_to_compactH1
    (N : ℕ) (c : Fin 3 → Plane → ℂ) (hc : ∀ i, MemLp (c i) 2 volume)
    (uL uR vL vR : ℝ) (hvL : 0 < vL) (hu : uL < uR) (hv : vL < vR)
    (hU : ∀ z : UpperHalfPlane, z.re ∈ Ioo uL uR → z.im ∈ Ioo vL vR →
      z ∈ reducedCarrier N)
    (hfinite : ∀ (ι : Type) (s : Finset ι) (T : ι → SmoothCompactTensor),
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
    exact hfinite ι s T (finiteTensorSupportK_subset_reducedCarrier N s T
      uL uR vL vR hU hTs)
  have hz := (closure_minimal hsub hclosed) hdense
  exact (H1Residual_eq c hc J) ▸ hz

/-- Expanded ordinary-coordinate weak PDE. The three coefficients may
in particular be the actual local weak gradient and the height-weighted
mass of a Gamma defect, once independently constructed. -/
theorem finite_carrier_weakPDE_H1_integral_identity
    (N : ℕ) (c : Fin 3 → Plane → ℂ) (hc : ∀ i, MemLp (c i) 2 volume)
    (uL uR vL vR : ℝ) (hvL : 0 < vL) (hu : uL < uR) (hv : vL < vR)
    (hU : ∀ z : UpperHalfPlane, z.re ∈ Ioo uL uR → z.im ∈ Ioo vL vR →
      z ∈ reducedCarrier N)
    (hfinite : ∀ (ι : Type) (s : Finset ι) (T : ι → SmoothCompactTensor),
      finiteCompactTensorSupportK s (fun t => (T t).toCompactTensor) ⊆ reducedCarrier N →
      smoothFirstOrderResidual c
        (finiteChartFunction s (fun t => (T t).toCompactTensor)) = 0)
    (J : CompactH1Jet) (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (hs : tsupport J.value ⊆ openRect uL uR vL vR) :
    (∫ p, star (J.dx p) * c 1 p) + (∫ p, star (J.dy p) * c 2 p) =
      -(∫ p, star (J.value p) * c 0 p) := by
  have h := finite_carrier_weakPDE_extends_to_compactH1 N c hc
    uL uR vL vR hvL hu hv hU hfinite J hx hy hs
  exact eq_neg_of_add_eq_zero_left h

end
end ImbalancedChen.Part3.LocalH1WeakPDEExtension20261026b
