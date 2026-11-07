import ImbalancedChen.Part3WholeSeedTestsRectangleLocalH1
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Uniqueness and compatibility of actual local weak gradients, using the
pinned fundamental lemma for compact smooth tests on OPEN sets. Equality
is almost everywhere on the overlap; boundary equality is not inferred.
No test-density or gradient-uniqueness hypothesis is assumed. -/

namespace ImbalancedChen.Part3.LocalL2WeakGradientUniqueness20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open ProductConvolutionSecondDerivatives20261026a
open PlanarLocalWeakGradientExtraction20261026b ActualPullbackLocalH1Transfer20261026b

def IsLocalWeakGradientOn (Ω : Set Plane) (F : Plane → ℂ) (gx gy : PlaneL2) : Prop :=
  ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
    ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional xDirection ψ p) * F p)) ∧
    ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional yDirection ψ p) * F p))

/-- The exact witnesses already present in the literal local-H1 definition. -/
theorem coordinateLocalH1_witnesses {Ω : Set Plane} {F : Plane → ℂ}
    (h : HasCoordinateLocalH1On Ω F) :
    ∃ gx gy : PlaneL2, IsLocalWeakGradientOn Ω F gx gy := h.2

theorem local_component_unique {Ω : Set Plane} (hΩ : IsOpen Ω)
    (F : Plane → ℂ) (v : Plane) (g h : PlaneL2)
    (hg : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ p, star (ψ p) * g p) = -(∫ p, star (directional v ψ p) * F p))
    (hh : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ p, star (ψ p) * h p) = -(∫ p, star (directional v ψ p) * F p)) :
    ∀ᵐ p ∂(volume : Measure Plane), p ∈ Ω → g p = h p := by
  have hl : LocallyIntegrableOn (fun p => g p - h p) Ω volume :=
    ((g.memLp.locallyIntegrable (by norm_num)).sub
      (h.memLp.locallyIntegrable (by norm_num))).locallyIntegrableOn Ω
  have hz : ∀ᵐ p ∂(volume : Measure Plane), p ∈ Ω → g p - h p = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hl
    intro φ hφ hφc hφs
    let ψ : Plane → ℂ := fun p => (φ p : ℂ)
    have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hφ
    have hψc : HasCompactSupport ψ := hφc.comp_left (g := Complex.ofReal) rfl
    have hψs : tsupport ψ ⊆ Ω :=
      (tsupport_comp_subset (g := Complex.ofReal) rfl φ).trans hφs
    have heq : (∫ p : Plane, φ p • g p) = ∫ p : Plane, φ p • h p := by
      have he := (hg ψ hψ hψc hψs).trans (hh ψ hψ hψc hψs).symm
      simpa only [ψ, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
        Complex.real_smul] using he
    have hig : Integrable (fun p => φ p • g p) :=
      (g.memLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        hφ.continuous hφc
    have hih : Integrable (fun p => φ p • h p) :=
      (h.memLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        hφ.continuous hφc
    simp only [smul_sub]
    rw [integral_sub hig hih, heq, sub_self]
  filter_upwards [hz] with p hp
  exact fun hpin => sub_eq_zero.mp (hp hpin)

/-- Independently extracted jets for the same function agree on every
open overlap, even if their global L2 extensions outside it differ. -/
theorem weak_gradients_agree_on_overlap {Ω Ξ : Set Plane}
    (hΩ : IsOpen Ω) (hΞ : IsOpen Ξ) (F : Plane → ℂ)
    (gx gy hx hy : PlaneL2)
    (hg : IsLocalWeakGradientOn Ω F gx gy)
    (hh : IsLocalWeakGradientOn Ξ F hx hy) :
    ∀ᵐ p ∂(volume : Measure Plane), p ∈ Ω ∩ Ξ → gx p = hx p ∧ gy p = hy p := by
  have htestg (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω ∩ Ξ) :=
    hg ψ hψ hc (hs.trans inter_subset_left)
  have htesth (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω ∩ Ξ) :=
    hh ψ hψ hc (hs.trans inter_subset_right)
  have hx := local_component_unique (hΩ.inter hΞ) F xDirection gx hx
    (fun ψ hψ hc hs => (htestg ψ hψ hc hs).1)
    (fun ψ hψ hc hs => (htesth ψ hψ hc hs).1)
  have hy := local_component_unique (hΩ.inter hΞ) F yDirection gy hy
    (fun ψ hψ hc hs => (htestg ψ hψ hc hs).2)
    (fun ψ hψ hc hs => (htesth ψ hψ hc hs).2)
  filter_upwards [hx, hy] with p hx' hy'
  exact fun hp => ⟨hx' hp, hy' hp⟩

end
end ImbalancedChen.Part3.LocalL2WeakGradientUniqueness20261026b
