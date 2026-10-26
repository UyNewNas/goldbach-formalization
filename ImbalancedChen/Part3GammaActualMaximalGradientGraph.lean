import ImbalancedChen.Part3GammaActualMaximalSobolevDomain
import ImbalancedChen.Part3GammaActualMaassGradientFactorization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL native closed gradient graph equals the maximal raw weak
derivative graph. The latter is defined using only ordinary local weak
derivatives of the actual quotient pullback and their represented carrier
vector. Neither a form domain nor an energy-completion object occurs in
that definition. Finite energy is derived from the supplied native L2
vector, then the genuine maximal-Sobolev converse pays form membership.
-/

namespace ImbalancedChen.Part3.GammaActualMaximalGradientGraph20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a Gamma0CompactCoreGradient20261025a
open Gamma0CarrierGradientHilbertMap20261026b
open ActualPullbackLocalH1Transfer20261026b WholeUpperChartWeakH1Patching20261026b
open GammaActualGlobalWeakGradientEnergy20261026b GammaRawWeightedFiberL220261026b
open GammaActualMaximalSobolevDomain20261026b GammaActualClosedGradientRealization20261026b
open GammaActualMaassGradientFactorization20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z

/-- A maximal weak graph in the ORIGINAL physical and carrier Hilbert
spaces. The output is not assumed to descend as scalar coordinate fields. -/
def MaximalRawGradientGraph (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (g : CarrierGradientL2 N) : Prop :=
  ∃ Gx Gy : Plane → ℂ,
    (∀ K : Set Plane, IsCompact K → K ⊆ upperChart →
      MemLp (actualPlanePullback N f) 2 (volume.restrict K) ∧
      MemLp Gx 2 (volume.restrict K) ∧ MemLp Gy 2 (volume.restrict K)) ∧
    (∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
      ((∫ p, star (ψ p)*Gx p) = -(∫ p,
        star (directional xDirection ψ p)*actualPlanePullback N f p)) ∧
      ((∫ p, star (ψ p)*Gy p) = -(∫ p,
        star (directional yDirection ψ p)*actualPlanePullback N f p))) ∧
    (g : UpperHalfPlane → GradientFiber) =ᵐ[carrierVolume N] rawWeightedFiber Gx Gy

theorem actual_closed_gradient_graph_iff_maximal_raw (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (g : CarrierGradientL2 N) :
    (f,g) ∈ (actualClosedGradient N).graph ↔ MaximalRawGradientGraph N f g := by
  constructor
  · intro hgraph
    obtain ⟨u,hu,hGu⟩ := LinearPMap.mem_graph_iff.mp hgraph
    obtain ⟨Gx,Gy,hb,hw,hi,he⟩ :=
      completed_has_global_raw_gradient_energy N (actualEnergyLift N u)
    have hid := completed_global_raw_gradient_identification N (actualEnergyLift N u)
      Gx Gy hb hw
    refine ⟨Gx,Gy,?_,?_,?_⟩
    · simpa only [actualEnergyLift_projection,hu] using hb
    · simpa only [actualEnergyLift_projection,hu] using hw
    · have hg : g = completedCarrierGradient N (actualEnergyLift N u) := hGu.symm
      rw [hg]
      filter_upwards [hid] with z hz
      ext i
      fin_cases i
      · simpa only [rawWeightedFiber,PiLp.smul_apply,PiLp.toLp_apply,Matrix.cons_val_zero,
          smul_eq_mul] using hz.1
      · simpa only [rawWeightedFiber,PiLp.smul_apply,PiLp.toLp_apply,Matrix.cons_val_one,
          smul_eq_mul] using hz.2
  · rintro ⟨Gx,Gy,hb,hw,hg⟩
    have hnorm : (fun z => ‖g z‖^2) =ᵐ[carrierVolume N] globalRawGradientEnergy Gx Gy := by
      filter_upwards [hg] with z hz
      rw [hz,rawWeightedFiber_norm_sq]
      rfl
    have hi : Integrable (globalRawGradientEnergy Gx Gy) (carrierVolume N) :=
      (g.memLp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).congr hnorm
    have hf : f ∈ actualEnergyFormDomain N :=
      finite_carrier_weakH1_mem_actual_form_domain N f ⟨Gx,Gy,hb,hw,hi⟩
    let u : actualEnergyFormDomain N := ⟨f,hf⟩
    have hid := completed_global_raw_gradient_identification N (actualEnergyLift N u)
      Gx Gy (by simpa only [actualEnergyLift_projection] using hb)
        (by simpa only [actualEnergyLift_projection] using hw)
    have hGu : actualClosedGradient N u = g := by
      apply Lp.ext
      filter_upwards [hid,hg] with z hz hgz
      rw [hgz]
      change completedCarrierGradient N (actualEnergyLift N u) z = rawWeightedFiber Gx Gy z
      ext i
      fin_cases i
      · simpa only [rawWeightedFiber,PiLp.smul_apply,PiLp.toLp_apply,Matrix.cons_val_zero,
          smul_eq_mul] using hz.1
      · simpa only [rawWeightedFiber,PiLp.smul_apply,PiLp.toLp_apply,Matrix.cons_val_one,
          smul_eq_mul] using hz.2
    exact LinearPMap.mem_graph_iff.mpr ⟨u,rfl,hGu⟩

/-- Closedness of the raw maximal weak relation is a theorem, inherited
only AFTER its genuine identification with the actual native graph. -/
theorem maximal_raw_gradient_graph_isClosed (N : ℕ) [NeZero N] :
    IsClosed {p : QuotientL2 N × CarrierGradientL2 N | MaximalRawGradientGraph N p.1 p.2} := by
  have heq : {p : QuotientL2 N × CarrierGradientL2 N | MaximalRawGradientGraph N p.1 p.2} =
      ((actualClosedGradient N).graph : Set (QuotientL2 N × CarrierGradientL2 N)) := by
    ext p
    exact (actual_closed_gradient_graph_iff_maximal_raw N p.1 p.2).symm
  rw [heq]
  exact actualClosedGradient_isClosed N

/-- Full native second-order graph as maximal weak gradient followed
by native adjoint divergence, retaining the required square-domain. -/
theorem actual_Maass_graph_iff_maximal_gradient_adjoint (N : ℕ) [NeZero N]
    (f w : QuotientL2 N) :
    (f,w) ∈ (actualClosedGammaMaass N).graph ↔
      ∃ g : CarrierGradientL2 N, MaximalRawGradientGraph N f g ∧
        (g,w) ∈ (actualClosedGradient N).adjoint.graph := by
  rw [actual_Maass_graph_iff_gradient_adjoint_graph]
  constructor
  · rintro ⟨u,hu,hadj⟩
    refine ⟨actualClosedGradient N u,?_,hadj⟩
    apply (actual_closed_gradient_graph_iff_maximal_raw N f _).mp
    exact LinearPMap.mem_graph_iff.mpr ⟨u,hu,rfl⟩
  · rintro ⟨g,hraw,hadj⟩
    obtain ⟨u,hu,hGu⟩ := LinearPMap.mem_graph_iff.mp
      ((actual_closed_gradient_graph_iff_maximal_raw N f g).mpr hraw)
    exact ⟨u,hu,hGu.symm ▸ hadj⟩

end
end ImbalancedChen.Part3.GammaActualMaximalGradientGraph20261026b
