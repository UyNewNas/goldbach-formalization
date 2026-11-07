import ImbalancedChen.Part3GammaEnergyOrdinaryLocalH1Jet
import ImbalancedChen.Part3GammaActualMaximalGradientGraph

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Ordinary local H1 jet convergence for arbitrary actual FORM vectors,
including reconstruction from only physical and raw carrier-gradient
limits in the maximal weak Sobolev graph. No operator output or PDE is
assumed. The new local estimate is paid by actual compact overlap and
the existing native (J,G) inverse estimate, rather than by weak extraction.
-/

namespace ImbalancedChen.Part3.GammaRawSobolevStrongLocalJet20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CarrierGradientHilbertMap20261026b GammaActualClosedGradientRealization20261026b
open GammaActualMaximalGradientGraph20261026b GammaActualMaximalSobolevDomain20261026b
open RestrictedL2WeakDerivative20261026b GammaGraphLocalGradientLinear20261026b
open GammaEnergyOrdinaryLocalH1Jet20261026b ProductConvolutionSecondDerivatives20261026a

theorem energyLocalH1Jet_difference_le (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (e d : EnergyCompletion N) :
    ‖energyLocalH1Jet N r e-energyLocalH1Jet N r d‖≤localEnergyJetConstant N r*
      (‖physicalProjection N e-physicalProjection N d‖+
        ‖completedCarrierGradient N e-completedCarrierGradient N d‖) := by
  have hC : 0≤localEnergyJetConstant N r := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  calc
    _ = ‖energyLocalH1Jet N r (e-d)‖ := by rw [map_sub]
    _ ≤ localEnergyJetConstant N r*‖e-d‖ := energyLocalH1Jet_norm_le N r (e-d)
    _ ≤ localEnergyJetConstant N r*(‖physicalProjection N (e-d)‖+
        ‖completedCarrierGradient N (e-d)‖) :=
      mul_le_mul_of_nonneg_left (energy_norm_le_value_add_gradient N (e-d)) hC
    _ = _ := by rw [map_sub,map_sub]

theorem energy_tendsto_strong_ordinary_localH1 (N : ℕ) [NeZero N] (r : PositiveRectangle)
    {ι : Type*} {l : Filter ι} (e : ι → EnergyCompletion N) (v : EnergyCompletion N)
    (he : Tendsto e l (𝓝 v)) :
    Tendsto (fun i => energyLocalH1Jet N r (e i)) l (𝓝 (energyLocalH1Jet N r v)) :=
  ((energyLocalH1Jet N r).continuous.tendsto v).comp he

/-- Any local scalar weak derivative of this physical form vector is the
same native local L2 class as the constructed coordinate jet component. -/
theorem energyLocalPartial_eq_any_weak_witness (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (e : EnergyCompletion N) (Gx Gy : LocalL2 r.region)
    (hx : HasRestrictedDerivative r.region (energyLocalValue N r e) Gx xDirection)
    (hy : HasRestrictedDerivative r.region (energyLocalValue N r e) Gy yDirection) :
    energyLocalGradient N r e=(Gx,Gy) := by
  obtain ⟨hX,hY⟩ := energyLocalGradient_weak N r e
  exact Prod.ext (restricted_derivative_unique r.region_open hX hx)
    (restricted_derivative_unique r.region_open hY hy)

def maximalRawFormPoint (N : ℕ) [NeZero N] (f : QuotientL2 N) (g : CarrierGradientL2 N)
    (hraw : MaximalRawGradientGraph N f g) : actualEnergyFormDomain N :=
  ⟨f,by
    change f∈(actualClosedGradient N).domain
    exact LinearPMap.mem_domain_iff.mpr ⟨g,(actual_closed_gradient_graph_iff_maximal_raw N f g).mpr hraw⟩⟩

def maximalRawEnergyLift (N : ℕ) [NeZero N] (f : QuotientL2 N) (g : CarrierGradientL2 N)
    (hraw : MaximalRawGradientGraph N f g) : EnergyCompletion N :=
  actualEnergyLift N (maximalRawFormPoint N f g hraw)

theorem maximalRawEnergyLift_value (N : ℕ) [NeZero N] (f : QuotientL2 N) (g : CarrierGradientL2 N)
    (hraw : MaximalRawGradientGraph N f g) : physicalProjection N (maximalRawEnergyLift N f g hraw)=f :=
  actualEnergyLift_projection N (maximalRawFormPoint N f g hraw)

theorem maximalRawEnergyLift_gradient (N : ℕ) [NeZero N] (f : QuotientL2 N) (g : CarrierGradientL2 N)
    (hraw : MaximalRawGradientGraph N f g) : completedCarrierGradient N (maximalRawEnergyLift N f g hraw)=g :=
  LinearPMap.mem_graph_snd_inj (actualClosedGradient N)
    (LinearPMap.mem_graph _ (maximalRawFormPoint N f g hraw))
    ((actual_closed_gradient_graph_iff_maximal_raw N f g).mpr hraw) rfl

/-- Only maximal RAW weak graph data are supplied for the sequence, with
physical and original carrier-L2 limits. Existing actual energy is
reconstructed, then the ordinary local H1 jet converges STRONGLY. -/
theorem raw_maximal_value_gradient_limits_strong_localH1 (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (f : ℕ → QuotientL2 N) (g : ℕ → CarrierGradientL2 N)
    (hraw : ∀ n,MaximalRawGradientGraph N (f n) (g n))
    (f₀ : QuotientL2 N) (g₀ : CarrierGradientL2 N)
    (hf : Tendsto f atTop (𝓝 f₀)) (hg : Tendsto g atTop (𝓝 g₀)) :
    ∃ v : EnergyCompletion N, physicalProjection N v=f₀ ∧ completedCarrierGradient N v=g₀ ∧
      Tendsto (fun n => energyLocalH1Jet N r (maximalRawEnergyLift N (f n) (g n) (hraw n)))
        atTop (𝓝 (energyLocalH1Jet N r v)) ∧
      (HasRestrictedDerivative r.region (energyLocalValue N r v) (energyLocalGradient N r v).1 xDirection ∧
        HasRestrictedDerivative r.region (energyLocalValue N r v) (energyLocalGradient N r v).2 yDirection) := by
  let e n := maximalRawEnergyLift N (f n) (g n) (hraw n)
  have hv : Tendsto (fun n => physicalProjection N (e n)) atTop (𝓝 f₀) := by
    simpa only [e,maximalRawEnergyLift_value] using hf
  have hG : Tendsto (fun n => completedCarrierGradient N (e n)) atTop (𝓝 g₀) := by
    simpa only [e,maximalRawEnergyLift_gradient] using hg
  obtain ⟨v,hvf,hvg,hev⟩ := energy_reconstruction_of_value_gradient_limits N e f₀ g₀ hv hG
  exact ⟨v,hvf,hvg,energy_tendsto_strong_ordinary_localH1 N r e v hev,energyLocalGradient_weak N r v⟩

end
end ImbalancedChen.Part3.GammaRawSobolevStrongLocalJet20261026b
