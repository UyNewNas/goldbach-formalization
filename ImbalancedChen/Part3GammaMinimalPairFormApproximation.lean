import ImbalancedChen.Part3GammaNonzeroCoreGraphFormLimit
import ImbalancedChen.Part3GammaFiniteTensorGraphCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every actual minimal closed graph pair has a CONSTRUCTED sequence of
original smooth-core inputs converging in the actual completed form norm
and global carrier-gradient norm. In particular every compact smooth
periodized seed has such a sequence, with its actual Maass output.
The approximation or form-domain conclusion is not a caller premise.
-/

namespace ImbalancedChen.Part3.GammaMinimalPairFormApproximation20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CarrierGradientHilbertMap20261026b GammaNonzeroCoreGraphFormLimit20261026b
open GammaFiniteTensorGraphCore20261026a

/-- Closure in the actual input/output quotient L2 product supplies the
core sequence. Each graph pair is rendered as its ORIGINAL typed core
input and actual core differential, before forming the energy limit. -/
theorem exists_minimal_pair_form_approximation
    (N : ℕ) [NeZero N] (f g : QuotientL2 N)
    (hfg : (f,g) ∈ (actualClosedGammaMaass N).graph) :
    ∃ (u : ℕ → EnergyCore N) (e : EnergyCompletion N),
      Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 f) ∧
      Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 g) ∧
      Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e) ∧
      physicalProjection N e = f ∧
      (∀ d : EnergyCompletion N, actualDirichletPair N d e =
        inner ℂ (physicalProjection N d) g) ∧
      Tendsto (fun n => carrierCoreGradient N (u n)) atTop
        (𝓝 (completedCarrierGradient N e)) ∧
      actualDirichletPair N e e = inner ℂ f g := by
  have hclosure : (f,g) ∈ closure (coreGraph N : Set (QuotientL2 N × QuotientL2 N)) := by
    rw [actualClosedGammaMaass_graph_eq] at hfg
    exact hfg
  obtain ⟨p,hp,hpLim⟩ := mem_closure_iff_seq_limit.mp hclosure
  have hdomain : ∀ n : ℕ, (p n).1 ∈ smoothCore N :=
    fun n => (coreGraph_actual N (hp n)).choose
  let u : ℕ → EnergyCore N := fun n => ⟨(p n).1,hdomain n⟩
  have hinput (n : ℕ) : physicalCore N (u n) = (p n).1 := rfl
  have houtput (n : ℕ) : coreLaplacian N (u n) = (p n).2 :=
    ((coreGraph_iff_operator N (u n) (p n).2).mp (hp n)).symm
  have hf : Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 f) := by
    simpa only [hinput] using hpLim.fst
  have hg : Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 g) := by
    simpa only [houtput] using hpLim.snd
  obtain ⟨e,he,hproj,ht,henergy,_⟩ := exists_energy_limit_of_core_graph N u f g hf hg
  have hgradient : Tendsto (fun n => carrierCoreGradient N (u n)) atTop
      (𝓝 (completedCarrierGradient N e)) := by
    simpa only [completedCarrierGradient_core] using
      ((completedCarrierGradient N).continuous.tendsto e).comp he
  exact ⟨u,e,hf,hg,he,hproj,ht,hgradient,henergy⟩

/-- Actual arbitrary compact smooth seed endpoint. The actual
finite-tensor graph-core theorem supplies the needed minimal graph pair;
the just-constructed sequence then supplies form and global-gradient
convergence for its genuine periodization and genuine Maass output. -/
theorem exists_compact_smooth_seed_form_approximation
    (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hfs : ContDiffOn ℝ ∞ (extendUpper f) positiveChart)
    (F G : QuotientL2 N)
    (hF : (F : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N f)
    (hG : (G : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperMaass f)) :
    ∃ (u : ℕ → EnergyCore N) (e : EnergyCompletion N),
      Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e) ∧
      physicalProjection N e = F ∧
      (∀ d : EnergyCompletion N, actualDirichletPair N d e =
        inner ℂ (physicalProjection N d) G) ∧
      Tendsto (fun n => carrierCoreGradient N (u n)) atTop
        (𝓝 (completedCarrierGradient N e)) ∧
      actualDirichletPair N e e = inner ℂ F G := by
  have hgraph := compact_smooth_seed_ae_pair_mem_minimalGraph N f hfc hfs F G hF hG
  obtain ⟨u,e,hp,hL,he,hproj,ht,hgradient,henergy⟩ :=
    exists_minimal_pair_form_approximation N F G hgraph
  exact ⟨u,e,he,hproj,ht,hgradient,henergy⟩

end
end ImbalancedChen.Part3.GammaMinimalPairFormApproximation20261026b
