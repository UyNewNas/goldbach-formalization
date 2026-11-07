import ImbalancedChen.Part3GammaCompactSeedEventualCutoffExact

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original finite smooth quotient core has an eventual EXACT cutoff
test, including its actual quotient-L2 differential output. The finite
family representation fixes one compact seed and hence one explicit
threshold before the point, orbit and scale. The legal multiplier graph
pair then equals the original core pair by actual closed-graph uniqueness.
This is equality of L2 vectors, not just convergence or raw value equality.
-/

namespace ImbalancedChen.Part3.GammaOriginalCoreCutoffEventualExact20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0SmoothCompactTensorCore20261025a
open Gamma0CompactTensorQuotientL2Core20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0SmoothCoreFinitePoincareRepresentation20261025a
open Gamma0ActualMaassClosedOperator20261025a
open ActualModularCutoffMaassBudget20261025a
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaCompactSeedCutoffPlateau20261026a GammaCompactSeedEventualCutoffExact20261026b

/-- Literal descended native Leibniz output from the existing legal
cutoff-square test. This retains all gradient and Maass terms. -/
def cutoffSquareDifferentialQuotient
    (N : ℕ) [NeZero N] (u : smoothCore N) (Y : ℝ) (hY : 0 < Y) :
    Gamma0OrbitSpace N → ℂ :=
  quotientMultiplier N
    (multiplierDifferential (complexGlobalH Y * complexGlobalH Y) (coreRepresentative N u))
    (multiplierDifferential_invariant N _ _ (actualCutoff_square_invariant N Y)
      (coreRepresentative_gamma0_invariant N u)
      ((actualCutoff_square_cinfty Y hY).of_le (by simp))
      ((coreRepresentative_cinfty N u).of_le (by simp)))

/-- Every original typed core vector has a common finite-family threshold.
Both physical input and native differential are eventually the original
functions; the quotient multiplier fixes the actual L2 input a.e. -/
theorem exists_original_core_eventual_fixed
    (N : ℕ) [NeZero N] (u : smoothCore N) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ Y : ℝ, plateauThreshold a b ≤ Y →
        (complexGlobalH Y * complexGlobalH Y) * coreRepresentative N u = coreRepresentative N u ∧
        multiplierDifferential (complexGlobalH Y * complexGlobalH Y) (coreRepresentative N u) =
          upperMaass (coreRepresentative N u) ∧
        (quotientMultiplier N (complexGlobalH Y * complexGlobalH Y)
            (actualCutoff_square_invariant N Y) * (u : Lp ℂ 2 (carrierPushforward N)))
          =ᵐ[carrierPushforward N] (u : Lp ℂ 2 (carrierPushforward N)) := by
  obtain ⟨n,T,hT⟩ := exists_finite_poincare_representation N u
  have hu : u = seedCoreElement N ⟨n,T⟩ := Subtype.ext hT
  have hrep : coreRepresentative N u = smoothFinitePoincare N Finset.univ T := by
    rw [hu,coreRepresentative_seed]
  have hua : ((u : Lp ℂ 2 (carrierPushforward N)) : Gamma0OrbitSpace N → ℂ)
      =ᵐ[carrierPushforward N]
        quotientTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor) := by
    rw [hT]
    exact (quotientTensorPoincare_memLp_two N Finset.univ
      (fun i => (T i).toCompactTensor)).coeFn_toLp
  obtain ⟨a,b,ha,hab,hexact⟩ := exists_finite_smooth_poincare_eventual_exact Finset.univ T
  refine ⟨a,b,ha,hab,?_⟩
  intro Y hY
  have he := hexact N Y hY
  refine ⟨by simpa only [hrep] using he.1,
    by simpa only [hrep] using he.2.2.1,?_⟩
  filter_upwards [hua] with q huq
  change quotientMultiplier N (complexGlobalH Y * complexGlobalH Y)
    (actualCutoff_square_invariant N Y) q * u q = u q
  rw [huq]
  exact congrFun he.2.2.2 q

/-- Exact original input AND original differential output in the same
actual quotient L2 space, with no cutoff-domain premise. The threshold is
the explicit plateau formula, fixed before Y and all quotient points. -/
theorem exists_original_core_eventual_exact_pair
    (N : ℕ) [NeZero N] (u : smoothCore N) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ Y : ℝ, ∀ hY : plateauThreshold a b ≤ Y,
        (((u : Lp ℂ 2 (carrierPushforward N)) : Gamma0OrbitSpace N → ℂ)
          =ᵐ[carrierPushforward N]
            quotientMultiplier N (complexGlobalH Y * complexGlobalH Y)
              (actualCutoff_square_invariant N Y) * (u : Lp ℂ 2 (carrierPushforward N))) ∧
        (((actualCoreLaplacian N u : Lp ℂ 2 (carrierPushforward N)) : Gamma0OrbitSpace N → ℂ)
          =ᵐ[carrierPushforward N]
            cutoffSquareDifferentialQuotient N u Y ((plateauThreshold_pos a b).trans_le hY)) ∧
        ((u : Lp ℂ 2 (carrierPushforward N)),actualCoreLaplacian N u)
          ∈ (actualClosedGammaMaass N).graph := by
  obtain ⟨a,b,ha,hab,hfixed⟩ := exists_original_core_eventual_fixed N u
  refine ⟨a,b,ha,hab,?_⟩
  intro Y hY
  have hYpos : 0 < Y := (plateauThreshold_pos a b).trans_le hY
  have hfix := (hfixed Y hY).2.2
  obtain ⟨U,V,hU,hV,hgraph⟩ := exists_legal_actualCutoff_square_core_test N u Y hYpos
  have hUeq : U = (u : Lp ℂ 2 (carrierPushforward N)) := Lp.ext (hU.trans hfix)
  have hVclosed : ((u : Lp ℂ 2 (carrierPushforward N)),V) ∈ closedGammaGraph N := by
    rw [← actualClosedGammaMaass_graph_eq]
    simpa only [hUeq] using hgraph
  have hbase : ((u : Lp ℂ 2 (carrierPushforward N)),actualCoreLaplacian N u)
      ∈ closedGammaGraph N :=
    (coreGraph N).le_topologicalClosure (graphOutput_mem N u)
  have hVeq : V = actualCoreLaplacian N u := closedGammaGraph_right_unique N hVclosed hbase
  refine ⟨hfix.symm,?_,?_⟩
  · simpa only [hVeq,cutoffSquareDifferentialQuotient] using hV
  · simpa only [hUeq,hVeq] using hgraph

/-- Any legal actual cutoff pair with the original raw cutoff input has
the exact original output above one uniform threshold. This also covers
any choices of the L2 representatives made by a downstream consumer. -/
theorem exists_original_core_eventual_pair_uniqueness
    (N : ℕ) [NeZero N] (u : smoothCore N) :
    ∃ Y0 : ℝ, 0 < Y0 ∧ ∀ Y : ℝ, Y0 ≤ Y →
      ∀ U V : Lp ℂ 2 (carrierPushforward N),
        ((U : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
          quotientMultiplier N (complexGlobalH Y * complexGlobalH Y)
            (actualCutoff_square_invariant N Y) * (u : Lp ℂ 2 (carrierPushforward N))) →
        (U,V) ∈ (actualClosedGammaMaass N).graph →
        U = (u : Lp ℂ 2 (carrierPushforward N)) ∧ V = actualCoreLaplacian N u := by
  obtain ⟨a,b,ha,hab,hfixed⟩ := exists_original_core_eventual_fixed N u
  refine ⟨plateauThreshold a b,plateauThreshold_pos a b,?_⟩
  intro Y hY U V hU hgraph
  have hUeq : U = (u : Lp ℂ 2 (carrierPushforward N)) :=
    Lp.ext (hU.trans (hfixed Y hY).2.2)
  refine ⟨hUeq,?_⟩
  have hVclosed : ((u : Lp ℂ 2 (carrierPushforward N)),V) ∈ closedGammaGraph N := by
    rw [← actualClosedGammaMaass_graph_eq]
    simpa only [hUeq] using hgraph
  exact closedGammaGraph_right_unique N hVclosed
    ((coreGraph N).le_topologicalClosure (graphOutput_mem N u))

end
end ImbalancedChen.Part3.GammaOriginalCoreCutoffEventualExact20261026b
