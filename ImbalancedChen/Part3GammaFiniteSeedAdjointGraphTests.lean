import ImbalancedChen.Part3Gamma0WholeSeedAdjointWeakEquation

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal whole-H finite-seed test equations characterize the native
adjoint graph of the ACTUAL minimal Gamma operator. The converse unfolds
both quotient pairings, extends the zero pairing through the original
core span and its genuine graph closure, and invokes native adjoint graph
semantics. No adjoint membership or form-domain premise is supplied.
-/
namespace ImbalancedChen.Part3.GammaFiniteSeedAdjointGraphTests20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactLaplacianSeed20261025a Gamma0SmoothCompactTensorCore20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a Gamma0ActualAdjointInteriorWeakEquation20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a Gamma0QuotientCellPushforward20261025a
open GammaCompactSeedGraphTransport20261026a Gamma0CompactSeedL2PairingUnfolding20261026b
open ActualCompactSeedMaassJoin20261025a Gamma0WholeSeedAdjointWeakEquation20261026b

/-- Finite actual quotient input pairing is the raw whole-H pairing,
with no reduced-carrier support restriction. -/
theorem finite_seed_input_unfold (N : ℕ) [NeZero N] (s : SmoothSeed) (w : QuotientL2 N) :
    inner ℂ (seedVector N s) w =
      ∫ z : UpperHalfPlane, star (finiteCoreFunction Finset.univ (seedTensors s) z) * w (orbitProjection N z) := by
  let K := finiteCompactTensorSupportK Finset.univ (seedTensors s)
  have hK : IsCompact K := finiteCompactTensorSupportK_isCompact _ _
  have hs : Function.support (finiteCoreFunction Finset.univ (seedTensors s)) ⊆ K :=
    finiteCoreFunction_support_subset _ _
  rw [← compactInput_finiteTensor_eq N s.2 K hK hs]
  exact compact_seed_L2_inner N _ (native_C2_continuous _ (finiteTensor_nativeC2 s.2)) hK hs
    _ w (compactInput_ae N _ (finiteTensor_nativeC2 s.2) K hK hs)

theorem finite_seed_output_unfold (N : ℕ) [NeZero N] (s : SmoothSeed) (f : QuotientL2 N) :
    inner ℂ (seedOutput N s) f =
      ∫ z : UpperHalfPlane, star (finiteCoreLaplacian Finset.univ (seedTensors s) z) * f (orbitProjection N z) := by
  let K := finiteCompactTensorSupportK Finset.univ (seedTensors s)
  have hK : IsCompact K := finiteCompactTensorSupportK_isCompact _ _
  have hs : Function.support (finiteCoreFunction Finset.univ (seedTensors s)) ⊆ K :=
    finiteCoreFunction_support_subset _ _
  rw [← compactOutput_finiteTensor_eq N s.2 K hK hs]
  have h := compact_seed_L2_inner N
    (upperMaass (finiteCoreFunction Finset.univ (seedTensors s)))
    (native_C2_upperMaass_continuous _ (finiteTensor_nativeC2 s.2)) hK
    (upperMaass_support_subset_closed _ hK.isClosed hs) _ f
    (compactOutput_ae N _ (finiteTensor_nativeC2 s.2) K hK hs)
  simpa only [upperMaass_finiteCoreFunction] using h

/-- Forward raw finite-test equation for arbitrary actual adjoint input
and output, not only negative-one defects. -/
theorem actual_adjoint_finite_seed_tests (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph) (s : SmoothSeed) :
    (∫ z : UpperHalfPlane, star (finiteCoreLaplacian Finset.univ (seedTensors s) z) * f (orbitProjection N z)) =
      ∫ z : UpperHalfPlane, star (finiteCoreFunction Finset.univ (seedTensors s) z) * w (orbitProjection N z) := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (actualClosedGammaMaass_dense_domain N)] at hfw
  have h := (Submodule.mem_adjoint_iff _ _).mp hfw
    (seedVector N s) (seedOutput N s) (seedPair_mem_actualClosed_graph N s)
  have heq := sub_eq_zero.mp h
  rw [finite_seed_output_unfold,finite_seed_input_unfold] at heq
  exact heq

/-- Reverse whole-H finite testing. The original finite quotient graph
span and its closure are proved to annihilate the residual pairing. -/
theorem actual_adjoint_graph_of_finite_seed_tests (N : ℕ) [NeZero N]
    {f w : QuotientL2 N}
    (htest : ∀ s : SmoothSeed,
      (∫ z : UpperHalfPlane, star (finiteCoreLaplacian Finset.univ (seedTensors s) z) * f (orbitProjection N z)) =
        ∫ z : UpperHalfPlane, star (finiteCoreFunction Finset.univ (seedTensors s) z) * w (orbitProjection N z)) :
    (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph := by
  let R : QuotientL2 N × QuotientL2 N → ℂ := fun p => inner ℂ p.2 f - inner ℂ p.1 w
  have hseed (s : SmoothSeed) : R (seedPair N s) = 0 := by
    change inner ℂ (seedOutput N s) f - inner ℂ (seedVector N s) w = 0
    rw [finite_seed_output_unfold,finite_seed_input_unfold]
    exact sub_eq_zero.mpr (htest s)
  have hspan : (coreGraph N : Set (QuotientL2 N × QuotientL2 N)) ⊆ {p | R p = 0} := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
        obtain ⟨s,rfl⟩ := hp
        exact hseed s
    | zero => simp only [R,Prod.zero_fst,Prod.zero_snd,inner_zero_left,sub_self]
    | add p q hp hq ihp ihq =>
        change inner ℂ (p.2+q.2) f - inner ℂ (p.1+q.1) w = 0
        simp only [inner_add_left]
        change inner ℂ p.2 f - inner ℂ p.1 w = 0 at ihp
        change inner ℂ q.2 f - inner ℂ q.1 w = 0 at ihq
        linear_combination ihp + ihq
    | smul c p hp ih =>
        change inner ℂ (c • p.2) f - inner ℂ (c • p.1) w = 0
        rw [inner_smul_left,inner_smul_left]
        calc
          _ = star c * (inner ℂ p.2 f - inner ℂ p.1 w) := by ring
          _ = 0 := by change R p = 0 at ih; change star c * R p = 0; rw [ih,mul_zero]
  have hclosed : IsClosed {p : QuotientL2 N × QuotientL2 N | R p = 0} :=
    isClosed_eq ((continuous_snd.inner continuous_const).sub (continuous_fst.inner continuous_const)) continuous_const
  have hclosure : (closedGammaGraph N : Set (QuotientL2 N × QuotientL2 N)) ⊆ {p | R p = 0} :=
    closure_minimal hspan hclosed
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (actualClosedGammaMaass_dense_domain N)]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro u v huv
  have hc : (u,v) ∈ closedGammaGraph N := by
    rw [← actualClosedGammaMaass_graph_eq]
    exact huv
  exact hclosure hc

/-- Exact finite raw-test characterization of the actual native adjoint
with global output in the ORIGINAL quotient L2 space. -/
theorem actual_adjoint_graph_iff_finite_seed_tests (N : ℕ) [NeZero N] (f w : QuotientL2 N) :
    (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph ↔
      ∀ s : SmoothSeed,
        (∫ z : UpperHalfPlane, star (finiteCoreLaplacian Finset.univ (seedTensors s) z) * f (orbitProjection N z)) =
          ∫ z : UpperHalfPlane, star (finiteCoreFunction Finset.univ (seedTensors s) z) * w (orbitProjection N z) :=
  ⟨fun h s => actual_adjoint_finite_seed_tests N h s,actual_adjoint_graph_of_finite_seed_tests N⟩

end
end ImbalancedChen.Part3.GammaFiniteSeedAdjointGraphTests20261026b
