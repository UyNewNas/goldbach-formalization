import ImbalancedChen.Part3Gamma0ActualFriedrichsOperator
import ImbalancedChen.Part3PositiveContractionResolventCalculus

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The shifted CFC resolvent is instantiated at the ACTUAL physical Gamma0
energy resolvent. Its outputs belong to the ACTUAL native Friedrichs domain,
and it is the two-sided inverse of aI+A_F there. The inverse is onto, unique,
self-adjoint and positive, with operator norm at most 1/a for a>0.

The actual completed Dirichlet-form graph supplies the genuine a-shifted
weak equation and its unique completed-energy solution. No resolvent,
weak graph, form-domain, positivity or uniqueness conclusion is assumed.
The generic CFC construction is reused rather than reproved.
-/

namespace ImbalancedChen.Part3.Gamma0ActualShiftedFriedrichsResolvent20261025a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open PositiveContractionResolventCalculus20261025a

theorem actualGammaResolvent_nonneg (N : ℕ) [NeZero N] :
    0 ≤ actualGammaResolvent N :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (actualGammaResolvent_isPositive N)

/-- Same physical quotient Hilbert space and same actual bounded R=JJ*. -/
def actualGammaShiftedResolvent (N : ℕ) [NeZero N] (a : ℝ) :
    QuotientL2 N →L[ℂ] QuotientL2 N := shiftedResolvent (actualGammaResolvent N) a

theorem actualGammaShiftedResolvent_graph_pair (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    (actualGammaShiftedResolvent N a f,
      f-(a:ℂ) • actualGammaShiftedResolvent N a f) ∈ (actualGammaFriedrichs N).graph := by
  apply (actualGammaFriedrichs_mem_graph_iff N).mpr
  exact shiftedResolvent_graph_pair (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_nonneg N)
    (actualGammaResolvent_opNorm_le_one N) ha f

/-- Every output lies in range R, the TRUE operator domain, not merely
the larger form domain range J. -/
theorem actualGammaShiftedResolvent_mem_domain (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    actualGammaShiftedResolvent N a f ∈ (actualGammaFriedrichs N).domain :=
  LinearPMap.mem_domain_of_mem_graph (actualGammaShiftedResolvent_graph_pair N ha f)

def actualShiftedResolventPoint (N : ℕ) [NeZero N] (a : ℝ) (ha : 0<a)
    (f : QuotientL2 N) : (actualGammaFriedrichs N).domain :=
  ⟨actualGammaShiftedResolvent N a f,actualGammaShiftedResolvent_mem_domain N ha f⟩

theorem actualGammaFriedrichs_apply_shiftedResolvent (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    actualGammaFriedrichs N (actualShiftedResolventPoint N a ha f)=
      f-(a:ℂ) • actualGammaShiftedResolvent N a f :=
  (actualGammaFriedrichs N).mem_graph_snd_inj
    ((actualGammaFriedrichs N).mem_graph (actualShiftedResolventPoint N a ha f))
    (actualGammaShiftedResolvent_graph_pair N ha f) rfl

/-- The inverse identity is proved on every member of the actual native
Friedrichs domain, rather than just on the original differential core. -/
theorem actualGammaShiftedResolvent_on_domain (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (u : (actualGammaFriedrichs N).domain) :
    actualGammaShiftedResolvent N a ((a:ℂ) • (u:QuotientL2 N)+actualGammaFriedrichs N u)=u := by
  apply shiftedResolvent_on_graph (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_nonneg N)
    (actualGammaResolvent_opNorm_le_one N) ha
  exact (actualGammaFriedrichs_mem_graph_iff N).mp ((actualGammaFriedrichs N).mem_graph u)

def actualShiftedFriedrichsMap (N : ℕ) [NeZero N] (a : ℝ) :
    (actualGammaFriedrichs N).domain →ₗ[ℂ] QuotientL2 N :=
  (a:ℂ) • (actualGammaFriedrichs N).domain.subtype+(actualGammaFriedrichs N).toFun

theorem actualShiftedFriedrichsMap_apply_inverse (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    actualShiftedFriedrichsMap N a (actualShiftedResolventPoint N a ha f)=f := by
  change (a:ℂ) • actualGammaShiftedResolvent N a f+
    actualGammaFriedrichs N (actualShiftedResolventPoint N a ha f)=f
  rw [actualGammaFriedrichs_apply_shiftedResolvent]
  abel

theorem actualShiftedFriedrichsMap_bijective (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) : Function.Bijective (actualShiftedFriedrichsMap N a) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    have hh := congrArg (actualGammaShiftedResolvent N a) huv
    change actualGammaShiftedResolvent N a ((a:ℂ) • (u:QuotientL2 N)+actualGammaFriedrichs N u)=
      actualGammaShiftedResolvent N a ((a:ℂ) • (v:QuotientL2 N)+actualGammaFriedrichs N v) at hh
    simpa only [actualGammaShiftedResolvent_on_domain N ha] using hh
  · intro f
    exact ⟨actualShiftedResolventPoint N a ha f,actualShiftedFriedrichsMap_apply_inverse N ha f⟩

theorem existsUnique_actual_shifted_operator_solution (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    ∃! u : (actualGammaFriedrichs N).domain,
      (a:ℂ) • (u:QuotientL2 N)+actualGammaFriedrichs N u=f := by
  refine ⟨actualShiftedResolventPoint N a ha f,actualShiftedFriedrichsMap_apply_inverse N ha f,?_⟩
  intro u hu
  apply (actualShiftedFriedrichsMap_bijective N ha).1
  exact hu.trans (actualShiftedFriedrichsMap_apply_inverse N ha f).symm

theorem actualGammaShiftedResolvent_selfAdjoint (N : ℕ) [NeZero N] (a : ℝ) :
    IsSelfAdjoint (actualGammaShiftedResolvent N a) :=
  cfc_predicate (resolventRatio a) (actualGammaResolvent N)

theorem actualGammaShiftedResolvent_nonneg (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) : 0 ≤ actualGammaShiftedResolvent N a := by
  apply cfc_nonneg
  intro t ht
  exact (resolventRatio_nonneg_le ha
    (spectrum_mem_unitInterval (actualGammaResolvent N) (actualGammaResolvent_nonneg N)
      (actualGammaResolvent_opNorm_le_one N) ht)).1

theorem actualGammaShiftedResolvent_isPositive (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) : (actualGammaShiftedResolvent N a).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mp (actualGammaShiftedResolvent_nonneg N ha)

theorem actualGammaShiftedResolvent_norm_le (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) : ‖actualGammaShiftedResolvent N a‖ ≤ 1/a :=
  shiftedResolvent_norm_le (actualGammaResolvent N) (actualGammaResolvent_nonneg N)
    (actualGammaResolvent_opNorm_le_one N) ha

theorem actualGammaShiftedResolvent_apply_norm_le (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    ‖actualGammaShiftedResolvent N a f‖ ≤ (1/a)*‖f‖ :=
  ((actualGammaShiftedResolvent N a).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (actualGammaShiftedResolvent_norm_le N ha) (norm_nonneg f))

/-- The genuine completed a-shifted Dirichlet variational problem. -/
def ActualShiftedDirichletSolution (N : ℕ) [NeZero N] (a : ℝ)
    (f : QuotientL2 N) (e : EnergyCompletion N) : Prop :=
  ∀ d : EnergyCompletion N,
    (a:ℂ)*inner ℂ (physicalProjection N d) (physicalProjection N e)+
      actualDirichletPair N d e=inner ℂ (physicalProjection N d) f

/-- The actual closed-form graph, not a supplied weak equation, gives
the equivalence between completed-energy solutions and operator solutions. -/
theorem actualShiftedDirichletSolution_iff_graph (N : ℕ) [NeZero N]
    (a : ℝ) (f : QuotientL2 N) (e : EnergyCompletion N) :
    ActualShiftedDirichletSolution N a f e ↔
      (physicalProjection N e,f-(a:ℂ) • physicalProjection N e) ∈
        (actualGammaFriedrichs N).graph := by
  rw [actualGammaFriedrichs_mem_graph_iff_formPair]
  constructor
  · intro he
    refine ⟨e,rfl,?_⟩
    intro d
    rw [inner_sub_right,inner_smul_right]
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans (he d)
  · rintro ⟨e',he',htest⟩
    have heq : e'=e := physicalProjection_injective N he'
    subst e'
    intro d
    have hh := htest d
    rw [inner_sub_right,inner_smul_right] at hh
    rw [hh]
    ring

theorem actualShiftedDirichletSolution_physical (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) (e : EnergyCompletion N)
    (he : ActualShiftedDirichletSolution N a f e) :
    physicalProjection N e=actualGammaShiftedResolvent N a f := by
  have hg := (actualShiftedDirichletSolution_iff_graph N a f e).mp he
  have hh := shiftedResolvent_on_graph (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_nonneg N)
    (actualGammaResolvent_opNorm_le_one N) ha
    ((actualGammaFriedrichs_mem_graph_iff N).mp hg)
  have hs : (a:ℂ) • physicalProjection N e+
      (f-(a:ℂ) • physicalProjection N e)=f := by abel
  rw [hs] at hh
  exact hh.symm

/-- Actual weak a-shift Dirichlet identity on ALL completed-energy tests,
with the physical solution equal to the actual shifted CFC resolvent. -/
theorem exists_actualShiftedDirichletSolution (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    ∃ e : EnergyCompletion N,
      physicalProjection N e=actualGammaShiftedResolvent N a f ∧
        ActualShiftedDirichletSolution N a f e := by
  obtain ⟨e,he,htest⟩ := (actualGammaFriedrichs_mem_graph_iff_formPair N).mp
    (actualGammaShiftedResolvent_graph_pair N ha f)
  refine ⟨e,he,(actualShiftedDirichletSolution_iff_graph N a f e).mpr ?_⟩
  rw [he]
  exact actualGammaShiftedResolvent_graph_pair N ha f

theorem existsUnique_actualShiftedDirichletSolution (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    ∃! e : EnergyCompletion N,ActualShiftedDirichletSolution N a f e := by
  obtain ⟨e,he,hsol⟩ := exists_actualShiftedDirichletSolution N ha f
  refine ⟨e,hsol,?_⟩
  intro d hd
  apply physicalProjection_injective N
  exact (actualShiftedDirichletSolution_physical N ha f d hd).trans he.symm

end
end ImbalancedChen.Part3.Gamma0ActualShiftedFriedrichsResolvent20261025a
