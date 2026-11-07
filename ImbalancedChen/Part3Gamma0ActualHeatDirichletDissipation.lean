import ImbalancedChen.Part3Gamma0ActualHeatGenerator
import ImbalancedChen.Part3Gamma0PhysicalClosedDirichletForm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Actual Friedrichs-domain heat invariance, commutation, strong positive-time
differentiability, and dissipation of the ACTUAL completed Dirichlet form.
The graph equation and true heat/resolvent commutation prove invariance.
The true right generator at zero, semigroup law and positive-time operator
norm continuity prove BOTH one-sided slopes at every positive time.

The resulting norm-square derivative is minus twice the genuine completed
Dirichlet energy. Its continuous physical pairing gives the exact integral
balance on [0,T]. No geometric C-infinity regularity, minimal-domain
invariance, smoothing conclusion, derivative or energy law is assumed.
-/

namespace ImbalancedChen.Part3.Gamma0ActualHeatDirichletDissipation20261025a

noncomputable section
open MeasureTheory Set Filter Topology
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0ActualHeatGenerator20261025a
open GenericPositiveResolventHeatGenerator20261025a

theorem actualGammaHeat_resolvent_commute (N : ℕ) [NeZero N]
    (s : ℝ) (f : QuotientL2 N) :
    actualGammaHeat N s (actualGammaResolvent N f)=
      actualGammaResolvent N (actualGammaHeat N s f) :=
  heatOperator_resolvent_apply (actualGammaHeatData N) s f

/-- The true actual native graph is invariant under the actual heat. -/
theorem actualGammaHeat_preserves_graph (N : ℕ) [NeZero N] (s : ℝ)
    {u v : QuotientL2 N} (huv : (u,v)∈(actualGammaFriedrichs N).graph) :
    (actualGammaHeat N s u,actualGammaHeat N s v)∈(actualGammaFriedrichs N).graph := by
  apply (actualGammaFriedrichs_mem_graph_iff N).mpr
  have hR := (actualGammaFriedrichs_mem_graph_iff N).mp huv
  rw [← map_add,← actualGammaHeat_resolvent_commute,hR]

def actualHeatDomainPoint (N : ℕ) [NeZero N] (s : ℝ)
    (u : (actualGammaFriedrichs N).domain) : (actualGammaFriedrichs N).domain :=
  ⟨actualGammaHeat N s (u:QuotientL2 N),LinearPMap.mem_domain_of_mem_graph
    (actualGammaHeat_preserves_graph N s ((actualGammaFriedrichs N).mem_graph u))⟩

theorem actualGammaFriedrichs_heat_commute (N : ℕ) [NeZero N] (s : ℝ)
    (u : (actualGammaFriedrichs N).domain) :
    actualGammaFriedrichs N (actualHeatDomainPoint N s u)=
      actualGammaHeat N s (actualGammaFriedrichs N u) :=
  (actualGammaFriedrichs N).mem_graph_snd_inj
    ((actualGammaFriedrichs N).mem_graph (actualHeatDomainPoint N s u))
    (actualGammaHeat_preserves_graph N s ((actualGammaFriedrichs N).mem_graph u)) rfl

/-- BOTH one-sided slopes are proved. In particular this is a full strong
derivative at positive time, not only the pre-existing right generator at0. -/
theorem actualGammaHeat_hasDerivAt_on_domain (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun s : ℝ => actualGammaHeat N s (u:QuotientL2 N))
      (-actualGammaHeat N t (actualGammaFriedrichs N u)) t := by
  have hq := actualGammaHeat_difference_quotient_on_domain N u
  have hrightShift : Tendsto (fun s : ℝ => s-t) (𝓝[>] t) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [sub_self] using
        (tendsto_id.sub_const t : Tendsto (fun s : ℝ => s-t) (𝓝 t) (𝓝 (t-t))).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr hs
  have hleftShift : Tendsto (fun s : ℝ => t-s) (𝓝[<] t) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [sub_self] using
        (tendsto_const_nhds.sub tendsto_id : Tendsto (fun s : ℝ => t-s) (𝓝 t) (𝓝 (t-t))).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr hs
  have hright := ((actualGammaHeat N t).continuous.tendsto
    (-actualGammaFriedrichs N u)).comp (hq.comp hrightShift)
  have hH : Tendsto (actualGammaHeat N) (𝓝[<] t) (𝓝 (actualGammaHeat N t)) :=
    ((actualGammaHeat_continuousOn_positive N).continuousAt
      (isOpen_Ioi.mem_nhds ht)).tendsto.mono_left inf_le_left
  have heval : Continuous (fun p :
      (QuotientL2 N→L[ℂ]QuotientL2 N)×QuotientL2 N => p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous
  have hleft := (heval.tendsto
      (actualGammaHeat N t,-actualGammaFriedrichs N u)).comp
    (hH.prodMk_nhds (hq.comp hleftShift))
  simp only [map_neg] at hright hleft
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  constructor
  · apply hleft.congr'
    have hpos : ∀ᶠ s : ℝ in 𝓝[<] t,0<s :=
      (gt_mem_nhds ht).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin,hpos] with s hs hspos
    have hsem := actualGammaHeat_add N hspos.le (sub_pos.mpr hs).le
    have htime : s+(t-s)=t := by ring
    rw [htime] at hsem
    have happ : actualGammaHeat N s (actualGammaHeat N (t-s) (u:QuotientL2 N))=
        actualGammaHeat N t (u:QuotientL2 N) :=
      (congrArg (fun T : QuotientL2 N→L[ℂ]QuotientL2 N => T (u:QuotientL2 N)) hsem).symm
    have hc : ((s-t:ℝ):ℂ)⁻¹ = -((t-s:ℝ):ℂ)⁻¹ := by
      have hneg : s-t=-(t-s) := by ring
      rw [hneg,Complex.ofReal_neg,inv_neg]
    change actualGammaHeat N s
      (((t-s:ℝ):ℂ)⁻¹ • (actualGammaHeat N (t-s) (u:QuotientL2 N)-(u:QuotientL2 N)))=
        slope (fun r : ℝ => actualGammaHeat N r (u:QuotientL2 N)) t s
    rw [map_smul,map_sub,happ,slope_def_module,
      RCLike.real_smul_eq_coe_smul (K:=ℂ),Complex.ofReal_inv,hc,neg_smul,← smul_neg,neg_sub]
  · apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsem := actualGammaHeat_add N ht.le (sub_pos.mpr hs).le
    have htime : t+(s-t)=s := by ring
    rw [htime] at hsem
    have happ : actualGammaHeat N t (actualGammaHeat N (s-t) (u:QuotientL2 N))=
        actualGammaHeat N s (u:QuotientL2 N) :=
      (congrArg (fun T : QuotientL2 N→L[ℂ]QuotientL2 N => T (u:QuotientL2 N)) hsem).symm
    change actualGammaHeat N t
      (((s-t:ℝ):ℂ)⁻¹ • (actualGammaHeat N (s-t) (u:QuotientL2 N)-(u:QuotientL2 N)))=
        slope (fun r : ℝ => actualGammaHeat N r (u:QuotientL2 N)) t s
    rw [map_smul,map_sub,happ,slope_def_module,
      RCLike.real_smul_eq_coe_smul (K:=ℂ),Complex.ofReal_inv]

/-- Canonical completed-energy lift of a TRUE operator-domain vector,
using the actual physical closed-form domain and its proved inverse J. -/
def actualOperatorEnergyLift (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) : EnergyCompletion N :=
  actualEnergyLift N ⟨(u:QuotientL2 N),actualGammaFriedrichs_domain_le_formDomain N u.2⟩

theorem actualOperatorEnergyLift_projection (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    physicalProjection N (actualOperatorEnergyLift N u)=(u:QuotientL2 N) :=
  actualEnergyLift_projection N _

theorem actualOperatorEnergyLift_pair (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualDirichletPair N (actualOperatorEnergyLift N u) (actualOperatorEnergyLift N u)=
      inner ℂ (u:QuotientL2 N) (actualGammaFriedrichs N u) := by
  obtain ⟨e,he,htest⟩ := (actualGammaFriedrichs_mem_graph_iff_formPair N).mp
    ((actualGammaFriedrichs N).mem_graph u)
  have heq : actualOperatorEnergyLift N u=e := physicalProjection_injective N
    ((actualOperatorEnergyLift_projection N u).trans he.symm)
  rw [heq,htest,he]

def actualHeatDirichletEnergy (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (s : ℝ) : ℝ :=
  (actualDirichletPair N
    (actualOperatorEnergyLift N (actualHeatDomainPoint N s u))
    (actualOperatorEnergyLift N (actualHeatDomainPoint N s u))).re

theorem actualHeatDirichletEnergy_eq_pair (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (s : ℝ) :
    actualHeatDirichletEnergy N u s=
      (inner ℂ (actualGammaHeat N s (u:QuotientL2 N))
        (actualGammaHeat N s (actualGammaFriedrichs N u))).re := by
  rw [actualHeatDirichletEnergy,actualOperatorEnergyLift_pair,actualGammaFriedrichs_heat_commute]

theorem actualHeatDirichletEnergy_nonneg (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (s : ℝ) :
    0≤actualHeatDirichletEnergy N u s := actualDirichletPair_nonneg N _

/-- The true physical completed-form energy is a continuous trajectory,
proved through its actual operator pairing rather than an assumed lift norm. -/
theorem actualHeatDirichletEnergy_continuousOn (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    ContinuousOn (actualHeatDirichletEnergy N u) (Ici (0:ℝ)) := by
  have h := (Complex.continuous_re.comp_continuousOn
    ((actualGammaHeat_strong_continuousOn N (u:QuotientL2 N)).inner ℂ
      (actualGammaHeat_strong_continuousOn N (actualGammaFriedrichs N u))))
  exact h.congr (fun s _ => (actualHeatDirichletEnergy_eq_pair N u s).symm)

/-- Exact Dirichlet dissipation, with the ACTUAL completed form energy. -/
theorem actualGammaHeat_norm_sq_hasDerivAt (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun s : ℝ => ‖actualGammaHeat N s (u:QuotientL2 N)‖^2)
      (-2*actualHeatDirichletEnergy N u t) t := by
  have hd := (actualGammaHeat_hasDerivAt_on_domain N u ht).norm_sq
  simpa only [real_inner_eq_re_inner (𝕜:=ℂ),inner_neg_right,Complex.neg_re,
    actualHeatDirichletEnergy_eq_pair,mul_neg,neg_mul] using hd

/-- Integral balance from time zero, where only strong continuity is
needed; the full strong derivative is used on the open time interval. -/
theorem actualGammaHeat_energy_balance (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) {T : ℝ} (hT : 0≤T) :
    ‖actualGammaHeat N T (u:QuotientL2 N)‖^2+
      2*(∫ s : ℝ in 0..T,actualHeatDirichletEnergy N u s)=‖(u:QuotientL2 N)‖^2 := by
  have henergy : ContinuousOn (actualHeatDirichletEnergy N u) (Icc 0 T) :=
    (actualHeatDirichletEnergy_continuousOn N u).mono (fun _ h => h.1)
  have hint : IntervalIntegrable (actualHeatDirichletEnergy N u) volume 0 T :=
    henergy.intervalIntegrable_of_Icc hT
  have hcont : ContinuousOn (fun s : ℝ => ‖actualGammaHeat N s (u:QuotientL2 N)‖^2)
      (Icc 0 T) :=
    (((actualGammaHeat_strong_continuousOn N (u:QuotientL2 N)).norm).pow 2).mono
      (fun _ h => h.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hcont
    (fun t ht => actualGammaHeat_norm_sq_hasDerivAt N u ht.1) (hint.const_mul (-2))
  rw [intervalIntegral.integral_const_mul,actualGammaHeat_zero] at hFTC
  change (-2)*(∫ s : ℝ in 0..T,actualHeatDirichletEnergy N u s)=
    ‖actualGammaHeat N T (u:QuotientL2 N)‖^2-‖(u:QuotientL2 N)‖^2 at hFTC
  linarith

end
end ImbalancedChen.Part3.Gamma0ActualHeatDirichletDissipation20261025a
