import ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient
import ImbalancedChen.ActualExtendedThirdFinitePhysicalKernel

namespace ImbalancedChen.P4AOrderedThirdFifthOwnersAndTail
noncomputable section
open Set Filter Topology HistoricalThirdCoarse VariableEnvelope P4AOriginalOrderedThirdTable
open P5OriginalCommonRefinedConstructor (OriginalData)
open P1OriginalVariableFifthContinuation (FifthRow eligible eligible_original_third_gate)
open scoped Classical ENNReal

theorem fifth_owner {d : OriginalData} {N : ℝ} (hN : 1<N) {pre : List ℕ}
    (hlen : pre.length=5) (hp : ∀ x∈pre,0<x) {r : FifthRow d.m}
    (hr : eligible d.e d.chi d.m d.omega d.J5 r (primeHistoryLogCoordinates N 5 pre)) :
    P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega N pre := by
  let A := rosserAncestor 3 pre
  let j := historicalPrefixProject (by decide : 3≤5) r.cell
  obtain ⟨hj,hlo⟩ := eligible_original_third_gate _ _ _ _ _ _ _ hr
  have ht : primeHistoryLogCoordinates N 3 A∈logPrimeMeshCell 0 (19/96) d.m j := by
    rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by decide : 3≤5) hlen]
    exact mem_logPrimeMeshCell_historicalPrefixProject _ hr.2.2
  have h3 : A.length=3 := by simp [A,hlen]
  have hl := (mem_logPrimeMeshCell.mp ht (2:Fin 3)).1
  have hcast : (qLogPrimeMeshLo 0 (19/96) d.m j 2:ℝ) = logPrimeMeshLo 0 (19/96) d.m j 2 := by
    simpa only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using congrFun (cast_qLogPrimeMeshLo 0 (19/96) d.m j) 2
  have hpow := Real.rpow_le_rpow_of_exponent_le hN.le (hlo.trans (hcast.le.trans hl))
  rw [rpow_primeHistoryLogCoordinates N hN h3 (fun x hx => hp x ((List.drop_sublist _ _).subset hx))] at hpow
  exact ⟨⟨h3,hpow⟩,j,hj,ht⟩

/-- Every genuinely eligible fifth parent in the exact old+new bank gives
the same complete decision at every later descendant for physical omega≤a. -/
theorem fifth_descendant {d : OriginalData} {N omega : ℝ} (hN : 1<N) (he : 0≤(d.e:ℝ))
    (hwa : omega≤d.omega) {pre : List ℕ} (hlen : (rosserAncestor 5 pre).length=5)
    (hp : ∀ x∈pre,0<x) {r : FifthRow d.m}
    (hr : eligible d.e d.chi d.m d.omega d.J5 r
      (primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre))) (delta : ℝ) (n : ℕ) (pos : Bool) :
    P4AOriginalOrderedThirdFullPolicy.policy delta n d omega N pos pre =
      P4AOriginalFull87DataPolicy.policy delta n d N pos pre := by
  apply P4AOriginalOrderedThirdFullPolicy.policy_on_old_owner he hN.le hwa
  have hs := fifth_owner hN hlen (fun x hx => hp x ((List.drop_sublist _ _).subset hx)) hr
  simpa only [P1ThirdFallbackSupport.frozenSupported,rosserAncestor_nested 3 5 (by decide)] using hs

/-- The true ordered lookup, with the runtime cut even inside a coarse
cell. This is the continuous profile used *after* a fixed-omega prime
limit. Its small-third majorant is uniform before that choice. -/
def levelAt (e omega : ℝ) (m : ℕ) (t : Point) :=
  if omega≤t 2 then atPoint e m t else initial e

theorem residual {e : ℝ} (he0 : 0≤e) (he : e≤1/384) (omega : ℝ) (m : ℕ)
    {t : Point} (ho : t∈actualExtendedThirdClosedOrder) (hx : t 0≤thirdPrefixRho) :
    thirdPrefixTailMargin≤levelAt e omega m t-t 0-t 1 ∧ levelAt e omega m t≤thirdPrefixTheta-2*e := by
  have hy := ho.2.2.trans hx
  have root : thirdPrefixTailMargin≤initial e-t 0-t 1 ∧ initial e≤thirdPrefixTheta-2*e := by
    dsimp [thirdPrefixTailMargin,thirdPrefixTheta,initial,extendedDistributionCap,thirdPrefixRho] at *
    exact ⟨by linarith,le_rfl⟩
  unfold levelAt atPoint
  split_ifs with hz h
  · let j := h.choose
    have hr := (Finset.mem_filter.mp h.choose_spec.1).2
    have hbase : (1/2:ℝ)≤infimum m j (actualExtendedThirdRobustBaseBranch 0) := by
      apply le_csInf (hr.1.image _)
      rintro _ ⟨s,hs,rfl⟩
      apply half_le_v_of_extended_range (hs.2.1.trans (hs.2.2.1.trans hs.2.2.2))
      linarith [(hs.1 0 (mem_univ _)).2,hr.2]
    have hg : 1/2≤envelope e m j := by
      unfold envelope
      split_ifs <;> first | exact hbase.trans (le_max_left _ _) | exact hbase
    exact ⟨thirdPrefixBufferedCap_residual_margin he hg hx hy,thirdPrefixBufferedCap_le_root _ _⟩
  all_goals exact root

def tail (e omega : ℝ) (m : ℕ) (h : ℝ) :=
  thirdPrefixTailMass (thirdPrefixTheta-2*e) (fun x y z => levelAt e omega m ![x,y,z]) thirdPrefixRho h

theorem tail_le {h : ℝ} (hh : 0<h) (hs : h≤thirdPrefixTailMargin/4)
    {e : ℝ} (he0 : 0≤e) (he : e≤1/384) (omega : ℝ) (m : ℕ) :
    tail e omega m h≤ENNReal.ofReal (18*h/(thirdPrefixTailMargin-h)^2*
      (Real.log (thirdPrefixRho/h)^2+2*Real.log (thirdPrefixRho/h)+2)) := by
  apply thirdPrefixTailMass_le_eighteen hh hs
  intro x y z hz _ hzy hyx hx
  have ho : ![x,y,z]∈actualExtendedThirdClosedOrder := ⟨hz.le,hzy,hyx⟩
  exact residual he0 he omega m ho hx

theorem uniform_tail {eta : ℝ} (ht : 0<eta) :
    ∃ h : ℝ, 0<h ∧ h≤thirdPrefixTailMargin/4 ∧ ∀ e : ℝ, 0≤e → e≤1/384 →
      ∀ m : ℕ, ∀ omega : ℝ, tail e omega m h≤ENNReal.ofReal eta := by
  have hu := ENNReal.tendsto_ofReal (tendsto_roughActivationTailEnvelope_zero
    (a:=thirdPrefixRho) (c:=thirdPrefixTailMargin)
    (by norm_num [thirdPrefixRho]) (by norm_num [thirdPrefixTailMargin]))
  rw [ENNReal.ofReal_zero] at hu
  have hs : Iio (thirdPrefixTailMargin/4) ∈ 𝓝[>] (0:ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num [thirdPrefixTailMargin]))
  have hp : Ioi (0:ℝ)∈𝓝[>] (0:ℝ) := self_mem_nhdsWithin
  obtain ⟨h,hh,hl,hb⟩ := (hp.and (hs.and (hu.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr ht))))).exists
  exact ⟨h,hh,hl.le,fun _ he0 he m omega => (tail_le hh hl.le he0 he omega m).trans hb.le⟩

end
end ImbalancedChen.P4AOrderedThirdFifthOwnersAndTail
