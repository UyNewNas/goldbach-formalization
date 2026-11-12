import ImbalancedChen.P4AOriginalEarlyMovingMinus
import ImbalancedChen.P1OriginalVariableFourthBoundedSourceLimit

namespace ImbalancedChen.P4AOriginalEarlyMovingPlus
noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P1FourthNearOneKernel (closedUpper continuousOn_closedUpper residual maxOneNormalized)
open P1FourthFullCellIntegral (extendedProfile)
open P1OriginalVariableFourthBoundedSourceLimit (exists_tuplePlus_bounded_levels_threshold)

private abbrev Tuple := Fin 4→ℝ
private abbrev cube : Set Tuple := univ.pi (fun _=>Icc (1/400:ℝ) (19/96))
private abbrev C : Set (ℝ×Tuple) := Icc (0:ℝ) 1 ×ˢ cube

private theorem joint : ContinuousOn (fun x : ℝ×Tuple => extendedProfile x.1 x.2) C := by
  let last : ℝ×Tuple→ℝ := fun x=>x.2 (Fin.last 3)
  have hl : Continuous last := by fun_prop
  have hs : Continuous (fun x : ℝ×Tuple => ∑ i,x.2 i) := by fun_prop
  have hn : ∀ x∈C,last x ≠ 0 := fun x hx =>
    ((by norm_num : (0:ℝ)<1/400).trans_le (hx.2 (Fin.last 3) (mem_univ _)).1).ne'
  have harg : ContinuousOn (fun x : ℝ×Tuple => max 1 ((x.1-∑ i,x.2 i)/last x)) C :=
    continuousOn_const.sup ((continuous_fst.continuousOn.sub hs.continuousOn).div hl.continuousOn hn)
  exact continuousOn_const.mul ((continuousOn_closedUpper.comp harg
    (fun _ _=>le_max_left _ _)).div hl.continuousOn hn)

/-- The true ordinary positive quotient is stable under the protected
fourth displacement, up to and including the legal endpoint one. -/
theorem compact_fourth_shift (eps : ℝ) (heps : 0<eps) :
    ∃ n0 : ℕ,∀ n≥n0,∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ cap : ℕ,
      (N:ℝ)^(19/96:ℝ)≤(cap:ℝ) →
      ∀ p∈actualPrimeBoxTuples N (fun _ : Fin 4=>1/400) (fun _=>19/96),
      let t := actualPrimeTupleLog N p
      ∀ L∈Icc (0:ℝ) 1,∀ M∈Icc (0:ℝ) 1,
      (∑ i,t i)+t (Fin.last 3)≤L → (∑ i,t i)+t (Fin.last 3)≤M → |L-M|≤2*width n →
        |fourthTuplePlusResidualP1 N cap L p-fourthTuplePlusResidualP1 N cap M p|<eps := by
  have hε : 0<eps/3 := by positivity
  have hC : IsCompact C := isCompact_Icc.prod (isCompact_univ_pi (fun _=>isCompact_Icc))
  obtain ⟨δ,hδ,Hδ⟩ := Metric.uniformContinuousOn_iff.mp (hC.uniformContinuousOn_of_continuous joint) (eps/3) hε
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp
    (width_tendsto.eventually (gt_mem_nhds (show 0<δ/2 by positivity)))
  obtain ⟨N0,hN0,A⟩ := exists_tuplePlus_bounded_levels_threshold
    (1/400) (19/96) 0 1 (by norm_num) (eps/3) hε
  refine ⟨n0,?_⟩
  intro n hn
  refine ⟨N0,hN0,?_⟩
  intro N hN heven cap hc p hp
  dsimp only
  intro L hL M hM hLegal hMegal hdiff
  let t := actualPrimeTupleLog N p
  have hT := ((mem_actualPrimeBoxTuples_log_iff (by omega : 1<N) _ _ p).mp hp).2
  have ht : t∈cube := fun i _ => ⟨(mem_logPrimeBox.mp hT i).1,(mem_logPrimeBox.mp hT i).2.le⟩
  have hd : dist (L,t) (M,t)<δ := by
    rw [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_left (abs_nonneg _)]
    linarith only [hdiff,hn0 n hn]
  have hc' := Hδ (show (L,t)∈C from ⟨hL,ht⟩) (show (M,t)∈C from ⟨hM,ht⟩) hd
  rw [Real.dist_eq] at hc'
  have h1 := A N hN heven cap hc p hp L hL hLegal
  have h2 := A N hN heven cap hc p hp M hM hMegal
  exact (abs_sub_le (fourthTuplePlusResidualP1 N cap L p) (extendedProfile L t) _).trans_lt
    (by have h3 := abs_sub_le (extendedProfile L t) (extendedProfile M t)
          (fourthTuplePlusResidualP1 N cap M p)
        rw [abs_sub_comm (extendedProfile M t)] at h3
        linarith only [h1,h2,hc',h3])

end
end ImbalancedChen.P4AOriginalEarlyMovingPlus
