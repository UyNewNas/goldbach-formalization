import ImbalancedChen.P4AOriginalEarlyFifthOwner
import ImbalancedChen.P1VariableOwnCubeResidualUniformity
import ImbalancedChen.ActualExtendedThirdOrderedIntegral

namespace ImbalancedChen.P4AOriginalEarlyMovingMinus
noncomputable section
open Set Filter Topology MathlibNt.SieveTheory
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P1VariableOwnCubeResidualUniformity

abbrev Tuple := Fin 5→ℝ
private abbrev cube : Set Tuple := univ.pi (fun _ => Icc (1/400:ℝ) (19/96))
private abbrev C : Set (ℝ×Tuple) := Icc (0:ℝ) 1 ×ˢ cube

private theorem joint : ContinuousOn (fun x : ℝ×Tuple => primeTupleMinusProfile x.1 x.2) C := by
  let last : ℝ×Tuple→ℝ := fun x => x.2 (Fin.last 4)
  have hl : Continuous last := by fun_prop
  have hs : Continuous (fun x : ℝ×Tuple => ∑ i,x.2 i) := by fun_prop
  have hn : ∀ x∈C,last x ≠ 0 := fun x hx =>
    ((by norm_num : (0:ℝ)<1/400).trans_le (hx.2 (Fin.last 4) (mem_univ _)).1).ne'
  have harg : ContinuousOn (fun x : ℝ×Tuple => max 2 ((x.1-∑ i,x.2 i)/last x)) C :=
    continuousOn_const.sup ((continuous_fst.continuousOn.sub hs.continuousOn).div hl.continuousOn hn)
  exact (continuousOn_const.div hl.continuousOn hn).mul
    (continuousOn_suzukiContinuousLowerFactor.comp harg (fun x _ => le_max_left _ _))

private theorem remove_gate (l : ℝ) (t : Tuple) (ht : 0<t (Fin.last 4)) :
    (if primeTupleOwnCubeForm t<l then primeTupleMinusProfile l t else 0) = primeTupleMinusProfile l t := by
  split_ifs with h
  · rfl
  have H : (l-∑i,t i)/t (Fin.last 4) ≤ 2 :=
    (div_le_iff₀ ht).mpr (by dsimp [primeTupleOwnCubeForm] at h; linarith only [le_of_not_gt h])
  have hz : suzukiContinuousLowerFactor 2=0 := by
    have h2 := thirdTailLowerFactor_two
    unfold thirdTailLowerFactor at h2
    exact (div_eq_zero_iff.mp h2).resolve_right (by positivity)
  simp [primeTupleMinusProfile,max_eq_left H,hz]

/-- A single resolution and target threshold work for all physical fifth
caps in [0,1], on the common positive box that contains both fifth
banks. Own cube admission is retested at each cap, including equality. -/
theorem compact_fifth_shift (eps : ℝ) (heps : 0<eps) :
    ∃ n0 : ℕ,∀ n≥n0,∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ cap : ℕ,
      (N:ℝ)^(19/96:ℝ)≤(cap:ℝ) →
      ∀ p∈actualPrimeBoxTuples N (fun _ : Fin 5=>1/400) (fun _=>19/96),
      ∀ L∈Icc (0:ℝ) 1,∀ M∈Icc (0:ℝ) 1, |L-M|≤2*width n →
        |actualPrimeTupleOwnCubeMinus N cap L p-actualPrimeTupleOwnCubeMinus N cap M p|<eps := by
  have hε : 0<eps/3 := by positivity
  have hC : IsCompact C := isCompact_Icc.prod (isCompact_univ_pi (fun _=>isCompact_Icc))
  obtain ⟨δ,hδ,Hδ⟩ := Metric.uniformContinuousOn_iff.mp (hC.uniformContinuousOn_of_continuous joint) (eps/3) hε
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp
    (width_tendsto.eventually (gt_mem_nhds (show 0<δ/2 by positivity)))
  obtain ⟨N0,hN0,A⟩ := exists_actualPrimeTupleOwnCubeMinus_uniform_levels_threshold
    4 (1/400) (19/96) 0 1 (by norm_num) (eps/3) hε
  refine ⟨n0,?_⟩
  intro n hn
  refine ⟨N0,hN0,?_⟩
  intro N hN heven cap hc p hp L hL M hM hdiff
  let t := actualPrimeTupleLog N p
  have hT := ((mem_actualPrimeBoxTuples_log_iff (by omega : 1<N) _ _ p).mp hp).2
  have ht : t∈cube := fun i _ => ⟨(mem_logPrimeBox.mp hT i).1,(mem_logPrimeBox.mp hT i).2.le⟩
  have hP : 0<t (Fin.last 4) := (by norm_num : (0:ℝ)<1/400).trans_le (ht _ (mem_univ _)).1
  have hd : dist (L,t) (M,t)<δ := by
    rw [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_left (abs_nonneg _)]
    linarith only [hdiff,hn0 n hn]
  have hc' := Hδ (show (L,t)∈C from ⟨hL,ht⟩) (show (M,t)∈C from ⟨hM,ht⟩) hd
  rw [Real.dist_eq] at hc'
  have h1 := A N hN heven cap hc p hp L hL
  have h2 := A N hN heven cap hc p hp M hM
  rw [remove_gate L t hP] at h1
  rw [remove_gate M t hP] at h2
  exact (abs_sub_le (actualPrimeTupleOwnCubeMinus N cap L p) (primeTupleMinusProfile L t) _).trans_lt
    (by have h3 := abs_sub_le (primeTupleMinusProfile L t) (primeTupleMinusProfile M t)
          (actualPrimeTupleOwnCubeMinus N cap M p)
        rw [abs_sub_comm (primeTupleMinusProfile M t)] at h3
        linarith only [h1,h2,hc',h3])

end
end ImbalancedChen.P4AOriginalEarlyMovingMinus
