import ImbalancedChen.P4AOriginalFiniteFallbackSecondTail

namespace ImbalancedChen.P4AOriginalFiniteFallbackSecondGain
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open P4AOriginalFiniteFallbackOwnCubeRows (secondRow)
open P4AOriginalFiniteFallbackSecondEndpoint (row endpoint_sum)
open P4AOriginalFiniteFallbackSecondWalls (W)
open P4AOriginalFiniteFallbackSecondTail (low small_payment)
open P4AOriginalFiniteFallbackSecondCompactPayment (S compact_payment)
open P4AOriginalFiniteFallbackSignedSource (sum)
open P4ACatalogFiveHistoricalPairBoundaryPayment (normalizedHistoricalEndpoint exists_historical_endpoint_catalog5_lower)
open P4ACatalogFiveCoarseWeightedPayment (candidateTuples)
open P4AOriginalFull87HistoryCore (width)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalNewFifthUnion (data)

theorem gaps (m : ℕ) (d : OriginalData) (w h : ℝ) (N : ℕ) (hn : 1<N) :
    normalizedHistoricalEndpoint d N-sum d N (secondRow m d w N)=
      (∑ p∈low d h N,W p*(row N p-secondRow m d w N p))+
      (∑ p∈S d h N,W p*(row N p-secondRow m d w N p)) := by
  rw [endpoint_sum d N hn]
  unfold sum low S
  simp only [Finset.sum_filter,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hz : actualPrimeTupleLog N p 2<h
  · simp [hz,not_le_of_gt hz,mul_sub]
  · simp [hz,le_of_not_gt hz,mul_sub]

/-- The real finite second-fallback row, including all rejected or restored rank-three
cubes, pays the original second fallback saving on the common chronology.
The absolute signed tiny residual bound is uniform in w≤h, independently
of the fixed outer a. -/
theorem gain (eps : ℝ) (heps : 0<eps) :
    ∃ h : ℝ,0<h ∧ ∃ m0 : ℕ,∀ m≥m0,∃ e0 : ℝ,0<e0 ∧
    ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<e0 → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a w : ℝ,w≤h →
    ∀ᶠ N : ℕ in atTop,Even N → currentUpperEighteenGains 4-eps<sum (data e q a) N (secondRow m (data e q a) w N) := by
  have ht : 0<eps/3 := by positivity
  obtain ⟨h,hh,hs,Ntail⟩ := small_payment (eps/3) ht
  have hr : h<(19/96:ℝ) := hs.trans_lt (by norm_num [P4AOriginalFiniteFallbackSmallThird.small])
  obtain ⟨m0,hm⟩ := compact_payment h (eps/3) hh hr ht
  obtain ⟨δ,hδ,Nb,hNb,hpair⟩ := exists_historical_endpoint_catalog5_lower (eps/3) ht
  refine ⟨h,hh,m0,?_⟩
  intro m hm0
  obtain ⟨Nc,hNc,Hc⟩ := hm m hm0
  obtain ⟨Nt,hNt,Ht⟩ := Ntail h hh le_rfl
  refine ⟨min (1/2048) (δ/8),lt_min (by norm_num) (by positivity),?_⟩
  intro e he hei
  obtain ⟨mMin,hstep⟩ := eventually_atTop.mp ((tendsto_logPrimeMeshStep 0 (19/96)).eventually
    (gt_mem_nhds (by positivity : 0<δ/2)))
  obtain ⟨q0,hq0,_,hQ⟩ := P4AActualRefinableArchivePayment.exists_actual_refinement_threshold 1 (by norm_num) 0 mMin
  refine ⟨q0,hq0,?_⟩
  intro q hq a w hw
  let d := data e q a
  have hclear : 4*(d.e:ℝ)+P4ACatalogFiveHistoricalCoverage.meshStep d.m≤δ := by
    have H := hstep d.m (hQ q hq).1
    change 4*(e:ℝ)+logPrimeMeshStep 0 (19/96) d.m≤δ
    linarith [hei.trans_le (min_le_right _ _)]
  filter_upwards [eventually_ge_atTop (max Nb (max Nc Nt))] with N hN hEven
  have hc := Hc N (by omega) hEven d he.le w hw
  have hh' := Ht N (by omega) hEven m d (hei.trans_le (min_le_left _ _)).le w
  have hp := hpair d he.le hclear N (by omega) hEven
  have heq := gaps m d w h N (by omega)
  rw [P4AAll22OriginalKLedger20261024zSourceOnly.fifth_saving_slot_is_coarse_endpoint]
  linarith only [hc,hh',hp,heq]

end
end ImbalancedChen.P4AOriginalFiniteFallbackSecondGain
