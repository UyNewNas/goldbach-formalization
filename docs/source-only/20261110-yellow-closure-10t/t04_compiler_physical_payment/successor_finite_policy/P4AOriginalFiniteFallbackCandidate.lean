import ImbalancedChen.P4AOriginalFiniteFallbackOccurrence

namespace ImbalancedChen.P4AOriginalFiniteFallbackCandidate
noncomputable section
open scoped Classical BigOperators
open Set HistoricalThirdCoarse VariableEnvelope
open HistoricalThirdCoarse.P1ActualTuple (history history_log parent_two_iff active_iff_log)
open P5OriginalCommonRefinedConstructor (OriginalData old3)
open P4ACatalogFiveCoarseWeightedPayment (candidateTuples carrier weight)
open P4AOriginalRankThreeRestorationSource (beforeThirdPolicy)
open P4AOriginalOrderedThirdTable (rawExponent atPoint retained capValue portion)
open P4AOriginalFiniteFallbackPolicy (point)
open P4AOriginalThirdFallbackAdmission (self)

theorem geometry (d : OriginalData) {N : ℕ} (hN : 1<N) {p : Fin 3 → ℕ} (hp : p∈candidateTuples d N) :
    StrictAnti p ∧ p∈actualPrimeBoxTuples N (fun _ => (0:ℝ)) (fun _ => (19/96:ℝ)) ∧
    (p 0:ℝ)^3<(N:ℝ)^initial (d.e:ℝ) ∧ firstStop (d.e:ℝ) d.m N [p 0] := by
  have hm := (mem_firstExitAdmittedTuples_iff_of_decreasing 3 (beforeThirdPolicy (old3 d (N:ℝ))) (carrier N)
    (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hp
  have hw (i : Fin 3) := mem_roughPrimeUniverse.mp (hm.2.1 i)
  have hn : (1:ℝ)≤N := by exact_mod_cast hN.le
  have hpos (i : Fin 3) := (hw i).2.1.pos
  have hpar : FirstExitValidSelection (HistoricalThirdCoarse.policy (d.e:ℝ) d.chi d.m d.omega N)
      [] true (List.ofFn p).dropLast := by
    simpa [List.ofFn_succ,FirstExitValidSelection,beforeThirdPolicy,firstExitDepthSplicePolicy,old3] using hm.2.2
  refine ⟨hm.1,mem_actualPrimeBoxTuples_iff.mpr (fun i => ⟨(hw i).2.1,(hw i).2.2.1,?_,(hw i).2.2.2.2⟩),
    (parent_two_iff _ _ _ _ _ p (hpos 0)).mp hpar⟩
  rw [Real.rpow_zero]
  exact_mod_cast hpos i

theorem owner {d : OriginalData} {N : ℕ} (hN : 1<N) (he : 0≤(d.e:ℝ))
    {w : ℝ} {p : Fin 3 → ℕ} (hp : p∈candidateTuples d N) (hw : w≤actualPrimeTupleLog N p 2) :
    ∃ j∈retained (d.e:ℝ) d.m, actualPrimeTupleLog N p∈portion d.m j ∧
      rawExponent (d.e:ℝ) d.m w N (history p)=capValue (d.e:ℝ) d.m j := by
  obtain ⟨hanti,hbox,_,hstop⟩ := geometry d hN hp
  have hpos (i : Fin 3) := (mem_actualPrimeBoxTuples_iff.mp hbox i).1.pos
  have hn : (1:ℝ)≤N := by exact_mod_cast hN.le
  have hpow : (N:ℝ)^w≤p 2 := (Real.rpow_le_rpow_of_exponent_le hn hw).trans
    (actualPrimeTupleLog_rpow hN p hpos 2).le
  obtain ⟨j,hj,_⟩ := P4AOriginalOrderedThirdActualCoefficient.actual_triple he hN p hbox hanti hpow hstop
  have hanti' := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hanti
  have hbox' := mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hbox).2
  exact ⟨j,hj.2.1,P4AOriginalOrderedThirdTable.owned_portion hj.1
    ⟨(hbox' 2).1,(hanti' (by decide : (1:Fin 3)<2)).le,(hanti' (by decide : (0:Fin 3)<1)).le⟩,hj.2.2.1⟩

theorem first_cube {d : OriginalData} {N : ℕ} (hN : 1<N) (he : 0<(d.e:ℝ))
    (hs : (d.e:ℝ)≤1/384) (hm : logPrimeMeshStep 0 (19/96) d.m≤(d.e:ℝ)/2)
    (w : ℝ) {p : Fin 3 → ℕ} (hp : p∈candidateTuples d N) :
    (p 0:ℝ)^3<(N:ℝ)^rawExponent (d.e:ℝ) d.m w N (history p) := by
  obtain ⟨_,hbox,hroot,_⟩ := geometry d hN hp
  have hpos (i : Fin 3) := (mem_actualPrimeBoxTuples_iff.mp hbox i).1.pos
  by_cases hw : w≤actualPrimeTupleLog N p 2
  · obtain ⟨j,hj,ht,hval⟩ := owner hN he.le hp hw
    rw [hval]
    exact first_cube_lt_level_of_exponent (p 0) (by exact_mod_cast hN : (1:ℝ)<N)
      (actualPrimeTupleLog_rpow hN p hpos 0).symm.le
      (P4AOriginalOrderedThirdTable.first_cube he hs hm ht (Finset.mem_filter.mp hj).2.2)
  · rw [rawExponent,if_neg (fun ha => hw ((active_iff_log hN w p hpos).mp ha))]
    exact hroot

theorem high_upper {d : OriginalData} {N : ℕ} (hN : 1<N) (he : 0≤(d.e:ℝ))
    {w : ℝ} {p : Fin 3 → ℕ} (hp : p∈candidateTuples d N) (hw : w≤actualPrimeTupleLog N p 2)
    (hx : mu<actualPrimeTupleLog N p 0) :
    rawExponent (d.e:ℝ) d.m w N (history p)≤v (actualPrimeTupleLog N p 0) := by
  obtain ⟨j,hj,ht,hval⟩ := owner hN he hp hw
  have hn : ¬logPrimeMeshHi 0 (19/96) d.m j 0≤mu-4*(d.e:ℝ) := by
    linarith [(ht.1 0 (mem_univ _)).2]
  rw [hval]
  have hh := P4AOriginalOrderedThirdTable.inf_le (continuous_actualExtendedThirdRobustBaseBranch 0) ht
  change P4AOriginalOrderedThirdTable.infimum d.m j (actualExtendedThirdRobustBaseBranch 0)≤v _ at hh
  exact (min_le_right _ _).trans (by
    rw [P4AOriginalOrderedThirdTable.envelope,if_neg hn]; linarith)

end
end ImbalancedChen.P4AOriginalFiniteFallbackCandidate
