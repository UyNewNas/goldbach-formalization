import ImbalancedChen.P4AOriginalFiniteFallbackInheritedFirst

namespace ImbalancedChen.P4AFinitePPLowActualRoot
noncomputable section
open scoped Classical
open VariableEnvelope
open P4AUpperTaggedParityCompiler P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)
open P4AUpperTaggedFirstPrefixDisagreement (polarityAfter decisionAt_eq_prefix)
open P4AOrderedThirdActualRoughGeometry (every_decision)
open P4AOriginalFiniteFallbackPolicy (F high point)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalOrderedThirdFullPolicy (current)
open P4AOriginalOrderedThirdTable (retained capValue)
open HistoricalThirdCoarse.P1ActualTuple (history history_log)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AFull87OrdinaryAdmissionDeletion (reversed_prefix)

/-- The actual physical third cutoff, the native cell and the dispatched low
mode all hold on the same raw witness, including equal coarse labels. -/
theorem owner (B : Bank) {delta w : ℝ} {n N cap u : ℕ} {d : OriginalData}
    (he : 0≤(d.e:ℝ)) (hN : 1<N) (hw : 0≤w)
    (hu : u∈rawSupport (F B delta n d w N) N cap ((N:ℝ)^w) ((N:ℝ)^(19/96:ℝ)))
    (hr : 3≤u.primeFactorsList.length) :
    let p := canonicalPrefix 3 u
    let t := actualPrimeTupleLog N p
    ∃ j∈retained (d.e:ℝ) d.m, t∈logPrimeMeshCell 0 (19/96) d.m j ∧
      (current d w N u.primeFactorsList).scalar=capValue (d.e:ℝ) d.m j ∧
      ((current d w N u.primeFactorsList).lower ↔ t 0≤mu) := by
  let p := canonicalPrefix 3 u
  let f := F B delta n d w N
  obtain ⟨hU,hv⟩ := (raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hu
  have ht := mem_actualPrimeBoxTuples_iff.mp (canonical_prefix_tail_data hU hr).1
  have hbox : p∈actualPrimeBoxTuples N (fun _ => (0:ℝ)) (fun _ => (19/96:ℝ)) := by
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    exact ⟨(ht i).1,(ht i).2.1,(Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hw).trans
      (ht i).2.2.1,(ht i).2.2.2⟩
  have hlen : 0<u.primeFactorsList.reverse.length := by simpa using (show 0<u.primeFactorsList.length by omega)
  have h0 := every_decision (oddFirstExitPolicy f) _ [] true hv 0 hlen
  rw [decisionAt_eq_prefix _ _ _ _ _ hlen] at h0
  have htake : u.primeFactorsList.reverse.take 1=[p 0] := by
    have H := congrArg (List.take 1) (canonicalPrefix_ofFn hr)
    simpa [p,List.ofFn_succ,List.take_take] using H.symm
  have hf : HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m (N:ℝ) [p 0] := by
    have H : ordinaryRosserPrefixAdmissible false ((N:ℝ)^HistoricalThirdCoarse.initial (d.e:ℝ)) [p 0] ∧
        HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m (N:ℝ) [p 0] := by
      by_cases hh : high (N:ℝ) [p 0] <;>
        simpa [htake,f,F,P4AOriginalFiniteFallbackPolicy.policy,P4AOriginalFiniteFallbackPolicy.dispatch,hh,
          P4AOriginalFiniteFallbackPolicy.upper,P4AOriginalOrderedThirdFullPolicy.policy,
          P4AOriginalOrderedThirdFullPolicy.eight,P4AOriginalOrderedThirdFullPolicy.six,
          P4AOriginalOrderedThirdFullPolicy.five,P4AOriginalOrderedThirdFullPolicy.common,
          P4AOriginalOrderedThirdFullPolicy.base,firstExitDepthSplicePolicy,
          HistoricalThirdCoarse.initialPolicy,polarityAfter,oddFirstExitPolicy] using h0
    exact H.2
  obtain ⟨j,⟨htj,hj,hc,_⟩,_⟩ := P4AOriginalOrderedThirdActualCoefficient.actual_triple he hN p hbox
    (canonicalPrefix_strictAnti hU hr) (ht 2).2.2.1 hf
  have hh : rosserAncestor 3 u.primeFactorsList=history p := by
    rw [←reversed_prefix u 3 hr]; simp [history,List.ofFn_succ,p]
  have ha : HistoricalThirdCoarse.active w N (history p) :=
    (HistoricalThirdCoarse.active_triple w N (p 0) (p 1) (p 2)).mpr (ht 2).2.2.1
  refine ⟨j,hj,htj,by simpa only [current,hh] using hc,?_⟩
  simp only [current,hh,history_log,ha,true_and]
  exact ⟨And.left,fun hl => ⟨hl,j,hj,htj⟩⟩

end
end ImbalancedChen.P4AFinitePPLowActualRoot
