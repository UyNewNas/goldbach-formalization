import ImbalancedChen.P4AOriginalFiniteFallbackSelectedMask
import ImbalancedChen.P4AOriginalFiniteFallbackAlignedOwners

namespace ImbalancedChen.P4AOriginalFiniteFallbackInheritedFirst
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackBank (read)
open P4AOriginalFiniteFallbackPolicy (F high policy dispatch upper level secondLevel choose)
open P4AOriginalFiniteFallbackOwnCubeRows (points old pairPoint)
open P4AOriginalFiniteFallbackOccurrence (post)
open P4AOriginalFiniteFallbackSelectedTail (post_dwell)
open P4AOriginalFiniteFallbackSelectedSupport (high_at data_of_word)
open P4AOriginalFiniteFallbackSelectedMask (front)
open P4AOriginalOrderedThirdTable (retained capValue envelope infimum owned_portion inf_le)
open P4AOriginalOrderedThirdFullPolicy (current)
open HistoricalThirdCoarse.P1ActualTuple (history)
open P4AFallbackCanonicalBanks (bank)
open P4AUpperTaggedParityCompiler (rawSupport)
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P5Z.PresievedRoughSlotAffineGates (original_upper_prefix_iff_log)
open VariableEnvelope

theorem inherited (m n N cap u : ℕ) (delta w : ℝ) (d : OriginalData) (hN : 1<N) (he : 0≤(d.e:ℝ))
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) ((N:ℝ)^(19/96:ℝ)))
    (p : Fin 3 → ℕ) (tail : List ℕ) (hword : u.primeFactorsList.reverse=front p tail)
    (hhigh : mu<actualPrimeTupleLog N p 0)
    (h2 : read m (bank m).second (pairPoint N p)=none)
    (h3 : read m (bank m).third (actualPrimeTupleLog N p)=none) :
    let t := actualPrimeTupleLog N p
    let M := old d w N p
    0≤t 0 ∧ t 0≤1 ∧ 1/2≤M ∧ M≤299/500 ∧ M+2*(d.e:ℝ)≤v (t 0) ∧
      actualDwellSupport ((N:ℝ)^M) (front p tail) ∧
      actualDwellSupport (((N:ℝ)^M)/(p 0:ℝ)) (p 1::p 2::tail) := by
  let t := actualPrimeTupleLog N p
  let M := old d w N p
  obtain ⟨hp,hs,hret⟩ := data_of_word hu p tail hword
  have hh := high_at hhigh
  have h2lev : secondLevel (bank m) d w N (history p)=M := by
    rw [secondLevel,(points N p).1,h2]
    simp [choose,M,old,current,P4AOriginalThirdFallbackAdmission.self]
  have hpost : post (bank m) d w N (history p)=M := by rw [post,(points N p).2,h3]; exact h2lev
  have hadm : ordinaryRosserPrefixAdmissible false ((N:ℝ)^M) (history p) := by
    simpa only [oddFirstExitPolicy,Bool.false_or,F,policy,dispatch,if_pos hh,
      P4AOriginalFiniteFallbackPolicy.rank_three _ _ _ _ _ (by simp [history]),h2lev,decide_eq_true_eq] using hret
  have hpow := (original_upper_prefix_iff_log hN M p hp hs).mp
    (by simpa only [P4AOriginalThirdFallbackAdmission.pre_eq] using hadm)
  have hf := hpow.2 (0:Fin 3) (by decide)
  have hhead : 3*t 0<M := by simpa [P5Z.PresievedRoughSlotAffineGates.cube,P5Z.PresievedRoughSlotAffineGates.prefix] using hf
  obtain ⟨hU,hv⟩ := (raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hu
  have hsub := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap _ _ hU).1
  rw [hword] at hsub hv
  have hs' : List.ofFn p <+ front p tail := by
    simpa [front,List.ofFn_succ] using List.take_sublist 3 (front p tail)
  have hb (i : Fin 3) := mem_roughPrimeUniverse.mp (hsub.subset (hs'.subset (List.mem_ofFn.mpr ⟨i,rfl⟩)))
  have hbox : p∈actualPrimeBoxTuples N (fun _ => (0:ℝ)) (fun _ => (19/96:ℝ)) := by
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    refine ⟨(hb i).2.1,(hb i).2.2.1,?_,(hb i).2.2.2.2⟩
    rw [Real.rpow_zero]; exact_mod_cast hp i
  have hhi : high N [p 0] := by
    simpa [high,P4AOriginalFiniteFallbackPolicy.point,rosserAncestor,primeHistoryLogCoordinates,primeHistoryTuple,
      actualPrimeTupleLog] using hhigh
  have hstop : HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m N [p 0] := by
    have h' := hv.1
    change oddFirstExitPolicy (F (bank m) delta n d w N) false [p 0]=true at h'
    have H : ordinaryRosserPrefixAdmissible false ((N:ℝ)^HistoricalThirdCoarse.initial (d.e:ℝ)) [p 0] ∧
        HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m N [p 0] := by
      simpa [F,policy,dispatch,hhi,upper,HistoricalThirdCoarse.initialPolicy,oddFirstExitPolicy] using h'
    exact H.2
  obtain ⟨j,⟨hj,hj',hlam,hcap⟩,_⟩ := P4AOriginalOrderedThirdActualCoefficient.actual_triple he hN p hbox hs (hb 2).2.2.2.1 hstop
  have ht := mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hbox).2
  have ho := (actualPrimeTupleLog_strictAnti_iff hN p hp).mpr hs
  have hp' := owned_portion hj ⟨(ht 2).1,(ho (by decide : (1:Fin 3)<2)).le,(ho (by decide : (0:Fin 3)<1)).le⟩
  have hinf : infimum d.m j (actualExtendedThirdRobustBaseBranch 0)≤v (t 0) :=
    inf_le (continuous_actualExtendedThirdRobustBaseBranch 0) hp'
  have hno : ¬logPrimeMeshHi 0 (19/96) d.m j 0≤mu-4*(d.e:ℝ) := by
    linarith [(mem_logPrimeMeshCell.mp hj 0).2]
  have hM : M=capValue (d.e:ℝ) d.m j := hlam
  have hmargin : M+2*(d.e:ℝ)≤v (t 0) := by
    rw [hM,capValue,thirdPrefixBufferedCap,envelope,if_neg hno]
    linarith only [min_le_right (thirdPrefixTheta-2*(d.e:ℝ)) (infimum d.m j (actualExtendedThirdRobustBaseBranch 0)-2*(d.e:ℝ)),hinf]
  have ha : ordinaryRosserPrefixAdmissible false ((N:ℝ)^post (bank m) d w N (history p)) (history p) := by
    rw [hpost]; exact hadm
  have H := post_dwell m d delta n w hu (p 0) (p 1) (p 2) tail hword hh ha
  change actualDwellSupport ((N:ℝ)^post (bank m) d w N (history p)) (front p tail) at H
  rw [hpost] at H
  refine ⟨(ht 0).1,by linarith [(ht 0).2],?_,?_,hmargin,H,?_⟩
  · dsimp [mu] at hhigh; change (1/2:ℝ)≤M; linarith
  · rw [hM]; dsimp [VariableEnvelope.cap] at hcap; linarith
  · simpa [front] using actualDwell_selected_prefix_budget [p 0] (p 1::p 2::tail)
      (by simpa using hp 0) H

end
end ImbalancedChen.P4AOriginalFiniteFallbackInheritedFirst
