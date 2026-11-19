import ImbalancedChen.P4AOriginalFiniteFallbackSelectedTail
import ImbalancedChen.P4AFallbackActualBankLicence

namespace ImbalancedChen.P4AOriginalFiniteFallbackSelectedSupport
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackPolicy (F high upper policy point secondLevel choose)
open P4AOriginalFiniteFallbackBank (read)
open P4AOriginalFiniteFallbackOccurrence (post)
open P4AOriginalFiniteFallbackFullTree (coord_zero)
open P4AOriginalFiniteFallbackSelectedTail (post_dwell)
open P4AOriginalFiniteFallbackOwnCubeRows (pairPoint points)
open P4AOriginalFiniteFallbackCanonical (selected_second selected_third exclusive)
open P4AFallbackCanonicalBanks (bank)
open P4AUpperTaggedParityCompiler (rawSupport)
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (secondMask thirdMask)
open HistoricalThirdCoarse.P1ActualTuple (history)
open P5Z.PresievedRoughSlotAffineGates (original_upper_prefix_iff_log cube prefix)
open VariableEnvelope

theorem high_at {N : ℕ} {p : Fin 3 → ℕ} (h : mu<actualPrimeTupleLog N p 0) : high N (history p) := by
  rw [high,←coord_zero (k:=2) (N:ℝ) (history p) (by simp [history]),(points N p).2]
  exact h

theorem triple_of_gates {N : ℕ} (hN : 1<N) {p : Fin 3 → ℕ}
    (hp : ∀ i,0<p i) (hs : StrictAnti p) {M : ℝ}
    (first : 3*actualPrimeTupleLog N p 0<M)
    (third : actualPrimeTupleLog N p 0+actualPrimeTupleLog N p 1+3*actualPrimeTupleLog N p 2<M) :
    ordinaryRosserPrefixAdmissible false ((N:ℝ)^M) (history p) := by
  have hn : 0≤actualPrimeTupleLog N p 2 := div_nonneg (Real.log_nonneg (by exact_mod_cast hp 2))
    (Real.log_nonneg (by exact_mod_cast hN.le))
  rw [←P4AOriginalThirdFallbackAdmission.pre_eq p]
  apply (original_upper_prefix_iff_log hN M p hp hs).mpr
  refine ⟨?_,?_⟩
  · rw [Fin.sum_univ_three]; linarith
  · intro i hi
    fin_cases i
    · simpa [cube,prefix] using first
    · norm_num at hi
    · simpa [cube,prefix,Fin.sum_univ_three,Finset.sum_filter] using third

theorem data_of_word {m n N cap u : ℕ} {delta w z : ℝ} {d : OriginalData}
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (p : Fin 3 → ℕ) (tail : List ℕ) (ht : u.primeFactorsList.reverse=p 0::p 1::p 2::tail) :
    (∀ i,0<p i) ∧ StrictAnti p ∧
    oddFirstExitPolicy (F (bank m) delta n d w N) false (history p)=true := by
  obtain ⟨hU,hv⟩ := (raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hu
  have hl := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap _ _ hU).1
  rw [ht] at hv hl
  have sub : List.ofFn p <+ roughPrimeUniverse N cap ((N:ℝ)^w) z := by
    have prefix : List.ofFn p <+ p 0::p 1::p 2::tail := by
      simpa [List.ofFn_succ] using List.take_sublist 3 (p 0::p 1::p 2::tail)
    exact prefix.trans hl
  refine ⟨fun i => (mem_roughPrimeUniverse_prime (sub.subset (List.mem_ofFn.mpr ⟨i,rfl⟩))).pos,
    List.pairwise_ofFn.mp ((roughPrimeUniverse_pairwise_gt _ _ _ _).sublist sub),hv.2.2.1⟩

theorem pair {m n N cap u : ℕ} {delta w z : ℝ} {d : OriginalData} (hN : 1<N)
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (p : Fin 3 → ℕ) (tail : List ℕ) (ht : u.primeFactorsList.reverse=p 0::p 1::p 2::tail)
    {M : ℚ} (hit : read m (bank m).second (pairPoint N p)=some M) :
    actualDwellSupport ((N:ℝ)^(M:ℝ)) (p 0::p 1::p 2::tail) ∧
    actualDwellSupport (((N:ℝ)^(M:ℝ))/(p 1)) (p 0::p 2::tail) := by
  obtain ⟨hp,hs,hret⟩ := data_of_word hu p tail ht
  have H := selected_second hit
  have hh := high_at H.1.1
  have hm : read m (bank m).third (actualPrimeTupleLog N p)=none := by
    cases h : read m (bank m).third (actualPrimeTupleLog N p) with
    | none => rfl
    | some c => have c' := exclusive h; rw [show read m (bank m).second (fun i => actualPrimeTupleLog N p (i.castLE (by decide)))=some M from hit] at c'; contradiction
  have hlev : secondLevel (bank m) d w N (history p)=(M:ℝ) := by rw [secondLevel,(points N p).1,hit]; rfl
  have hpost : post (bank m) d w N (history p)=(M:ℝ) := by rw [post,(points N p).2,hm]; exact hlev
  have ha : ordinaryRosserPrefixAdmissible false ((N:ℝ)^post (bank m) d w N (history p)) (history p) := by
    rw [hpost]
    simpa only [oddFirstExitPolicy,Bool.false_or,F,policy,P4AOriginalFiniteFallbackPolicy.dispatch,if_pos hh,
      P4AOriginalFiniteFallbackPolicy.rank_three _ _ _ _ _ (by simp [history]),hlev,decide_eq_true_eq] using hret
  have full := post_dwell m d delta n w hu (p 0) (p 1) (p 2) tail ht hh ha
  change actualDwellSupport ((N:ℝ)^post (bank m) d w N (history p)) _ at full
  rw [hpost] at full
  refine ⟨full,actualDwell_selected_p2_budget _ _ _ (hp 1) full ?_⟩
  have hg := H.2.2.2.2.2.2.1 (0:Fin 2) (by decide)
  have gate : actualPrimeTupleLog N p 1+2*actualPrimeTupleLog N p 0≤(M:ℝ) := by
    simpa [selectedSquareExpr,secondMask,pairPoint] using hg.le
  let t := actualPrimeTupleLog N p
  have hx : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  calc
    (p 0:ℝ)^2*p 1 = (N:ℝ)^(t 1+(t 0+t 0)) := by
      simp only [Real.rpow_add hx,t,actualPrimeTupleLog_rpow hN p hp]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) (by dsimp [t]; linarith)

theorem triple {m n N cap u : ℕ} {delta w z : ℝ} {d : OriginalData} (hN : 1<N)
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (p : Fin 3 → ℕ) (tail : List ℕ) (ht : u.primeFactorsList.reverse=p 0::p 1::p 2::tail)
    {M : ℚ} (hit : read m (bank m).third (actualPrimeTupleLog N p)=some M) :
    actualDwellSupport ((N:ℝ)^(M:ℝ)) (p 0::p 1::p 2::tail) ∧
    actualDwellSupport (((N:ℝ)^(M:ℝ))/(p 1*p 2 : ℕ)) (p 0::tail) := by
  obtain ⟨hp,hs,_⟩ := data_of_word hu p tail ht
  have H := selected_third hit
  have hh := high_at H.1.1
  have hpost : post (bank m) d w N (history p)=(M:ℝ) := by rw [post,(points N p).2,hit]; rfl
  have ha := triple_of_gates hN hp hs (H.2.1.trans H.2.2.2.1) (H.2.2.1.trans H.2.2.2.1)
  rw [←hpost] at ha
  have full := post_dwell m d delta n w hu (p 0) (p 1) (p 2) tail ht hh ha
  change actualDwellSupport ((N:ℝ)^post (bank m) d w N (history p)) _ at full
  rw [hpost] at full
  refine ⟨full,actualDwell_selected_p2p3_budget _ _ _ _ (hp 1) (hp 2) full ?_⟩
  have hg := H.2.2.2.2.2.2.2.1 (0:Fin 3) (by decide)
  have gate : actualPrimeTupleLog N p 1+actualPrimeTupleLog N p 2+2*actualPrimeTupleLog N p 0≤(M:ℝ) := by
    simpa [selectedSquareExpr,thirdMask,add_assoc] using hg.le
  let t := actualPrimeTupleLog N p
  have hx : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  calc
    (p 0:ℝ)^2*p 1*p 2 = (N:ℝ)^((t 1+t 2)+(t 0+t 0)) := by
      simp only [Real.rpow_add hx,t,actualPrimeTupleLog_rpow hN p hp]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) (by dsimp [t]; linarith)

end
end ImbalancedChen.P4AOriginalFiniteFallbackSelectedSupport
