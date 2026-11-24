import ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient
import ImbalancedChen.P4AOriginalHistoricalThirdMajorant

namespace ImbalancedChen.P4AOrderedThirdArithmeticOccurrence
noncomputable section
open Set HistoricalThirdCoarse
open HistoricalThirdCoarse.P1ActualTuple (history history_log active_iff_log parent_two_iff mem_gateRegion)
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87RawChronology (cutoff rawRoot)
open P4ACatalogFiveCoarseWeightedPayment (weight carrier candidateTuples admittedOrdinary admittedOrdinary_normalized)
open P4AOriginalRankThreeRestorationSource
open P1Pair12RetainedSignedSource
open P5OriginalCommonFourthSourceLedger (signedTest_one_eq_polynomial)
open P5OriginalCommonPositivePresieve (normalize normalize_sub)
open P4AOriginalHistoricalThirdOccurrence (base primes base_admitted)
open P4AOriginalHistoricalThirdMajorant (ordered)
open P4AOriginalOrderedThirdTable (Point retained capValue rawExponent atPoint)
open scoped Classical BigOperators

abbrev fresh (d : OriginalData) (w : ℝ) (N : ℕ) :=
  P4AOriginalOrderedThirdTable.policy (d.e:ℝ) d.m w (N:ℝ)

def region {m : ℕ} (j : Cell m) := logPrimeMeshCell 0 (19/96) m j ∩ ordered

def diff (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) :=
  actualPrimeTupleOwnCubeMinus N N (initial (d.e:ℝ)) p -
    actualPrimeTupleOwnCubeMinus N N (rawExponent (d.e:ℝ) d.m w N (history p)) p

def localDiff (d : OriginalData) (N : ℕ) (j : Cell d.m) (p : Fin 3 → ℕ) :=
  if actualPrimeTupleLog N p ∈ region j then
    actualPrimeTupleOwnCubeMinus N N (initial (d.e:ℝ)) p -
      actualPrimeTupleOwnCubeMinus N N (capValue (d.e:ℝ) d.m j) p else 0

theorem continuation (d : OriginalData) (w : ℝ) (N : ℕ)
    (pre : List ℕ) (hl : 3≤pre.length) (pos : Bool) (mass : ℝ) (rem : List ℕ) :
    signedTest (fresh d w N) weight (fun _ _ => 1) pre pos mass rem =
      signedTest (frozenParityRosserPolicy false 3 (fun h => (N:ℝ)^rawExponent (d.e:ℝ) d.m w N h))
        weight (fun _ _ => 1) pre pos mass rem := by
  induction rem generalizing pre pos mass with
  | nil => rfl
  | cons p ps ih =>
    have hn : ¬(p::pre).length≤2 := by simp; omega
    have hnode : fresh d w N (!pos) (p::pre)=
        frozenParityRosserPolicy false 3 (fun h => (N:ℝ)^rawExponent (d.e:ℝ) d.m w N h) (!pos) (p::pre) := by
      simp only [fresh,P4AOriginalOrderedThirdTable.policy,thirdCappedUpperPolicy,firstExitDepthSplicePolicy,if_neg hn]
    simp only [signedTest,hnode]
    rw [ih pre hl pos mass,ih (p::pre) (by simp; omega) (!pos) (mass*weight p)]

theorem admitted (d : OriginalData) (w : ℝ) (N : ℕ) (s : FirstExitDepthState ℕ)
    (hl : s.selectedPrefix.length=3) (hb : s.positive=false) :
    admittedTest (fresh d w N) weight (fun _ _ => 1) s =
      admittedOrdinary ((N:ℝ)^rawExponent (d.e:ℝ) d.m w N s.selectedPrefix) N s := by
  have hn : ¬s.selectedPrefix.length≤2 := by omega
  have hnode : fresh d w N s.positive s.selectedPrefix =
      ordinaryParityRosserPolicy false ((N:ℝ)^rawExponent (d.e:ℝ) d.m w N s.selectedPrefix)
        s.positive s.selectedPrefix := by
    simp only [fresh,P4AOriginalOrderedThirdTable.policy,thirdCappedUpperPolicy,firstExitDepthSplicePolicy,
      if_neg hn,frozenParityRosserPolicy,ancestorFrozenPolicy,rosserAncestor_self_of_length 3 _ hl]
  rw [admittedTest,hnode]
  simp only [hb,ordinaryParityRosserPolicy,oddFirstExitPolicy,Bool.false_eq_true,if_false,decide_eq_true_eq]
  unfold admittedOrdinary
  simp only [hb]
  split_ifs
  · rw [continuation d w N _ (by omega),signedTest_one_eq_polynomial,signedTest_one_eq_polynomial,
      firstExitRetainedPolynomial_frozenParityRosser_eq false 3 _ _ _ _ _ _ hl]
  · rfl

theorem row (d : OriginalData) (w : ℝ) (he : 0<(d.e:ℝ)) (hsmall : (d.e:ℝ)≤1/384)
    (hstep : logPrimeMeshStep 0 (19/96) d.m≤(d.e:ℝ)/2) {N : ℕ} (hN : 1<N)
    (s : FirstExitDepthState ℕ) (hs : s∈candidates d (N:ℝ) weight (carrier N)) :
    normalize N (admittedTest (fresh d w N) weight (fun _ _ => 1) s -
      admittedTest (base d N) weight (fun _ _ => 1) s) =
      (s.selectedPrefix.map weight).prod*diff d w N (primeHistoryTuple 3 s.selectedPrefix) := by
  obtain ⟨hl,hsort,hprod,_,_,hb,hm⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d (N:ℝ))) N N (cutoff N) s hs
  let p := primeHistoryTuple 3 s.selectedPrefix
  have hp : s.selectedPrefix=history p := by simpa only [← P4AOriginalThirdFallbackAdmission.pre_eq]
    using (primeHistoryTuple_reverse_ofFn hl).symm
  have hpos : ∀ i,0<p i := by
    rw [hp] at hprod
    simp only [history,List.prod_cons,List.prod_nil,Nat.cast_mul,Nat.cast_one,mul_one] at hprod
    intro i; fin_cases i <;> by_contra! h <;> simp [Nat.eq_zero_of_le_zero h] at hprod
  have hfalse : s.positive=false := by simpa [hp,history,evenListLength] using hb
  rw [admitted d w N s hl hfalse,base_admitted d N s hl hfalse,←hm]
  change _ = s.mass*diff d w N p
  rw [hp]
  let t := actualPrimeTupleLog N p
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have ho : StrictAnti p := by
    rw [hp] at hsort
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i; fin_cases i
    · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 _ (by simp)
    · exact (List.pairwise_cons.mp hsort).1 _ (by simp)
  have hanti := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr ho
  have hz : 0≤t 2 := div_nonneg (Real.log_nonneg (by exact_mod_cast hpos 2)) (Real.log_pos hNr).le
  have hord : t∈actualExtendedThirdClosedOrder :=
    ⟨hz,(hanti (by decide : (1:Fin 3)<2)).le,(hanti (by decide : (0:Fin 3)<1)).le⟩
  let lam := rawExponent (d.e:ℝ) d.m w N (history p)
  by_cases same : lam=initial (d.e:ℝ)
  · change normalize N (admittedOrdinary ((N:ℝ)^lam) N s - _) = _
    change normalize N (admittedOrdinary ((N:ℝ)^lam) N s - _) =
      s.mass*(actualPrimeTupleOwnCubeMinus N N (initial (d.e:ℝ)) p-actualPrimeTupleOwnCubeMinus N N lam p)
    simp [same,normalize]
  · obtain ⟨j,hj,ht,heq⟩ : ∃ j∈retained (d.e:ℝ) d.m,
        t∈logPrimeMeshCell 0 (19/96) d.m j ∧ lam=capValue (d.e:ℝ) d.m j := by
      by_cases ha : active w (N:ℝ) (history p)
      · by_cases hh : ∃ j∈retained (d.e:ℝ) d.m,t∈logPrimeMeshCell 0 (19/96) d.m j
        · obtain ⟨j,hj,ht⟩ := hh
          exact ⟨j,hj,ht,by
            rw [show lam=atPoint (d.e:ℝ) d.m t by simp [lam,rawExponent,ha,history_log,t]]
            exact P4AOriginalOrderedThirdTable.atPoint_on_cell hj ht⟩
        · exact False.elim (same (by
            change rawExponent (d.e:ℝ) d.m w N (history p)=_
            rw [rawExponent,if_pos ha,history_log,atPoint,dif_neg hh]))
      · exact False.elim (same (by simp [lam,rawExponent,ha]))
    have hfirst := P4AOriginalOrderedThirdTable.first_cube he hsmall hstep
      (P4AOriginalOrderedThirdTable.owned_portion ht hord) (Finset.mem_filter.mp hj).2.2
    have hc := VariableEnvelope.first_cube_lt_level_of_exponent (lambda:=lam) (p 0) hNr
      (actualPrimeTupleLog_rpow hN p hpos 0).symm.le (by rw [heq]; exact hfirst)
    have hroot : lam≤initial (d.e:ℝ) := heq.le.trans (thirdPrefixBufferedCap_le_root _ _)
    have hbase := hc.trans_le (Real.rpow_le_rpow_of_exponent_le hNr.le hroot)
    rw [normalize_sub]
    unfold normalize
    rw [admittedOrdinary_normalized d N s hs p hp (hpos 2) _ hc,
      admittedOrdinary_normalized d N s hs p hp (hpos 2) _ hbase]
    change -s.mass*actualPrimeTupleOwnCubeMinus N N lam p -
      -s.mass*actualPrimeTupleOwnCubeMinus N N (initial (d.e:ℝ)) p = _
    unfold diff; dsimp only [lam]; ring

theorem source (d : OriginalData) (w : ℝ) (he : 0<(d.e:ℝ)) (hsmall : (d.e:ℝ)≤1/384)
    (hstep : logPrimeMeshStep 0 (19/96) d.m≤(d.e:ℝ)/2) {N : ℕ} (hN : 1<N) :
    normalize N (rawRoot (fresh d w N) N-rawRoot (base d N) N) =
      ∑ p∈candidateTuples d N,(∏ i,weight (p i))*diff d w N p := by
  let P := old3 d (N:ℝ)
  have hr (R : Bool → List ℕ → Bool) (hr : ∀ pre,R true pre=true) :
      signedTest R weight (fun _ _ => 1) [] true 1 (carrier N)=rawRoot R N := by
    rw [signedTest_one_eq_polynomial]
    exact UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained R hr N N 0 _
  have hf (pre : List ℕ) : fresh d w N true pre=true := by
    simp [fresh,P4AOriginalOrderedThirdTable.policy,thirdCappedUpperPolicy,firstExitDepthSplicePolicy,
      initialPolicy,frozenParityRosserPolicy,ancestorFrozenPolicy,ordinaryParityRosserPolicy,oddFirstExitPolicy]
  rw [←hr _ hf,←hr (base d N) (fun _ => rfl),signed_difference_before_third P (base d N) (fresh d w N)
    (fun b pre hl => (policy_through_two _ _ _ _ _ b pre hl).symm)
    (fun b pre hl => by
      change fresh d w N b pre=HistoricalThirdCoarse.policy _ _ _ _ _ b pre
      rw [policy_through_two _ _ _ _ _ b pre hl]
      simp [fresh,P4AOriginalOrderedThirdTable.policy,thirdCappedUpperPolicy,firstExitDepthSplicePolicy,hl])
      weight (fun _ _ => 1) [] (by simp) true 1 (carrier N)]
  have hmap (L : List (FirstExitDepthState ℕ)) (f : FirstExitDepthState ℕ → ℝ) :
      normalize N (L.map f).sum=(L.map (fun s => normalize N (f s))).sum := by
    induction L with
    | nil => simp [normalize]
    | cons s ss ih => simp only [List.map_cons,List.sum_cons,P5OriginalCommonPositivePresieve.normalize_add,ih]
  rw [hmap,←firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 3
    (beforeThirdPolicy P) weight (carrier N) (roughPrimeUniverse_nodup _ _ _ _) (diff d w N)]
  congr 1
  apply List.map_congr_left
  intro s hs
  exact row d w he hsmall hstep hN s hs

end
end ImbalancedChen.P4AOrderedThirdArithmeticOccurrence

