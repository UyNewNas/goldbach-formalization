import ImbalancedChen.P4AOriginalSavedSixthOwnCaps
import ImbalancedChen.P4AOriginalFull87PolicyReverseAdmission

/-! Reverse incidence on the original G4 rectangles. The actual old first
label and all three odd cube checks are made at their own levels. The
equality removes every unadmitted and outside word from the finite sums
by its actual zero residual, before applying an asymptotic estimate. -/
namespace ImbalancedChen.P4AOriginalSavedSixthOccurrence
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalSavedSixthHistoricalOwner
open P4AOriginalSavedSixthSigned
open P4AOriginalSavedSixthPrimeMean (primes bounds ordered6 cube_subset)
open P4AOriginalSavedSixthSourceGates (source_iff)
open P4AOriginalSavedSixthOwnCaps (on_positive)
open P4AOriginalSavedSixthPlanes (box)
open P4AOriginalSavedSixthArchive (Row Source)
open P4AOriginalFull87DataPolicy (fifthPolicy fifth_even)
open P4AOriginalNewFifthCoverage (Schedule)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (weight)
open P4AOriginalFull87RawChronology (cutoff)
open P5OriginalCommonPositivePresieve (normalize)

private theorem strict_primes {i : Row} {N : ℕ} (hN : 1<N) {p : Fin 6 → ℕ} (hp : ∀ j,0<p j)
    (ht : actualPrimeTupleLog N p∈box i) : StrictAnti p := by
  intro j k hjk
  have h := Real.rpow_lt_rpow_of_exponent_lt (show (1:ℝ)<N by exact_mod_cast hN) (ordered6 i ht hjk)
  rw [actualPrimeTupleLog_rpow hN p hp,actualPrimeTupleLog_rpow hN p hp] at h
  exact_mod_cast h

theorem selected (n : ℕ) (hn : 4*width n<1/1600) {e : ℚ} {q : ℕ} {a : ℝ} (hs : Schedule e q a)
    {i : Row} {N : ℕ} (hN : 1<N) (p : Fin 6 → ℕ) (hp : ∀ j,(p j).Prime)
    (hsrc : Source i (actualPrimeTupleLog N p)) :
    FirstExitValidSelection (fifthPolicy n (bank e q a) (N:ℝ)) [] true (List.ofFn p) := by
  let d := bank e q a
  let t := actualPrimeTupleLog N p
  let L := root d N p
  have ht := ((source_iff i _).mp hsrc).1
  have hg := ((source_iff i _).mp hsrc).2
  have hpos := fun i => (hp i).pos
  have ho := strict_primes hN hpos ht
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hN0 := zero_lt_one.trans hNr
  have hist := actual_owner i hs hN p hpos ht
  have hcap := on_positive i (d:=d) hs.1 p ht hg hist n hn
  have hr (j : Fin 6) : (N:ℝ)^t j = (p j:ℝ) := actualPrimeTupleLog_rpow hN p hpos j
  have cube (j : Fin 6) : (N:ℝ)^(3*t j)=(p j:ℝ)^3 := by
    rw [mul_comm,Real.rpow_mul_natCast hN0.le,hr]
  have h1 : (p 0:ℝ)^3 < (N:ℝ)^L := by
    simpa only [cube] using Real.rpow_lt_rpow_of_exponent_lt hNr hist.first
  have h3 : (p 0:ℝ)*p 1*(p 2:ℝ)^3 < (N:ℝ)^L := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith only [hist.third] : Certificates.P2OriginalSixthElevenLogSemantics.H3 t < L)
    simpa only [Certificates.P2OriginalSixthElevenLogSemantics.H3,Real.rpow_add hN0,hr,cube] using h
  have h5 : (([p 4,p 3,p 2,p 1,p 0].prod:ℕ):ℝ)*(p 4:ℝ)^2 < (N:ℝ)^L := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith only [hist.fifth] : Certificates.P2OriginalSixthElevenLogSemantics.H5 t < L)
    simp only [Certificates.P2OriginalSixthElevenLogSemantics.H5,Real.rpow_add hN0,hr,cube] at h
    convert h using 1 <;> simp [pow_succ,mul_comm,mul_left_comm,mul_assoc]
  have adm5 := (ordinaryRosserPrefixAdmissible_upper_five_iff ((N:ℝ)^L) (p 0) (p 1) (p 2) (p 3) (p 4)
    (hpos 4) (ho (by decide)) (ho (by decide)) (ho (by decide)) (ho (by decide))).mpr ⟨h1,h3,h5⟩
  have hprime5 : ∀ x ∈ [p 4,p 3,p 2,p 1,p 0], x.Prime := by
    intro x hx; simp only [List.mem_cons,List.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> exact hp _
  have hsort : (List.ofFn p).reverse.Pairwise (· < ·) := by
    rw [List.pairwise_reverse]; exact List.pairwise_ofFn.mpr ho
  have hsort5 : [p 4,p 3,p 2,p 1,p 0].Pairwise (· < ·) := by
    change (pre p).Pairwise (· < ·) at hsort; rw [pre_list] at hsort
    exact (List.pairwise_cons.mp hsort).2
  have adm3 := ordinaryRosserPrefixAdmissible_of_append false ((N:ℝ)^L) [p 4,p 3]
    [p 2,p 1,p 0] hprime5 hsort5 adm5
  have adm1 := ordinaryRosserPrefixAdmissible_of_append false ((N:ℝ)^L) [p 4,p 3,p 2,p 1]
    [p 0] hprime5 hsort5 adm5
  have adm1' := ordinaryRosserPrefixAdmissible_mono false _ (Real.rpow_le_rpow_of_exponent_le hNr.le hist.initial.le) adm1
  have old1 : old3 d (N:ℝ) false [p 0]=true := by
    rw [old3,HistoricalThirdCoarse.policy_through_two _ _ _ _ _ _ _ (by simp)]
    simp [HistoricalThirdCoarse.initialPolicy,oddFirstExitPolicy,adm1',hist.stop]
  have hs3 : originalSeed d (N:ℝ) [p 2,p 1,p 0] = L := by
    change _ = root d N p
    rw [hist.seed]
    simp [originalSeed,P1OriginalVariableFourthContinuation.seedExponent,pre_list,rosserAncestor]
  have old3test : old3 d (N:ℝ) false [p 2,p 1,p 0]=true := by
    rw [old3_after_two d _ _ _ (by simp),hs3]
    simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using adm3
  have hf : old n d (N:ℝ) (pre p) = P4AOriginalFull87DataPolicy.level5Exponent n d (N:ℝ)
      [p 4,p 3,p 2,p 1,p 0] := by simp [old,pre_list,rosserAncestor]
  have adm5' := ordinaryRosserPrefixAdmissible_mono false _
    (Real.rpow_le_rpow_of_exponent_le hNr.le (hf ▸ hcap.1)) adm5
  have a1 : fifthPolicy n d (N:ℝ) false [p 0]=true := by simp [fifthPolicy,firstExitDepthSplicePolicy,common3,old1]
  have a3 : fifthPolicy n d (N:ℝ) false [p 2,p 1,p 0]=true := by simp [fifthPolicy,firstExitDepthSplicePolicy,common3,old3test]
  have a5 : fifthPolicy n d (N:ℝ) false [p 4,p 3,p 2,p 1,p 0]=true := by
    simpa [fifthPolicy,firstExitDepthSplicePolicy,frozenParityRosserPolicy,ancestorFrozenPolicy,
      rosserAncestor,ordinaryParityRosserPolicy,oddFirstExitPolicy] using adm5'
  have heq : List.ofFn p=[p 0,p 1,p 2,p 3,p 4,p 5] := by simp [List.ofFn_succ]
  rw [heq]
  simp only [FirstExitValidSelection,Bool.not_true,Bool.not_false]
  exact ⟨a1,fifth_even n d _ _,a3,fifth_even n d _ _,a5,fifth_even n d _ _,trivial⟩

theorem admitted_on_source (n : ℕ) (hn : 4*width n<1/1600) {e : ℚ} {q : ℕ} {a : ℝ} (hs : Schedule e q a)
    {i : Row} {N : ℕ} (hN : 1<N) (p : Fin 6 → ℕ) (hsrc : Source i (actualPrimeTupleLog N p)) :
    p∈admitted n (bank e q a) N N (cutoff N) ↔ p∈primes N := by
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hcut : cutoff N≤(N:ℝ) := by
    change (N:ℝ)^(19/96:ℝ)≤N; simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num : (19/96:ℝ)≤1)
  rw [admitted,mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap _ _ _ _ _ _ hcut,
    mem_actualPrimeBoxTuples_log_iff hN]
  have ht := ((source_iff i _).mp hsrc).1
  constructor
  · intro hh
    exact ⟨fun j => ⟨(hh.2.1 j).1,(hh.2.1 j).2.1⟩,cube_subset i ht⟩
  · rintro ⟨hp,_⟩
    have hpos (j) := (hp j).1.pos
    refine ⟨strict_primes hN hpos ht,fun j => ⟨(hp j).1,(hp j).2,Nat.cast_nonneg _,?_⟩,
      selected n hn hs hN p (fun j => (hp j).1) hsrc⟩
    rw [← actualPrimeTupleLog_rpow hN p hpos j]
    exact Real.rpow_lt_rpow_of_exponent_lt hNr ((bounds i ht j).2.trans (by norm_num))

theorem off_source (n : ℕ) (d : OriginalData) (N cap : ℕ) (p : Fin 6 → ℕ)
    (h : ∀ i : Row,¬Source i (actualPrimeTupleLog N p)) : tupleResidual n d N cap p=0 := by
  have he := P4AOriginalSavedSixthStage.inherit_if_no_source n d (N:ℝ) (pre p)
    (fun i => by rw [pre_log]; exact h i)
  simp only [tupleResidual,he,old,actualPrimeTupleInitialSaving,sub_self,zero_mul,zero_div]

theorem original_raw_difference_eq_box (n : ℕ) (hn : 4*width n<1/1600) {e : ℚ} {q : ℕ} {a : ℝ}
    (hs : Schedule e q a) {N : ℕ} (hN : 1<N) :
    normalize N (P4AOriginalSavedSixthStage.before n (bank e q a) N) =
      ∑ p∈primes N,(∏ j,weight (p j))*tupleResidual n (bank e q a) N N p := by
  let d := bank e q a
  let f := fun p : Fin 6 → ℕ => (∏ j,weight (p j))*tupleResidual n d N N p
  let own := fun p : Fin 6 → ℕ => ∃ i : Row,Source i (actualPrimeTupleLog N p)
  have ff (B : Finset (Fin 6 → ℕ)) : (∑ p∈B.filter own,f p)=∑ p∈B,f p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : own p
    · simp [hp]
    · have h : ∀ i : Row,¬Source i (actualPrimeTupleLog N p) := fun i hi => hp ⟨i,hi⟩
      simp [f,hp,off_source n d N N p h]
  have he : (admitted n d N N (cutoff N)).filter own=(primes N).filter own := by
    ext p
    simp only [Finset.mem_filter]
    by_cases hp : own p
    · obtain ⟨i,hi⟩ := hp; rw [admitted_on_source n hn hs hN p hi]
    · simp [hp]
  rw [show normalize N (P4AOriginalSavedSixthStage.before n d N) =
      ∑ p∈admitted n d N N (cutoff N), f p from original_raw_difference_eq_admitted n d N N (cutoff N)
        (by exact_mod_cast hN.le)]
  exact (ff _).symm.trans ((congrArg (fun B : Finset (Fin 6 → ℕ) => ∑ p∈B,f p) he).trans (ff _))

end
end ImbalancedChen.P4AOriginalSavedSixthOccurrence
