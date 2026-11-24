import ImbalancedChen.P4AOrderedThirdEighthSelectionProgram
import ImbalancedChen.P4AFull87UnionPhysicalSupport

namespace ImbalancedChen.P4AOrderedThirdGlobalRange
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open VariableEnvelope P4AOriginalOrderedThirdFullPolicy
open P4AOriginalOrderedThirdTable (rawExponent atPoint capValue)
open P1OriginalVariableFourthContinuation (finiteMax_le)
open P4AOriginalSixthActionBank (allActions)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8)
open P1GuardFrozenFiniteCapAlgebra (rounded protect)
open P4AFull87UnionCompilerPayment (top)
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport

theorem rounded_le (n : ℕ) (x : ℝ) : (rounded n x:ℝ)≤VariableEnvelope.cap := by
  rw [rounded,Rat.cast_max,Rat.cast_zero]
  have h := (P4AOriginalFull87FiniteEighthCap.downCap_error n (P1GuardFrozenFiniteCapAlgebra.clamp x)).2
  have hu := (P1GuardFrozenFiniteCapAlgebra.clamp_bounds x).2
  exact max_le (by norm_num [VariableEnvelope.cap]) (by linarith [P4AOriginalFull87HistoryCore.width_pos n])

theorem selected_le {delta : ℝ} (hd : 0<delta) (n : ℕ) (N : ℝ) (p : List ℕ) {a : ℚ}
    (hs : selectedCap delta n N p=some a) : (a:ℝ)≤VariableEnvelope.cap := by
  cases ho : ownerAtPrefix N p with
  | none => simp [selectedCap,ho] at hs
  | some c =>
    by_cases ht : point8 N p∈P4AOriginalFull87StrictActionTrim.trim c delta
    · have he : P4AOriginalFull87FiniteEighthCap.finiteCap n c (point8 N p)=a := by
        simpa only [selectedCap,ho,if_pos ht,Option.some.injEq] using hs
      rw [← he]
      have hcap := P4AOriginalFull87SourceDictionary.source_physical_ceiling
        (P4AOriginalFull87StrictActionTrim.trim_subset_source c hd ht)
      have h := (P4AOriginalFull87FiniteEighthCap.downCap_error n
        (P4AOriginalFull87SourceDictionary.newCap c (point8 N p))).2
      unfold P4AOriginalFull87FiniteEighthCap.finiteCap
      dsimp only [VariableEnvelope.cap]
      linarith [P4AOriginalFull87HistoryCore.width_pos n]
    · simp [selectedCap,ho,ht] at hs

theorem seed_le (d : OriginalData) (he : 0≤d.e) (w N : ℝ) (p : List ℕ) :
    (current d w N p).scalar≤top := by
  have hi := P5Z.ActualCommonRefinedRange.initial_le_theta d.e he
  unfold current rawExponent atPoint
  split_ifs <;> first | exact hi | exact (min_le_left _ _).trans hi

theorem stages (R : Root) (d : OriginalData) (he : 0≤d.e) (N L : ℝ) (hL : VariableEnvelope.cap≤L)
    (hr : R.scalar≤L) (n : ℕ) :
    (∀ p, fifth R d N p≤L) ∧ (∀ p, after R d N p 8≤L) ∧
    (∀ p, cap5 R d N n p≤L) ∧ (∀ p, cap6 R d N n p≤L) := by
  have heR : (0:ℝ)≤d.e := by exact_mod_cast he
  have ht (p : List ℕ) : third R N p≤L := by
    unfold third
    apply max_le hr
    split_ifs <;> first | exact (v_le_cap _).trans hL | exact hr
  have hf (p : List ℕ) : fourth R d N p≤L := by
    rw [fourth]; split
    · apply finiteMax_le _ _ _ _ _ (ht p)
      intro r _ _
      rw [r.bufferedCandidate_eq]
      linarith [(v_le_cap (∑ i∈r.selected,primeHistoryLogCoordinates N 4 p i)).trans hL]
    · exact ht p
  have h5 (p : List ℕ) : fifth R d N p≤L := by
    rw [fifth]; split
    · apply finiteMax_le _ _ _ _ _ (hf _)
      intro r _ _
      unfold P1OriginalVariableFifthContinuation.candidate
      rw [P1OriginalVariableFifthContinuation.envelope_eq_v]
      linarith [(v_le_cap (∑ i∈r.selected,primeHistoryLogCoordinates N 5 p i)).trans hL]
    · exact hf _
  have ha (p : List ℕ) (j : ℕ) : after R d N p j≤L := by
    induction j with
    | zero =>
      unfold after
      apply finiteMax_le
      · apply finiteMax_le _ _ _ _ _ (h5 _)
        intro i _ _
        exact (v_le_cap _).trans hL
      · intro c _ hc
        exact (P5Z.ActualCommonRefinedRange.eleven_newCap_lt_envelope hc.2.1).le.trans hL
    | succ k ih =>
      apply finiteMax_le _ _ _ _ _ ih
      intro c _ hc
      exact (P4AOriginalSixthLaterSemantics.source_endpoint_lt_selected_tent c _ hc.2.2.1).le.trans
        ((v_le_cap _).trans hL)
  have hq (p : List ℕ) : cap5 R d N n p≤L := by
    exact max_le (max_le hr ((rounded_le _ _).trans hL)) ((rounded_le _ _).trans hL)
  refine ⟨h5,fun p => ha p 8,hq,?_⟩
  intro p
  apply finiteMax_le _ _ _ _ _ (hq _)
  intro _ _ _
  exact (rounded_le _ _).trans hL

theorem raw_guard (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (he : 0≤d.e)
    (w : ℝ) (N : ℕ) (hN : (1:ℝ)≤N) (p : List ℕ)
    (hk : policy delta n d w N false p=true) :
    ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) p := by
  let R := current d w N p
  have hR : R.scalar≤top := seed_le d he w N p
  have hL : VariableEnvelope.cap≤top := by norm_num [VariableEnvelope.cap,top]
  obtain ⟨h5,h6,hq,hl⟩ := stages R d he N top hL hR n
  have mono (a : ℝ) (ha : a≤top) (h : ordinaryParityRosserPolicy false ((N:ℝ)^a) false p=true) :
      ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) p :=
    ordinaryRosserPrefixAdmissible_mono false p (Real.rpow_le_rpow_of_exponent_le hN ha)
      (by simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using h)
  have hb (h : base R d N false p=true) : ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) p := by
    rw [base] at h
    split at h
    · have hh := (show ordinaryRosserPrefixAdmissible false ((N:ℝ)^HistoricalThirdCoarse.initial (d.e:ℝ)) p ∧
          (p.length=1 → HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m N p) from
        (by simpa [HistoricalThirdCoarse.initialPolicy,oddFirstExitPolicy] using h)).1
      exact ordinaryRosserPrefixAdmissible_mono false p (Real.rpow_le_rpow_of_exponent_le hN
        (P5Z.ActualCommonRefinedRange.initial_le_theta _ he)) hh
    · exact mono _ hR h
  have hc (h : common R d N false p=true) : ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) p := by
    simp only [common,Bool.or_eq_true] at h
    rcases h with h|h
    · exact hb h
    · split_ifs at h <;> first | exact hb h | exact mono _ ((v_le_cap _).trans hL) h
  have hf (h : five R d N n false p=true) : ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) p := by
    unfold five firstExitDepthSplicePolicy at h
    split at h
    · exact hc h
    · apply mono _ _ h
      split <;> first | exact hq _ | exact h5 _
  have hs (h : six R d N n false p=true) : ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) p := by
    unfold six firstExitDepthSplicePolicy at h
    split at h
    · exact hf h
    · apply mono _ _ h
      split <;> first | exact hl _ | exact h6 _
  change eight R d N delta n false p=true at hk
  unfold eight firstExitDepthSplicePolicy at hk
  split at hk
  · exact hs hk
  · cases h : selectedCap delta n (N:ℝ) p with
    | none => exact hs (by simpa only [h] using hk)
    | some a => exact mono _ ((selected_le hd n N p h).trans hL) (by simpa only [h] using hk)

theorem raw_range (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (he : 0≤d.e)
    (w : ℝ) (N cap : ℕ) (hN : 2≤N) (omega z : ℝ) (hw : 0<omega) {x : ℕ}
    (hm : x∈rawSupport (policy delta n d w N false) N cap ((N:ℝ)^omega) z) :
    x.primeFactorsList.length<J0 omega ∧ (x:ℝ)<(N:ℝ)^top := by
  let F := policy delta n d w N false
  have hroot : P4AFiniteCapTaggedConstructor.keep (fun _ : Fin 1 => top) (fun _ => 0) F N=F := by
    funext p
    by_cases h : F p=true
    · have hp := raw_guard delta hd n d he w N (by exact_mod_cast (show 1≤N by omega)) p h
      simpa [P4AFiniteCapTaggedConstructor.keep,P4AFiniteCapTaggedConstructor.boundedCap,top,h] using hp
    · cases hh : F p <;> simp [P4AFiniteCapTaggedConstructor.keep,hh] at h ⊢
  change x∈rawSupport F N cap ((N:ℝ)^omega) z at hm
  rw [← hroot] at hm
  exact ⟨P4AFiniteCapTaggedConstructor.raw_rank_lt _ _ _ omega hw N cap hN z hm,
    P4AFiniteCapTaggedConstructor.raw_support_lt _ _ _ N cap hN _ z hm⟩

end
end ImbalancedChen.P4AOrderedThirdGlobalRange
