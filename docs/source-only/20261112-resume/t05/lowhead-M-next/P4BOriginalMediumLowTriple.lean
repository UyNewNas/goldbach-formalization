import ImbalancedChen.P4BOriginalMediumOccupiedLengths
import ImbalancedChen.VariableEnvelopeRegularity

/-! Read the actual singleton selected by the finite compiler and its
three original prime exponents. -/
namespace ImbalancedChen.P4BOriginalMediumLowTriple
noncomputable section
open Classical Set
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (ownerHead)
open P4AOriginalFiniteFallbackPhysicalSelected (word head pick witnesses)
open P4AOriginalFiniteFallbackOwnCubeRows (old)
open P4AOriginalFiniteFallbackSelectedMask (value)
open P4AOriginalFiniteFallbackCommonGroups (choice)
open P4AOriginalFiniteFallbackCanonical (selected_second selected_third)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalOrderedThirdTable
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFiniteFallbackNaturalEndpoints (upper tag endpoint_bounds)
open HistoricalThirdCoarse.P1ActualTuple (history history_log)
open VariableEnvelope (mu v A)

private theorem cap_lower {e : ℝ} (he : e≤1/2048) {m : ℕ}
    (hs : logPrimeMeshStep 0 (19/96) m≤1/1000) {j : HistoricalThirdCoarse.Cell m}
    (hr : j∈retained e m) {t : Point} (ht : t∈logPrimeMeshCell 0 (19/96) m j)
    (ht0 : t 0≤mu) : t 0+3/8≤capValue e m j := by
  have hbase : t 0+3/8+2*e≤infimum m j (actualExtendedThirdRobustBaseBranch 0) := by
    apply le_csInf ((Finset.mem_filter.mp hr).2.1.image _)
    rintro _ ⟨s,hsp,rfl⟩
    change t 0+3/8+2*e≤v (s 0)
    have hsp0 := hsp.1 0 (mem_univ _)
    have htp0 := mem_logPrimeMeshCell.mp ht 0
    have hd : |s 0-t 0|≤1/1000 := by
      have H := logPrimeMeshHi_eq_lo_add_step 0 (19/96) m j 0
      exact abs_le.mpr ⟨by linarith [hsp0.1,htp0.2],by linarith [hsp0.2,htp0.1]⟩
    have hl := (abs_le.mp (VariableEnvelope.v_abs_sub_le (s 0) (t 0))).1
    rw [VariableEnvelope.v_eq_A ht0] at hl
    dsimp only [A,mu] at *
    linarith
  have henv : infimum m j (actualExtendedThirdRobustBaseBranch 0)≤envelope e m j := by
    unfold envelope
    split <;> first | exact le_max_left _ _ | exact le_rfl
  apply le_min
  · dsimp only [mu] at ht0
    change t 0+3/8≤299/500-2*e
    linarith
  · linarith only [hbase,henv]

theorem low_choice (P : Params) (p : Fin 3→ℕ) (h : actualPrimeTupleLog P.N p 0≤mu) :
    choice P.m P.N (data P.e P.q P.a) P.omega p =
      (none,old (data P.e P.q P.a) P.omega P.N p) := by
  have h3 : value P.m .third P.N p=none := by
    cases H : value P.m .third P.N p with
    | none => rfl
    | some c => exact False.elim ((not_lt_of_ge h) (selected_third H).1.1)
  have h2 : value P.m .second P.N p=none := by
    cases H : value P.m .second P.N p with
    | none => rfl
    | some c => exact False.elim ((not_lt_of_ge h) (selected_second H).1.1)
  simp only [choice,h3,h2]

theorem actual_cap_lower (P : Params) (hE : (P.e:ℝ)≤1/2048) (hq : 0<P.q)
    (p : Fin 3→ℕ) (hlow : actualPrimeTupleLog P.N p 0≤mu) :
    actualPrimeTupleLog P.N p 0+3/8≤old (data P.e P.q P.a) P.omega P.N p := by
  have hq' : (1:ℝ)≤P.q := by exact_mod_cast hq
  have hs : logPrimeMeshStep 0 (19/96) (data P.e P.q P.a).m≤1/1000 := by
    rw [show (data P.e P.q P.a).m=P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh P.q from rfl,
      P1OriginalFifthGrid400RefinedFullBoxCover.refined_step P.q hq]
    apply (div_le_iff₀ (by positivity : 0<(2400:ℝ)*P.q)).mpr
    linarith
  have hinit : actualPrimeTupleLog P.N p 0+3/8≤HistoricalThirdCoarse.initial (P.e:ℝ) := by
    dsimp only [HistoricalThirdCoarse.initial,extendedDistributionCap,mu] at *
    linarith
  unfold old rawExponent
  split
  · rw [history_log]
    unfold atPoint
    split
    next h => exact cap_lower hE hs h.choose_spec.1 h.choose_spec.2 hlow
    next => exact hinit
  · exact hinit

def representative (P : Params) (J : List ℕ) :=
  pick P.f P.N P.N P.W (cutoff P.N) P.T (J.map (fun j => (j:ℤ)))

theorem representative_raw (P : Params) (hN : 1<P.N) {J : List ℕ} (hJ : J∈P.words) :
    representative P J∈P.raw ∧ P.wordOf (representative P J)=J := by
  obtain ⟨v,hv,hvJ⟩ := P.word_witness hJ
  have vU := P4AUpperTaggedParityCompiler.rawSupport_subset_universe _ _ _ _ _ hv
  have hbox := (P4BOriginalCollisionPhysical.own_label P hN vU J).mpr hvJ
  let S := witnesses P.f P.N P.N P.W (cutoff P.N) P.T (J.map (fun j => (j:ℤ)))
  have hS : S.Nonempty := ⟨v,Finset.mem_filter.mpr ⟨hv,P4BOriginalCollisionPhysical.owner_key P hN hbox⟩⟩
  have hmem : representative P J∈S := by
    change (if h : S.Nonempty then S.min' h else 1)∈S
    rw [dif_pos hS]
    exact S.min'_mem hS
  obtain ⟨hr,heq⟩ := Finset.mem_filter.mp hmem
  refine ⟨hr,?_⟩
  simpa [Params.wordOf,word,tag,P4AUpperTaggedParityCompiler.primeWordLabel,
    P2LowerFiniteCellRounding.label,List.map_map,Function.comp_def]
    using congrArg (List.map Int.toNat) heq

private theorem three (l : List ℕ) (h : l.length=3) :
    l=[head l 0,head l 1,head l 2] := by
  rcases l with _|⟨a,l⟩ <;> try simp at h
  rcases l with _|⟨b,l⟩ <;> try simp at h
  rcases l with _|⟨c,l⟩ <;> try simp at h
  rcases l with _|⟨d,l⟩
  · rfl
  · simp at h

/-- The two nonleading logarithms in the third Rosser cube come from
the very same raw representative used by splitAt. -/
theorem actual_third (P : Params) (hN : 1<P.N) (he : 0≤P.e) {J : List ℕ}
    (hJ : J∈P.words) (h3 : J.length=3) :
    let p := ownerHead P J
    let t := actualPrimeTupleLog P.N p
    J=[tag P.N P.T (p 0),tag P.N P.T (p 1),tag P.N P.T (p 2)] ∧
    (∀ i,(p i).Prime ∧ ¬p i∣P.N) ∧ StrictAnti t ∧ t 0+t 1+3*t 2<299/500 := by
  let g := representative P J
  let p := ownerHead P J
  obtain ⟨hraw,hword⟩ := representative_raw P hN hJ
  have hlen : g.primeFactorsList.reverse.length=3 := by
    simpa only [Params.wordOf,word,List.length_map] using (congrArg List.length hword).trans h3
  have hv : g.primeFactorsList.reverse=[p 0,p 1,p 2] := three _ hlen
  obtain ⟨pp,hanti,hret⟩ := P4AOriginalFiniteFallbackSelectedSupport.data_of_word hraw p [] hv
  have hU := P4AUpperTaggedParityCompiler.rawSupport_subset_universe _ _ _ _ _ hraw
  have hsub := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe _ _ _ _ hU).1
  have prime (i : Fin 3) : (p i).Prime ∧ ¬p i∣P.N := by
    have hi : p i∈g.primeFactorsList.reverse := by rw [hv]; fin_cases i <;> simp
    have H := mem_roughPrimeUniverse.mp (hsub.subset hi)
    exact ⟨H.2.1,H.2.2.1⟩
  have hh : P.f (history p)=true := by simpa only [oddFirstExitPolicy,Bool.false_or] using hret
  have hc := P4AOriginalFiniteFallbackRange.raw_guard _ (P4AOriginalFiniteFallbackCanonical.bounded P.m)
    _ (P4AOriginalFull87HistoryCore.width_pos P.r) _ (data P.e P.q P.a) he _ P.N
    (by exact_mod_cast hN.le) (history p) hh
  rw [←P4AOriginalThirdFallbackAdmission.pre_eq] at hc
  have hg := (P5Z.PresievedRoughSlotAffineGates.original_upper_prefix_iff_log hN _ p pp hanti).mp hc
  have hc3 := hg.2 (2:Fin 3) (by decide)
  refine ⟨?_,prime,(actualPrimeTupleLog_strictAnti_iff hN p pp).mpr hanti,?_⟩
  · change g.primeFactorsList.reverse.map (tag P.N P.T)=J at hword
    simpa only [hv,List.map_cons,List.map_nil] using hword.symm
  · simpa [P5Z.PresievedRoughSlotAffineGates.cube,P5Z.PresievedRoughSlotAffineGates.prefix,
      Fin.sum_univ_three,Finset.sum_filter,P4AFull87UnionCompilerPayment.top] using hc3

end
end ImbalancedChen.P4BOriginalMediumLowTriple
