import ImbalancedChen.P4AFull87DataCompilerReads
import ImbalancedChen.P4AFull87PhysicalReserveFromRate
import ImbalancedChen.P4AOriginalNewFifthUnion

/-! Same full87 policy as the union-fifth ordinary gain. Its actual
coarse scalar reads are taken from the enlarged fifth bank and its
resulting licensed sixth. All remaining words are the genuine historical
ones on that bank. No cut at any native affine-sign test is appended. -/
namespace ImbalancedChen.P4AFull87UnionCompilerPayment
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedFirstPrefixDisagreement P4AHeldTaggedCompilerSupport
open P4AUpperTaggedFrozenAdmissionCatalogue P4AFull87NativeAdmissionFamilies
open P4AFull87OrdinaryAdmissionDeletion P4AFull87NativeThirdProgram
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87DataPolicy P4AFull87DataCompilerReads
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AFull87PhysicalReserveFromRate (Paid WallRate)
open P5Z.ActualCommonRefinedRange

abbrev top : ℝ := 299/500
abbrev keep (delta : ℝ) (n : ℕ) (d : OriginalData) (N : ℕ) := policy delta n d (N:ℝ) false

private theorem rounded_le (n : ℕ) (x : ℝ) :
    (P1GuardFrozenFiniteCapAlgebra.rounded n x : ℝ) ≤ top := by
  have h := (P4AOriginalFull87FiniteEighthCap.downCap_error n
    (P1GuardFrozenFiniteCapAlgebra.clamp x)).2
  rw [P1GuardFrozenFiniteCapAlgebra.rounded,Rat.cast_max,Rat.cast_zero]
  apply max_le (by norm_num [top])
  have hc := (P1GuardFrozenFiniteCapAlgebra.clamp_bounds x).2
  dsimp only [VariableEnvelope.cap] at hc
  dsimp only [top]
  linarith [P4AOriginalFull87HistoryCore.width_pos n]

private theorem eighth_le (delta : ℝ) (hd : 0 < delta) (n : ℕ) (N : ℝ) (pre : List ℕ)
    (a : ℚ) (ha : selectedCap delta n N pre=some a) : (a:ℝ)≤top := by
  obtain ⟨c,_,ht,rfl⟩ := P4AOriginalFull87FiniteEighthPolicy.selectedCap_some_spec delta hd n N pre a ha
  have hs := P4AOriginalFull87StrictActionTrim.trim_subset_source c hd ht
  have hc := P4AOriginalFull87SourceDictionary.source_physical_ceiling hs
  have hh := (P4AOriginalFull87FiniteEighthCap.downCap_error n
    (P4AOriginalFull87SourceDictionary.newCap c (P4AOriginalFull87SourceDispatch.point8 N pre))).2
  unfold P4AOriginalFull87FiniteEighthCap.finiteCap
  dsimp only [top]
  linarith [P4AOriginalFull87HistoryCore.width_pos n]

theorem raw_guard (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (he : 0≤d.e)
    (N : ℕ) (hN : (1:ℝ) ≤ N) (pre : List ℕ) (h : keep delta n d N pre=true) :
    ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) pre := by
  have cap5le (xs : List ℕ) : cap5 n d N xs ≤ top := by
    rw [cap5_eq_protect]
    exact max_le (originalSeed_le_theta d he N xs) (rounded_le _ _)
  have fifthExp (xs : List ℕ) : level5Exponent n d N xs ≤ top := by
    unfold level5Exponent
    split
    · exact cap5le xs
    · exact exponent5_le_theta d he N xs
  have sixthExp (xs : List ℕ) : level6Exponent n d N xs ≤ top := by
    unfold level6Exponent
    split
    · apply P1OriginalVariableFourthContinuation.finiteMax_le _ _ _ _ _ (cap5le _)
      intro _ _ _
      exact rounded_le _ _
    · apply current_le_of_subset_tents _ _ _ _ (actualParent5_le_theta d he N xs)
      intro m _
      exact (VariableEnvelope.v_le_cap _).trans (by norm_num [VariableEnvelope.cap,top])
  have mono (a : ℝ) (ha : a≤top)
      (hp : ordinaryParityRosserPolicy false ((N:ℝ)^a) false pre=true) :
      ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) pre := by
    apply ordinaryRosserPrefixAdmissible_mono false pre (Real.rpow_le_rpow_of_exponent_le hN ha)
    simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using hp
  have fifth (hp : fifthPolicy n d N false pre=true) :
      ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) pre := by
    unfold fifthPolicy firstExitDepthSplicePolicy at hp
    split at hp
    · simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy,top] using common3_implies_root d he N hN false pre hp
    · exact mono _ (fifthExp _) hp
  have sixth (hp : sixthPolicy n d N false pre=true) :
      ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) pre := by
    unfold sixthPolicy firstExitDepthSplicePolicy at hp
    split at hp
    · exact fifth hp
    · exact mono _ (sixthExp _) hp
  change policy delta n d (N:ℝ) false pre=true at h
  unfold policy firstExitDepthSplicePolicy at h
  split at h
  · exact sixth h
  · cases hs : selectedCap delta n N pre with
    | none => exact sixth (by simpa only [eighthContinuation,hs] using h)
    | some a => exact mono _ (eighth_le delta hd n N pre a hs)
        (by simpa only [eighthContinuation,hs] using h)

theorem raw_range (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (he : 0≤d.e)
    (N cap : ℕ) (hN : 2≤N) (omega z : ℝ) (hw : 0<omega) {x : ℕ}
    (hm : x ∈ rawSupport (keep delta n d N) N cap ((N:ℝ)^omega) z) :
    x.primeFactorsList.length < J0 omega ∧ (x:ℝ)<(N:ℝ)^top := by
  let F := keep delta n d N
  have hroot : P4AFiniteCapTaggedConstructor.keep (fun _ : Fin 1 => top)
      (fun _ => 0) F N = F := by
    funext pre
    by_cases h : F pre=true
    · have hp := raw_guard delta hd n d he N (by exact_mod_cast (show 1≤N by omega)) pre h
      simpa [P4AFiniteCapTaggedConstructor.keep,P4AFiniteCapTaggedConstructor.boundedCap,top,h] using hp
    · cases hh : F pre <;> simp [P4AFiniteCapTaggedConstructor.keep,hh] at h ⊢
  change x ∈ rawSupport F N cap ((N:ℝ)^omega) z at hm
  rw [← hroot] at hm
  exact ⟨P4AFiniteCapTaggedConstructor.raw_rank_lt _ _ _ omega hw N cap hN z hm,
    P4AFiniteCapTaggedConstructor.raw_support_lt _ _ _ N cap hN _ z hm⟩

theorem changed_seen (delta : ℝ) (hd : 0<delta) (n : ℕ) (D : OriginalData) (he : 0≤D.e)
    (N cap : ℕ) (hN : 2 ≤ N) (omega v tau : ℝ)
    (hw : 0 < omega) (hv : omega ≤ v) (ht : 0 < tau) {x : ℕ}
    (hx : x ∈ universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (hc : changed (keep delta n D N) (tag delta hd n D N) N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau x) :
    Seen (complete D) (scalars n D) N cap (J0 omega) omega v tau x := by
  let F := keep delta n D N
  let tags := tag delta hd n D N
  have hJ : x.primeFactorsList.length < J0 omega := by
    obtain ⟨u,hu⟩ := (changed_implies_crossing F tags _ _ _ _ _ hx hc).1
    obtain ⟨hu1,hu2⟩ := Finset.mem_inter.mp hu
    rw [← cell_rank_preserved _ _ _ _ _ _ hu1]
    exact (raw_range delta hd n D he N cap hN omega _ hw hu2).1
  obtain ⟨y,hy,heq,_,k,hk,ho,hneq,_⟩ := changed_first_actual_odd_prefix F tags _ _ _ _ _ hx hc
  let r := k+1
  have hr : r ≤ x.primeFactorsList.length := hk
  have hry : r ≤ y.primeFactorsList.length := by rw [cell_rank_preserved _ _ _ _ _ _ hy]; exact hr
  have rev (z : ℕ) (hz : r≤z.primeFactorsList.length) :
      (z.primeFactorsList.reverse.take r).reverse=rosserAncestor r z.primeFactorsList := by
    rw [← canonicalPrefix_ofFn hz,reversed_prefix z r hz]
  rw [rev x hr,rev y hry] at hneq
  obtain ⟨hread,hhist⟩ := read_tag hd heq
  let q := reads delta hd n D N x
  have hvx := policy_read delta hd n D N r x hr
  have hvy := policy_read delta hd n D N r y hry
  rw [hread] at hvy
  have hdiff : evaluate D N r x (mode r q) ≠ evaluate D N r y (mode r q) :=
    fun e => hneq (hvx.trans (e.trans hvy.symm))
  cases hmode : mode r q with
  | common =>
    have ha := (mode_bounds r q).1 hmode
    have hsame := (early_agree D N x y r (by omega) hr hry hhist.symm ho).1
    exact False.elim (hdiff (by simpa only [hmode,evaluate] using hsame))
  | oldFifth =>
    have ha := (mode_bounds r q).2.1 hmode
    have hsame := (early_agree D N x y r ha hr hry hhist.symm ho).2
    exact False.elim (hdiff (by simpa only [hmode,evaluate] using hsame))
  | fixed a =>
    apply constant_seen _ _ N cap _ (by omega) omega v tau hw hv ht tags hx hy hr (hr.trans hJ.le) a.property
    intro h
    exact hdiff (by simpa only [hmode,evaluate] using congrArg (fun q : Prop => decide q) (propext h))
  | native =>
    have h6 := (mode_bounds r q).2.2 hmode
    apply native_seen _ _ N cap _ (by omega) omega v tau hw hv ht tags hx hy h6.le hr (hr.trans hJ.le)
    rw [data_complete_on_modulus D N cap x (by omega) omega v hx (h6.le.trans hr),
      data_complete_on_modulus D N cap y (by omega) omega v (Finset.mem_filter.mp hy).1 (h6.le.trans hry)]
    intro h
    exact hdiff (by simpa only [hmode,evaluate] using congrArg (fun q : Prop => decide q) (propext h))

abbrev count (n : ℕ) (d : OriginalData) := Fintype.card (Family (complete d) (scalars n d))

theorem actual_rate (delta : ℝ) (hd : 0<delta) (n : ℕ) (D : OriginalData) (he : 0≤D.e) :
    WallRate (count n D) (keep delta n D) (tag delta hd n D) := by
  obtain ⟨K,E,hK,hE,hh⟩ := P4AFull87FiniteWallRate.exists_finite_rate
    (ι := Family (complete D) (scalars n D))
  refine ⟨K,E,hK,hE,?_⟩
  intro B hB N cap hN hEven omega v tau hw hv hv1 ht h3 hlog
  apply hh B hB N cap (by omega) hEven omega v tau hw hv hv1 ht.le h3 hlog
    (bank (complete D) (scalars n D) N (J0 omega))
  intro x hx
  obtain ⟨hU,hc⟩ := Finset.mem_filter.mp hx
  exact changed_seen delta hd n D he N cap hN omega v tau hw hv ht hU hc

theorem union_paid (delta : ℝ) (hd : 0 < delta) (n : ℕ) (e : ℚ) (he : 0≤e) (q : ℕ) (om : ℝ)
    (nu r u_c epsilonMax : ℝ) (hnu : 0<nu) (hr : 0<r) (hv : nu*r≤1)
    (hu : 0<u_c) (hmax : 0<epsilonMax) :
    let D := P4AOriginalNewFifthUnion.data e q om
    Paid (fun N => P4AOriginalFull87DataPolicy.policy delta n D (N:ℝ) false)
      (tag delta hd n D) nu r u_c epsilonMax :=
  P4AFull87PhysicalReserveFromRate.of_wallRate
    (actual_rate delta hd n (P4AOriginalNewFifthUnion.data e q om) he)
    nu r u_c epsilonMax hnu hr hv hu hmax

end
end ImbalancedChen.P4AFull87UnionCompilerPayment
