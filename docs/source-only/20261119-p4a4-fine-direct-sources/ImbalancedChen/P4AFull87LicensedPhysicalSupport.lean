import ImbalancedChen.P4AFull87CompilerPhysicalPayment
import ImbalancedChen.P5ActualCommonRefinedRange

/-! The original prefix levels, the complete saved/eleven/later sixth,
and the actual finite trimmed eighth all fit the same ordinary ceiling.
Use the S14 ordinary envelope on RAW supports only. The physical tag
and both Rosser beta branches below are the licensed ones. -/
namespace ImbalancedChen.P4AFull87LicensedPhysicalSupport
noncomputable section
open scoped Classical BigOperators
open P4AFull87CompilerChangedPartition
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport
open P4AOriginalCompleteSixthChronology (data currentSixthExponent)
open P4AOriginalFull87FiniteParentCaps (cap5 cap6)
open P4AOriginalFull87FiniteParentPolicy (fifthPolicy level5Exponent)
open P4AOriginalFull87LicensedSixthPolicy (policy sixthPolicy level6Exponent eighthContinuation)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AOriginalFull87HistoryCore (width_pos)
open P5Z.ActualCommonRefinedRange
open P1GuardFrozenFiniteCapAlgebra (clamp clamp_bounds)

abbrev topExponent : ℝ := 299 / 500

private theorem rounded_le (n : ℕ) (x : ℝ) :
    (P1GuardFrozenFiniteCapAlgebra.rounded n x : ℝ) ≤ topExponent := by
  have h := (P4AOriginalFull87FiniteEighthCap.downCap_error n (clamp x)).2
  rw [P1GuardFrozenFiniteCapAlgebra.rounded,Rat.cast_max,Rat.cast_zero]
  apply max_le (by norm_num [topExponent])
  have hc := (clamp_bounds x).2
  dsimp only [VariableEnvelope.cap] at hc
  dsimp only [topExponent]
  linarith [width_pos n]

private theorem cap5_range (P : Parameters) (he : 0 ≤ P.e) (N : ℝ) (pre : List ℕ) :
    cap5 P.n P.e P.q P.om N pre ≤ topExponent := by
  rw [P4AOriginalFull87FiniteParentCaps.cap5_eq_protect]
  exact max_le (originalSeed_le_theta (data P.e P.q P.om) he N pre) (rounded_le _ _)

theorem current_range (P : Parameters) (he : 0 ≤ P.e) (N : ℝ) (pre : List ℕ) :
    currentSixthExponent P.e P.q P.om N pre ≤ topExponent := by
  apply P4AOriginalCompleteSixthChronology.current_le_of_subset_tents
  · exact actualParent5_le_theta (data P.e P.q P.om) he N pre
  · intro m _
    exact (VariableEnvelope.v_le_cap _).trans (by norm_num [VariableEnvelope.cap,topExponent])

private theorem level5_range (P : Parameters) (he : 0 ≤ P.e) (N : ℝ) (pre : List ℕ) :
    level5Exponent P.n P.e P.q P.om N pre ≤ topExponent := by
  unfold level5Exponent
  split
  · exact cap5_range P he N pre
  · exact exponent5_le_theta _ he N pre

private theorem level6_range (P : Parameters) (he : 0 ≤ P.e) (N : ℝ) (pre : List ℕ) :
    level6Exponent P.n P.e P.q P.om N pre ≤ topExponent := by
  unfold level6Exponent
  split
  · apply (P4AOriginalSixthLicensedFilter.licensedCap_le_old P.n P.e P.q P.om N pre).trans
    exact max_le (cap5_range P he N _) (rounded_le _ _)
  · exact current_range P he N pre

private theorem eighth_range (P : Parameters) (hd : 0 < P.delta) (N : ℝ)
    (pre : List ℕ) (a : ℚ) (ha : selectedCap P.delta P.n N pre = some a) :
    (a : ℝ) ≤ topExponent := by
  obtain ⟨c,_,ht,rfl⟩ := P4AOriginalFull87FiniteEighthPolicy.selectedCap_some_spec
    P.delta P.n N pre a ha
  have hs := P4AOriginalFull87StrictActionTrim.trim_subset_source c hd ht
  have hc := P4AOriginalFull87SourceDictionary.source_physical_ceiling hs
  have hh := (P4AOriginalFull87FiniteEighthCap.downCap_error P.n
    (P4AOriginalFull87SourceDictionary.newCap c (P4AOriginalFull87SourceDispatch.point8 N pre))).2
  unfold P4AOriginalFull87FiniteEighthCap.finiteCap
  exact le_trans hh (by dsimp only [topExponent]; linarith [width_pos P.n])

theorem keep_implies_ordinary (P : Parameters) (he : 0 ≤ P.e) (hd : 0 < P.delta)
    (N : ℕ) (hN : (1 : ℝ) ≤ N) (pre : List ℕ) (h : P.keep N pre = true) :
    ordinaryRosserPrefixAdmissible false ((N : ℝ)^topExponent) pre := by
  have mono (a : ℝ) (ha : a ≤ topExponent)
      (hp : ordinaryParityRosserPolicy false ((N : ℝ)^a) false pre = true) :
      ordinaryRosserPrefixAdmissible false ((N : ℝ)^topExponent) pre := by
    apply ordinaryRosserPrefixAdmissible_mono false pre (Real.rpow_le_rpow_of_exponent_le hN ha)
    simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using hp
  have fifth (hp : fifthPolicy P.n P.e P.q P.om (N : ℝ) false pre = true) :
      ordinaryRosserPrefixAdmissible false ((N : ℝ)^topExponent) pre := by
    unfold fifthPolicy firstExitDepthSplicePolicy at hp
    split at hp
    · have hh := common3_implies_root (data P.e P.q P.om) he (N : ℝ) hN false pre hp
      simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy,topExponent] using hh
    · exact mono _ (level5_range P he (N : ℝ) _) hp
  have sixth (hp : sixthPolicy P.n P.e P.q P.om (N : ℝ) false pre = true) :
      ordinaryRosserPrefixAdmissible false ((N : ℝ)^topExponent) pre := by
    unfold sixthPolicy firstExitDepthSplicePolicy at hp
    split at hp
    · exact fifth hp
    · exact mono _ (level6_range P he (N : ℝ) _) hp
  change policy P.delta P.n P.e P.q P.om (N : ℝ) false pre = true at h
  unfold policy firstExitDepthSplicePolicy at h
  split at h
  · exact sixth h
  · cases hs : selectedCap P.delta P.n (N : ℝ) pre with
    | none => exact sixth (by simpa only [eighthContinuation,hs] using h)
    | some a =>
      apply mono _ (eighth_range P hd (N : ℝ) pre a hs)
      simpa only [eighthContinuation,hs] using h

/-- The one-cap factorization is an identity of raw Boolean predicates.
It is used solely for the ordinary support and rank theorem. -/
private theorem root_filter (P : Parameters) (he : 0 ≤ P.e) (hd : 0 < P.delta)
    (N : ℕ) (hN : (1 : ℝ) ≤ N) :
    P4AFiniteCapTaggedConstructor.keep (fun _ : Fin 1 => topExponent)
      (fun _ => 0) (P.keep N) N = P.keep N := by
  funext pre
  by_cases h : P.keep N pre = true
  · have hp := keep_implies_ordinary P he hd N hN pre h
    simpa [P4AFiniteCapTaggedConstructor.keep,P4AFiniteCapTaggedConstructor.boundedCap,
      topExponent,h] using hp
  · cases hh : P.keep N pre <;> simp [P4AFiniteCapTaggedConstructor.keep,hh] at h ⊢

theorem raw_rank_range (P : Parameters) (he : 0 ≤ P.e) (hd : 0 < P.delta)
    (N cap : ℕ) (hN : 2 ≤ N) (omega z : ℝ) (hw : 0 < omega) {d : ℕ}
    (hm : d ∈ rawSupport (P.keep N) N cap ((N : ℝ)^omega) z) :
    d.primeFactorsList.length < J0 omega ∧ (d : ℝ) < (N : ℝ)^topExponent := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  rw [← root_filter P he hd N hn] at hm
  exact ⟨P4AFiniteCapTaggedConstructor.raw_rank_lt _ _ _ omega hw N cap hN z hm,
    P4AFiniteCapTaggedConstructor.raw_support_lt _ _ _ N cap hN _ z hm⟩

/-- Every actual occupied mixed cell has a retained witness of the same
rank, including when the given changed modulus itself was rejected. -/
theorem changed_rank_lt (P : Parameters) (he : 0 ≤ P.e) (hd : 0 < P.delta)
    (tags : ℕ → List Bool) (N cap : ℕ) (hN : 2 ≤ N) (omega z tau : ℝ)
    (hw : 0 < omega) {d : ℕ} (hm : d ∈ universe N cap ((N : ℝ)^omega) z)
    (hc : changed (P.keep N) tags N cap ((N : ℝ)^omega) z tau d) :
    d.primeFactorsList.length < J0 omega := by
  obtain ⟨f,hf⟩ := (changed_implies_crossing _ _ _ _ _ _ _ hm hc).1
  obtain ⟨hcell,hraw⟩ := Finset.mem_inter.mp hf
  rw [← cell_rank_preserved _ _ _ _ _ _ hcell]
  exact (raw_rank_range P he hd N cap hN omega z hw hraw).1

private theorem rough_range (P : Parameters) (he : 0 ≤ P.e) (hd : 0 < P.delta)
    (tags : ℕ → List Bool) (N cap : ℕ) (hN : 2 ≤ N) (omega z tau : ℝ)
    (hw : 0 < omega) (ht : 0 < tau) {d : ℕ}
    (hc : coefficient (P.keep N) tags N cap ((N : ℝ)^omega) z tau d ≠ 0) :
    (d : ℝ) < (N : ℝ)^(topExponent + tau*(J0 omega : ℝ)) := by
  obtain ⟨f,hraw,hcell,_,_⟩ := active_has_raw_witness _ _ _ _ _ _ _ hc
  obtain ⟨hr,hf⟩ := raw_rank_range P he hd N cap hN omega z hw hraw
  have hr' : (d.primeFactorsList.length : ℝ) ≤ (J0 omega : ℝ) := by
    rw [← cell_rank_preserved _ _ _ _ _ _ hcell]
    exact_mod_cast hr.le
  have hm : d ∈ universe N cap ((N : ℝ)^omega) z := by
    by_contra h
    exact hc (by simp only [coefficient,if_neg h])
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  calc
    _ ≤ _ := same_cell_product_le _ N cap hN _ z tau ht hm hcell
    _ < (N : ℝ)^(tau*(d.primeFactorsList.length : ℝ)) * (N : ℝ)^topExponent :=
      mul_lt_mul_of_pos_left hf (Real.rpow_pos_of_pos hn0 _)
    _ = (N : ℝ)^(topExponent+tau*(d.primeFactorsList.length : ℝ)) := by
      rw [Real.rpow_add hn0]
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le
      (add_le_add_left (mul_le_mul_of_nonneg_left hr' ht.le) _)

/-- The nonzero *same tagged physical rho* has the manuscript's strict
599/1000 support, with both small-beta slopes and actual eighth fallback.
The common width restriction can be intersected with the compiler mesh. -/
theorem licensed_physical_range (P : Parameters) (he : 0 ≤ P.e) (hd : 0 < P.delta)
    (omega ell : ℝ) (hw : 0 < omega) (hl : ell < 1/1000) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
    ell + tau*(J0 omega : ℝ) < 1/1000 ∧
    ∀ (N cap : ℕ), 2 ≤ N → ∀ (z : ℝ) (tags : ℕ → List Bool) (q : ℕ),
    P4AUpperTaggedBetaAttachment.rho (P.keep N) tags N cap ((N : ℝ)^omega) z tau
      ((N : ℝ)^ell) q ≠ 0 → (q : ℝ) < (N : ℝ)^(599/1000 : ℝ) := by
  let J := (J0 omega : ℝ)
  let tau0 := (1/1000-ell)/(2*(J+1))
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have hden : 0 < 2*(J+1) := by positivity
  have hbudget := div_mul_cancel₀ (1/1000-ell) hden.ne'
  refine ⟨tau0,div_pos (sub_pos.mpr hl) hden,?_⟩
  intro tau ht hsmall
  have htime : ell+tau*J < 1/1000 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hJ
    have heq : tau0*(2*(J+1)) = 1/1000-ell := hbudget
    nlinarith [show 0 < tau0 from ht.trans_le hsmall, mul_nonneg (ht.trans_le hsmall).le hJ]
  refine ⟨htime,?_⟩
  intro N cap hN z tags q hq
  let w := (N : ℝ)^omega
  let L := (N : ℝ)^ell
  have hm : q ∈ P4AUpperTaggedBetaAttachment.support N cap w z := by
    by_contra hx
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hx)
  obtain ⟨⟨a,d⟩,had,hprod⟩ := Finset.mem_image.mp hm
  obtain ⟨ha,hh⟩ := Finset.mem_product.mp had
  have hv := P4AUpperTaggedBetaAttachment.rho_at_product (P.keep N) tags N cap w z tau L ha hh
  have hpair : coefficient (P.keep N) tags N cap w z tau d *
      (if 0 ≤ coefficient (P.keep N) tags N cap w z tau d then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) ≠ 0 := by rw [← hv,hprod]; exact hq
  obtain ⟨hc,hb⟩ := mul_ne_zero_iff.mp hpair
  have haL : (a : ℝ) < L := by
    split_ifs at hb
    · exact (actualSmallRosserPlus_active hb).2.1
    · exact (actualSmallRosserMinus_active hb).2.1
  have hrough := rough_range P he hd tags N cap hN omega z tau hw ht hc
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  calc
    (q : ℝ) = (a : ℝ)*(d : ℝ) := by rw [← hprod,Nat.cast_mul]
    _ ≤ L*(d : ℝ) := mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg d)
    _ < L*(N : ℝ)^(topExponent+tau*J) :=
      mul_lt_mul_of_pos_left hrough (Real.rpow_pos_of_pos hn0 ell)
    _ = (N : ℝ)^(ell+(topExponent+tau*J)) := (Real.rpow_add hn0 _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hn.le
      dsimp only [topExponent]
      linarith

end
end ImbalancedChen.P4AFull87LicensedPhysicalSupport
