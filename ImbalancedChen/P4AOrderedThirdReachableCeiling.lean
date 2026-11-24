import ImbalancedChen.P4AOrderedThirdPhysicalSplit

namespace ImbalancedChen.P4AOrderedThirdReachableCeiling
noncomputable section
open scoped Classical BigOperators
open P4AOriginalOrderedThirdFullPolicy
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AUpperTaggedParityCompiler P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AHeldTaggedCompilerSupport (same_cell_product_le)
open P4AUpperTaggedFirstPrefixDisagreement (decisionAt decisionAt_eq_prefix polarityAfter)
open P4AOrderedThirdActualRoughGeometry (every_decision high_raw_root)
open P4AOrderedThirdGlobalRange (stages selected_le)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)

private theorem accepted_iff_decisions {α : Type*} (P : Bool→List α→Bool) (xs pre : List α) (pos : Bool) :
    FirstExitValidSelection P pre pos xs ↔ ∀ k<xs.length,decisionAt P pre pos xs k=true := by
  refine ⟨fun hh k hk => every_decision P xs pre pos hh k hk,?_⟩
  induction xs generalizing pre pos with
  | nil => simp [FirstExitValidSelection]
  | cons a xs ih =>
    intro hh
    exact ⟨hh 0 (by simp),ih _ _ (fun k hk => hh (k+1) (by simpa))⟩

theorem high_guard (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (he : 0≤d.e)
    (omega N : ℝ) (hN : 1≤N) (p : List ℕ) (hl : 3≤p.length)
    (hseed : (current d omega N p).scalar≤VariableEnvelope.cap)
    (h : policy delta n d omega N false p=true) :
    ordinaryRosserPrefixAdmissible false (N^VariableEnvelope.cap) p := by
  let R := current d omega N p
  obtain ⟨h5,h6,hq,hc⟩ := stages R d he N VariableEnvelope.cap le_rfl hseed n
  have mono (t : ℝ) (ht : t≤VariableEnvelope.cap) (hp : ordinaryParityRosserPolicy false (N^t) false p=true) :=
    ordinaryRosserPrefixAdmissible_mono false p (Real.rpow_le_rpow_of_exponent_le hN ht)
      (by simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using hp :
        ordinaryRosserPrefixAdmissible false (N^t) p)
  have hb (hk : base R d N false p=true) :
      ordinaryRosserPrefixAdmissible false (N^VariableEnvelope.cap) p := by
    exact mono _ hseed (by simpa [base,show ¬p.length≤2 by omega] using hk)
  have hcommon (hk : common R d N false p=true) :
      ordinaryRosserPrefixAdmissible false (N^VariableEnvelope.cap) p := by
    simp only [common,Bool.or_eq_true] at hk
    rcases hk with hk|hk
    · exact hb hk
    · split_ifs at hk <;> first | exact hb hk | exact mono _ (VariableEnvelope.v_le_cap _) hk
  have hf (hk : five R d N n false p=true) :
      ordinaryRosserPrefixAdmissible false (N^VariableEnvelope.cap) p := by
    unfold five firstExitDepthSplicePolicy at hk
    split at hk
    · exact hcommon hk
    · apply mono _ _ hk
      split <;> first | exact hq _ | exact h5 _
  have hs (hk : six R d N n false p=true) :
      ordinaryRosserPrefixAdmissible false (N^VariableEnvelope.cap) p := by
    unfold six firstExitDepthSplicePolicy at hk
    split at hk
    · exact hf hk
    · apply mono _ _ hk
      split <;> first | exact hc _ | exact h6 _
  change eight R d N delta n false p=true at h
  unfold eight firstExitDepthSplicePolicy at h
  split at h
  · exact hs h
  · cases hv : selectedCap delta n N p with
    | none => exact hs (by simpa only [hv] using h)
    | some a => exact mono _ (selected_le hd n N p hv) (by simpa only [hv] using h)

theorem raw_strict (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (he : 0≤d.e)
    {N C x : ℕ} (hN : 1<N) {omega : ℝ} (hw : 0≤omega)
    (hx : x∈rawSupport (policy delta n d omega N false) N C ((N:ℝ)^omega) ((N:ℝ)^(19/96:ℝ))) :
    (x:ℝ)<(N:ℝ)^VariableEnvelope.cap := by
  let F := policy delta n d omega N false
  let w := (N:ℝ)^omega
  let z := (N:ℝ)^(19/96:ℝ)
  let R := (N:ℝ)^VariableEnvelope.cap
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hR : 1<R := Real.one_lt_rpow hn (by norm_num [VariableEnvelope.cap])
  obtain ⟨hU,hvalid⟩ := (P4AUpperTaggedMixedWallPayment.raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hx
  obtain ⟨hsub,hprod⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N C w z hU
  have hv : FirstExitValidSelection (ordinaryParityRosserPolicy false R) [] true x.primeFactorsList.reverse := by
    apply (accepted_iff_decisions _ _ _ _).mpr
    intro k hk
    let r := k+1
    have hr : r≤x.primeFactorsList.length := by simpa [r] using hk
    have hraw := every_decision (oddFirstExitPolicy F) _ [] true hvalid k hk
    rw [decisionAt_eq_prefix _ _ _ _ _ hk,List.append_nil,← canonicalPrefix_ofFn hr,
      P4AFull87OrdinaryAdmissionDeletion.reversed_prefix x r hr] at hraw ⊢
    cases hpar : polarityAfter true (k+1) with
    | true => exact ordinaryParityRosserPolicy_upper_even _ _
    | false =>
      have hf : F (rosserAncestor r x.primeFactorsList)=true := by simpa [oddFirstExitPolicy,hpar] using hraw
      suffices H : ordinaryRosserPrefixAdmissible false R (rosserAncestor r x.primeFactorsList) by
        simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using H
      by_cases h3 : 3≤r
      · obtain ⟨j,_,_,hcap,hbound⟩ := high_raw_root delta n d he hN hw hx (h3.trans hr)
        apply high_guard delta hd n d he omega N hn.le _ (by simpa [Nat.min_eq_left hr] using h3) _ hf
        rw [current_ancestor d omega N x.primeFactorsList r h3,hcap]
        have hnon : (0:ℝ)≤d.e := by exact_mod_cast he
        linarith
      · have hr1 : r=1 := by
          change ¬3≤k+1 at h3
          have : k≤1 := by omega
          interval_cases k <;> simp [polarityAfter,r] at hpar ⊢
        let p := canonicalPrefix 1 x
        have hr' : 1≤x.primeFactorsList.length := by omega
        have ht := (canonical_prefix_tail_data hU hr').1
        have hp := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp ht
        have hu := (mem_logPrimeBox.mp hp.2 (0:Fin 1)).2
        have hc : actualPrimeTupleLog N p∈P5Z.PresievedRoughSlotAffineGates.region 1 VariableEnvelope.cap := by
          constructor
          · simp only [Fin.sum_univ_one]
            dsimp [VariableEnvelope.cap]; linarith
          · intro i hi
            fin_cases i
            simp [P5Z.PresievedRoughSlotAffineGates.cube,P5Z.PresievedRoughSlotAffineGates.prefix,
              VariableEnvelope.cap]
            <;> linarith
        rw [hr1,← P4AFull87OrdinaryAdmissionDeletion.reversed_prefix x 1 hr']
        exact (P5Z.PresievedRoughSlotAffineGates.original_upper_prefix_iff_log hN _ p
          (canonicalPrefix_pos hU hr') (canonicalPrefix_strictAnti hU hr')).mpr hc
  have hh := (mem_firstExitRetainedModuli_iff_validSelection (ordinaryParityRosserPolicy false R) _ x).mpr
    ⟨x.primeFactorsList.reverse,hsub,hv,hprod⟩
  rw [ordinaryParityRosserRetainedModuli_eq false R hR _ (roughPrimeUniverse_pairwise_gt N C w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) (by simp)] at hh
  exact ((mem_ordinaryRosserRetainedModuli_iff false R hR _ (roughPrimeUniverse_pairwise_gt N C w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) x).mp hh).2.1

theorem physical_inflation (delta : ℝ) (hd : 0<delta) (n : ℕ) (D : OriginalData) (he : 0≤D.e)
    {N c q : ℕ} (hN : 2≤N) (omega ell tau : ℝ) (hw : 0<omega) (ht : 0<tau)
    (hq : P4AUpperTaggedBetaAttachment.rho (policy delta n D omega N false) (fun _ => []) N c
      ((N:ℝ)^omega) ((N:ℝ)^(19/96:ℝ)) tau ((N:ℝ)^ell) q≠0) :
    (q:ℝ)<(N:ℝ)^(VariableEnvelope.cap+tau*(P4AHeldTaggedCompilerSupport.J0 omega:ℝ)+ell) := by
  let f := policy delta n D omega N false
  let w := (N:ℝ)^omega
  let z := (N:ℝ)^(19/96:ℝ)
  let L := (N:ℝ)^ell
  have hm : q∈P4AUpperTaggedBetaAttachment.support N c w z := by
    by_contra hx
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hx)
  obtain ⟨⟨b,x⟩,hpair,hprod⟩ := Finset.mem_image.mp hm
  obtain ⟨hb,hx⟩ := Finset.mem_product.mp hpair
  have hval := P4AUpperTaggedBetaAttachment.rho_at_product f (fun _ => []) N c w z tau L hb hx
  have hnon : coefficient f (fun _ => []) N c w z tau x*
      (if 0≤coefficient f (fun _ => []) N c w z tau x then actualSmallRosserPlus N c w L b
       else actualSmallRosserMinus N c w L b)≠0 := by rw [← hval,hprod]; exact hq
  obtain ⟨hc,hs⟩ := mul_ne_zero_iff.mp hnon
  have hbL : (b:ℝ)<L := by
    split_ifs at hs
    · exact (actualSmallRosserPlus_active hs).2.1
    · exact (actualSmallRosserMinus_active hs).2.1
  obtain ⟨y,hy,hcell,_,_⟩ := active_has_raw_witness _ _ _ _ _ _ _ hc
  have hraw := raw_strict delta hd n D he (by omega) hw.le hy
  have hr := (P4AOrderedThirdGlobalRange.raw_range delta hd n D he omega N c hN omega z hw hy).1
  have hj : (x.primeFactorsList.length:ℝ)≤P4AHeldTaggedCompilerSupport.J0 omega := by
    rw [← cell_rank_preserved _ _ _ _ _ _ hcell]
    exact_mod_cast hr.le
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hpos := zero_lt_one.trans hn
  have hxB := same_cell_product_le _ N c hN w z tau ht hx hcell
  have hrough : (x:ℝ)<(N:ℝ)^(VariableEnvelope.cap+tau*(P4AHeldTaggedCompilerSupport.J0 omega:ℝ)) := by
    calc
      _ ≤ _ := hxB
      _ < (N:ℝ)^(tau*(x.primeFactorsList.length:ℝ))*(N:ℝ)^VariableEnvelope.cap :=
        mul_lt_mul_of_pos_left hraw (Real.rpow_pos_of_pos hpos _)
      _ = (N:ℝ)^(VariableEnvelope.cap+tau*(x.primeFactorsList.length:ℝ)) := by rw [Real.rpow_add hpos]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le (add_le_add_left (mul_le_mul_of_nonneg_left hj ht.le) _)
  calc
    (q:ℝ)=(x:ℝ)*(b:ℝ) := by rw [←hprod,Nat.cast_mul]; ring
    _ ≤ (x:ℝ)*L := mul_le_mul_of_nonneg_left hbL.le (Nat.cast_nonneg _)
    _ < _ := by rw [Real.rpow_add hpos]; exact mul_lt_mul_of_pos_right hrough (Real.rpow_pos_of_pos hpos ell)

end
end ImbalancedChen.P4AOrderedThirdReachableCeiling
