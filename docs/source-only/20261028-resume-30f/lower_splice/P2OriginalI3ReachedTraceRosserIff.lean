import ImbalancedChen.P2OriginalLowerRosserCubeInsertion
import ImbalancedChen.P2OriginalI3ActualFrozenTraceLevel
import ImbalancedChen.P2OriginalI3ActualSmallRosserAttachment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Derive provider admissibility from actual reached rank3 seed tests, then
prove the cumulative Trace/provider iff on all sorted prime descendants
at its actual frozen total level. No missing provider property is a premise
of the actual W-prefix receiver theorem.
-/
namespace ImbalancedChen.P2OriginalI3ReachedTraceRosserIff
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerWJointTraceSplice
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment
open P2OriginalI3ActualFrozenTraceLevel
open P2OriginalLowerRosserCubeInsertion

private theorem ordinary_three_from_seed_cubes (Q : ℝ) (p1 p2 p3 : ℕ)
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime)
    (hsort : [p3,p2,p1].Pairwise (· < ·))
    (hfirst : (p1 : ℝ)^2 < Q) (hsecond : (p1 : ℝ)*(p2 : ℝ)^3 < Q) :
    ordinaryRosserPrefixAdmissible true Q [p3,p2,p1] := by
  have hp11 : (1 : ℝ) ≤ p1 := by exact_mod_cast hp1.one_le
  have hp1Q : (p1 : ℝ) < Q := by nlinarith
  have hQ : 1 < Q := lt_of_le_of_lt hp11 hp1Q
  have h21 : p2 < p1 := (List.pairwise_cons.mp
    (List.pairwise_cons.mp hsort).2).1 p1 (by simp)
  have h32 : p3 < p2 := (List.pairwise_cons.mp hsort).1 p2 (by simp)
  have hp2Q : (p2 : ℝ) < Q := lt_trans (by exact_mod_cast h21) hp1Q
  have hp3Q : (p3 : ℝ) < Q := lt_trans (by exact_mod_cast h32) hp2Q
  have hnil := ordinaryRosserPrefixAdmissible_nil true hQ
  have h1 : ordinaryRosserPrefixAdmissible true Q [p1] := by
    apply (ordinary_lower_cons_iff Q p1 [] hp1 hp1Q (by simp)).mpr
    exact ⟨hnil,by norm_num⟩
  have h2 : ordinaryRosserPrefixAdmissible true Q [p2,p1] := by
    apply (ordinary_lower_cons_iff Q p2 [p1] hp2 hp2Q
      (List.pairwise_cons.mp hsort).2).mpr
    exact ⟨h1,by intro _; simpa using hsecond⟩
  apply (ordinary_lower_cons_iff Q p3 [p2,p1] hp3 hp3Q hsort).mpr
  exact ⟨h2,by norm_num⟩

/-- Both integer cubes are derived from the actual seed Trace. -/
theorem actual_seed_three_admissible {mesh : ℕ} (D : ThirdStage mesh)
    (N p1 p2 p3 : ℕ) (hN : 1 < (N : ℝ))
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime)
    (hsort : [p3,p2,p1].Pairwise (· < ·))
    (hret : seedRetain D N [p3,p2,p1] = true) :
    ordinaryRosserPrefixAdmissible true ((N : ℝ)^(baselineCap D.rho)) [p3,p2,p1] := by
  have ht : retainEven D.seedPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N [p2,p1] = true := by
    exact (odd_rank_bypass _ _ _ _ N p3 [p2,p1] (by simp) (by norm_num)).mp hret
  have hg := (baseline_two_tests D.seedPlan _ _ _ N p1 p2).mp ht
  have hpN : 0 < (N : ℝ) := zero_lt_one.trans hN
  have hpow : (N : ℝ)^(2*coordinate N p1) = (p1 : ℝ)^2 := by
    rw [mul_comm (2 : ℝ) (coordinate N p1), Real.rpow_mul hpN.le,
      coordinate_power hN hp1.pos]
    norm_num
  have hfirst : (p1 : ℝ)^2 < (N : ℝ)^(baselineCap D.rho) := by
    rw [← hpow]
    exact (Real.rpow_lt_rpow_left_iff hN).mpr hg.1
  have hlogcube : (physicalWord N [p1]).sum + 3*coordinate N p2 < baselineCap D.rho := by
    simpa [physicalWord] using hg.2
  have hsecond := (cube_test_integer_iff hN hp2.pos [p1]
    (by intro q hq; rcases List.mem_singleton.mp hq with rfl; exact hp1.pos)
    (baselineCap D.rho)).mp hlogcube
  apply ordinary_three_from_seed_cubes _ p1 p2 p3 hp1 hp2 hp3 hsort hfirst
  simpa using hsecond

/-- An actual reached rank3 state has passed the seed Trace's first two
cumulative tests, even though its third odd policy test is inactive. -/
theorem reached_three_seed_retained {mesh : ℕ} (D : ThirdStage mesh)
    (N cap p1 p2 p3 : ℕ) (y z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 3 (D.oldPolicy N) h [] true 1
      (roughPrimeUniverse N cap y z))
    (hpre : state.selectedPrefix = [p3,p2,p1]) :
    seedRetain D N [p3,p2,p1] = true := by
  have hl := firstExitDepthFrontier_toLeaf_mem 3 (D.oldPolicy N) h []
    (roughPrimeUniverse N cap y z) true 1 state hs
  obtain ⟨chosen,_,hv,heq⟩ := exists_validSelection_of_mem_firstExitRetainedLeaves
    (D.oldPolicy N) h [] (roughPrimeUniverse N cap y z) true 1 _ hl
  have hchosen : chosen = [p1,p2,p3] := by
    have hh := congrArg List.reverse heq
    simpa [hpre] using hh.symm
  rw [hchosen] at hv
  have ht : seedRetain D N [p2,p1] = true := by
    simpa [FirstExitValidSelection,ThirdStage.oldPolicy,evenFirstExitPolicy,seedRetain]
      using hv
  exact (odd_rank_bypass _ _ _ _ N p3 [p2,p1] (by simp) (by norm_num)).mpr ht

theorem new_trace_three_retained_of_seed {mesh : ℕ} (D : ThirdStage mesh)
    (N p1 p2 p3 : ℕ) (hret : seedRetain D N [p3,p2,p1] = true) :
    thirdRetain D N [p3,p2,p1] = true := by
  have ho := (odd_rank_bypass D.seedPlan _ _ _ N p3 [p2,p1]
    (by simp) (by norm_num)).mp hret
  have hg := (baseline_two_tests D.seedPlan _ _ _ N p1 p2).mp ho
  have hn := (baseline_two_tests D.thirdPlan _ _ _ N p1 p2).mpr hg
  exact (odd_rank_bypass D.thirdPlan _ _ _ N p3 [p2,p1]
    (by simp) (by norm_num)).mpr hn

private def traceRetain {mesh : ℕ} (D : ThirdStage mesh) (P : CapPlan 5 mesh)
    (N : ℕ) : List ℕ → Bool :=
  retainEven P (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
    (baselineCap D.rho) N

private theorem seedPlan_choose_inherit {mesh : ℕ} (D : ThirdStage mesh)
    (rank : Fin 6) (code : P2OriginalLowerSelectedCapConstructor.Code mesh) :
    D.seedPlan.choose rank code = .inherit 2 := by
  fin_cases rank <;> simp [ThirdStage.seedPlan,compactPlan,checkedChoice,emptyRows]

private theorem seedPlan_planChoice_inherit {mesh : ℕ} (D : ThirdStage mesh)
    (a w : ℝ) (word : List ℝ) : planChoice D.seedPlan a w word = .inherit 2 := by
  unfold planChoice
  split_ifs
  · unfold incomingChoice
    exact seedPlan_choose_inherit D _ _
  · rfl

private theorem seedPlan_run_cap {mesh : ℕ} (D : ThirdStage mesh)
    (a w : ℝ) (H : Trace) (word : List ℝ) :
    (run D.seedPlan a w H word).cap = H.cap := by
  induction word generalizing H with
  | nil => rfl
  | cons x xs ih =>
    change (run D.seedPlan a w (step D.seedPlan a w H x) xs).cap = H.cap
    rw [ih]
    change (planChoice D.seedPlan a w (H.word++[x])).freeze H.cap = H.cap
    rw [seedPlan_planChoice_inherit]
    rfl

theorem actual_seed_trace_cap {mesh : ℕ} (D : ThirdStage mesh)
    (N : ℕ) (pre : List ℕ) :
    (integerTrace D.seedPlan (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
      (baselineCap D.rho) N pre).cap = baselineCap D.rho := by
  exact seedPlan_run_cap D _ _ (root (baselineCap D.rho)) (physicalWord N pre)

/-- The frozen mixed Trace and the original provider have identical tests
on every later sorted prime history. The two base facts in this helper
are discharged from the ACTUAL reached W state below. -/
private theorem extensions_iff_at_actual_frozen_level {mesh : ℕ} (D : ThirdStage mesh) (P : CapPlan 5 mesh)
    (N : ℕ) (pre later : List ℕ) (Q : ℝ) (hN : 1 < (N : ℝ))
    (hlen : 3 ≤ pre.length)
    (hQ : Q = (N : ℝ)^(integerTrace P (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap)
    (hfreeze : ∀ future : List ℕ,
      (integerTrace P (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
        (baselineCap D.rho) N (future++pre)).cap =
      (integerTrace P (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
        (baselineCap D.rho) N pre).cap)
    (hret : traceRetain D P N pre = true)
    (hadm : ordinaryRosserPrefixAdmissible true Q pre)
    (hprime : ∀ p ∈ later++pre, p.Prime)
    (hlevel : ∀ p ∈ later, (p : ℝ) < Q)
    (hsort : (later++pre).Pairwise (· < ·)) :
    traceRetain D P N (later++pre) = true ↔
      ordinaryRosserPrefixAdmissible true Q (later++pre) := by
  revert hprime hlevel hsort
  induction later with
  | nil =>
      intro _ _ _
      simpa only [List.nil_append] using (iff_of_true hret hadm)
  | cons q qs ih =>
      intro hprime hlevel hsort
      have hq : q.Prime := hprime q (by simp)
      have hqQ : (q : ℝ) < Q := hlevel q (by simp)
      have hs : (q::(qs++pre)).Pairwise (· < ·) := hsort
      have hpt : ∀ p ∈ qs++pre, p.Prime :=
        fun p hp => hprime p (List.mem_cons_of_mem q hp)
      have hlt : ∀ p ∈ qs, (p : ℝ) < Q :=
        fun p hp => hlevel p (List.mem_cons_of_mem q hp)
      have ht := ih hpt hlt (List.pairwise_cons.mp hs).2
      have hadmission :
          admission (integerTrace P (D.start.epsilon : ℝ)
            (startCutoff D.start.start : ℝ) (baselineCap D.rho) N (qs++pre))
            (coordinate N q) ↔
          (Even ((qs++pre).length+1) → ((qs++pre).prod : ℝ)*(q : ℝ)^3 < Q) := by
        have hlenword : (physicalWord N (qs++pre)).length = (qs++pre).length := by
          simp [physicalWord]
        have hnonzero : (qs++pre).length ≠ 0 := by
          simp only [List.length_append]
          omega
        simp only [admission,integerTrace_word,hlenword,if_neg hnonzero]
        by_cases he : ((qs++pre).length+1)%2 = 0
        · have hev : Even ((qs++pre).length+1) := Nat.even_iff.mpr he
          simp only [he,if_true,hev,true_implies]
          rw [hfreeze qs,hQ]
          exact cube_test_integer_iff hN hq.pos (qs++pre)
            (fun p hp => (hpt p hp).pos) _
        · have hne : ¬Even ((qs++pre).length+1) := by
            simpa only [Nat.even_iff] using he
          simp [he,hne]
      change traceRetain D P N (q::(qs++pre)) = true ↔ _
      rw [show traceRetain D P N (q::(qs++pre)) =
        retainEven P (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
          (baselineCap D.rho) N (q::(qs++pre)) from rfl]
      rw [retainEven_cons_iff,hadmission]
      change (traceRetain D P N (qs++pre) = true ∧ _) ↔ _
      rw [ht,ordinary_lower_cons_iff Q q (qs++pre) hq hqQ hs]

/-- Fully actual W receiver: the old provider prefix is derived from the
reached seed tests; the new prefix is derived by the licensed cap increase.
Every later prime is selected from the state's REAL remaining carrier.
No prefix-provider or final continuation property is an input. -/
theorem reached_W_actual_trace_admissible_iff {mesh : ℕ} (D : ThirdStage mesh)
    (N cap p1 p2 p3 : ℕ) (y z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 3 (D.oldPolicy N) h [] true 1
      (roughPrimeUniverse N cap y z))
    (hpre : state.selectedPrefix = [p3,p2,p1]) (hN : 1 < (N : ℝ))
    (code : P2OriginalLowerSelectedCapConstructor.Code mesh)
    (hcode : incomingCode (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
      5 mesh 3 (marked (physicalWord N [p3,p2,p1])) = code)
    (hsel : P2OriginalMixedThirdWTentSelector.mixedWinner D.start D.rho
      D.screen D.buffer D.delta D.inherited D.argument code =
      some (P2OriginalMixedThirdWTentSelector.wRow D.start
        (P2OriginalLowerSelectedCapConstructor.prefixCode 3 code) D.buffer))
    (later : List ℕ) (hfuture : later.reverse <+ state.remaining) :
    ordinaryRosserPrefixAdmissible true ((N : ℝ)^(baselineCap D.rho))
        [p3,p2,p1] ∧
      (thirdRetain D N (later++[p3,p2,p1]) = true ↔
        ordinaryRosserPrefixAdmissible true
          ((N : ℝ)^(integerTrace D.thirdPlan (D.start.epsilon : ℝ)
            (startCutoff D.start.start : ℝ) (baselineCap D.rho) N [p3,p2,p1]).cap)
          (later++[p3,p2,p1])) := by
  have hcarrier := roughPrimeUniverse_pairwise_gt N cap y z
  have hall : state.selectedPrefix.reverse ++ state.remaining <+
      roughPrimeUniverse N cap y z := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist 3 (D.oldPolicy N)
      h [] (roughPrimeUniverse N cap y z) true 1 state hs
  have hfull : (later++state.selectedPrefix).reverse <+
      roughPrimeUniverse N cap y z := by
    rw [List.reverse_append]
    exact ((List.Sublist.refl _).append hfuture).trans hall
  have hprimeFull : ∀ p ∈ later++state.selectedPrefix, p.Prime := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hfull.subset (List.mem_reverse.mpr hp))
  have hsortFull : (later++state.selectedPrefix).Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using hcarrier.sublist hfull
  have hsubPre := mem_firstExitDepthFrontier_selected_reverse_sublist
    3 (D.oldPolicy N) h (roughPrimeUniverse N cap y z) state hs
  have hsortPre : [p3,p2,p1].Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse,hpre] using hcarrier.sublist hsubPre
  have hp (p : ℕ) (hp : p ∈ [p3,p2,p1]) : p.Prime := by
    have hps : p ∈ state.selectedPrefix := by simpa only [hpre] using hp
    exact hprimeFull p (List.mem_append_right later hps)
  have hp1 := hp p1 (by simp)
  have hp2 := hp p2 (by simp)
  have hp3 := hp p3 (by simp)
  have hseed := reached_three_seed_retained D N cap p1 p2 p3 y z h state hs hpre
  have hold := actual_seed_three_admissible D N p1 p2 p3 hN hp1 hp2 hp3 hsortPre hseed
  have hnewret := new_trace_three_retained_of_seed D N p1 p2 p3 hseed
  have hW := (P2OriginalMixedThirdWTentSelector.mixedWinner_W_physical_row
    D.start D.rho D.screen D.buffer D.delta D.inherited D.argument code hsel).1
  have hcap : (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N [p3,p2,p1]).cap =
      (P2OriginalLowerWThirdPhysicalRow.wCap D.start
        (P2OriginalLowerSelectedCapConstructor.prefixCode 3 code) D.buffer : ℝ) := by
    exact P2OriginalMixedThirdBranchTableTrace.mixed_W_actual_third_trace D.start
      (emptyRows mesh) D.rho D.screen D.buffer D.delta D.inherited D.argument
      N p1 p2 p3 code hcode hsel
  have hQmono : (N : ℝ)^(baselineCap D.rho) ≤
      (N : ℝ)^(integerTrace D.thirdPlan (D.start.epsilon : ℝ)
        (startCutoff D.start.start : ℝ) (baselineCap D.rho) N [p3,p2,p1]).cap := by
    apply Real.rpow_le_rpow_of_exponent_le hN.le
    rw [hcap]
    exact hW.compact_gates.1.le
  have hnewadm := ordinary_lower_level_mono hQmono [p3,p2,p1] hold
  have hprodpos : 0 < [p3,p2,p1].prod := by
    simp only [List.prod_cons,List.prod_nil,mul_one]
    exact Nat.mul_pos hp3.pos (Nat.mul_pos hp2.pos hp1.pos)
  have hp1dvd : p1 ∣ [p3,p2,p1].prod := by
    simp only [List.prod_cons,List.prod_nil,mul_one]
    exact dvd_mul_of_dvd_right (dvd_mul_left p1 p2) p3
  have hp1le : (p1 : ℝ) ≤ [p3,p2,p1].prod := by
    exact_mod_cast Nat.le_of_dvd hprodpos hp1dvd
  have hp1Q : (p1 : ℝ) < (N : ℝ)^(integerTrace D.thirdPlan
      (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
      (baselineCap D.rho) N [p3,p2,p1]).cap :=
    (hp1le.trans_lt hold.1).trans_le hQmono
  have hlevel : ∀ q ∈ later, (q : ℝ) < (N : ℝ)^(integerTrace D.thirdPlan
      (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
      (baselineCap D.rho) N [p3,p2,p1]).cap := by
    intro q hq
    have hremain : q ∈ state.remaining := hfuture.subset (List.mem_reverse.mpr hq)
    have hlt := mem_firstExitDepthFrontier_selected_gt_remaining 3 (D.oldPolicy N) h
      (roughPrimeUniverse N cap y z) hcarrier state hs p1
      (by simp [hpre]) q hremain
    exact lt_trans (by exact_mod_cast hlt) hp1Q
  refine ⟨hold,?_⟩
  apply extensions_iff_at_actual_frozen_level D D.thirdPlan N [p3,p2,p1] later _ hN
    (by simp) rfl
    (fun future => thirdPlan_trace_append_frozen D N [p3,p2,p1] future (by simp))
    hnewret hnewadm
  · simpa only [hpre] using hprimeFull
  · exact hlevel
  · simpa only [hpre] using hsortFull

/-- At the ACTUAL reached W state, the retained later history is exactly
the original upper Rosser admissibility at Q_new / ENTIRE prefix product.
Odd rank3 flips lower to upper. The provider prefix is derived here rather
than imposed, and the future primes remain in the actual y-carrier. -/
theorem reached_W_actual_trace_upper_quotient_iff {mesh : ℕ} (D : ThirdStage mesh)
    (N cap p1 p2 p3 : ℕ) (y z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 3 (D.oldPolicy N) h [] true 1
      (roughPrimeUniverse N cap y z))
    (hpre : state.selectedPrefix = [p3,p2,p1]) (hN : 1 < (N : ℝ))
    (code : P2OriginalLowerSelectedCapConstructor.Code mesh)
    (hcode : incomingCode (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
      5 mesh 3 (marked (physicalWord N [p3,p2,p1])) = code)
    (hsel : P2OriginalMixedThirdWTentSelector.mixedWinner D.start D.rho
      D.screen D.buffer D.delta D.inherited D.argument code =
      some (P2OriginalMixedThirdWTentSelector.wRow D.start
        (P2OriginalLowerSelectedCapConstructor.prefixCode 3 code) D.buffer))
    (later : List ℕ) (hfuture : later.reverse <+ state.remaining) :
    thirdRetain D N (later++[p3,p2,p1]) = true ↔
      ordinaryRosserPrefixAdmissible false
        (((N : ℝ)^(integerTrace D.thirdPlan (D.start.epsilon : ℝ)
          (startCutoff D.start.start : ℝ) (baselineCap D.rho) N [p3,p2,p1]).cap) /
            ([p3,p2,p1].prod : ℝ)) later := by
  have hi := reached_W_actual_trace_admissible_iff D N cap p1 p2 p3 y z h state
    hs hpre hN code hcode hsel later hfuture
  have hi0 := reached_W_actual_trace_admissible_iff D N cap p1 p2 p3 y z h state
    hs hpre hN code hcode hsel [] (by simp)
  have hseed := reached_three_seed_retained D N cap p1 p2 p3 y z h state hs hpre
  have hnewret := new_trace_three_retained_of_seed D N p1 p2 p3 hseed
  have hnewadm := hi0.2.mp (by simpa using hnewret)
  have hcarrier := roughPrimeUniverse_pairwise_gt N cap y z
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 3 (D.oldPolicy N)
    h (roughPrimeUniverse N cap y z) state hs
  have hsort : [p3,p2,p1].Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse,hpre] using hcarrier.sublist hsub
  have hprime : ∀ p ∈ [p3,p2,p1], p.Prime := by
    intro p hp
    have hps : p ∈ state.selectedPrefix := by simpa only [hpre] using hp
    exact mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hps))
  have hPnat : 0 < [p3,p2,p1].prod := List.prod_pos (fun p hp => (hprime p hp).pos)
  have hP : (0 : ℝ) < [p3,p2,p1].prod := by exact_mod_cast hPnat
  have hsep : ∀ q ∈ later, ∀ p ∈ [p3,p2,p1], q < p := by
    intro q hq p hp
    have hqr : q ∈ state.remaining := hfuture.subset (List.mem_reverse.mpr hq)
    have hps : p ∈ state.selectedPrefix := by simpa only [hpre] using hp
    exact mem_firstExitDepthFrontier_selected_gt_remaining 3 (D.oldPolicy N) h
      (roughPrimeUniverse N cap y z) hcarrier state hs p hps q hqr
  rw [hi.2, ordinaryRosserPrefixAdmissible_append_iff true _ [p3,p2,p1] later
    hnewadm hsort.nodup hP hsep]
  norm_num [ordinaryRosserResidualLower, Nat.even_iff]

/-- The OLD side is derived from the same reached frontier, not supplied
as an independently normalized ordinary source. Both quotient receivers
therefore retain the same physical prefix and strict residual carrier. -/
theorem reached_W_seed_trace_upper_quotient_iff {mesh : ℕ} (D : ThirdStage mesh)
    (N cap p1 p2 p3 : ℕ) (y z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 3 (D.oldPolicy N) h [] true 1
      (roughPrimeUniverse N cap y z))
    (hpre : state.selectedPrefix = [p3,p2,p1]) (hN : 1 < (N : ℝ))
    (code : P2OriginalLowerSelectedCapConstructor.Code mesh)
    (hcode : incomingCode (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
      5 mesh 3 (marked (physicalWord N [p3,p2,p1])) = code)
    (hsel : P2OriginalMixedThirdWTentSelector.mixedWinner D.start D.rho
      D.screen D.buffer D.delta D.inherited D.argument code =
      some (P2OriginalMixedThirdWTentSelector.wRow D.start
        (P2OriginalLowerSelectedCapConstructor.prefixCode 3 code) D.buffer))
    (later : List ℕ) (hfuture : later.reverse <+ state.remaining) :
    seedRetain D N (later++[p3,p2,p1]) = true ↔
      ordinaryRosserPrefixAdmissible false
        (((N : ℝ)^(baselineCap D.rho)) / ([p3,p2,p1].prod : ℝ)) later := by
  have hi := reached_W_actual_trace_admissible_iff D N cap p1 p2 p3 y z h state
    hs hpre hN code hcode hsel later hfuture
  have hold := hi.1
  have hseed := reached_three_seed_retained D N cap p1 p2 p3 y z h state hs hpre
  have hcarrier := roughPrimeUniverse_pairwise_gt N cap y z
  have hall : state.selectedPrefix.reverse ++ state.remaining <+
      roughPrimeUniverse N cap y z := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist 3 (D.oldPolicy N)
      h [] (roughPrimeUniverse N cap y z) true 1 state hs
  have hfull : (later++state.selectedPrefix).reverse <+
      roughPrimeUniverse N cap y z := by
    rw [List.reverse_append]
    exact ((List.Sublist.refl _).append hfuture).trans hall
  have hprimeFull : ∀ p ∈ later++[p3,p2,p1], p.Prime := by
    intro p hp
    have hp' : p ∈ later++state.selectedPrefix := by simpa only [hpre] using hp
    exact mem_roughPrimeUniverse_prime (hfull.subset (List.mem_reverse.mpr hp'))
  have hsortFull : (later++[p3,p2,p1]).Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse,hpre] using hcarrier.sublist hfull
  have hprime : ∀ p ∈ [p3,p2,p1], p.Prime :=
    fun p hp => hprimeFull p (List.mem_append_right _ hp)
  have hPnat : 0 < [p3,p2,p1].prod := List.prod_pos (fun p hp => (hprime p hp).pos)
  have hP : (0 : ℝ) < [p3,p2,p1].prod := by exact_mod_cast hPnat
  have hp1dvd : p1 ∣ [p3,p2,p1].prod := by
    simp only [List.prod_cons,List.prod_nil,mul_one]
    exact dvd_mul_of_dvd_right (dvd_mul_left p1 p2) p3
  have hp1le : (p1 : ℝ) ≤ [p3,p2,p1].prod := by
    exact_mod_cast Nat.le_of_dvd hPnat hp1dvd
  have hsep : ∀ q ∈ later, ∀ p ∈ [p3,p2,p1], q < p := by
    intro q hq p hp
    have hqr : q ∈ state.remaining := hfuture.subset (List.mem_reverse.mpr hq)
    have hps : p ∈ state.selectedPrefix := by simpa only [hpre] using hp
    exact mem_firstExitDepthFrontier_selected_gt_remaining 3 (D.oldPolicy N) h
      (roughPrimeUniverse N cap y z) hcarrier state hs p hps q hqr
  have hlevel : ∀ q ∈ later, (q : ℝ) < (N : ℝ)^(baselineCap D.rho) := by
    intro q hq
    have hqp := hsep q hq p1 (by simp)
    exact (show (q : ℝ) < p1 by exact_mod_cast hqp).trans (hp1le.trans_lt hold.1)
  have hiff : seedRetain D N (later++[p3,p2,p1]) = true ↔
      ordinaryRosserPrefixAdmissible true ((N : ℝ)^(baselineCap D.rho))
        (later++[p3,p2,p1]) := by
    apply extensions_iff_at_actual_frozen_level D D.seedPlan N [p3,p2,p1] later _ hN
      (by simp) (by rw [actual_seed_trace_cap])
      (fun future => by rw [actual_seed_trace_cap,actual_seed_trace_cap])
      hseed hold hprimeFull hlevel hsortFull
  have hsubPre := mem_firstExitDepthFrontier_selected_reverse_sublist
    3 (D.oldPolicy N) h (roughPrimeUniverse N cap y z) state hs
  have hsortPre : [p3,p2,p1].Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse,hpre] using hcarrier.sublist hsubPre
  rw [hiff,ordinaryRosserPrefixAdmissible_append_iff true _ [p3,p2,p1] later
    hold hsortPre.nodup hP hsep]
  norm_num [ordinaryRosserResidualLower,Nat.even_iff]

end
end ImbalancedChen.P2OriginalI3ReachedTraceRosserIff
