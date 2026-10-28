import ImbalancedChen.P2OriginalI3ActualUpperContinuation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual mixed table, including inherited/failed-gate and tent decisions,
never lowers the seed cap. That independently proved fact removes F's W-only
restriction in the reached-Trace/provider receiver. The same actual cap stays
frozen through all later tests; no global W or adopted coverage is presumed.
The finite test/recursion helpers are re-used as source derivations at this
strictly larger actual source, not asserted as new analytic convergence.
-/
namespace ImbalancedChen.P2OriginalMixedI3AllFrontierRosser
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment
open P2OriginalI3ActualFrozenTraceLevel
open P2OriginalLowerRosserCubeInsertion
open P2OriginalI3ReachedTraceRosserIff

/-- Every actually computed mixed choice either inherits the seed or passes
its strict parent gate. This covers W, tent, failed-gate and no-row cases. -/
theorem actual_third_cap_ge_seed {mesh : ℕ} (D : ThirdStage mesh)
    (N p1 p2 p3 : ℕ) :
    baselineCap D.rho ≤ (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N [p3,p2,p1]).cap := by
  let a := (D.start.epsilon : ℝ)
  let w := (startCutoff D.start.start : ℝ)
  let seed := baselineCap D.rho
  let before := integerTrace D.thirdPlan a w seed N [p2,p1]
  let code := incomingCode a w 5 mesh 3 (marked (physicalWord N [p3,p2,p1]))
  have hbefore : before.cap = seed := by
    simp [before,integerTrace,physicalWord,run,root,step,planChoice,CapChoice.freeze]
  have hword : before.word ++ [coordinate N p3] = physicalWord N [p3,p2,p1] := by
    rw [integerTrace_word]
    simp [physicalWord]
  have hc : planChoice D.thirdPlan a w (physicalWord N [p3,p2,p1]) =
      checkedChoice D.start (P2OriginalMixedThirdBranchTableTrace.mixedThirdRows
        D.start (emptyRows mesh) D.rho D.screen D.buffer D.delta D.inherited D.argument)
        3 seed code := by
    have hlen : (physicalWord N [p3,p2,p1]).length = 3 := by simp [physicalWord]
    simp only [planChoice,hlen,eq_self,true_or,if_true]
    unfold incomingChoice
    simp only [Nat.min_eq_left (by omega : 3 ≤ 5)]
    rfl
  change seed ≤ (integerTrace D.thirdPlan a w seed N [p3,p2,p1]).cap
  rw [integerTrace_cons]
  change seed ≤ (planChoice D.thirdPlan a w
    (before.word ++ [coordinate N p3])).freeze before.cap
  rw [hword,hc,hbefore]
  exact checkedCap_monotone D.start _ 3 seed code

private def traceRetain {mesh : ℕ} (D : ThirdStage mesh) (P : CapPlan 5 mesh)
    (N : ℕ) : List ℕ → Bool :=
  retainEven P (D.start.epsilon : ℝ) (startCutoff D.start.start : ℝ)
    (baselineCap D.rho) N

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

/-- The actual selected cap is licensed by its computed branchGates or
inherits unchanged. This is a receiver for EVERY reached mixed frontier. -/
theorem reached_actual_trace_admissible_iff {mesh : ℕ} (D : ThirdStage mesh)
    (N cap p1 p2 p3 : ℕ) (y z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 3 (D.oldPolicy N) h [] true 1
      (roughPrimeUniverse N cap y z))
    (hpre : state.selectedPrefix = [p3,p2,p1]) (hN : 1 < (N : ℝ))
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
  have hQmono : (N : ℝ)^(baselineCap D.rho) ≤
      (N : ℝ)^(integerTrace D.thirdPlan (D.start.epsilon : ℝ)
        (startCutoff D.start.start : ℝ) (baselineCap D.rho) N [p3,p2,p1]).cap := by
    exact Real.rpow_le_rpow_of_exponent_le hN.le (actual_third_cap_ge_seed D N p1 p2 p3)
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


/-- The seed's actual cumulative tests and provider remain equal on every
future subhistory of this reached source; no selection label is required. -/
theorem reached_seed_trace_admissible_iff {mesh : ℕ} (D : ThirdStage mesh)
    (N cap p1 p2 p3 : ℕ) (y z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 3 (D.oldPolicy N) h [] true 1
      (roughPrimeUniverse N cap y z))
    (hpre : state.selectedPrefix = [p3,p2,p1]) (hN : 1 < (N : ℝ))
    (later : List ℕ) (hfuture : later.reverse <+ state.remaining) :
    seedRetain D N (later++[p3,p2,p1]) = true ↔
      ordinaryRosserPrefixAdmissible true ((N : ℝ)^(baselineCap D.rho))
        (later++[p3,p2,p1]) := by
  have hold := (reached_actual_trace_admissible_iff D N cap p1 p2 p3 y z h
    state hs hpre hN [] (by simp)).1
  have hcarrier := roughPrimeUniverse_pairwise_gt N cap y z
  have hall : state.selectedPrefix.reverse ++ state.remaining <+
      roughPrimeUniverse N cap y z := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist 3 (D.oldPolicy N)
      h [] (roughPrimeUniverse N cap y z) true 1 state hs
  have hfull : (later++state.selectedPrefix).reverse <+ roughPrimeUniverse N cap y z := by
    rw [List.reverse_append]
    exact ((List.Sublist.refl _).append hfuture).trans hall
  have hprimeFull : ∀ p ∈ later++state.selectedPrefix, p.Prime := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hfull.subset (List.mem_reverse.mpr hp))
  have hsortFull : (later++state.selectedPrefix).Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using hcarrier.sublist hfull
  have hp1 : p1.Prime := hprimeFull p1 (by simp [hpre])
  have hp2 : p2.Prime := hprimeFull p2 (by simp [hpre])
  have hp3 : p3.Prime := hprimeFull p3 (by simp [hpre])
  have hprodpos : 0 < [p3,p2,p1].prod := by
    simp only [List.prod_cons,List.prod_nil,mul_one]
    exact Nat.mul_pos hp3.pos (Nat.mul_pos hp2.pos hp1.pos)
  have hp1dvd : p1 ∣ [p3,p2,p1].prod := by
    simp only [List.prod_cons,List.prod_nil,mul_one]
    exact dvd_mul_of_dvd_right (dvd_mul_left p1 p2) p3
  have hp1le : (p1 : ℝ) ≤ [p3,p2,p1].prod := by
    exact_mod_cast Nat.le_of_dvd hprodpos hp1dvd
  have hlevel : ∀ q ∈ later, (q : ℝ) < (N : ℝ)^(baselineCap D.rho) := by
    intro q hq
    have hremain : q ∈ state.remaining := hfuture.subset (List.mem_reverse.mpr hq)
    have hlt := mem_firstExitDepthFrontier_selected_gt_remaining 3 (D.oldPolicy N) h
      (roughPrimeUniverse N cap y z) hcarrier state hs p1
      (by simp [hpre]) q hremain
    exact (show (q : ℝ) < p1 by exact_mod_cast hlt).trans (hp1le.trans_lt hold.1)
  apply extensions_iff_at_actual_frozen_level D D.seedPlan N [p3,p2,p1] later _ hN
    (by simp) (by rw [actual_seed_trace_cap])
    (fun future => by rw [actual_seed_trace_cap,actual_seed_trace_cap])
    (reached_three_seed_retained D N cap p1 p2 p3 y z h state hs hpre) hold
  · simpa only [hpre] using hprimeFull
  · exact hlevel
  · simpa only [hpre] using hsortFull

private theorem even_policy_eq_provider_of_retention_iff
    (retain : List ℕ → Bool) (Q : ℝ) (pre : List ℕ)
    (hi : retain pre = true ↔ ordinaryRosserPrefixAdmissible true Q pre)
    (positive : Bool) :
    evenFirstExitPolicy retain positive pre = ordinaryParityRosserPolicy true Q positive pre := by
  cases positive with
  | false => rfl
  | true =>
    change retain pre = decide (ordinaryRosserPrefixAdmissible true Q pre)
    by_cases ha : ordinaryRosserPrefixAdmissible true Q pre
    · have hr := hi.mpr ha
      simp [hr,ha]
    · have hr : retain pre = false := by
        cases hh : retain pre with
        | false => rfl
        | true => exact False.elim (ha (hi.mp hh))
      simp [hr,ha]

/-- Exact finite recursive congruence on the actual selected subhistories.
The caller proves a Boolean atom iff, not a polynomial equality. -/
private theorem polynomial_congr_on_subhistories
    (P Q : Bool → List ℕ → Bool) (h : ℕ → ℝ) (pre rootCarrier : List ℕ)
    (htests : ∀ later : List ℕ, later.reverse <+ rootCarrier → ∀ positive,
      P positive (later++pre) = Q positive (later++pre))
    (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial P h pre positive mass rootCarrier =
      firstExitRetainedPolynomial Q h pre positive mass rootCarrier := by
  have aux : ∀ remaining suffix : List ℕ,
      suffix.reverse++remaining <+ rootCarrier → ∀ sign mass,
      firstExitRetainedPolynomial P h (suffix++pre) sign mass remaining =
        firstExitRetainedPolynomial Q h (suffix++pre) sign mass remaining := by
    intro remaining
    induction remaining with
    | nil => intro suffix hinv sign mass; rfl
    | cons q qs ih =>
      intro suffix hinv sign mass
      have hskip : suffix.reverse++qs <+ rootCarrier :=
        (((List.Sublist.refl suffix.reverse).append (List.sublist_cons_self q qs)).trans hinv)
      have hnew : (q::suffix).reverse++qs <+ rootCarrier := by
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hinv
      have hprefix : (q::suffix).reverse <+ rootCarrier := by
        have hh := (List.Sublist.refl (q::suffix).reverse).append
          (show [] <+ qs from by simp)
        have hpref : (q::suffix).reverse <+ (q::suffix).reverse++qs := by
          simpa only [List.append_nil] using hh
        exact hpref.trans hnew
      have ht := htests (q::suffix) hprefix (!sign)
      simp only [firstExitRetainedPolynomial,ht]
      rw [ih suffix hskip sign mass,ih (q::suffix) hnew (!sign) (mass*h q)]
  simpa only [List.nil_append] using aux rootCarrier [] (by simp) positive mass

/-- All actually computed mixed choices have literal OLD/NEW ordinary
upper residual polynomials at the actual entire-prefix quotient levels. -/
theorem reached_actual_I3_upper_continuations {mesh : ℕ} (D : ThirdStage mesh)
    (N cap p1 p2 p3 : ℕ) (y z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 3 (D.oldPolicy N) h [] true 1
      (roughPrimeUniverse N cap y z))
    (hpre : state.selectedPrefix = [p3,p2,p1]) (hN : 1 < (N : ℝ)) :
    let Qold := (N : ℝ)^(baselineCap D.rho)
    let Qnew := (N : ℝ)^(integerTrace D.thirdPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N [p3,p2,p1]).cap
    firstExitRetainedPolynomial (D.newPolicy N) h [p3,p2,p1]
        state.positive state.mass state.remaining -
      firstExitRetainedPolynomial (D.oldPolicy N) h [p3,p2,p1]
        state.positive state.mass state.remaining =
      state.mass *
        (firstExitRetainedPolynomial
            (ordinaryRosserRetainedPolicy false (Qold / ([p3,p2,p1].prod : ℝ)))
            h [] true 1 state.remaining -
          firstExitRetainedPolynomial
            (ordinaryRosserRetainedPolicy false (Qnew / ([p3,p2,p1].prod : ℝ)))
            h [] true 1 state.remaining) := by
  let pre := [p3,p2,p1]
  let Qold := (N : ℝ)^(baselineCap D.rho)
  let Qnew := (N : ℝ)^(integerTrace D.thirdPlan (D.start.epsilon : ℝ)
    (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap
  have hi0 := reached_actual_trace_admissible_iff D N cap p1 p2 p3 y z h state
    hs hpre hN [] (by simp)
  have hold : ordinaryRosserPrefixAdmissible true Qold pre := hi0.1
  have hseed := reached_three_seed_retained D N cap p1 p2 p3 y z h state hs hpre
  have hnewret := new_trace_three_retained_of_seed D N p1 p2 p3 hseed
  have hnew : ordinaryRosserPrefixAdmissible true Qnew pre :=
    hi0.2.mp (by simpa using hnewret)
  have hcarrier := roughPrimeUniverse_pairwise_gt N cap y z
  have hall : state.selectedPrefix.reverse++state.remaining <+
      roughPrimeUniverse N cap y z := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist 3 (D.oldPolicy N)
      h [] (roughPrimeUniverse N cap y z) true 1 state hs
  have hsort : (state.remaining.reverse++pre).Pairwise (· < ·) := by
    have hh := hcarrier.sublist hall
    have hrev : (state.selectedPrefix.reverse++state.remaining).reverse =
        state.remaining.reverse++pre := by simp [hpre,pre]
    rw [← hrev]
    simpa only [List.pairwise_reverse] using hh
  have hsubpre := mem_firstExitDepthFrontier_selected_reverse_sublist 3 (D.oldPolicy N)
    h (roughPrimeUniverse N cap y z) state hs
  have hsortpre : pre.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse,hpre] using hcarrier.sublist hsubpre
  have hprimepre : ∀ p ∈ pre, p.Prime := by
    intro p hp
    have hps : p ∈ state.selectedPrefix := by simpa only [hpre] using hp
    exact mem_roughPrimeUniverse_prime (hsubpre.subset (List.mem_reverse.mpr hps))
  have hPnat : 0 < pre.prod := List.prod_pos (fun p hp => (hprimepre p hp).pos)
  have hP : (0 : ℝ) < pre.prod := by exact_mod_cast hPnat
  have hsep : ∀ q ∈ state.remaining, ∀ p ∈ pre, q < p := by
    intro q hq p hp
    have hps : p ∈ state.selectedPrefix := by simpa only [hpre] using hp
    exact mem_firstExitDepthFrontier_selected_gt_remaining 3 (D.oldPolicy N) h
      (roughPrimeUniverse N cap y z) hcarrier state hs p hps q hq
  have hprimeRem : ∀ q ∈ state.remaining, q.Prime := by
    intro q hq
    exact mem_roughPrimeUniverse_prime (hall.subset (List.mem_append_right _ hq))
  have hp1dvd : p1 ∣ pre.prod := by
    dsimp [pre]
    simp only [List.prod_cons,List.prod_nil,mul_one]
    exact dvd_mul_of_dvd_right (dvd_mul_left p1 p2) p3
  have hp1le : (p1 : ℝ) ≤ pre.prod := by exact_mod_cast Nat.le_of_dvd hPnat hp1dvd
  have hlevels (Q : ℝ) (hvalid : ordinaryRosserPrefixAdmissible true Q pre) :
      ∀ q ∈ state.remaining, (q : ℝ) < Q := by
    intro q hq
    have hqp := hsep q hq p1 (by simp [pre])
    exact (show (q : ℝ) < p1 by exact_mod_cast hqp).trans (hp1le.trans_lt hvalid.1)
  have htestsNew : ∀ later : List ℕ, later.reverse <+ state.remaining → ∀ positive,
      D.newPolicy N positive (later++pre) = ordinaryParityRosserPolicy true Qnew positive
        (later++pre) := by
    intro later hf positive
    have hi := (reached_actual_trace_admissible_iff D N cap p1 p2 p3 y z h state
      hs hpre hN later hf).2
    exact even_policy_eq_provider_of_retention_iff (thirdRetain D N) Qnew (later++pre)
      hi positive
  have htestsOld : ∀ later : List ℕ, later.reverse <+ state.remaining → ∀ positive,
      D.oldPolicy N positive (later++pre) = ordinaryParityRosserPolicy true Qold positive
        (later++pre) := by
    intro later hf positive
    have hi := reached_seed_trace_admissible_iff D N cap p1 p2 p3 y z h state
      hs hpre hN later hf
    exact even_policy_eq_provider_of_retention_iff (seedRetain D N) Qold (later++pre)
      hi positive
  have hsg : state.positive = evenListLength pre := by
    simpa only [hpre] using mem_firstExitDepthFrontier_positive_eq_evenListLength
      3 (D.oldPolicy N) h (roughPrimeUniverse N cap y z) state hs
  have hnegative : state.positive = false := by simpa [pre,evenListLength] using hsg
  have neweq : firstExitRetainedPolynomial (D.newPolicy N) h pre state.positive state.mass
      state.remaining = -state.mass * firstExitRetainedPolynomial
        (ordinaryRosserRetainedPolicy false (Qnew / (pre.prod : ℝ))) h [] true 1 state.remaining := by
    rw [polynomial_congr_on_subhistories _ _ h pre state.remaining htestsNew,
      firstExitRetainedPolynomial_ordinaryParityRosser_eq_full_valid true Qnew
        state.remaining pre state.positive state.mass h hnew hsg hprimeRem
        (fun _ => hlevels Qnew hnew) hsort,
      firstExitRetainedPolynomial_ordinaryRosser_continuation true Qnew pre state.remaining
        hnew hsortpre.nodup hP hsep h state.positive state.mass]
    simp [pre,ordinaryRosserResidualLower,Nat.even_iff,hnegative]
  have oldeq : firstExitRetainedPolynomial (D.oldPolicy N) h pre state.positive state.mass
      state.remaining = -state.mass * firstExitRetainedPolynomial
        (ordinaryRosserRetainedPolicy false (Qold / (pre.prod : ℝ))) h [] true 1 state.remaining := by
    rw [polynomial_congr_on_subhistories _ _ h pre state.remaining htestsOld,
      firstExitRetainedPolynomial_ordinaryParityRosser_eq_full_valid true Qold
        state.remaining pre state.positive state.mass h hold hsg hprimeRem
        (fun _ => hlevels Qold hold) hsort,
      firstExitRetainedPolynomial_ordinaryRosser_continuation true Qold pre state.remaining
        hold hsortpre.nodup hP hsep h state.positive state.mass]
    simp [pre,ordinaryRosserResidualLower,Nat.even_iff,hnegative]
  change firstExitRetainedPolynomial (D.newPolicy N) h pre state.positive state.mass state.remaining -
    firstExitRetainedPolynomial (D.oldPolicy N) h pre state.positive state.mass state.remaining = _
  rw [neweq,oldeq]
  ring


end
end ImbalancedChen.P2OriginalMixedI3AllFrontierRosser
