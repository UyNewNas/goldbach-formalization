import ImbalancedChen.P2OriginalI3ReachedTraceRosserIff

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual reached lower Trace is identified with the original provider's
UPPER residual polynomial at its OLD/NEW quotient total levels. The strict
y-separated remaining carrier is retained; no 0/y whole-source equality
or externally supplied continuation identity is used.
-/
namespace ImbalancedChen.P2OriginalI3ActualUpperContinuation
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment
open P2OriginalI3ReachedTraceRosserIff

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

/-- Both physical continuations use the actual same reached prime prefix,
remaining y-carrier, signs and mass. The resulting upper polynomials are
the independently defined original ordinary Rosser provider at Q/P. -/
theorem reached_W_actual_I3_upper_continuations {mesh : ℕ} (D : ThirdStage mesh)
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
        (P2OriginalLowerSelectedCapConstructor.prefixCode 3 code) D.buffer)) :
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
  have hi0 := reached_W_actual_trace_admissible_iff D N cap p1 p2 p3 y z h state
    hs hpre hN code hcode hsel [] (by simp)
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
    have hi := (reached_W_actual_trace_admissible_iff D N cap p1 p2 p3 y z h state
      hs hpre hN code hcode hsel later hf).2
    exact even_policy_eq_provider_of_retention_iff (thirdRetain D N) Qnew (later++pre)
      hi positive
  have htestsOld : ∀ later : List ℕ, later.reverse <+ state.remaining → ∀ positive,
      D.oldPolicy N positive (later++pre) = ordinaryParityRosserPolicy true Qold positive
        (later++pre) := by
    intro later hf positive
    have hq := reached_W_seed_trace_upper_quotient_iff D N cap p1 p2 p3 y z h state
      hs hpre hN code hcode hsel later hf
    have hsepl : ∀ q ∈ later, ∀ p ∈ pre, q < p :=
      fun q hq p hp => hsep q (hf.subset (List.mem_reverse.mpr hq)) p hp
    have hd := ordinaryRosserPrefixAdmissible_append_iff true Qold pre later
      hold hsortpre.nodup hP hsepl
    have hi : seedRetain D N (later++pre) = true ↔
        ordinaryRosserPrefixAdmissible true Qold (later++pre) := by
      have hd' : ordinaryRosserPrefixAdmissible true Qold (later++pre) ↔
          ordinaryRosserPrefixAdmissible false (Qold / (pre.prod : ℝ)) later := by
        simpa [pre,ordinaryRosserResidualLower,Nat.even_iff] using hd
      exact hq.trans hd'.symm
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
end ImbalancedChen.P2OriginalI3ActualUpperContinuation
