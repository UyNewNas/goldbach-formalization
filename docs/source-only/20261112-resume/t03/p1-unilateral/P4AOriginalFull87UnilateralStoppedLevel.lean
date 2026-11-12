import ImbalancedChen.P4AOriginalFull87SixthBothInvoice
import ImbalancedChen.P4AOriginalFull87StoppedTerminalPopulation
import ImbalancedChen.P4AOriginalFull87WholeSixthCeiling
import ImbalancedChen.P4AActualEighthInheritedHistoryGuard
import ImbalancedChen.FirstExitFrontierInvariants

/-! The two original policies of the P1 stopped invoice. A retained fifth
tests its own odd cube. A terminal before rank eight can append at most two
smaller primes. The small Rosser bound is used only at a nonzero coefficient.
This source leaves the rank-eight frontier invoices in their original ledger. -/
namespace ImbalancedChen.P4AOriginalFull87UnilateralStoppedLevel
noncomputable section
open scoped Classical BigOperators List
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87FirstFifthStoppedEvents (firstFifthEvents)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (fifthSixthWithoutBoth actualFifthSixthWithoutBoth actualFifthSixthExclusiveAbsInvoice)
open P4AOriginalFull87StoppedTerminalPopulation
  (StoppedTerminal stoppedTerminals mem_stoppedTerminals_depth_lt
   nonzero_stopped_has_actual_ancestor_highq_witness)
open P4AOriginalFull87WholeSixthCeiling
  (exponent5_le_initial_ceiling finite_cap5_le_initial_ceiling)
open P4AOriginalCompleteSixthChronology (data)

/-- The raw side is true and the licensed side is false. -/
abbrev eventPolicy (rawSide : Bool) (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N : ℕ) : Bool → List ℕ → Bool :=
  if rawSide then P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  else P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)

/-- Recover the cube from the actual fifth gate, including the inactive
raw fifth fallback in the licensed policy. -/
theorem admitted_fifth_cube (side : Bool) (delta : ℝ) (n : ℕ) (e : ℚ)
    (q : ℕ) (om : ℝ) (N p : ℕ) (pre : List ℕ)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (h4 : pre.length = 4) (hord : (p :: pre).Pairwise (· < ·))
    (hgate : eventPolicy side delta n e q om N false (p :: pre) = true) :
    (((p :: pre).prod : ℕ) : ℝ) * (p : ℝ)^2 < (N : ℝ)^(299/500 : ℝ) := by
  let child := p :: pre
  have h5 : child.length = 5 := by simp [child,h4]
  have hgt : ¬child.length ≤ 4 := by omega
  have takeCube (D : ℝ) (hD : D ≤ (N : ℝ)^(299/500 : ℝ))
      (h : ordinaryParityRosserPolicy false D false child = true) :
      ((child.prod : ℕ) : ℝ) * (p : ℝ)^2 < (N : ℝ)^(299/500 : ℝ) := by
    have adm : ordinaryRosserPrefixAdmissible false D child := by
      simpa only [ordinaryParityRosserPolicy, Bool.false_eq_true, if_false,
        oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using h
    exact (P4AActualEighthInheritedHistoryGuard.odd_history_own_cube D p pre hord
      (by change ¬Even child.length; rw [h5] <;> decide) adm).trans_le hD
  cases side with
  | false =>
    change P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om N false child = true at hgate
    rw [P4AOriginalFull87LicensedSixthPolicy.through_eight delta n e q om N false child
      (by omega)] at hgate
    let b := rosserAncestor 5 child
    have hlev : P4AOriginalFull87FiniteParentPolicy.level5Exponent n e q om N b ≤
        (299/500 : ℝ) := by
      unfold P4AOriginalFull87FiniteParentPolicy.level5Exponent
      split_ifs
      · exact finite_cap5_le_initial_ceiling n e q om N he b
      · exact exponent5_le_initial_ceiling _ he N b
    apply takeCube _ (Real.rpow_le_rpow_of_exponent_le hN.le hlev)
    simpa only [P4AOriginalFull87LicensedSixthPolicy.sixthPolicy,
      P4AOriginalFull87FiniteParentPolicy.fifthPolicy,firstExitDepthSplicePolicy,
      if_pos (show child.length ≤ 6 by omega),if_neg hgt,
      frozenParityRosserPolicy,ancestorFrozenPolicy] using hgate
  | true =>
    change P4AOriginalFull87CompleteSixthDispatch.policy e q om N false child = true at hgate
    rw [P4AOriginalFull87CompleteSixthDispatch.policy_through_eight e q om N false child
      (by omega), P4AOriginalCompleteSixthChronology.current_policy_through_six e q om N
      false child (by omega)] at hgate
    apply takeCube _ (Real.rpow_le_rpow_of_exponent_le hN.le
      (exponent5_le_initial_ceiling (data e q om) he N (rosserAncestor 5 child)))
    simpa only [P5OriginalCommonRefinedConstructor.policy5,firstExitDepthSplicePolicy,
      if_neg hgt,frozenParityRosserPolicy,ancestorFrozenPolicy,
      P5OriginalCommonRefinedConstructor.level5] using hgate

/-- Keep the provenance of the extra factors. They were selected from this
literal post-fifth suffix, so each is at most the fifth prime. -/
private theorem stopped_extension {R : Bool → List ℕ → Bool} (p : ℕ)
    (pre : List ℕ) (s : Bool) (mass : ℝ) (rest : List ℕ)
    (hr : ∀ x ∈ rest, x ≤ p) (t : StoppedTerminal ℕ)
    (ht : t ∈ stoppedTerminals 8 R (fun _ => 1) pre s mass rest) :
    ∃ extra : List ℕ, t.selected = extra ++ pre ∧ ∀ x ∈ extra, x ≤ p := by
  induction rest generalizing pre s mass with
  | nil =>
    by_cases hk : 8 ≤ pre.length
    · simp [stoppedTerminals,hk] at ht
    · have h : t = ⟨pre,s,mass⟩ := by simpa [stoppedTerminals,hk] using ht
      subst t
      exact ⟨[],by simp,by simp⟩
  | cons x xs ih =>
    have hxs : ∀ y ∈ xs, y ≤ p :=
      fun y hy => hr y (List.mem_cons_of_mem _ hy)
    by_cases hk : 8 ≤ pre.length
    · simp [stoppedTerminals,hk] at ht
    · rw [stoppedTerminals,if_neg hk,List.mem_append] at ht
      rcases ht with hskip | htake
      · exact ih pre s mass hxs hskip
      · by_cases hg : R (!s) (x :: pre) = true
        · rw [if_pos hg] at htake
          obtain ⟨ys,hy,hys⟩ := ih (x :: pre) (!s) (mass*1) hxs htake
          refine ⟨ys ++ [x],by simpa only [List.append_assoc,List.singleton_append] using hy,?_⟩
          intro y h
          rcases List.mem_append.mp h with h | h
          · exact hys y h
          · have hyx : y = x := by simpa only [List.mem_singleton] using h
            subst y
            exact hr x (by simp)
        · simp [hg] at htake

private theorem prod_le_pow (p : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ p) :
    xs.prod ≤ p^xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.prod_cons,List.length_cons,pow_succ']
    exact Nat.mul_le_mul (h x (by simp))
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- Complete modulus of each nonzero attachment on either admitted fifth
side, for its own prefix, suffix, stopped terminal and parity-selected beta. -/
theorem actual_fifth_terminal_full_modulus
    (side : Bool) (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (heps : epsilon ≤ 1/500)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (pre : List ℕ) (p : ℕ) (rest : List ℕ) (mass : ℝ)
    (h4 : pre.length = 4) (hp : 0 < p) (hord : (p :: pre).Pairwise (· < ·))
    (hr : ∀ x ∈ rest, x ≤ p)
    (hgate : eventPolicy side delta n e q om N false (p :: pre) = true)
    (t : StoppedTerminal ℕ)
    (ht : t ∈ stoppedTerminals 8 (eventPolicy side delta n e q om N)
      (fun _ => 1) (p :: pre) false mass rest)
    (a : ℕ) (ha : (if t.positive then actualSmallRosserPlus N cap w ((N : ℝ)^epsilon) a
        else actualSmallRosserMinus N cap w ((N : ℝ)^epsilon) a) ≠ 0) :
    ((a * t.selected.prod : ℕ) : ℝ) < (N : ℝ)^(3/5 : ℝ) := by
  obtain ⟨ys,hy,hys⟩ := stopped_extension p (p :: pre) false mass rest hr t ht
  have hd := mem_stoppedTerminals_depth_lt 8 _ (fun _ => (1 : ℝ))
    (p :: pre) false mass rest t ht
  rw [hy,List.length_append,List.length_cons,h4] at hd
  have htwo : ys.length ≤ 2 := by omega
  have hprod : (ys.prod : ℝ) ≤ (p : ℝ)^2 := by
    exact_mod_cast (prod_le_pow p ys hys).trans (Nat.pow_le_pow_right hp htwo)
  have hc := admitted_fifth_cube side delta n e q om N p pre he hN h4 hord hgate
  have hb : (t.selected.prod : ℝ) < (N : ℝ)^(299/500 : ℝ) := by
    rw [hy,List.prod_append,Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _)).trans_lt
      (by simpa only [mul_comm] using hc)
  have hsmall : (a : ℝ) < (N : ℝ)^epsilon := by
    cases hs : t.positive with
    | false => exact (actualSmallRosserMinus_active (by simpa [hs] using ha)).2.1
    | true => exact (actualSmallRosserPlus_active (by simpa [hs] using ha)).2.1
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hN
  rw [Nat.cast_mul]
  calc
    _ ≤ (a : ℝ) * (N : ℝ)^(299/500 : ℝ) :=
      mul_le_mul_of_nonneg_left hb.le (Nat.cast_nonneg _)
    _ < (N : ℝ)^epsilon * (N : ℝ)^(299/500 : ℝ) :=
      mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hNpos _)
    _ = (N : ℝ)^(epsilon + 299/500 : ℝ) := (Real.rpow_add hNpos _ _).symm
    _ ≤ (N : ℝ)^(3/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [heps])

/-- At a common negative fifth history the sixth query has positive sign.
Both original policies retain it; the existing filtered list is empty. -/
private theorem no_sixth_unilateral (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N : ℕ) (T : Bool → List ℕ → ℝ) (child : List ℕ)
    (mass : ℝ) (rest : List ℕ) :
    ((firstFifthEvents (eventPolicy true delta n e q om N)
      (eventPolicy false delta n e q om N) (fun _ => 1) T child false mass rest).filter
      (fun ev => decide (ev.kind ≠ .both))) = [] := by
  induction rest with
  | nil => rfl
  | cons p ps ih =>
    have hR : eventPolicy true delta n e q om N true (p :: child) = true :=
      P4AOriginalFull87CompleteSixthDispatch.policy_even e q om N (p :: child)
    have hS : eventPolicy false delta n e q om N true (p :: child) = true :=
      P4AOriginalFull87LicensedSixthPolicy.policy_even delta n e q om N (p :: child)
    simp [firstFifthEvents,hR,hS,ih]

private theorem events_on_four (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (heps : epsilon ≤ 1/500)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (X : ℕ) (hX : (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ)) (F : ℕ → ℝ)
    (pre : List ℕ) (mass : ℝ) (h4 : pre.length = 4) (ho : pre.Pairwise (· < ·))
    (rest : List ℕ) (hs : rest.Pairwise (· > ·))
    (hpos : ∀ y ∈ rest, 0 < y) (hcross : ∀ x ∈ pre, ∀ y ∈ rest, y < x) :
    ∀ ev ∈ fifthSixthWithoutBoth (eventPolicy true delta n e q om N)
        (eventPolicy false delta n e q om N) (fun _ => 1)
        (attachedLeafTest N cap 1 w ((N : ℝ)^epsilon) (highQTest X F)) pre true mass rest,
      ev.signedValue = 0 := by
  induction rest with
  | nil => simp [fifthSixthWithoutBoth]
  | cons p ps ih =>
    have hps := List.pairwise_cons.mp hs
    have htail := ih hps.2 (fun y hy => hpos y (List.mem_cons_of_mem _ hy))
      (fun x hx y hy => hcross x hx y (List.mem_cons_of_mem _ hy))
    have hord := List.pairwise_cons.mpr ⟨fun x hx => hcross x hx p (by simp),ho⟩
    let T := attachedLeafTest N cap 1 w ((N : ℝ)^epsilon) (highQTest X F)
    have hz (side : Bool) (hg : eventPolicy side delta n e q om N false (p :: pre) = true) :
        stoppedTest 8 (eventPolicy side delta n e q om N) (fun _ => 1) T
          (p :: pre) false (mass*1) ps = 0 := by
      by_contra hn
      obtain ⟨t,ht,_,_,a,_,hlarge,hbeta,_⟩ :=
        nonzero_stopped_has_actual_ancestor_highq_witness _ (fun _ => 1)
          N cap w ((N : ℝ)^epsilon) X F (p :: pre) false (mass*1) ps hn
      have hfull := actual_fifth_terminal_full_modulus side delta n e q om
        N cap w epsilon heps he hN pre p ps (mass*1) h4 (hpos p (by simp))
        hord (fun y hy => (hps.1 y hy).le) hg t ht a hbeta
      have hc : a * t.selected.prod ≤ X := by exact_mod_cast (hfull.le.trans hX)
      exact (Nat.not_lt_of_ge hc) hlarge
    intro ev hev
    change ev ∈ fifthSixthWithoutBoth _ _ (fun _ => 1) T pre true mass (p :: ps) at hev
    rw [fifthSixthWithoutBoth,List.mem_append] at hev
    rcases hev with h | h
    · by_cases hR : eventPolicy true delta n e q om N false (p :: pre) = true
      · by_cases hS : eventPolicy false delta n e q om N false (p :: pre) = true
        · simp only [Bool.not_true,if_pos hR,if_pos hS,no_sixth_unilateral,
            List.map_nil,List.not_mem_nil] at h
        · simp only [Bool.not_true,if_pos hR,if_neg hS,List.mem_singleton] at h
          subst ev
          exact hz true hR
      · by_cases hS : eventPolicy false delta n e q om N false (p :: pre) = true
        · simp only [Bool.not_true,if_neg hR,if_pos hS,List.mem_singleton] at h
          subst ev
          exact neg_eq_zero.mpr (hz false hS)
        · simp only [Bool.not_true,if_neg hR,if_neg hS,List.not_mem_nil] at h
    · exact htail ev h

/-- Every entry of the actual reduced invoice has zero value. -/
theorem actual_event_zero (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (heps : epsilon ≤ 1/500)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (X : ℕ) (hX : (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ)) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) (hs : s ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hv : ev ∈ actualFifthSixthWithoutBoth delta n e q om N cap w ((N : ℝ)^epsilon) X F s) :
    ev.signedValue = 0 := by
  let R := eventPolicy true delta n e q om N
  let C := roughPrimeUniverse N cap w z
  have h4 := firstExitDepthFrontier_selected_length 4 R (fun _ => (1 : ℝ))
    [] C true 1 (by simp) s hs
  have hs4 := mem_firstExitDepthFrontier_positive_eq_evenListLength 4 R
    (fun _ => (1 : ℝ)) C s hs
  have parity (xs : List ℕ) : evenListLength xs = decide (Even xs.length) := by
    induction xs with
    | nil => simp [evenListLength]
    | cons x xs ih => simp only [evenListLength,ih,List.length_cons,Nat.even_add_one,decide_not]
  have hsign : s.positive = true := by rw [hs4,parity,h4] <;> decide
  have hsub : s.selectedPrefix.reverse ++ s.remaining <+ C := by
    simpa only [List.reverse_nil,List.nil_append] using
      firstExitDepthFrontier_selected_remaining_sublist 4 R (fun _ => (1 : ℝ))
        [] C true 1 s hs
  have hpair := List.pairwise_append.mp ((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub)
  have hp : s.selectedPrefix.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using hpair.1
  unfold actualFifthSixthWithoutBoth at hv
  rw [hsign] at hv
  exact events_on_four delta n e q om N cap w epsilon heps he hN X hX F
    s.selectedPrefix s.mass h4 hp s.remaining hpair.2.1
    (fun y hy => (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_append.mpr (Or.inr hy)))).pos)
    (fun x hx y hy => hpair.2.2 x (List.mem_reverse.mpr hx) y hy) ev hv

private theorem map_sum_zero {α : Type*} (xs : List α) (f : α → ℝ)
    (h : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,h x (by simp),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy)),add_zero]

theorem actual_exclusive_invoice_zero (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (heps : epsilon ≤ 1/500)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (X : ℕ) (hX : (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ)) (F : ℕ → ℝ) :
    actualFifthSixthExclusiveAbsInvoice delta n e q om N cap w z ((N : ℝ)^epsilon) X F = 0 := by
  unfold actualFifthSixthExclusiveAbsInvoice
  apply map_sum_zero
  intro s hs
  apply map_sum_zero
  intro ev hv
  rw [actual_event_zero delta n e q om N cap w z epsilon heps he hN X hX F s hs ev hv,abs_zero]

theorem actual_stopped_difference_zero (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (heps : epsilon ≤ 1/500)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (X : ℕ) (hX : (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ)) (F : ℕ → ℝ) :
    P4AOriginalFull87EarlyStopPhysicalGap.rawStopped e q om N cap w z ((N : ℝ)^epsilon) X F -
      P4AOriginalFull87EarlyStopPhysicalGap.licensedStopped delta n e q om N cap w z
        ((N : ℝ)^epsilon) X F = 0 := by
  have h := P4AOriginalFull87SixthBothInvoice.abs_actual_stopped_le_fifth_sixth_exclusive_invoice
    delta n e q om N cap w z he hN epsilon heps X hX F
  rw [actual_exclusive_invoice_zero delta n e q om N cap w z epsilon heps he hN X hX F] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- The original physical difference now charges precisely its existing
frontier terms. No dropped fifth/sixth occurrence is transferred there. -/
theorem physical_highq_le_frontier (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (heps : epsilon ≤ 1/500)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (X : ℕ) (hX : (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ)) (F : ℕ → ℝ) :
    |P4AOriginalLicensedSixthSignedLedger.physical (eventPolicy true delta n e q om N)
        N cap w z ((N : ℝ)^epsilon) (highQTest X F) -
      P4AOriginalLicensedSixthSignedLedger.physical (eventPolicy false delta n e q om N)
        N cap w z ((N : ℝ)^epsilon) (highQTest X F)| ≤
      (P4AOriginalFull87RawTrimSignedHighQ.rawOutsideHighQInvoice delta e q om N cap w z
        ((N : ℝ)^epsilon) X F +
       P4AOriginalFull87ThreeClassLeafInvoices.actualProducerThreeClassLeafBill
        delta n e q om N cap w z ((N : ℝ)^epsilon) X F) +
      P4AOriginalFull87LicensedOutsideThreeInvoices.licensedOutsideHighQInvoice
        delta n e q om N cap w z ((N : ℝ)^epsilon) X F := by
  simpa only [actual_exclusive_invoice_zero delta n e q om N cap w z epsilon heps he hN X hX F,
    zero_add] using
    P4AOriginalFull87SixthBothInvoice.abs_full_physical_le_exclusive_fifth_sixth_and_frontier
      delta n e q om N cap w z he hN epsilon heps X hX F

end
end ImbalancedChen.P4AOriginalFull87UnilateralStoppedLevel
