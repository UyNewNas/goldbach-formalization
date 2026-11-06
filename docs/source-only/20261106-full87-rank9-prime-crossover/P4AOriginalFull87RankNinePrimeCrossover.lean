import ImbalancedChen.P4AOriginalFull87RankNineBothBadCancellation
import ImbalancedChen.P4AOriginalFull87RankNineHistoryRisk
import ImbalancedChen.P4AOriginalFull87RankNineInheritedSplit
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: the genuine first-choice rank-nine physical correction is controlled
by the exact three-mode real threshold at EACH original remaining prime.
This improves the previous double-historical-failure cancellation:
only actual first-choice decisions that differ at the two frozen levels
can contribute to the old-minus-new ninth correction.

The source is the literal firstExitRejectedAttempts recursion; no new
sieve policy, no fabricated retained leaf, no changed parent, no
occurrence deduplication, and no inherited mask. The unprocessed suffix
Euler product is retained in every individual physical invoice.

These are finite conditional candidate proofs, NOT a small-o estimate,
not a reserve payment, and not a full-q arithmetic identification.
-/

namespace ImbalancedChen.P4AOriginalFull87RankNinePrimeCrossover
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87OwnedEighthSource
  (frontier states_eq_owner_filter frontier_sign_mass)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87RankNineHistoryRisk
  (historyOddSquareCeiling upper_history_iff_ceiling_lt)
open P4AOriginalFull87RankNineInheritedSplit
  (rank_nine_upper_rejected_iff_three_modes)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts
    failed_attempt_mem_valid_prefix_and_suffix)
open P4AOriginalFull87CorrectionRankTerminal
  (rankNinePhysicalFailedAt rankNineSigned ownedRankNineSigned)
open P4AOriginalFull87SignedDeletionLedger (physicalFailedAt)

/-- Literal rank-nine threshold for the next genuine remaining prime.
The max keeps all three tests: total, inherited odd square, and the
NEW minimum square. The inherited term is computed on the original
eight-prime word; the occurrence list is never replaced by a Finset. -/
def rankNineChoiceThreshold (older : List ℕ) (p : ℕ) : ℝ :=
  max ((((p :: older).prod : ℕ) : ℝ))
    (max (historyOddSquareCeiling older)
      ((((p :: older).prod : ℕ) : ℝ) * (p : ℝ) ^ 2))

/-- Rank-nine selection is STRICTLY above all three actual thresholds.
No assumption that the old inherited history was already admissible.
If the product test passes, positivity of R follows from the product's
nonnegativity, so the historical ceiling lemma is applied legally. -/
theorem rankNine_first_choice_pass_iff_threshold
    (R : ℝ) (older : List ℕ) (p : ℕ)
    (hlen : older.length = 8) (hnodup : older.Nodup)
    (hpmin : ∀ r ∈ older, p < r) :
    ordinaryParityRosserPolicy false R false (p :: older) = true ↔
      rankNineChoiceThreshold older p < R := by
  let T : ℝ := (((p :: older).prod : ℕ) : ℝ)
  let H : ℝ := historyOddSquareCeiling older
  let U : ℝ := T * (p : ℝ) ^ 2
  have hfail :
      ordinaryParityRosserPolicy false R false (p :: older) = false ↔
        R ≤ T ∨
        ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R older.toFinset ∨
        R ≤ U := by
    simpa [T, U] using
      rank_nine_upper_rejected_iff_three_modes R older p hlen hnodup hpmin
  have hnonneg : (0 : ℝ) ≤ T := by
    dsimp [T]
    exact Nat.cast_nonneg _
  change ordinaryParityRosserPolicy false R false (p :: older) = true ↔
    max T (max H U) < R
  constructor
  · intro hpass
    have hnotfail :
        ¬ ordinaryParityRosserPolicy false R false (p :: older) = false := by
      simp [hpass]
    have hno :
        ¬ (R ≤ T ∨
          ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R older.toFinset ∨
          R ≤ U) := fun hh => hnotfail (hfail.mpr hh)
    have hT : T < R := lt_of_not_ge (fun h => hno (Or.inl h))
    have hUpper :
        LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
          R older.toFinset := by
      by_contra hbad
      exact hno (Or.inr (Or.inl hbad))
    have hR : 0 < R := lt_of_le_of_lt hnonneg hT
    have hH : H < R :=
      (upper_history_iff_ceiling_lt older R hR).mp hUpper
    have hU : U < R := lt_of_not_ge (fun h => hno (Or.inr (Or.inr h)))
    exact max_lt hT (max_lt hH hU)
  · intro hcut
    have hT : T < R :=
      lt_of_le_of_lt (le_max_left T (max H U)) hcut
    have hrest : max H U < R :=
      lt_of_le_of_lt (le_max_right T (max H U)) hcut
    have hH : H < R :=
      lt_of_le_of_lt (le_max_left H U) hrest
    have hU : U < R :=
      lt_of_le_of_lt (le_max_right H U) hrest
    have hR : 0 < R := lt_of_le_of_lt hnonneg hT
    have hUpper :
        LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
          R older.toFinset :=
      (upper_history_iff_ceiling_lt older R hR).mpr hH
    have hnotfail :
        ¬ ordinaryParityRosserPolicy false R false (p :: older) = false := by
      intro hf
      rcases hfail.mp hf with ht | hbad | hu
      · exact (not_le_of_gt hT) ht
      · exact hbad hUpper
      · exact (not_le_of_gt hU) hu
    cases hp : ordinaryParityRosserPolicy false R false (p :: older) with
    | false => exact (hnotfail hp).elim
    | true => rfl

/-- The same exact threshold at a REAL owner/trim eighth occurrence. -/
theorem actual_rankNine_first_choice_iff_threshold
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool) (p : ℕ) (hp : p ∈ s.remaining) :
    ordinaryParityRosserPolicy false
      (actualFrozenPost8Level n e q om N c s useParent)
      false (p :: s.selectedPrefix) = true ↔
    rankNineChoiceThreshold s.selectedPrefix p <
      actualFrozenPost8Level n e q om N c s useParent := by
  obtain ⟨h8, hsorted, _, hboundary, _⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  exact rankNine_first_choice_pass_iff_threshold
    _ s.selectedPrefix p h8 hsorted.nodup (hboundary p hp)

/-- Exact half-open crossing of the TWO unchanged frozen real levels.
An equality with either threshold belongs to the rejected side. -/
def rankNineThresholdCrosses
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (p : ℕ) : Prop :=
  let t := rankNineChoiceThreshold s.selectedPrefix p
  let old := actualFrozenPost8Level n e q om N c s true
  let new := actualFrozenPost8Level n e q om N c s false
  (t < old ∧ new ≤ t) ∨ (t < new ∧ old ≤ t)

/-- All three modes, including total and new-minimum squares, enter the
SAME exact crossover condition; no historical mode classification is
subtracted across two unrelated frozen levels. -/
theorem actual_rankNine_cross_iff_decisions_differ
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (p : ℕ) (hp : p ∈ s.remaining) :
    (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s true)
        false (p :: s.selectedPrefix) ≠
      ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s false)
        false (p :: s.selectedPrefix)) ↔
      rankNineThresholdCrosses n e q om N c s p := by
  let T := rankNineChoiceThreshold s.selectedPrefix p
  let Rold := actualFrozenPost8Level n e q om N c s true
  let Rnew := actualFrozenPost8Level n e q om N c s false
  have hOld := actual_rankNine_first_choice_iff_threshold
    delta n e q om N cap w z c s hs true p hp
  have hNew := actual_rankNine_first_choice_iff_threshold
    delta n e q om N cap w z c s hs false p hp
  unfold rankNineThresholdCrosses
  change _ ↔ (T < Rold ∧ Rnew ≤ T) ∨ (T < Rnew ∧ Rold ≤ T)
  rw [le_iff_not_gt, le_iff_not_gt]
  rw [← hOld, ← hNew]
  cases ho : ordinaryParityRosserPolicy false Rold false
      (p :: s.selectedPrefix) <;>
    cases hn : ordinaryParityRosserPolicy false Rnew false
      (p :: s.selectedPrefix) <;> simp [ho, hn]

/-- Direct one-step physical score, with its ORIGINAL smaller suffix. -/
private def firstChoiceSigned {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → ℝ
  | [] => 0
  | p :: ps =>
      firstChoiceSigned policy h pre positive mass ps +
        if policy (!positive) (p :: pre) = true then 0
        else FirstExitRejectedAttempt.value h
          { older := pre, rejected := p, smaller := ps,
            positive := positive, mass := mass }

/-- The only non-cancelled first-choice invoice is a genuine policy
disagreement. It uses one physical score, not both separate absolute
failure invoices; each occurrence is visited exactly once. -/
private def firstChoiceCrossCost {α : Type*}
    (P Q : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → ℝ
  | [] => 0
  | p :: ps =>
      firstChoiceCrossCost P Q h pre positive mass ps +
        if P (!positive) (p :: pre) = Q (!positive) (p :: pre) then 0
        else |FirstExitRejectedAttempt.value h
          { older := pre, rejected := p, smaller := ps,
            positive := positive, mass := mass }|

/-- Every rejected event following a successful post-eight selection
is strictly deeper than rank nine in the ORIGINAL recursion. -/
private theorem deep_firstExit_no_rankNine {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (hdeep : 8 < pre.length) :
    (firstExitRejectedAttempts policy h pre positive mass remaining).filter
      (fun a => decide (a.older.length ≤ 8)) = [] := by
  classical
  cases hlist :
      (firstExitRejectedAttempts policy h pre positive mass remaining).filter
        (fun a => decide (a.older.length ≤ 8)) with
  | nil => rfl
  | cons a tail =>
      have ha : a ∈
          (firstExitRejectedAttempts policy h pre positive mass remaining).filter
            (fun b => decide (b.older.length ≤ 8)) := by
        rw [hlist]
        simp
      obtain ⟨hsource, htag⟩ := List.mem_filter.mp ha
      have hle : a.older.length ≤ 8 := of_decide_eq_true htag
      obtain ⟨before, chosen, _, _, _, hword⟩ :=
        failed_attempt_mem_valid_prefix_and_suffix
          policy h pre remaining positive mass a hsource
      have hge : pre.length ≤ a.older.length := by
        rw [hword]
        simp only [List.length_append, List.length_reverse]
        omega
      omega

/-- Actual filtered rank-nine signed sum equals the per-prime first
choice scores, preserving even the skipped candidates and their suffix
locations. The previous root list helper was private, so this theorem
is proved directly from the literal original recursion. -/
private theorem rankNine_source_sum_eq_firstChoice {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (h8 : pre.length = 8) :
    (((firstExitRejectedAttempts policy h pre positive mass remaining).filter
      (fun a => decide (a.older.length ≤ 8))).map
      (FirstExitRejectedAttempt.value h)).sum =
        firstChoiceSigned policy h pre positive mass remaining := by
  classical
  induction remaining with
  | nil => simp [firstExitRejectedAttempts, firstChoiceSigned]
  | cons p ps ih =>
      by_cases hp : policy (!positive) (p :: pre) = true
      · have hdeep :
            (firstExitRejectedAttempts policy h (p :: pre) (!positive)
                (mass * h p) ps).filter
                (fun a => decide (a.older.length ≤ 8)) = [] :=
          deep_firstExit_no_rankNine policy h (p :: pre) ps
            (!positive) (mass * h p) (by simp [h8])
        simp [firstExitRejectedAttempts, firstChoiceSigned, hp,
          List.filter_append, ih, hdeep]
      · simp [firstExitRejectedAttempts, firstChoiceSigned, hp,
          List.filter_append, ih, h8]

private theorem one_choice_cross_bound (a b : Bool) (v : ℝ) :
    |(if a = true then (0 : ℝ) else v) -
       (if b = true then (0 : ℝ) else v)| ≤
      (if a = b then (0 : ℝ) else |v|) := by
  cases a <;> cases b <;> simp

/-- Finite exact support budget on ONE physical remaining word:
agreement contributes zero, and disagreement costs only the value
with the original suffix. No positivity or monotonicity of signed
savings is inferred from the cap. -/
private theorem firstChoice_gap_le_cross_cost {α : Type*}
    (P Q : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    |firstChoiceSigned P h pre positive mass remaining -
      firstChoiceSigned Q h pre positive mass remaining| ≤
        firstChoiceCrossCost P Q h pre positive mass remaining := by
  induction remaining with
  | nil => simp [firstChoiceSigned, firstChoiceCrossCost]
  | cons p ps ih =>
      let a := P (!positive) (p :: pre)
      let b := Q (!positive) (p :: pre)
      let v : ℝ := FirstExitRejectedAttempt.value h
        { older := pre, rejected := p, smaller := ps,
          positive := positive, mass := mass }
      change
        |(firstChoiceSigned P h pre positive mass ps +
            (if a = true then (0 : ℝ) else v)) -
          (firstChoiceSigned Q h pre positive mass ps +
            (if b = true then (0 : ℝ) else v))| ≤
        firstChoiceCrossCost P Q h pre positive mass ps +
          (if a = b then (0 : ℝ) else |v|)
      calc
        _ = |(firstChoiceSigned P h pre positive mass ps -
                firstChoiceSigned Q h pre positive mass ps) +
             ((if a = true then (0 : ℝ) else v) -
              (if b = true then (0 : ℝ) else v))| := by
               congr 1
               ring
        _ ≤ |firstChoiceSigned P h pre positive mass ps -
                firstChoiceSigned Q h pre positive mass ps| +
             |(if a = true then (0 : ℝ) else v) -
                (if b = true then (0 : ℝ) else v)| :=
                  abs_add_le _ _
        _ ≤ firstChoiceCrossCost P Q h pre positive mass ps +
             (if a = b then (0 : ℝ) else |v|) :=
               add_le_add ih (one_choice_cross_bound a b v)

/-- Physical eighth mass is attached ONCE to each genuine first choice;
the value includes the rejected-prime density and actual Euler suffix.
The policy test uses its true parent or finite cap at the same state. -/
def rankNineCrossingInvoice
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  firstChoiceCrossCost
    (ordinaryParityRosserPolicy false
      (actualFrozenPost8Level n e q om N c s true))
    (ordinaryParityRosserPolicy false
      (actualFrozenPost8Level n e q om N c s false))
    halfProductDensity s.selectedPrefix s.positive
    (s.mass * (s.selectedPrefix.map halfProductDensity).prod)
    s.remaining

/-- One-state ninth old-minus-new comparison, with EXACT crossed
first-choice physical invoice instead of both absolute old/new costs.
It is a finite bound, not yet normalized to H_N or paid to a reserve. -/
theorem actual_rankNine_signed_gap_le_crossing_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    |rankNineSigned n e q om N c s true -
      rankNineSigned n e q om N c s false| ≤
        rankNineCrossingInvoice n e q om N c s := by
  have h8 : s.selectedPrefix.length = 8 :=
    (owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs).1
  let m8 : ℝ := s.mass * (s.selectedPrefix.map halfProductDensity).prod
  unfold rankNineSigned rankNinePhysicalFailedAt rankNineCrossingInvoice
  change
    |(((firstExitRejectedAttempts
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s true))
        halfProductDensity s.selectedPrefix s.positive m8
        s.remaining).filter
        (fun a => decide (a.older.length ≤ 8))).map
        (FirstExitRejectedAttempt.value halfProductDensity)).sum -
     (((firstExitRejectedAttempts
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s false))
        halfProductDensity s.selectedPrefix s.positive m8
        s.remaining).filter
        (fun a => decide (a.older.length ≤ 8))).map
        (FirstExitRejectedAttempt.value halfProductDensity)).sum| ≤
      firstChoiceCrossCost
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s true))
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s false))
        halfProductDensity s.selectedPrefix s.positive m8 s.remaining
  rw [rankNine_source_sum_eq_firstChoice
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s true))
        halfProductDensity s.selectedPrefix s.remaining
        s.positive m8 h8,
      rankNine_source_sum_eq_firstChoice
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s false))
        halfProductDensity s.selectedPrefix s.remaining
        s.positive m8 h8]
  exact firstChoice_gap_le_cross_cost _ _ _ _ _ _ _

private theorem cross_cost_zero_of_all_agree {α : Type*}
    (P Q : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (hagree : ∀ p ∈ remaining,
      P (!positive) (p :: pre) = Q (!positive) (p :: pre)) :
    firstChoiceCrossCost P Q h pre positive mass remaining = 0 := by
  induction remaining with
  | nil => rfl
  | cons p ps ih =>
      have hp : P (!positive) (p :: pre) =
          Q (!positive) (p :: pre) := hagree p (by simp)
      have htail : ∀ t ∈ ps,
          P (!positive) (t :: pre) = Q (!positive) (t :: pre) := by
        intro t ht
        exact hagree t (by simp [ht])
      simp [firstChoiceCrossCost, hp, ih htail]

/-- The exact crossing test suffices for ZERO complete ninth GAP, even
when BOTH individual rank-nine correction sums are nonzero. This
strictly extends the previous both-historical-guards-bad cancellation. -/
theorem actual_rankNine_gap_zero_without_prime_crossing
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hno : ∀ p ∈ s.remaining,
      ¬ rankNineThresholdCrosses n e q om N c s p) :
    rankNineSigned n e q om N c s true -
      rankNineSigned n e q om N c s false = 0 := by
  have hfront : s ∈ frontier n e q om N cap w z := by
    have ht := hs
    rw [states_eq_owner_filter] at ht
    exact (List.mem_filter.mp ht).1
  have hpos : s.positive = true :=
    (frontier_sign_mass n e q om N cap w z s hfront).1
  have hagree : ∀ p ∈ s.remaining,
      ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s true)
        (!s.positive) (p :: s.selectedPrefix) =
      ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s false)
        (!s.positive) (p :: s.selectedPrefix) := by
    intro p hp
    have hnot : ¬
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s true)
        false (p :: s.selectedPrefix) ≠
       ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s false)
        false (p :: s.selectedPrefix)) := by
      intro hdiff
      exact hno p hp ((actual_rankNine_cross_iff_decisions_differ
        delta n e q om N cap w z c s hs p hp).mp hdiff)
    simpa [hpos] using (not_not.mp hnot)
  have hzero : rankNineCrossingInvoice n e q om N c s = 0 := by
    unfold rankNineCrossingInvoice
    exact cross_cost_zero_of_all_agree _ _ _ _ _ _ _ hagree
  have hbound := actual_rankNine_signed_gap_le_crossing_invoice
    delta n e q om N cap w z c s hs
  have hvalue :
      |rankNineSigned n e q om N c s true -
        rankNineSigned n e q om N c s false| = 0 := by
    apply le_antisymm
    · simpa [hzero] using hbound
    · exact abs_nonneg _
  exact abs_eq_zero.mp hvalue

/-- Support-only filtering of the ORIGINAL ordered, owned 87-domain
eighth state list. This does NOT modify either sieve policy or attach
a foreign mask to an inherited branch. -/
def ownedRankNinePrimeCrossStates
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) :=
  (states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c).filter
    (fun s => decide (∃ p ∈ s.remaining,
       rankNineThresholdCrosses n e q om N c s p))

private theorem list_sum_filter_of_zero {α : Type*}
    (xs : List α) (f : α → ℝ) (P : α → Prop)
    [DecidablePred P]
    (hzero : ∀ x ∈ xs, ¬ P x → f x = 0) :
    (xs.map f).sum =
      ((xs.filter (fun x => decide (P x))).map f).sum := by
  induction xs with
  | nil => simp
  | cons x ys ih =>
      have htail : ∀ y ∈ ys, ¬ P y → f y = 0 := by
        intro y hy hnot
        exact hzero y (by simp [hy]) hnot
      by_cases hp : P x
      · simp [hp, ih htail]
      · have hx : f x = 0 := hzero x (by simp) hp
        simp [hp, hx, ih htail]

private theorem list_map_sum_sub {α : Type*}
    (xs : List α) (f g : α → ℝ) :
    (xs.map (fun x => f x - g x)).sum =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x ys ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem list_abs_sum_le_invoice {α : Type*}
    (xs : List α) (f b : α → ℝ)
    (h : ∀ a ∈ xs, |f a| ≤ b a) :
    |(xs.map f).sum| ≤ (xs.map b).sum := by
  induction xs with
  | nil => simp
  | cons a ys ih =>
      have ha := h a (by simp)
      have htail : ∀ y ∈ ys, |f y| ≤ b y := by
        intro y hy
        exact h y (by simp [hy])
      have hr := ih htail
      simp only [List.map_cons, List.sum_cons]
      calc
        |f a + (ys.map f).sum| ≤ |f a| + |(ys.map f).sum| :=
          abs_add_le _ _
        _ ≤ b a + (ys.map b).sum := add_le_add ha hr

/-- Exact ORIGINAL87 old-minus-new rank-nine signed gap uses only the
first-choice threshold crossing support. The previous both-bad domain
is included among the cancelled states, but additional states can
cancel because all actual first-choice decisions agree. -/
theorem owned_rankNine_gap_eq_prime_cross_support
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    ownedRankNineSigned r n e q om N cap w z c true -
      ownedRankNineSigned r n e q om N cap w z c false =
      ((ownedRankNinePrimeCrossStates r n e q om N cap w z c).map
        (fun s => rankNineSigned n e q om N c s true -
          rankNineSigned n e q om N c s false)).sum := by
  classical
  unfold ownedRankNineSigned ownedRankNinePrimeCrossStates
  rw [← list_map_sum_sub]
  apply list_sum_filter_of_zero
  intro s hs hnot
  apply actual_rankNine_gap_zero_without_prime_crossing
    (width r) n e q om N cap w z c s hs
  intro p hp hc
  exact hnot ⟨p, hp, hc⟩

/-- A single EXACT finite invoice of the full87 rank-nine GAP, summing
only actual crossed decisions, rather than two old/new historical risk
invoices. Neither ordinary residual asymptotics nor reserve payment
has been established by this finite absolute inequality. -/
theorem owned_rankNine_gap_abs_le_prime_cross_invoices
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    |ownedRankNineSigned r n e q om N cap w z c true -
      ownedRankNineSigned r n e q om N cap w z c false| ≤
      ((states (width r) n e q om N cap w z
        (fun _ : ℕ => (1 : ℝ)) c).map
        (rankNineCrossingInvoice n e q om N c)).sum := by
  unfold ownedRankNineSigned
  rw [← list_map_sum_sub]
  apply list_abs_sum_le_invoice
  intro s hs
  exact actual_rankNine_signed_gap_le_crossing_invoice
    (width r) n e q om N cap w z c s hs

end
end ImbalancedChen.P4AOriginalFull87RankNinePrimeCrossover
