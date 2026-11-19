import ImbalancedChen.P4AOriginalFull87ReflectedNonprimeRoom
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Finite discrete Abel transfer for the ORIGINAL reflected prime condition
and ORIGINAL PLUS-Rosser weight on the actual bounded quotient room.

The reference density is deliberately an arbitrary function of the FULL
modulus. No prime distribution or estimate is assumed. The result isolates
an exact prefix discrepancy and the total variation of the TRUE room weight,
not a supposed small reflected-nonprime complement.
-/

namespace ImbalancedChen.P4AOriginalFull87ReflectedPrefixAbel
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87ActualPrimitiveRosserRoom (actualPrimitiveRosserRoom)
open P4AOriginalFull87ReflectedNonprimeRoom (reflectedNonprimeRosserRoom)
open P4AOriginalFull87SignedBetaFrozenGlobal (originalSignedFullBetaEvent)

/-- Finite summation by parts, including the endpoint term. -/
private theorem range_abel (w u : ℕ → ℝ) (m : ℕ) :
    (∑ a ∈ Finset.range m, w a * u a) =
    w m * (∑ a ∈ Finset.range m, u a) +
    ∑ t ∈ Finset.range m, (w t - w (t + 1)) *
      (∑ a ∈ Finset.range (t + 1), u a) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hU : (∑ a ∈ Finset.range (m + 1), u a) =
          (∑ a ∈ Finset.range m, u a) + u m := by
        rw [Finset.sum_range_succ]
      have hT :
          (∑ t ∈ Finset.range (m + 1), (w t - w (t + 1)) *
            (∑ a ∈ Finset.range (t + 1), u a)) =
          (∑ t ∈ Finset.range m, (w t - w (t + 1)) *
            (∑ a ∈ Finset.range (t + 1), u a)) +
            (w m - w (m + 1)) *
              ((∑ a ∈ Finset.range m, u a) + u m) := by
        rw [Finset.sum_range_succ, hU]
      rw [Finset.sum_range_succ, hU, hT, ih]
      ring

/-- A general finite set may be embedded in a whole integer range
without dropping repeated original fifth/sixth occurrences (which are
handled at the outer List level, not by this inner Finset). -/
private theorem room_sum_range (room : Finset ℕ) (m : ℕ)
    (hroom : room ⊆ Finset.range m) (beta d : ℕ → ℝ) :
    (∑ a ∈ room, beta a * d a) =
    ∑ a ∈ Finset.range m, (if a ∈ room then beta a else 0) * d a := by
  classical
  calc
    _ = ∑ a ∈ room, (if a ∈ room then beta a else 0) * d a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [ha]
    _ = _ := Finset.sum_subset hroom (by
      intro a ha hnot
      simp [hnot])

/-- The upper endpoint is the literal complete-modulus quotient,
not N or a separately invented sieve cutoff; b=0 also yields empty room. -/
private theorem actual_room_bounded (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p : ℕ) :
    actualPrimitiveRosserRoom N cap w L X pre p ⊆
      Finset.range (N / (p :: pre).prod + 1) := by
  intro a ha
  have hfull := (Finset.mem_filter.mp ha).1
  let b : ℕ := (p :: pre).prod
  change a ∈ Finset.Ico
    ((N / (2 * b) + 1).max (X / b + 1))
    ((Nat.ceil L).min (N / b + 1)) at hfull
  have hupper : a < N / b + 1 :=
    lt_of_lt_of_le (Finset.mem_Ico.mp hfull).2 (min_le_right _ _)
  exact Finset.mem_range.mpr hupper

/-- The same original PLUS coefficient, zero outside the actual room. -/
def actualRoomBetaWeight (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p a : ℕ) : ℝ :=
  if a ∈ actualPrimitiveRosserRoom N cap w L X pre p then
    actualSmallRosserPlus N cap w L a else 0

/-- The original reflected prime test, not an auxiliary AP surrogate. -/
def reflectedPrimeStep (N : ℕ) (pre : List ℕ)
    (p a : ℕ) : ℝ :=
  if N - a * (p :: pre).prod ∈ chenPrimePrefix N then 1 else 0

/-- A wholly finite prefix discrepancy for the literal reflected test.
The value mean b is only a reference scalar supplied separately for each
complete modulus b, not a hypothesis that it is the true prime density. -/
def reflectedPrimePrefixDiscrepancy (N : ℕ) (pre : List ℕ)
    (p : ℕ) (mean : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ a ∈ Finset.range k,
    (reflectedPrimeStep N pre p a - mean (p :: pre).prod)

/-- Exact total-variation correction, with the real PLUS-Rosser weights,
including the jump across every gap in its original bounded support. -/
def originalRoomAbelCorrection (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
    (actualRoomBetaWeight N cap w L X pre p t -
      actualRoomBetaWeight N cap w L X pre p (t + 1)) *
      reflectedPrimePrefixDiscrepancy N pre p mean (t + 1)

/-- Actual room's endpoint weight vanishes, without changing strict gates. -/
private theorem actual_weight_endpoint_zero (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p : ℕ) :
    actualRoomBetaWeight N cap w L X pre p (N / (p :: pre).prod + 1) = 0 := by
  have hn : N / (p :: pre).prod + 1 ∉ actualPrimitiveRosserRoom N cap w L X pre p := by
    intro h
    have hbound := actual_room_bounded N cap w L X pre p h
    have hlt := Finset.mem_range.mp hbound
    omega
  simp [actualRoomBetaWeight, hn]

/-- Exact room-weighted reflected PRIME sum equals a modulus-dependent
reference mean plus the genuine prefix-discrepancy variation invoice.
Neither the mean nor the discrepancy has been authenticated analytically. -/
theorem actual_room_reflected_prime_abel
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) :
    (∑ a ∈ (actualPrimitiveRosserRoom N cap w L X pre p).filter
        (fun a => N - a * (p :: pre).prod ∈ chenPrimePrefix N),
        actualSmallRosserPlus N cap w L a) =
    mean (p :: pre).prod *
      (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
        actualSmallRosserPlus N cap w L a) +
      originalRoomAbelCorrection N cap w L X pre p mean := by
  classical
  let room := actualPrimitiveRosserRoom N cap w L X pre p
  let beta := actualSmallRosserPlus N cap w L
  let weight := actualRoomBetaWeight N cap w L X pre p
  let prime := reflectedPrimeStep N pre p
  let mu := mean (p :: pre).prod
  let U := fun a : ℕ => prime a - mu
  let m := N / (p :: pre).prod + 1
  have hsub : room ⊆ Finset.range m := actual_room_bounded N cap w L X pre p
  have hmass : (∑ a ∈ Finset.range m, weight a) =
      ∑ a ∈ room, beta a := by
    have h := room_sum_range room m hsub beta (fun _ => (1 : ℝ))
    simpa [weight, actualRoomBetaWeight, room, beta] using h.symm
  have hprime :
      (∑ a ∈ room.filter (fun a => N - a * (p :: pre).prod ∈ chenPrimePrefix N),
        beta a) =
      ∑ a ∈ Finset.range m, weight a * prime a := by
    rw [Finset.sum_filter]
    calc
      _ = ∑ a ∈ room, beta a * prime a := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hp : N - a * (p :: pre).prod ∈ chenPrimePrefix N
        · simp [prime, reflectedPrimeStep, hp]
        · simp [prime, reflectedPrimeStep, hp]
      _ = _ := room_sum_range room m hsub beta prime
  have hzero : weight m = 0 := actual_weight_endpoint_zero N cap w L X pre p
  have habel := range_abel weight U m
  have hweighted :
      (∑ a ∈ Finset.range m, weight a * U a) =
      (∑ a ∈ Finset.range m, weight a * prime a) -
        mu * (∑ a ∈ Finset.range m, weight a) := by
    dsimp [U]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    ring
  rw [hweighted, hzero] at habel
  simp only [zero_mul, zero_add] at habel
  change (∑ a ∈ room.filter
      (fun a => N - a * (p :: pre).prod ∈ chenPrimePrefix N), beta a) =
    mu * (∑ a ∈ room, beta a) +
      originalRoomAbelCorrection N cap w L X pre p mean
  rw [hprime, ← hmass]
  unfold originalRoomAbelCorrection reflectedPrimePrefixDiscrepancy
  change (∑ a ∈ Finset.range m, weight a * prime a) =
    mu * (∑ a ∈ Finset.range m, weight a) +
    ∑ t ∈ Finset.range m,
      (weight t - weight (t + 1)) *
        (∑ a ∈ Finset.range (t + 1), U a)
  linarith

/-- Literal nonprime complement equals (1 - mean) times the full
original PLUS room, minus the exact, still-unpaid AP prefix invoice. -/
theorem original_reflected_nonprime_abel
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) :
    (∑ a ∈ reflectedNonprimeRosserRoom N cap w L X pre p,
      actualSmallRosserPlus N cap w L a) =
    (1 - mean (p :: pre).prod) *
      (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
        actualSmallRosserPlus N cap w L a) -
    originalRoomAbelCorrection N cap w L X pre p mean := by
  classical
  let room := actualPrimitiveRosserRoom N cap w L X pre p
  let beta := actualSmallRosserPlus N cap w L
  let prime : ℕ → Prop := fun a => N - a * (p :: pre).prod ∈ chenPrimePrefix N
  have hpartition :
      (∑ a ∈ room.filter (fun a => ¬ prime a), beta a) +
        (∑ a ∈ room.filter prime, beta a) =
      ∑ a ∈ room, beta a := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hp : prime a <;> simp [hp]
  have hprime := actual_room_reflected_prime_abel
    N cap w L X pre p mean
  unfold reflectedNonprimeRosserRoom
  change (∑ a ∈ room.filter (fun a => ¬ prime a), beta a) = _
  change (∑ a ∈ room.filter prime, beta a) =
    mean (p :: pre).prod * (∑ a ∈ room, beta a) +
      originalRoomAbelCorrection N cap w L X pre p mean at hprime
  nlinarith

/-- The exact price of replacing arbitrary PLUS-beta by a reference mean
is the total variation of the original ROOM-TRUNCATED coefficient, not
just its supremum. Gaps, sign changes and strict endpoints all count. -/
def originalRoomBetaVariation (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
    |actualRoomBetaWeight N cap w L X pre p t -
      actualRoomBetaWeight N cap w L X pre p (t + 1)|

/-- Conditional finite transfer: the hypothesis is the explicit bound on
EVERY unweighted reflected prefix (a genuine arithmetic obligation), not
an upper bound on the target weighted prime sum. No external theorem has
been invoked here and E need not yet be o(H_N). -/
theorem actual_room_abel_correction_abs_le_variation
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) (E : ℝ)
    (hE : ∀ k ≤ N / (p :: pre).prod + 1,
      |reflectedPrimePrefixDiscrepancy N pre p mean k| ≤ E) :
    |originalRoomAbelCorrection N cap w L X pre p mean| ≤
      E * originalRoomBetaVariation N cap w L X pre p := by
  classical
  let weight := actualRoomBetaWeight N cap w L X pre p
  let Q := reflectedPrimePrefixDiscrepancy N pre p mean
  unfold originalRoomAbelCorrection originalRoomBetaVariation
  calc
    |∑ t ∈ Finset.range (N / (p :: pre).prod + 1), (weight t - weight (t + 1)) * Q (t + 1)|
        ≤ ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
            |(weight t - weight (t + 1)) * Q (t + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
          |weight t - weight (t + 1)| * |Q (t + 1)| := by
      simp_rw [abs_mul]
    _ ≤ ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
          |weight t - weight (t + 1)| * E := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_left
        (hE (t + 1) (by
          have hlt := Finset.mem_range.mp ht
          omega)) (abs_nonneg _)
    _ = E * ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
          |weight t - weight (t + 1)| := by
      rw [← Finset.sum_mul]
      ring

/-- Source-exact finite primitive-AP error transfer. This does not claim
that the prefix hypothesis holds, that variation is affordable, or that
an external AP theorem has been matched to the true full modulus. -/
theorem actual_room_prime_error_le_primitive_prefix
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) (E : ℝ)
    (hE : ∀ k ≤ N / (p :: pre).prod + 1,
      |reflectedPrimePrefixDiscrepancy N pre p mean k| ≤ E) :
    |(∑ a ∈ (actualPrimitiveRosserRoom N cap w L X pre p).filter
        (fun a => N - a * (p :: pre).prod ∈ chenPrimePrefix N),
        actualSmallRosserPlus N cap w L a) -
      mean (p :: pre).prod *
        (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
          actualSmallRosserPlus N cap w L a)| ≤
      E * originalRoomBetaVariation N cap w L X pre p := by
  rw [actual_room_reflected_prime_abel]
  simp only [add_sub_cancel_left]
  exact actual_room_abel_correction_abs_le_variation
    N cap w L X pre p mean E hE

/-- No ordered source occurrence is converted into a Finset. -/
private theorem list_map_sum_sub {α : Type*} (xs : List α)
    (F G : α → ℝ) :
    (xs.map (fun x => F x - G x)).sum =
    (xs.map F).sum - (xs.map G).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

open P4AOriginalFull87SignedBetaFrozenGlobal
  (frozenSurvivorSignedFullBetaRoom originalSignedFullBetaEvent)
open P4AOriginalFull87ReflectedNonprimeRoom
  (frozenSurvivorSignedReflectedNonprimeBetaRoom
   originalSignedReflectedNonprimeBetaEvent
   physical_after_lower_eq_full_sub_reflected_nonprime)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FrozenSurvivorInvoice (keepFrozenUpperSurvivor)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)

/-- Actual fifth RAW-only/LICENSED-only sign and actual ordered sixth
occurrences, now with each COMPLETE modulus carrying its own mean and
unweighted-reflection discrepancy. Both/inherited remain exactly zero. -/
def originalSignedAbelPrimeEvent
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (mean : ℕ → ℝ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          (mean (p :: fifth.selectedAfter).prod *
            (∑ a ∈ actualPrimitiveRosserRoom N cap w L X
              fifth.selectedAfter p,
              actualSmallRosserPlus N cap w L a) +
           originalRoomAbelCorrection N cap w L X
             fifth.selectedAfter p mean))).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- Exact signed decomposition at the original event, with NO extra
fifth mask and no prime theorem assumed. -/
theorem signed_event_full_minus_nonprime_eq_abel
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (mean : ℕ → ℝ)
    (ev : FifthSixthStoppedEvent ℕ) :
    originalSignedFullBetaEvent N cap w L X ev -
      originalSignedReflectedNonprimeBetaEvent N cap w L X ev =
      originalSignedAbelPrimeEvent N cap w L X mean ev := by
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [originalSignedFullBetaEvent,
        originalSignedReflectedNonprimeBetaEvent,
        originalSignedAbelPrimeEvent]
  | fifthExclusive fifth =>
      let coeff : ℝ := signedTreeCoefficient true fifth.massAfter
      let full : ℕ → ℝ := fun p =>
        ∑ a ∈ actualPrimitiveRosserRoom N cap w L X
          fifth.selectedAfter p, actualSmallRosserPlus N cap w L a
      let missing : ℕ → ℝ := fun p =>
        ∑ a ∈ reflectedNonprimeRosserRoom N cap w L X
          fifth.selectedAfter p, actualSmallRosserPlus N cap w L a
      let abel : ℕ → ℝ := fun p =>
        mean (p :: fifth.selectedAfter).prod * full p +
          originalRoomAbelCorrection N cap w L X
            fifth.selectedAfter p mean
      have hlist :
          (fifth.remainingAfter.map (fun p => coeff * full p)).sum -
          (fifth.remainingAfter.map (fun p => coeff * missing p)).sum =
          (fifth.remainingAfter.map (fun p => coeff * abel p)).sum := by
        calc
          _ = (fifth.remainingAfter.map
                (fun p => coeff * full p - coeff * missing p)).sum :=
            (list_map_sum_sub fifth.remainingAfter
              (fun p => coeff * full p)
              (fun p => coeff * missing p)).symm
          _ = _ := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro p hp
            have h := original_reflected_nonprime_abel N cap w L X
              fifth.selectedAfter p mean
            change missing p = (1 - mean (p :: fifth.selectedAfter).prod) *
              full p - originalRoomAbelCorrection N cap w L X
                fifth.selectedAfter p mean at h
            change coeff * full p - coeff * missing p = coeff * abel p
            rw [h]
            dsimp [abel]
            ring
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [originalSignedFullBetaEvent,
            originalSignedReflectedNonprimeBetaEvent,
            originalSignedAbelPrimeEvent, hk, coeff, full, missing, abel]
            using hlist
      | licensedOnly =>
          have hneg :
              -((fifth.remainingAfter.map (fun p => coeff * full p)).sum) -
                -((fifth.remainingAfter.map (fun p => coeff * missing p)).sum) =
              -((fifth.remainingAfter.map (fun p => coeff * abel p)).sum) := by
            linarith
          simpa [originalSignedFullBetaEvent,
            originalSignedReflectedNonprimeBetaEvent,
            originalSignedAbelPrimeEvent, hk, coeff, full, missing, abel]
            using hneg
      | both =>
          simp [originalSignedFullBetaEvent,
            originalSignedReflectedNonprimeBetaEvent,
            originalSignedAbelPrimeEvent, hk]

/-- Same sharedRankFour, same frozen selector, same occurrence
multiplicity: no independent replacement producer is introduced. -/
def frozenSurvivorSignedAbelPrimeRoom
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalSignedAbelPrimeEvent N cap w
        ((N : ℝ) ^ epsilon) X mean)).sum)).sum

/-- Exact global lifted Abel identity on the same original tagged Lists. -/
theorem frozen_full_minus_reflected_eq_abel
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) :
    frozenSurvivorSignedFullBetaRoom delta n e q om N cap w epsilon X -
      frozenSurvivorSignedReflectedNonprimeBetaRoom
        delta n e q om N cap w epsilon X =
      frozenSurvivorSignedAbelPrimeRoom
        delta n e q om N cap w epsilon X mean := by
  let states := sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))
  let events := fun state =>
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
      (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X)
  let F := originalSignedFullBetaEvent N cap w ((N : ℝ) ^ epsilon) X
  let G := originalSignedReflectedNonprimeBetaEvent
    N cap w ((N : ℝ) ^ epsilon) X
  let H := originalSignedAbelPrimeEvent
    N cap w ((N : ℝ) ^ epsilon) X mean
  change (states.map (fun s => ((events s).map F).sum)).sum -
    (states.map (fun s => ((events s).map G).sum)).sum =
    (states.map (fun s => ((events s).map H).sum)).sum
  calc
    _ = (states.map (fun s =>
          ((events s).map F).sum - ((events s).map G).sum)).sum :=
      (list_map_sum_sub states
        (fun s => ((events s).map F).sum)
        (fun s => ((events s).map G).sum)).symm
    _ = (states.map (fun s =>
          ((events s).map (fun ev => F ev - G ev)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro state hs
      exact (list_map_sum_sub (events state) F G).symm
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro state hs
      apply congrArg List.sum
      apply List.map_congr_left
      intro ev hev
      exact signed_event_full_minus_nonprime_eq_abel
        N cap w ((N : ℝ) ^ epsilon) X mean ev

/-- Original physical RAW-LICENSED stopped difference, with the lower
receiver removed ONCE, equals the actually tagged, full-modulus Abel
ledger. This is a finite equality, not an asymptotic saving. -/
theorem physical_after_lower_eq_original_reflected_abel
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) (mean : ℕ → ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    (rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X (receiverTest N) -
     licensedStopped delta n e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X (receiverTest N)) -
     actualFixedSignedFifthTail delta n e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96))
      ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N) =
    frozenSurvivorSignedAbelPrimeRoom
      delta n e q om N cap w epsilon X mean := by
  rw [physical_after_lower_eq_full_sub_reflected_nonprime
    delta n e q om N cap w epsilon X he hN heps hX]
  exact frozen_full_minus_reflected_eq_abel
    delta n e q om N cap w epsilon X mean

end
end ImbalancedChen.P4AOriginalFull87ReflectedPrefixAbel
