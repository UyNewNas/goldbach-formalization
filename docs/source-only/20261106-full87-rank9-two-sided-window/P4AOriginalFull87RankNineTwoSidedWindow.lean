import ImbalancedChen.P4AOriginalFull87RankNinePrimeCrossover
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4 continuation on the literal owned 87-domain rank-nine physical source.
The preceding prime reciprocal invoice had a STRICT cubic upper cutoff
but no lower support condition.  This packet separates the exact
half-open crossing window into two disjoint, explicitly historical
and cubic cases, without replacing the frozen levels, changing any
prime occurrence, or charging the old/new bills twice.

No prime harmonic asymptotic or reserve payment is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87RankNineTwoSidedWindow
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualEighthCarrier (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87RankNineHistoryRisk (historyOddSquareCeiling)
open P4AOriginalFull87RankNinePrimeCrossover
  (rankNineChoiceThreshold rankNineThresholdCrosses
   rankNineReciprocalCrossingCost ownedRankNineReciprocalCost
   owned_rankNine_gap_abs_le_reciprocal_cost)
open P4AOriginalFull87CorrectionRankTerminal (ownedRankNineSigned)

/-- The total-product test is already implied by the NEW square test
at an actual positive prime. The historical odd-square test remains:
it cannot be dropped. The cubic product is the ORIGINAL eight primes
times the actual rejected prime cubed. -/
theorem threshold_eq_history_max_cubic
    (older : List ℕ) (p : ℕ) (hp : 1 ≤ p) :
    rankNineChoiceThreshold older p =
      max (historyOddSquareCeiling older)
        ((older.prod : ℝ) * (p : ℝ) ^ 3) := by
  let T : ℝ := (((p :: older).prod : ℕ) : ℝ)
  let J : ℝ := historyOddSquareCeiling older
  let U : ℝ := T * (p : ℝ) ^ 2
  have hpReal : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hsq : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have hTU : T ≤ U := by
    simpa [U] using (mul_le_mul_of_nonneg_left hsq hT0)
  have hMax : max T (max J U) = max J U := by
    apply le_antisymm
    · exact max_le (hTU.trans (le_max_right J U)) le_rfl
    · exact le_max_right _ _
  calc
    rankNineChoiceThreshold older p = max J U := by
      change max T (max J U) = max J U
      exact hMax
    _ = max (historyOddSquareCeiling older)
          ((older.prod : ℝ) * (p : ℝ) ^ 3) := by
      dsimp [J, U, T]
      congr 1
      simp only [List.prod_cons, Nat.cast_mul]
      ring

/-- The strict original choice test produces a HALF-OPEN crossing
interval, even when one frozen level or the test is exactly an endpoint. -/
private theorem crossing_iff_minmax (t old new : ℝ) :
    ((t < old ∧ new ≤ t) ∨ (t < new ∧ old ≤ t)) ↔
      min old new ≤ t ∧ t < max old new := by
  constructor
  · rintro (h | h)
    · exact ⟨(min_le_right old new).trans h.2,
        h.1.trans_le (le_max_left old new)⟩
    · exact ⟨(min_le_left old new).trans h.2,
        h.1.trans_le (le_max_right old new)⟩
  · rintro ⟨hlo, hhi⟩
    rcases le_total old new with h | h
    · rw [min_eq_left h] at hlo
      rw [max_eq_right h] at hhi
      exact Or.inr ⟨hhi, hlo⟩
    · rw [min_eq_right h] at hlo
      rw [max_eq_left h] at hhi
      exact Or.inl ⟨hhi, hlo⟩

/-- A geometric historical square threshold can sit INSIDE the level
crossing interval; then every sufficiently small remaining prime may
contribute. Otherwise a crossing prime must lie in the genuine cubic
annulus. The two alternatives are DISJOINT, not two costs for one prime. -/
def historicalShell (older : List ℕ) (p : ℕ)
    (old new : ℝ) : Prop :=
  let lo := min old new
  let hi := max old new
  let J := historyOddSquareCeiling older
  let C := (older.prod : ℝ) * (p : ℝ) ^ 3
  lo ≤ J ∧ J < hi ∧ C < hi

def cubicAnnulus (older : List ℕ) (p : ℕ)
    (old new : ℝ) : Prop :=
  let lo := min old new
  let hi := max old new
  let J := historyOddSquareCeiling older
  let C := (older.prod : ℝ) * (p : ℝ) ^ 3
  J < lo ∧ lo ≤ C ∧ C < hi

private theorem max_window_split (J C lo hi : ℝ) :
    (lo ≤ max J C ∧ max J C < hi) ↔
      ((lo ≤ J ∧ J < hi ∧ C < hi) ∨
       (J < lo ∧ lo ≤ C ∧ C < hi)) := by
  constructor
  · rintro ⟨hl, hu⟩
    have hJ : J < hi := (le_max_left J C).trans_lt hu
    have hC : C < hi := (le_max_right J C).trans_lt hu
    by_cases hjlo : lo ≤ J
    · exact Or.inl ⟨hjlo, hJ, hC⟩
    · have hjlt : J < lo := lt_of_not_ge hjlo
      have hclo : lo ≤ C := by
        rcases (le_max_iff.mp hl) with h | h
        · exact (not_le_of_gt hjlt h).elim
        · exact h
      exact Or.inr ⟨hjlt, hclo, hC⟩
  · rintro (⟨hjl, hjh, hch⟩ | ⟨hjl, hcl, hch⟩)
    · exact ⟨hjl.trans (le_max_left J C), max_lt hjh hch⟩
    · have hjh : J < hi := hjl.trans (hcl.trans_lt hch)
      exact ⟨hcl.trans (le_max_right J C), max_lt hjh hch⟩

theorem crossing_iff_two_disjoint_windows
    (older : List ℕ) (p : ℕ) (old new : ℝ)
    (hp : 1 ≤ p) :
    ((rankNineChoiceThreshold older p < old ∧
        new ≤ rankNineChoiceThreshold older p) ∨
     (rankNineChoiceThreshold older p < new ∧
        old ≤ rankNineChoiceThreshold older p)) ↔
      historicalShell older p old new ∨
      cubicAnnulus older p old new := by
  rw [crossing_iff_minmax,
      threshold_eq_history_max_cubic older p hp]
  simpa only [historicalShell, cubicAnnulus] using
    (max_window_split (historyOddSquareCeiling older)
       ((older.prod : ℝ) * (p : ℝ) ^ 3)
       (min old new) (max old new))

/-- The disjointness is purely the original historical threshold vs.
the smaller of the two REAL frozen levels. -/
theorem historicalShell_disjoint_cubicAnnulus
    (older : List ℕ) (p : ℕ) (old new : ℝ) :
    ¬ (historicalShell older p old new ∧
       cubicAnnulus older p old new) := by
  intro h
  rcases h with ⟨hh, hc⟩
  dsimp [historicalShell] at hh
  dsimp [cubicAnnulus] at hc
  exact not_lt_of_ge hh.1 hc.1

/-- The abstract window theorem is applied to each REAL target-deleted
prime occurrence of the original licensed-sixth eighth frontier. -/
theorem actual_cross_iff_two_disjoint_windows
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (p : ℕ) (hp : p ∈ s.remaining) :
    rankNineThresholdCrosses n e q om N c s p ↔
      historicalShell s.selectedPrefix p
        (actualFrozenPost8Level n e q om N c s true)
        (actualFrozenPost8Level n e q om N c s false) ∨
      cubicAnnulus s.selectedPrefix p
        (actualFrozenPost8Level n e q om N c s true)
        (actualFrozenPost8Level n e q om N c s false) := by
  obtain ⟨_, _, _, _, last, _, _, _, hrem⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  have hmem : p ∈ roughPrimeUniverse N cap w (last : ℝ) := by
    simpa only [hrem] using hp
  have hprime : Nat.Prime p := mem_roughPrimeUniverse_prime hmem
  have hp1 : 1 ≤ p := by have h := hprime.two_le; omega
  simpa only [rankNineThresholdCrosses] using
    crossing_iff_two_disjoint_windows s.selectedPrefix p
      (actualFrozenPost8Level n e q om N c s true)
      (actualFrozenPost8Level n e q om N c s false) hp1

/-- Two finite fees over the SAME ordered prime list. No mask is attached
to any continuing tree; these are just partitions of an already-proved
absolute rank-nine discrepancy budget. -/
def actualHistoricalShellCost (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  (s.remaining.map (fun p =>
    if historicalShell s.selectedPrefix p
        (actualFrozenPost8Level n e q om N c s true)
        (actualFrozenPost8Level n e q om N c s false)
    then 1 / ((p : ℝ) - 1) else 0)).sum

def actualCubicAnnulusCost (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  (s.remaining.map (fun p =>
    if cubicAnnulus s.selectedPrefix p
        (actualFrozenPost8Level n e q om N c s true)
        (actualFrozenPost8Level n e q om N c s false)
    then 1 / ((p : ℝ) - 1) else 0)).sum

private theorem map_sum_add {α : Type*} (xs : List α)
    (f g : α → ℝ) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- Exact partition, not an upper bound counted twice. Original
occurrence multiplicities survive even if two primes share coordinates. -/
theorem actual_reciprocal_cost_eq_disjoint_windows
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    rankNineReciprocalCrossingCost n e q om N c s =
      actualHistoricalShellCost n e q om N c s +
      actualCubicAnnulusCost n e q om N c s := by
  unfold rankNineReciprocalCrossingCost
    actualHistoricalShellCost actualCubicAnnulusCost
  calc
    (s.remaining.map (fun p =>
      if rankNineThresholdCrosses n e q om N c s p
      then 1 / ((p : ℝ) - 1) else 0)).sum =
      (s.remaining.map (fun p =>
        (if historicalShell s.selectedPrefix p
            (actualFrozenPost8Level n e q om N c s true)
            (actualFrozenPost8Level n e q om N c s false)
          then 1 / ((p : ℝ) - 1) else 0) +
        (if cubicAnnulus s.selectedPrefix p
            (actualFrozenPost8Level n e q om N c s true)
            (actualFrozenPost8Level n e q om N c s false)
          then 1 / ((p : ℝ) - 1) else 0))).sum := by
        congr 1
        apply List.map_congr_left
        intro p hp
        have heq := actual_cross_iff_two_disjoint_windows
          delta n e q om N cap w z c s hs p hp
        have hdis := historicalShell_disjoint_cubicAnnulus
          s.selectedPrefix p
          (actualFrozenPost8Level n e q om N c s true)
          (actualFrozenPost8Level n e q om N c s false)
        by_cases hh : historicalShell s.selectedPrefix p
            (actualFrozenPost8Level n e q om N c s true)
            (actualFrozenPost8Level n e q om N c s false)
        · have hc : ¬ cubicAnnulus s.selectedPrefix p
              (actualFrozenPost8Level n e q om N c s true)
              (actualFrozenPost8Level n e q om N c s false) :=
            fun hc => hdis ⟨hh, hc⟩
          simp [heq, hh, hc]
        · by_cases hc : cubicAnnulus s.selectedPrefix p
              (actualFrozenPost8Level n e q om N c s true)
              (actualFrozenPost8Level n e q om N c s false)
          · simp [heq, hh, hc]
          · simp [heq, hh, hc]
    _ = _ := map_sum_add _ _ _

/-- An original state whose inherited square ceiling lies strictly below
BOTH frozen levels has NO historical-shell fee: only the genuine cubic
annulus remains. This is conditional, not a claimed full-87 licence. -/
theorem actual_historical_shell_cost_zero_of_safe_history
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hSafe : historyOddSquareCeiling s.selectedPrefix <
      min (actualFrozenPost8Level n e q om N c s true)
          (actualFrozenPost8Level n e q om N c s false)) :
    actualHistoricalShellCost n e q om N c s = 0 := by
  unfold actualHistoricalShellCost
  have hmap :
      (s.remaining.map (fun p =>
        if historicalShell s.selectedPrefix p
            (actualFrozenPost8Level n e q om N c s true)
            (actualFrozenPost8Level n e q om N c s false)
        then 1 / ((p : ℝ) - 1) else 0)) =
        s.remaining.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro p hp
    have hnot : ¬ historicalShell s.selectedPrefix p
        (actualFrozenPost8Level n e q om N c s true)
        (actualFrozenPost8Level n e q om N c s false) := by
      intro h
      exact (not_le_of_gt hSafe) (show
        min (actualFrozenPost8Level n e q om N c s true)
            (actualFrozenPost8Level n e q om N c s false) ≤
        historyOddSquareCeiling s.selectedPrefix from h.1)
    simp [hnot]
  rw [hmap]
  simp

/-- All 87 source occurrences remain, and each physical eighth mass is
attached once. No unknown archive frequency or reserve balance is used. -/
theorem owned_rankNine_gap_abs_le_two_window_invoice
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hEven : 2 ∣ N) (w z : ℝ) (c : Cell) :
    |ownedRankNineSigned r n e q om N cap w z c true -
      ownedRankNineSigned r n e q om N cap w z c false| ≤
      ((states (width r) n e q om N cap w z
        (fun _ : ℕ => (1 : ℝ)) c).map (fun s =>
          |s.mass * (s.selectedPrefix.map halfProductDensity).prod| *
            (actualHistoricalShellCost n e q om N c s +
             actualCubicAnnulusCost n e q om N c s))).sum := by
  calc
    _ ≤ ownedRankNineReciprocalCost r n e q om N cap w z c :=
      owned_rankNine_gap_abs_le_reciprocal_cost
        r n e q om N cap hEven w z c
    _ = _ := by
      unfold ownedRankNineReciprocalCost
      congr 1
      apply List.map_congr_left
      intro s hs
      rw [actual_reciprocal_cost_eq_disjoint_windows
        (width r) n e q om N cap w z c s hs]

end
end ImbalancedChen.P4AOriginalFull87RankNineTwoSidedWindow
