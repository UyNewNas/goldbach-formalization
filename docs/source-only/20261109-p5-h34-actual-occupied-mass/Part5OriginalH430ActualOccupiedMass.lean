import ImbalancedChen.Part5OriginalH430ActualSievedPositionPayment

/-!
P5.6 / h34: the ENTIRE occupied original source-sieve portion of the
genuine resolved request history, counted at its original LIST indices.

Earlier source proved a lower bound on Phi using ONE occupied position.
This packet uses ALL positions with positive literal sourceSieveCount,
retaining collisions among equal integer parent products and the actual
positive path marks. It gives an unconditional, quantitative improvement
of the original q-to-marked unpaid envelope, not an identification of an
arithmetic quotient q with a historical product d.

No assertion is made that any occupied position exists uniformly, that
its mark pays a specific q/tag, or that the original H430 selected owner
has been identified. The original physical Q and cutoff 11/5 are used.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualOccupiedMass

noncomputable section

open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430ActualResolvedMarkedPushforward
open Part5OriginalH430ActualUnpaidOrdinaryEnvelope
open Part5OriginalH430ActualSievedPositionPayment
open Part5OriginalH430TrueCountMarkedGap
open Part5UpperTables.OriginalU34
open P2EnhancedTwentyOneSameQWeighted

/-- The literal source-sieve cardinality at one genuinely resolved index.
Its integer product is not the arithmetic quotient prime q. -/
def actualPositionSourceCount (N n : ℕ) (k : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (l : Index N n k tau p g) : ℕ :=
  let d := parentProduct (levelOccurrence l).current.old
  sourceSieveCount N d (d * N)
    (cutoff (rootQ N n k tau p) d (11/5))

/-- Only the actual resolved positions whose original sieve is nonempty.
The Fin position, rather than the integer product, remains the index. -/
def actualOccupiedPositions (N n : ℕ) (k : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : Finset (Index N n k tau p g) :=
  (activePositions N n k tau p g).filter
    (fun l => 0 < actualPositionSourceCount N n k tau p g l)

/-- Original positive path marks at ALL occupied positions; an empty
occupied source has zero mass even when its Theta is positive. -/
def actualOccupiedMass (N n : ℕ) (k : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ actualOccupiedPositions N n k tau p g, levelMark l

theorem occupied_positions_are_resolved
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualOccupiedPositions N n k tau p g ⊆
      activePositions N n k tau p g := by
  intro l hl
  exact (Finset.mem_filter.mp hl).1

/-- Exact restriction of the genuine Phi to occupied Fin positions.
Unoccupied summands vanish because their natural sieve count is zero;
different positions with equal d are NOT collapsed. -/
theorem actual_Phi_eq_occupied_position_sum
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    Phi N (rootQ N n k tau p)
      (activeProductSupport N n k tau p g)
      (activeProductSigma N n k tau p g) (11/5) =
    ∑ l ∈ actualOccupiedPositions N n k tau p g,
      actualPositionPhiTerm N n k tau p g l := by
  rw [activeProduct_Phi_exact]
  change
    (∑ l ∈ activePositions N n k tau p g,
      actualPositionPhiTerm N n k tau p g l) =
    ∑ l ∈ actualOccupiedPositions N n k tau p g,
      actualPositionPhiTerm N n k tau p g l
  unfold actualOccupiedPositions
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hsrc : 0 < actualPositionSourceCount N n k tau p g l
  · simp [hsrc]
  · have hz : actualPositionSourceCount N n k tau p g l = 0 :=
      Nat.eq_zero_of_not_pos hsrc
    have hterm : actualPositionPhiTerm N n k tau p g l = 0 := by
      change levelMark l *
        (actualPositionSourceCount N n k tau p g l : ℝ) = 0
      rw [hz]
      simp
    simp [hsrc, hterm]

theorem actual_occupied_mass_nonneg
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    0 ≤ actualOccupiedMass N n k tau p g := by
  unfold actualOccupiedMass
  apply Finset.sum_nonneg
  intro l hl
  exact (mark_pos (levelOccurrence l)).le

theorem actual_occupied_mass_pos_of_nonempty
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (h : (actualOccupiedPositions N n k tau p g).Nonempty) :
    0 < actualOccupiedMass N n k tau p g := by
  obtain ⟨l, hl⟩ := h
  unfold actualOccupiedMass
  apply Finset.sum_pos'
  · intro j hj
    exact (mark_pos (levelOccurrence j)).le
  · exact ⟨l, hl, mark_pos (levelOccurrence l)⟩

/-- EVERY occupied occurrence supplies at least one copy of its real
positive path mark to Phi. This is stronger than taking one position,
and it needs neither an owner nor a fabricated q-product correspondence. -/
theorem actual_occupied_mass_le_Phi
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualOccupiedMass N n k tau p g ≤
      Phi N (rootQ N n k tau p)
        (activeProductSupport N n k tau p g)
        (activeProductSigma N n k tau p g) (11/5) := by
  rw [actual_Phi_eq_occupied_position_sum]
  unfold actualOccupiedMass
  apply Finset.sum_le_sum
  intro l hl
  have hsrc : 0 < actualPositionSourceCount N n k tau p g l := by
    exact (Finset.mem_filter.mp hl).2
  have hn : 1 ≤ actualPositionSourceCount N n k tau p g l := hsrc
  have hr : (1 : ℝ) ≤
      (actualPositionSourceCount N n k tau p g l : ℝ) := by
    exact_mod_cast hn
  change levelMark l ≤
    levelMark l * (actualPositionSourceCount N n k tau p g l : ℝ)
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hr (mark_pos (levelOccurrence l)).le)

/-- The original arithmetic q debt is bounded using ALL real occupied
historical marks, rather than only one position or the ordinary count.
No term is deemed to have paid a q receipt. -/
theorem actual_unpaid_le_occupied_mass_envelope
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualUnpaidAt N n k tau p g ≤
      max (((originalReceiver N p).card : ℝ) -
        5 * actualOccupiedMass N n k tau p g) 0 := by
  have hphi := actual_occupied_mass_le_Phi N n k tau p g
  have hdiff :
      ((originalReceiver N p).card : ℝ) -
        5 * Phi N (rootQ N n k tau p)
          (activeProductSupport N n k tau p g)
          (activeProductSigma N n k tau p g) (11/5) ≤
      ((originalReceiver N p).card : ℝ) -
        5 * actualOccupiedMass N n k tau p g := by
    linarith
  dsimp only [actualUnpaidAt, unpaidOriginalMarkedGap,
    originalMarkedDiscrepancy]
  exact max_le (hdiff.trans (le_max_left _ _)) (le_max_right _ _)

/-- The literal two-tag original U3/U4 finite occupancy envelope.
A root in the overlap has TWO summands; no quotient over q, tag,
product or resolved Fin position is taken. -/
def actualU34OccupiedEnvelope
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) : ℝ :=
  (∑ p ∈ originalBand N .U3,
    max (((originalReceiver N p).card : ℝ) -
      5 * actualOccupiedMass N n .U3 tau p (depth .U3 p)) 0) +
  (∑ p ∈ originalBand N .U4,
    max (((originalReceiver N p).card : ℝ) -
      5 * actualOccupiedMass N n .U4 tau p (depth .U4 p)) 0)

/-- Genuine original U3/U4 unpaid arithmetic totals are controlled by
the full occupied-index mass at independently chosen actual histories.
The selected owner and effective H430 debt payment remain open. -/
theorem actual_U34_unpaid_le_occupied_envelope
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) :
    actualU34Unpaid N n tau depth ≤
      actualU34OccupiedEnvelope N n tau depth := by
  unfold actualU34Unpaid actualU34OccupiedEnvelope
  apply add_le_add
  · apply Finset.sum_le_sum
    intro p hp
    exact actual_unpaid_le_occupied_mass_envelope
      N n .U3 tau p (depth .U3 p)
  · apply Finset.sum_le_sum
    intro p hp
    exact actual_unpaid_le_occupied_mass_envelope
      N n .U4 tau p (depth .U4 p)

end
end ImbalancedChen.Part5OriginalH430ActualOccupiedMass
