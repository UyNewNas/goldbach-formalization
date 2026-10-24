import ImbalancedChen.CurrentChenUpsilon1011JointSource

/-!
The original eleventh source, disintegrated over its last pair.

This is a finite prerequisite for the original selected-mask mean.  The
quotient source still uses all four factors and the second-prime cutoff.
Neither a pointwise distribution estimate nor an asymptotic mean is asserted.

CP / exact remaining analytic gap: after this disintegration one must prove
the original averaged upper estimate on the common positive four-prefix
partition.  Its pointwise candidate kernels are the switched
`K * omega ((1-S4)/z) / z` and all eligible ordinary
`4 * (1-H248 (max 2 (L/w))) / L`, with every full/selected square gate.
The numerical cover alone does not estimate these cardinal weights.  The
pinned LiLiu closed cross quadruple `goldbachWeightG12` has weak ordering,
closed prime walls and `literalH`; it is not this selected-mask source.
No such mean, source-to-kernel estimate, or numerical conclusion is an input
to any declaration here.  Status: source_written / uncompiled.
-/

namespace ImbalancedChen.P5Z.U11Original

open scoped BigOperators
open Classical

noncomputable section

/-- Finite Fubini with a predicate belonging only to the second label.
The weight may have either sign. -/
theorem sum_last_label {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → β → Prop) (Q : β → Prop)
    (f : α × β → ℝ) :
    (∑ v ∈ (s ×ˢ t).filter (fun v => P v.1 v.2 ∧ Q v.2), f v) =
      ∑ b ∈ t.filter Q, ∑ a ∈ s.filter (fun a => P a b), f (a, b) := by
  classical
  simp only [Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hQ : Q b <;> simp [hQ]

/-- The last pair is ordered automatically by its two walls.  The lower
wall of the fourth prime is weak and its original upper wall is strict. -/
def lastPairs (N : ℕ) (H D : ℝ) (E : ℕ × ℕ → Prop) : Finset (ℕ × ℕ) :=
  (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter fun q =>
    (q.1 : ℝ) < H ∧ H ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) < D ∧ ¬ E q

/-- The first two labels of the original four-prime source. -/
def firstPairs (N : ℕ) (A : ℝ) (q : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter fun p =>
    A ≤ (p.1 : ℝ) ∧ p.1 < p.2 ∧ p.2 < q.1

/-- Exact factorization before any averaging or inequality. -/
theorem sum_fullSelector (N : ℕ) (A H D : ℝ) (E : ℕ × ℕ → Prop)
    (f : ((ℕ × ℕ) × (ℕ × ℕ)) → ℝ) :
    (∑ v ∈ (chenY11FullPrimeSelector N A H D).filter (fun v => ¬ E v.2),
      f v) =
      ∑ q ∈ lastPairs N H D E, ∑ p ∈ firstPairs N A q, f (p, q) := by
  classical
  have hs : (chenY11FullPrimeSelector N A H D).filter (fun v => ¬ E v.2) =
      ((chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N) ×ˢ
        (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N)).filter
        (fun v => (A ≤ (v.1.1 : ℝ) ∧ v.1.1 < v.1.2 ∧ v.1.2 < v.2.1) ∧
          ((v.2.1 : ℝ) < H ∧ H ≤ (v.2.2 : ℝ) ∧ (v.2.2 : ℝ) < D ∧
            ¬ E v.2)) := by
    ext v
    simp only [chenY11FullPrimeSelector, Finset.mem_filter]
    tauto
  rw [hs]
  exact sum_last_label _ _ _ _ f

/-- The actual cardinal weight attached to one retained last pair. -/
def sourceMass (N : ℕ) (A : ℝ) (q : ℕ × ℕ) : ℝ :=
  ∑ p ∈ firstPairs N A q,
    ((chenSiftedQuotientPrimeSource N (p.1 * p.2 * q.1 * q.2)
      (p.2 : ℝ)).card : ℝ)

theorem sourceMass_nonneg (N : ℕ) (A : ℝ) (q : ℕ × ℕ) :
    0 ≤ sourceMass N A q := by
  unfold sourceMass
  exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- Strict prefix ordering leaves no mass when the third label is at or
below the first-prime wall.  This removes no fourth-prime interval. -/
theorem firstPairs_eq_empty_of_third_le (N : ℕ) (A : ℝ) (q : ℕ × ℕ)
    (hq : (q.1 : ℝ) ≤ A) : firstPairs N A q = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨_, hA, h12, h2q⟩ := Finset.mem_filter.mp hp
  have h1q : (p.1 : ℝ) < (q.1 : ℝ) := by
    exact_mod_cast h12.trans h2q
  exact (not_lt_of_ge (hq.trans hA)) h1q

theorem sourceMass_eq_zero_of_third_le (N : ℕ) (A : ℝ) (q : ℕ × ℕ)
    (hq : (q.1 : ℝ) ≤ A) : sourceMass N A q = 0 := by
  simp only [sourceMass, firstPairs_eq_empty_of_third_le N A q hq,
    Finset.sum_empty]

/-- Literal selected receiver counts become a positive measure on the
last pair, with no squarefreeness assumption and no loss of labels. -/
theorem sum_selectedReceivers (N : ℕ) (A H D : ℝ) (E : ℕ × ℕ → Prop) :
    (∑ P ∈ chenAdditivePrimeCarrier N,
      (chenY11Selected (N - P) A H D (fun q => ¬ E q) : ℝ)) =
      ∑ q ∈ lastPairs N H D E, sourceMass N A q := by
  rw [sum_chenY11Selected_eq_siftedQuotientPrimeSource]
  exact sum_fullSelector N A H D E _

/-- Current cutoffs are substituted literally; in particular no shorter
fourth-prime band is used to obtain this decomposition. -/
theorem current_eq_lastPair_source (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon11 N E =
      ∑ q ∈ lastPairs N ((N : ℝ) ^ (19 / 125 : ℝ))
          ((N : ℝ) ^ (59 / 250 : ℝ)) E,
        sourceMass N ((N : ℝ) ^ (417 / 5000 : ℝ)) q := by
  rw [currentChenUpsilon11_eq_siftedQuotientPrimeSource]
  exact sum_fullSelector N _ _ _ E _

/-- Only strictly positive-width third-prime fibers contribute.  The
last-prime band remains the full original half-open band. -/
theorem current_eq_active_lastPair_source (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon11 N E =
      ∑ q ∈ (lastPairs N ((N : ℝ) ^ (19 / 125 : ℝ))
          ((N : ℝ) ^ (59 / 250 : ℝ)) E).filter
            (fun q => (N : ℝ) ^ (417 / 5000 : ℝ) < (q.1 : ℝ)),
        sourceMass N ((N : ℝ) ^ (417 / 5000 : ℝ)) q := by
  rw [current_eq_lastPair_source, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hA : (N : ℝ) ^ (417 / 5000 : ℝ) < (q.1 : ℝ)
  · simp only [hA, if_pos]
  · rw [if_neg hA]
    exact sourceMass_eq_zero_of_third_le N _ q (le_of_not_gt hA)

/-- The finite last-pair measure has exactly the original half-open
fourth-prime interval, including its left wall. -/
theorem mem_lastPairs_iff (N : ℕ) (H D : ℝ) (E : ℕ × ℕ → Prop)
    (q : ℕ × ℕ) :
    q ∈ lastPairs N H D E ↔
      q.1 ∈ chenAdditivePrimeCarrier N ∧ q.2 ∈ chenAdditivePrimeCarrier N ∧
        (q.1 : ℝ) < H ∧ H ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) < D ∧ ¬ E q := by
  simp only [lastPairs, Finset.mem_filter, Finset.mem_product]
  tauto

theorem lastPairs_antitone_mask (N : ℕ) (H D : ℝ)
    (E F : ℕ × ℕ → Prop) (hEF : ∀ q, E q → F q) :
    lastPairs N H D F ⊆ lastPairs N H D E := by
  intro q hq
  rw [mem_lastPairs_iff] at hq ⊢
  exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1,
    fun hE => hq.2.2.2.2.2 (hEF q hE)⟩

/-- Enlarging the deleted pair set reduces the actual eleventh count.
This uses positivity of the derived four-prime fiber, rather than an
unproved sign assertion about an analytic kernel. -/
theorem current_antitone_mask (N : ℕ) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ q, E q → F q) :
    currentChenUpsilon11 N F ≤ currentChenUpsilon11 N E := by
  rw [current_eq_lastPair_source, current_eq_lastPair_source]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (lastPairs_antitone_mask N _ _ E F hEF)
    (fun q _ _ => sourceMass_nonneg N _ q)

/-- Finite pair localization: only mask values on the full original
last-pair domain can affect the eleventh count. -/
theorem current_mask_congr (N : ℕ) (E F : ℕ × ℕ → Prop)
    (hEF : ∀ q, q ∈ lastPairs N ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ)) (fun _ => False) → (E q ↔ F q)) :
    currentChenUpsilon11 N E = currentChenUpsilon11 N F := by
  rw [current_eq_lastPair_source, current_eq_lastPair_source]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext q
  simp only [lastPairs, Finset.mem_filter] at hEF ⊢
  by_cases hq : q ∈ chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N ∧
      (q.1 : ℝ) < (N : ℝ) ^ (19 / 125 : ℝ) ∧
      (N : ℝ) ^ (19 / 125 : ℝ) ≤ (q.2 : ℝ) ∧
      (q.2 : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ)
  · have heq := hEF q (by tauto)
    tauto
  · tauto

end

end ImbalancedChen.P5Z.U11Original
