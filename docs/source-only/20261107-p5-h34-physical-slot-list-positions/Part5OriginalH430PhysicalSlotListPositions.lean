import ImbalancedChen.Part5OriginalH430PhysicalSlotCollisionLedger

/-!
P5.6 / h34: the first ACTUAL LIST-POSITION witness for each observed
physical (Q,p,ell) slot.

A rank-two frontier membership is a membership in a LIST, not an indexed
occurrence and not a full/selected/inherited payment. This packet extracts
an actual Fin index in the true recursive firstExitDepthFrontier 2 for
each observed original U3/U4 physical slot. The chosen position is
relative to that slot's physical Q; different Q histories are not put
in a common payment pool. At any fixed Q and fixed position, the
selected prefix determines p and ell; a position cannot independently
support different ordered two-prime prefixes.

No number of historical positions is assumed, no per-q duplication is
introduced, and the chosen list index is NOT asserted to survive the
full/selected/inherited filters or to carry an owner payment.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430PhysicalSlotListPositions

noncomputable section
open scoped Classical
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430RankTwoFrontierConverse
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger

/-- Literal recursive LIST at one and only one actual physical Q. -/
def actualPhysicalRankTwoList (N cap : ℕ) (z0 Q : ℝ) (lower : Bool) :
    List (FirstExitDepthState ℕ) :=
  firstExitDepthFrontier 2
    (ordinaryRosserRetainedPolicy lower Q)
    (fun r : ℕ => 1 / ((r : ℝ) - 1))
    [] true 1 (roughPrimeUniverse N cap 0 z0)

/-- A genuine list membership carries an actual bounded occurrence
position. This does not assume Nodup and does not quotient state values. -/
private theorem member_has_fin_position {α : Type*}
    (xs : List α) (x : α) (hx : x ∈ xs) :
    ∃ i : Fin xs.length, xs[i] = x := by
  induction xs with
  | nil =>
      simp at hx
  | cons a ys ih =>
      rcases List.mem_cons.mp hx with heq | htail
      · subst x
        exact ⟨⟨0, by simp⟩, rfl⟩
      · obtain ⟨i, hi⟩ := ih htail
        refine ⟨⟨i.1 + 1, by simp; omega⟩, ?_⟩
        simpa using hi

/-- Every actually OBSERVED physical (Q,p,ell) slot has an actual
bounded list position with precisely [ell,p] as selected prefix.
The q-to-ell step uses the original retained second-factor supplier;
neither q nor its tag is replaced by a fabricated second-stage letter. -/
theorem observed_slot_has_actual_rank_two_position
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower) :
    ∃ i : Fin (actualPhysicalRankTwoList N cap z0 slot.1 lower).length,
      (actualPhysicalRankTwoList N cap z0 slot.1 lower)[i].selectedPrefix =
        [slot.2.2, slot.2.1] := by
  obtain ⟨key, hkey, hslot⟩ := Finset.mem_image.mp hs
  obtain ⟨z, hz, hchosen⟩ := Finset.mem_image.mp hkey
  have hret : hasRetainedOriginalSecond N cap precision tau z0 lower z := by
    exact (Finset.mem_filter.mp hz).2
  have hfactor := chosen_second_factor_spec
    N cap precision tau z0 lower z hret
  obtain ⟨d, hd, hpre⟩ :=
    (retained_original_second_iff_actual_rank_two
      N cap precision tau z0 lower z
      (chosenSecondFactor N cap precision tau z0 lower z)).mp hfactor.2.2
  have hphysical :
      (originalPhysicalQ N precision tau z, arithmeticPrime z,
        chosenSecondFactor N cap precision tau z0 lower z) = slot := by
    calc
      _ = physicalRankTwoSlot N precision tau
          (chosenRankTwoKey N cap precision tau z0 lower z) :=
        (chosen_key_physical_source N cap precision tau z0 lower z).symm
      _ = physicalRankTwoSlot N precision tau key := by rw [hchosen]
      _ = slot := hslot
  have hQ : originalPhysicalQ N precision tau z = slot.1 :=
    congrArg (fun t : ℝ × ℕ × ℕ => t.1) hphysical
  have hp : arithmeticPrime z = slot.2.1 :=
    congrArg (fun t : ℝ × ℕ × ℕ => t.2.1) hphysical
  have hell :
      chosenSecondFactor N cap precision tau z0 lower z = slot.2.2 :=
    congrArg (fun t : ℝ × ℕ × ℕ => t.2.2) hphysical
  have hd' : d ∈ actualPhysicalRankTwoList N cap z0 slot.1 lower := by
    simpa only [actualPhysicalRankTwoList, hQ] using hd
  have hprefix : d.selectedPrefix = [slot.2.2, slot.2.1] := by
    calc
      _ = [chosenSecondFactor N cap precision tau z0 lower z,
          arithmeticPrime z] := hpre
      _ = [slot.2.2, slot.2.1] := by rw [hell, hp]
  obtain ⟨i, hi⟩ := member_has_fin_position
    (actualPhysicalRankTwoList N cap z0 slot.1 lower) d hd'
  refine ⟨i, ?_⟩
  rw [hi]
  exact hprefix

/-- Canonical bounded occurrence choice, made only for an observed
slot. It is NOT a full/selected/inherited owner or paid position. -/
def observedSlotRankTwoPosition
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower) :
    Fin (actualPhysicalRankTwoList N cap z0 slot.1 lower).length :=
  Classical.choose
    (observed_slot_has_actual_rank_two_position
      N cap precision tau z0 lower slot hs)

/-- The chosen position's state has the exact physical slot prefix;
the index is in the REAL frontier list, not an auxiliary Finset. -/
theorem observed_slot_rank_two_position_prefix
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower) :
    (actualPhysicalRankTwoList N cap z0 slot.1 lower)[
        observedSlotRankTwoPosition
          N cap precision tau z0 lower slot hs].selectedPrefix =
      [slot.2.2, slot.2.1] := by
  exact Classical.choose_spec
    (observed_slot_has_actual_rank_two_position
      N cap precision tau z0 lower slot hs)

/-- An individual real LIST POSITION, under fixed physical Q, cannot
represent two different ordered (p,ell) slots. This is not an
unproved global cross-Q injection or historical payment. -/
theorem same_actual_position_forces_same_prime_pair
    (N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length)
    (p ell p' ell' : ℕ)
    (h : (actualPhysicalRankTwoList N cap z0 Q lower)[i].selectedPrefix =
      [ell, p])
    (h' : (actualPhysicalRankTwoList N cap z0 Q lower)[i].selectedPrefix =
      [ell', p']) : p = p' ∧ ell = ell' := by
  have heq : ([ell, p] : List ℕ) = [ell', p'] := h.symm.trans h'
  have hell : ell = ell' := (List.cons.inj heq).1
  have hp : p = p' := (List.cons.inj (List.cons.inj heq).2).1
  exact ⟨hp, hell⟩

end
end ImbalancedChen.Part5OriginalH430PhysicalSlotListPositions
