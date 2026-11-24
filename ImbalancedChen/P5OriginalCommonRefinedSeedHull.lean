import ImbalancedChen.P5OriginalCommonRefinedPreservation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The E constructor is unchanged.  This file computes its new fourth and
fifth levels in terms of the independently defined ORIGINAL row maxima.
Only the seed changes: the original eligibility predicates, licensed rows,
pointwise selected masks and buffers are kept literally.  In particular a
changed fifth parent is a specific fallback-over-old-fourth source region,
not a new arbitrary flag.  No original numerical bank is inferred from
the type OriginalData, and no signed-density monotonicity is asserted.
-/

namespace ImbalancedChen.P5OriginalCommonRefinedSeedHull
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonRefinedPreservation
open P1OriginalVariableFourthContinuation hiding exponent4

/-- Adding a second seed commutes with this actual finite maximum. -/
theorem finiteMax_max_seed {ι : Type*} (rows : Finset ι)
    (eligible : ι → Prop) (profile : ι → ℝ) (a b : ℝ) :
    finiteMax rows eligible profile (max a b) =
      max (finiteMax rows eligible profile a) b := by
  apply le_antisymm
  · apply finiteMax_le
    · exact max_le ((finiteMax_seed_le rows eligible profile a).trans (le_max_left _ _))
        (le_max_right _ _)
    · intro r hr he
      exact (finiteMax_row_le rows eligible profile a r hr he).trans (le_max_left _ _)
  · apply max_le
    · apply finiteMax_le
      · exact (le_max_left a b).trans (finiteMax_seed_le rows eligible profile (max a b))
      · intro r hr he
        exact finiteMax_row_le rows eligible profile (max a b) r hr he
    · exact (le_max_right a b).trans (finiteMax_seed_le rows eligible profile (max a b))

def oldFourth (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  P1OriginalVariableFourthContinuation.exponent4 (d.e : ℝ) d.chi d.m d.omega N d.rows4
    (producerEligible d.licensed4) (fun r => r.bufferedCandidate (d.e : ℝ)) pre

def oldInherited (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  P1OriginalVariableFifthContinuation.inherited4 d.e d.chi d.m d.omega N
    d.rows4 d.licensed4 pre

def oldFifth (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  P1OriginalVariableFifthContinuation.exponent5 d.e d.chi d.m d.omega N
    d.rows4 d.licensed4 d.J5 d.rows5 pre

def commonInherited (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  exponent4 d N (rosserAncestor 4 pre)

/-- The exact fallback read by the fifth node, on its SAME fourth ancestor. -/
def inheritedFallback (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  fallbackSeed d N (rosserAncestor 4 pre)

theorem oldInherited_eq (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    oldInherited d N pre = oldFourth d N (rosserAncestor 4 pre) := rfl

theorem fourth_eq_old_max_fallback (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    exponent4 d N pre = max (oldFourth d N pre) (fallbackSeed d N pre) := by
  unfold exponent4 oldFourth P1OriginalVariableFourthContinuation.exponent4
  split_ifs
  · exact finiteMax_max_seed _ _ _ _ _
  · rfl

theorem inherited_eq_old_max_fallback (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    commonInherited d N pre = max (oldInherited d N pre) (inheritedFallback d N pre) :=
  fourth_eq_old_max_fallback d N (rosserAncestor 4 pre)

theorem fifth_eq_old_max_fallback (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    exponent5 d N pre = max (oldFifth d N pre) (inheritedFallback d N pre) := by
  have hi := inherited_eq_old_max_fallback d N pre
  unfold exponent5 oldFifth P1OriginalVariableFifthContinuation.exponent5
  change (if pre.length = 5 then
    finiteMax d.rows5
      (fun r => P1OriginalVariableFifthContinuation.eligible d.e d.chi d.m d.omega
        d.J5 r (primeHistoryLogCoordinates N 5 pre))
      (fun r => P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected
        (primeHistoryLogCoordinates N 5 pre)) (commonInherited d N pre)
    else commonInherited d N pre) = _
  rw [hi]
  split_ifs
  · exact finiteMax_max_seed _ _ _ _ _
  · rfl

theorem oldInherited_le_oldFifth (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    oldInherited d N pre ≤ oldFifth d N pre :=
  P1OriginalVariableFifthContinuation.inherited4_le_exponent5
    d.e d.chi d.m d.omega N d.rows4 d.licensed4 d.J5 d.rows5 pre

def changedParents (d : OriginalData) (N : ℝ) : Set (List ℕ) :=
  {pre | pre.length = 5 ∧ commonInherited d N pre ≠ oldInherited d N pre}

/-- No unknown parent equality occurs in this source-region description. -/
theorem changedParents_iff_fallback (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    pre ∈ changedParents d N ↔ pre.length = 5 ∧
      oldInherited d N pre < inheritedFallback d N pre := by
  rw [changedParents, Set.mem_setOf_eq, inherited_eq_old_max_fallback]
  constructor
  · rintro ⟨hl, hn⟩
    exact ⟨hl, lt_of_not_ge (fun h => hn (max_eq_left h))⟩
  · rintro ⟨hl, hh⟩
    exact ⟨hl, fun he => (not_lt_of_ge (le_of_eq he))
      (hh.trans_le (le_max_right _ _))⟩

theorem changedParents_iff_literal_guards (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    pre ∈ changedParents d N ↔ pre.length = 5 ∧
      ((P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdGuard N (rosserAncestor 4 pre) ∧
        oldInherited d N pre < VariableEnvelope.v
          (primeHistoryLogCoordinates N 3 (rosserAncestor 3 (rosserAncestor 4 pre)) 1 +
            primeHistoryLogCoordinates N 3 (rosserAncestor 3 (rosserAncestor 4 pre)) 2)) ∨
       (¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdGuard N (rosserAncestor 4 pre) ∧
        P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondGuard N (rosserAncestor 4 pre) ∧
        oldInherited d N pre < VariableEnvelope.v
          (primeHistoryLogCoordinates N 2 (rosserAncestor 2 (rosserAncestor 4 pre)) 1))) := by
  have hs : originalSeed d N (rosserAncestor 4 pre) ≤ oldInherited d N pre :=
    seedExponent_le_exponent4 (d.e : ℝ) d.chi d.m d.omega N d.rows4
      (producerEligible d.licensed4) (fun r => r.bufferedCandidate (d.e : ℝ))
      (rosserAncestor 4 pre)
  rw [changedParents_iff_fallback]
  unfold inheritedFallback fallbackSeed
  split_ifs <;> simp_all [not_lt_of_ge hs]

theorem fifth_eq_old_off_changedParents (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5) (hout : pre ∉ changedParents d N) :
    exponent5 d N pre = oldFifth d N pre := by
  have hf : inheritedFallback d N pre ≤ oldInherited d N pre := by
    by_contra hn
    exact hout ((changedParents_iff_fallback d N pre).mpr ⟨hlen, lt_of_not_ge hn⟩)
  rw [fifth_eq_old_max_fallback, max_eq_left (hf.trans (oldInherited_le_oldFifth d N pre))]

/-- A changed inherited parent need not change the fifth final cap:
an original fifth candidate can already dominate the actual fallback. -/
theorem fifth_eq_old_iff (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    exponent5 d N pre = oldFifth d N pre ↔ inheritedFallback d N pre ≤ oldFifth d N pre := by
  rw [fifth_eq_old_max_fallback, max_eq_left_iff]

/-- If the fallback clears the old final cap, the new fifth action itself
has zero level increment over its actual newly raised fourth parent. -/
theorem fallback_above_old_fifth (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hf : oldFifth d N pre ≤ inheritedFallback d N pre) :
    exponent5 d N pre = commonInherited d N pre := by
  rw [fifth_eq_old_max_fallback, inherited_eq_old_max_fallback,
    max_eq_right hf, max_eq_right ((oldInherited_le_oldFifth d N pre).trans hf)]

end
end ImbalancedChen.P5OriginalCommonRefinedSeedHull
