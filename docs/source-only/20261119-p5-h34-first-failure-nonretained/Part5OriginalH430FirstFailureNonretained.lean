import ImbalancedChen.Part5OriginalH430ExactQ80FullSeedBase

/-!
P5.6 / h34: a genuine earliest-crossing certificate for the original
430-step integer Q80 table. It is a NECESSARY failure classification,
not a payment of the Buchstab or bank sources and not a CLOSED-CELL
induction. If an integer ceiling dominates the authentic seed but fails
at round 430, the first round of failure cannot be caused by retention:
one of the actual enabled Buchstab suffixes, or a targeted upper-table
row from the literal 106-row bank scan, is strictly above that ceiling.

No new source, count family, target-equivalent hypothesis, numerical
coefficient, rounding convention, or external theorem is introduced.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FirstFailureNonretained
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (rows)
open Part5OriginalH430LiteralRoundActionStep

/-- Finite first-crossing induction. The witness is an ACTUAL previous
iterate, not a newly chosen hypothetical predecessor array. It works
with the same integer ceiling for all cells and both tables. -/
theorem first_round_crossing (ceiling : Table)
    (hseed : ∀ upper i, iterate 0 upper i ≤ ceiling upper i) :
    ∀ m : ℕ,
      (∃ upper i, ceiling upper i < iterate (m + 1) upper i) →
      ∃ j : ℕ, j ≤ m ∧
        (∀ upper i, iterate j upper i ≤ ceiling upper i) ∧
        ∃ upper i, ceiling upper i < iterate (j + 1) upper i := by
  intro m
  induction m with
  | zero =>
      intro hbad
      exact ⟨0, by omega, hseed, by simpa using hbad⟩
  | succ m ih =>
      intro hbad
      by_cases hsafe : ∀ upper i,
          iterate (m + 1) upper i ≤ ceiling upper i
      · refine ⟨m + 1, by omega, hsafe, ?_⟩
        simpa [Nat.succ_eq_add_one] using hbad
      · have hprevbad : ∃ upper i,
            ceiling upper i < iterate (m + 1) upper i := by
          by_contra hn
          apply hsafe
          intro upper i
          exact le_of_not_gt (fun hgt => hn ⟨upper, i, hgt⟩)
        obtain ⟨j, hj, hbefore, hcross⟩ := ih hprevbad
        exact ⟨j, by omega, hbefore, hcross⟩

/-- A failure of the ACTUAL 430-round Q80 iterate above any valid
common integer ceiling has a first offending generation g < 430.
Retention cannot be responsible there, because every predecessor cell
in BOTH tables still obeys the ceiling. The remaining alternatives
are exactly the authentic Buchstab suffix or a targeted original
106-bank upper-table row. No choice is added to the producer. -/
theorem literal_first_failure_is_nonretained (ceiling : Table)
    (hseed : ∀ upper i, iterate 0 upper i ≤ ceiling upper i)
    (hterminal : ∃ upper i,
      ceiling upper i < iterate 430 upper i) :
    ∃ g : Fin 430,
      (∀ upper i, iterate g.val upper i ≤ ceiling upper i) ∧
      ∃ upper i,
        (50 ≤ i.val ∧
          ceiling upper i <
            (if upper then
              suffix (iterate g.val) false (max 50 (i.val - 49))
             else suffix (iterate g.val) true (i.val - 49))) ∨
        (upper = true ∧ ∃ k : Fin 106,
          i.val ∈ (rows k).targets ∧
          ceiling upper i < candidate (iterate g.val) (rows k)) := by
  have hlast : ∃ upper i,
      ceiling upper i < iterate (429 + 1) upper i := by
    simpa only [show 429 + 1 = 430 by decide] using hterminal
  obtain ⟨j, hj, hbefore, upper, i, hcross⟩ :=
    first_round_crossing ceiling hseed 429 hlast
  let g : Fin 430 := ⟨j, by omega⟩
  refine ⟨g, ?_, upper, i, ?_⟩
  · change ∀ upper i, iterate j upper i ≤ ceiling upper i
    exact hbefore
  · have hcross' : ceiling upper i <
        iterate (g.val + 1) upper i := by
      change ceiling upper i < iterate (j + 1) upper i
      exact hcross
    rcases actual_iteration_overflow_has_action_witness
      g upper i (ceiling upper i) hcross' with hr | hb | hk
    · exact False.elim ((not_lt_of_ge (hbefore upper i)) hr)
    · exact Or.inl hb
    · exact Or.inr hk

end
end ImbalancedChen.Part5OriginalH430FirstFailureNonretained
