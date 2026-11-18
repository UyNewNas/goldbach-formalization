import ImbalancedChen.Part5OriginalH430LiteralRoundActionStep

/-!
P5.6 h34: exact literal generation-zero Q80 seed on BOTH tables, not
just the 106-bank fixed read anchors (which are all zero initially).
The exact Q80 division remainder is retained. The base condition is
reduced, by an IFF, to the positive first-60-upper analytic bound and
nonnegative upper-tail/lower analytic bounds at actual closed query cells.
These analytic inequalities are NOT asserted or proved here.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ExactQ80FullSeedBase
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (q)
open Part5OriginalUpsilon5CausalDictionary (floorValue)

/-- The exact frozen integer-grid seed, not 2327/100000 as a real. -/
def literalSeedHeight : ℝ :=
  ((2327 * q / 100000 : ℤ) : ℝ) / (2 ^ 80 : ℝ)

theorem literal_seed_integer_quotient :
    (2327 * q / 100000 : ℤ) = 28131703822432420895412 := by
  norm_num [q]

theorem literal_seed_integer_remainder :
    (2327 * q : ℤ) =
      (100000 : ℤ) * (2327 * q / 100000 : ℤ) + 71552 := by
  norm_num [q]

/-- The original Q80 round-down has an exact nonzero remainder. -/
theorem literal_seed_quantization_gap :
    (2327 : ℝ) / 100000 - literalSeedHeight =
      (71552 : ℝ) / (100000 * (2 ^ 80 : ℝ)) := by
  norm_num [literalSeedHeight, q]

theorem literal_seed_height_pos : 0 < literalSeedHeight := by
  norm_num [literalSeedHeight, q]

theorem literal_seed_height_below_analytic :
    literalSeedHeight < (2327 : ℝ) / 100000 := by
  have hgap :
      (0 : ℝ) < (71552 : ℝ) / (100000 * (2 ^ 80 : ℝ)) := by
    positivity
  linarith only [literal_seed_quantization_gap, hgap]

/-- ALL 400 original Boolean-table cells, not just bank fixed anchors. -/
theorem literal_seed_floor_at_every_cell
    (upper : Bool) (i : Fin 200) :
    floorValue (iterate 0 upper) i =
      if upper = true ∧ i.val < 60 then literalSeedHeight else 0 := by
  cases upper with
  | false =>
      simp [floorValue, iterate, seed, literalSeedHeight]
  | true =>
      by_cases hi : i.val < 60
      · simp [floorValue, iterate, seed, literalSeedHeight, hi]
      · simp [floorValue, iterate, seed, literalSeedHeight, hi]

/-- Exact CLOSED-CELL base requirement for the unchanged Q80 producer:
first 60 upper cells require a strictly positive seed; remaining upper
and all lower cells require F nonnegative. Each queryCell is CLOSED,
including its overlapping endpoints. This is a base-case reduction,
NOT an assumed all-430 CLOSED-CELL theorem or analytic F estimate. -/
theorem literal_seed_closed_cell_iff
    (F : Bool → ℝ → ℝ) :
    (∀ (upper : Bool) (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate 0 upper) i ≤ F upper s) ↔
      ( (∀ (i : Fin 200) (s : ℝ),
          i.val < 60 → s ∈ queryCell i →
            literalSeedHeight ≤ F true s) ∧
        (∀ (i : Fin 200) (s : ℝ),
          60 ≤ i.val → s ∈ queryCell i →
            (0 : ℝ) ≤ F true s) ∧
        (∀ (i : Fin 200) (s : ℝ),
          s ∈ queryCell i →
            (0 : ℝ) ≤ F false s)) := by
  constructor
  · intro hbase
    refine ⟨?_, ?_, ?_⟩
    · intro i s hi hs
      have h := hbase true i s hs
      simpa [literal_seed_floor_at_every_cell, hi] using h
    · intro i s hi hs
      have hnot : ¬ i.val < 60 := Nat.not_lt.mpr hi
      have h := hbase true i s hs
      simpa [literal_seed_floor_at_every_cell, hnot] using h
    · intro i s hs
      have h := hbase false i s hs
      simpa [literal_seed_floor_at_every_cell] using h
  · rintro ⟨hnear, hfar, hlower⟩ upper i s hs
    cases upper with
    | false =>
        simpa [literal_seed_floor_at_every_cell] using
          (hlower i s hs)
    | true =>
        by_cases hi : i.val < 60
        · simpa [literal_seed_floor_at_every_cell, hi] using
            (hnear i s hi hs)
        · have hfarIndex : 60 ≤ i.val := Nat.le_of_not_gt hi
          simpa [literal_seed_floor_at_every_cell, hi] using
            (hfar i s hfarIndex hs)

end
end ImbalancedChen.Part5OriginalH430ExactQ80FullSeedBase
