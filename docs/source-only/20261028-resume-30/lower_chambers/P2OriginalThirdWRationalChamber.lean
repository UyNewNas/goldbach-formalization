import ImbalancedChen.P2OriginalLowerWThirdPhysicalRow

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A positive rational box around the missing W-winning point. The numerical
margins below prove the full WBoxCheck on every mesh cell inside this box,
including the actual historical parent and buffered full squares. This
fills a local existence/gate obligation, not global mesh coverage or the
arithmetic factorization licence. The grid is the corrected [epsilon,w].
-/

namespace ImbalancedChen.P2OriginalThirdWRationalChamber

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code strictSquareGates)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerOrderedWBranch
open P2OriginalLowerWThirdPhysicalRow

-- These endpoints are fixed independently of N, epsilon and the mesh.
-- Their interiors contain (1/20,1/25,3/100), and are disjoint in the
-- descending order x > y > z. The wider inherited first-start cutoff
-- is 417/5000, so these small positive exponents are legitimate.
structure CellInWRectangle (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) : Prop where
  first_hi : qHi S code 0 ≤ 51 / 1000
  first_lo : 49 / 1000 ≤ qLo S code 0
  second_hi : qHi S code 1 ≤ 41 / 1000
  second_lo : 39 / 1000 ≤ qLo S code 1
  third_hi_lower : 29 / 1000 ≤ qHi S code 2
  third_hi_upper : qHi S code 2 ≤ 31 / 1000
  no_marks : ∀ i : Fin 5, i.val < 3 → (code i).2 = false

-- No positivity of the long-rank query or branch gates is supplied as
-- a premise: all are deduced from this explicit compact rectangle.
theorem WBoxCheck_of_rectangle (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (hbox : CellInWRectangle S code)
    (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1 / 100)
    (buffer delta : ℚ) (hbuffer0 : 0 < buffer)
    (hbuffer1 : buffer ≤ 1 / 10000)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1 / 200000) :
    WBoxCheck S code rho buffer delta := by
  have hx : (qHi S code 0 : ℝ) ≤ 51 / 1000 := by
    exact_mod_cast hbox.first_hi
  have hy : (qHi S code 1 : ℝ) ≤ 41 / 1000 := by
    exact_mod_cast hbox.second_hi
  have hz0 : (29 : ℝ) / 1000 ≤ qHi S code 2 := by
    exact_mod_cast hbox.third_hi_lower
  have hz1 : (qHi S code 2 : ℝ) ≤ 31 / 1000 := by
    exact_mod_cast hbox.third_hi_upper
  have hb0 : (0 : ℝ) < buffer := by exact_mod_cast hbuffer0
  have hb1 : (buffer : ℝ) ≤ 1 / 10000 := by exact_mod_cast hbuffer1
  have hd1 : (delta : ℝ) ≤ 1 / 200000 := by exact_mod_cast hdelta1
  have hcap : (wCap S code buffer : ℝ) =
      (153 : ℝ) / 256 - 3 * (qHi S code 2 : ℝ) / 8 - buffer := by
    unfold wCap
    push_cast
    ring
  have hcaplow : (117 : ℝ) / 200 < wCap S code buffer := by
    rw [hcap]
    linarith
  have hcapupper : (wCap S code buffer : ℝ) < topCap := by
    rw [hcap]
    dsimp [topCap]
    linarith
  have hparentlow : (54 : ℝ) / 100 < baselineCap rho := by
    dsimp [baselineCap]
    linarith
  have hparentupper : baselineCap rho < (56 : ℝ) / 100 := by
    dsimp [baselineCap]
    linarith
  have hfirst : 2 * (qHi S code 0 : ℝ) <
      (wCap S code buffer : ℝ) - 2 * delta := by linarith
  have hsecond : (qHi S code 0 : ℝ) + 2 * qHi S code 1 <
      (wCap S code buffer : ℝ) - 2 * delta := by linarith
  have hthird : (qHi S code 0 : ℝ) + qHi S code 1 + 2 * qHi S code 2 <
      (wCap S code buffer : ℝ) - 2 * delta := by linarith
  have hprefix : strictSquareGates
      ((wCap S code buffer : ℝ) - 2 * delta) 0
      [(qHi S code 0 : ℝ), (qHi S code 1 : ℝ),
        (qHi S code 2 : ℝ)] := by
    dsimp [strictSquareGates]
    exact ⟨by linarith, ⟨by linarith, ⟨by linarith, trivial⟩⟩⟩
  have hplain : strictSquareGates (wCap S code buffer : ℝ) 0
      [(qHi S code 0 : ℝ), (qHi S code 1 : ℝ),
        (qHi S code 2 : ℝ)] := by
    have hd0 : (0 : ℝ) < delta := by exact_mod_cast hdelta0
    dsimp [strictSquareGates]
    exact ⟨by linarith, ⟨by linarith, ⟨by linarith, trivial⟩⟩⟩
  have hm0 := hbox.no_marks 0 (by norm_num)
  have hm1 := hbox.no_marks 1 (by norm_num)
  have hm2 := hbox.no_marks 2 (by norm_num)
  have hslots : prefixSlots S 3 code =
      [⟨(qHi S code 0 : ℝ), false⟩,
       ⟨(qHi S code 1 : ℝ), false⟩,
       ⟨(qHi S code 2 : ℝ), false⟩] := by
    simp [prefixSlots, upperSlot, hm0, hm1, hm2, qHi, qCellHi_cast]
  refine ⟨hbuffer0, hdelta0, by linarith, by linarith [hbox.third_hi_lower],
    by linarith [hbox.first_hi], by linarith [hbox.second_hi, hbox.first_lo],
    by linarith [hbox.third_hi_upper, hbox.second_lo],
    hbox.no_marks, ?_, ?_, hprefix⟩
  · refine ⟨by linarith, hcapupper.le, ?_, ?_, ?_⟩
    · change cellUpper S mesh (code 0).1 +
        3 * cellUpper S mesh (code 1).1 < baselineCap rho
      rw [← qCellHi_cast S mesh (code 0).1,
        ← qCellHi_cast S mesh (code 1).1]
      change (qHi S code 0 : ℝ) + 3 * qHi S code 1 < baselineCap rho
      linarith
    · simpa [hslots] using hplain
    · simpa [hslots, selectedWord, remainingWord] using hplain
  · dsimp [A]
    linarith

theorem rectangle_buffers_exist (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (hbox : CellInWRectangle S code)
    (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1 / 100) :
    ∃ buffer delta : ℚ,
      0 < buffer ∧ 0 < delta ∧ WBoxCheck S code rho buffer delta := by
  refine ⟨1 / 20000, 1 / 400000, by norm_num, by norm_num, ?_⟩
  exact WBoxCheck_of_rectangle S code hbox rho hrho0 hrho1
    (1 / 20000) (1 / 400000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- W strictly wins against the inherited nu and the universal third tent
-- upper bound on this full rectangle, even after the fixed W buffer.
theorem rectangle_W_strict_margin (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (hbox : CellInWRectangle S code)
    (buffer : ℚ) (hbuffer : buffer ≤ 1 / 10000) :
    (249 : ℚ) / 448 < wCap S code buffer ∧
    (1 + qHi S code 0 + qHi S code 1 + qHi S code 2) / 2 <
      wCap S code buffer := by
  dsimp [wCap]
  constructor <;> linarith [hbox.first_hi, hbox.second_hi, hbox.third_hi_upper]


-- A literal nonempty compact-grid instance; existence of a valid W cell
-- is therefore not left as a CellInWRectangle premise. The cell contains
-- the exact rational obstruction point from the PhaseC source.
def witnessStart : CompactStart :=
  { start := .first
    epsilon := 1 / 1000
    epsilon_pos := by norm_num
    epsilon_lt_start := by norm_num [startCutoff] }

def witnessCode : Code 999 := fun i =>
  ((match i.val with
    | 0 => some ⟨594, by norm_num⟩
    | 1 => some ⟨473, by norm_num⟩
    | 2 => some ⟨351, by norm_num⟩
    | _ => none), false)

theorem witnessCode_rectangle : CellInWRectangle witnessStart witnessCode := by
  constructor
  · norm_num [qHi, qCellHi, qGridPoint, witnessStart, witnessCode, startCutoff]
  · norm_num [qLo, qCellLo, qGridPoint, witnessStart, witnessCode, startCutoff]
  · norm_num [qHi, qCellHi, qGridPoint, witnessStart, witnessCode, startCutoff]
  · norm_num [qLo, qCellLo, qGridPoint, witnessStart, witnessCode, startCutoff]
  · norm_num [qHi, qCellHi, qGridPoint, witnessStart, witnessCode, startCutoff]
  · norm_num [qHi, qCellHi, qGridPoint, witnessStart, witnessCode, startCutoff]
  · intro i _
    rfl

theorem witnessCode_contains_obstruction_point :
    qLo witnessStart witnessCode 0 ≤ 1 / 20 ∧
    1 / 20 < qHi witnessStart witnessCode 0 ∧
    qLo witnessStart witnessCode 1 ≤ 1 / 25 ∧
    1 / 25 < qHi witnessStart witnessCode 1 ∧
    qLo witnessStart witnessCode 2 ≤ 3 / 100 ∧
    3 / 100 < qHi witnessStart witnessCode 2 := by
  norm_num [qLo, qHi, qCellLo, qCellHi, qGridPoint,
    witnessStart, witnessCode, startCutoff]

theorem witnessCode_licensed_W :
    WBoxCheck witnessStart witnessCode 0 (1 / 20000) (1 / 400000) := by
  exact WBoxCheck_of_rectangle witnessStart witnessCode witnessCode_rectangle
    0 (by norm_num) (by norm_num) (1 / 20000) (1 / 400000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem witnessCode_W_row :
    (WThirdTable witnessStart 0 (1 / 20000) (1 / 400000)).row
      3 witnessCode =
      some (wCap witnessStart witnessCode (1 / 20000),
        wQueryLower witnessStart witnessCode (1 / 20000)) := by
  exact WThirdTable_row witnessStart 0 (1 / 20000) (1 / 400000)
    witnessCode witnessCode_licensed_W

end
end ImbalancedChen.P2OriginalThirdWRationalChamber
