import ImbalancedChen.P2OriginalStrictWLocalRationalCover

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The rational strict-W boxes feed the original whole-cell WBoxCheck.
Only the actual corrected compact mesh is used. Unselected ordinary marks
are explicit; this result does not erase an inherited selected source.
-/

namespace ImbalancedChen.P2OriginalLocalWBoxMeshLicence

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code strictSquareGates)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerOrderedWBranch
open P2OriginalLowerWThirdPhysicalRow
open P2OriginalStrictWLocalRationalCover

theorem qLo_le_qHi (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (i : Fin 5) : qLo S code i ≤ qHi S code i := by
  change qCellLo S mesh (code i).1 ≤ qCellHi S mesh (code i).1
  cases (code i).1 with
  | none => exact le_rfl
  | some j =>
      have hstep : 0 ≤ (startCutoff S.start - S.epsilon) / (mesh + 1 : ℚ) :=
        div_nonneg (sub_nonneg.mpr S.epsilon_lt_start.le) (by positivity)
      dsimp [qCellLo, qCellHi, qGridPoint]
      push_cast
      nlinarith

-- The three physical coordinates use the same prefix positions.
def CellRefines {S : CompactStart} {rho : ℝ}
    (Q : LocalWBox S rho) {mesh : ℕ} (code : Code mesh) : Prop :=
  ∀ i : Fin 3,
    Q.lo i ≤ qLo S code ⟨i.val, by omega⟩ ∧
      qHi S code ⟨i.val, by omega⟩ ≤ Q.hi i

theorem refined_cell_WBoxCheck (S : CompactStart) {rho : ℝ}
    (Q : LocalWBox S rho) {mesh : ℕ} (code : Code mesh)
    (href : CellRefines Q code)
    (hmarks : ∀ i : Fin 5, i.val < 3 → (code i).2 = false) :
    WBoxCheck S code rho Q.beta Q.delta := by
  have hlo0 := (href 0).1
  have hlo1 := (href 1).1
  have hlo2 := (href 2).1
  have hhi0 := (href 0).2
  have hhi1 := (href 1).2
  have hhi2 := (href 2).2
  have hcell2 := qLo_le_qHi S code 2
  have hgeo := Q.feasible.1
  have h0 := hgeo 0
  have h1 := hgeo 1
  have h2 := hgeo 2
  have h3 := hgeo 3
  have h4 := hgeo 4
  have h5 := hgeo 5
  have h6 := hgeo 6
  have h7 := hgeo 7
  have h8 := hgeo 8
  have h9 := hgeo 9
  have h10 := hgeo 10
  have h11 := hgeo 11
  have h12 := hgeo 12
  have h13 := hgeo 13
  simp only [geometricSlack, endpointCap, lower_pack, upper_pack] at
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  dsimp [pack] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have hx : (qHi S code 0 : ℝ) ≤ Q.hi 0 := by exact_mod_cast hhi0
  have hy : (qHi S code 1 : ℝ) ≤ Q.hi 1 := by exact_mod_cast hhi1
  have hz : (qHi S code 2 : ℝ) ≤ Q.hi 2 := by exact_mod_cast hhi2
  have hzlo : (Q.lo 2 : ℝ) ≤ qHi S code 2 := by
    exact_mod_cast (hlo2.trans hcell2)
  have hthird : 0 < (qHi S code 2 : ℝ) := by linarith
  have hb : (0 : ℝ) < Q.beta := by exact_mod_cast Q.beta_pos
  have hd : (0 : ℝ) < Q.delta := by exact_mod_cast Q.delta_pos
  have hcap : (wCap S code Q.beta : ℝ) =
      B (qHi S code 2) - Q.beta := by
    unfold wCap B Lambda
    push_cast
    ring
  have hcaplo : B (Q.hi 2) - Q.beta ≤ (wCap S code Q.beta : ℝ) := by
    rw [hcap]
    dsimp [B]
    linarith
  have htop : (wCap S code Q.beta : ℝ) < topCap := by
    rw [hcap]
    dsimp [B, Lambda, topCap]
    linarith
  have hfirst : 2 * (qHi S code 0 : ℝ) <
      (wCap S code Q.beta : ℝ) - 2 * Q.delta := by linarith
  have hsecond : (qHi S code 0 : ℝ) + 2 * qHi S code 1 <
      (wCap S code Q.beta : ℝ) - 2 * Q.delta := by linarith
  have hthirdsq : (qHi S code 0 : ℝ) + qHi S code 1 + 2 * qHi S code 2 <
      (wCap S code Q.beta : ℝ) - 2 * Q.delta := by linarith
  have hbuffered : strictSquareGates
      ((wCap S code Q.beta : ℝ) - 2 * Q.delta) 0
      [(qHi S code 0 : ℝ), (qHi S code 1 : ℝ), (qHi S code 2 : ℝ)] := by
    dsimp [strictSquareGates]
    exact ⟨by linarith, ⟨by linarith, ⟨by linarith, trivial⟩⟩⟩
  have hplain : strictSquareGates (wCap S code Q.beta : ℝ) 0
      [(qHi S code 0 : ℝ), (qHi S code 1 : ℝ), (qHi S code 2 : ℝ)] := by
    dsimp [strictSquareGates]
    exact ⟨by linarith, ⟨by linarith, ⟨by linarith, trivial⟩⟩⟩
  have hm0 := hmarks 0 (by norm_num)
  have hm1 := hmarks 1 (by norm_num)
  have hm2 := hmarks 2 (by norm_num)
  have hslots : prefixSlots S 3 code =
      [⟨(qHi S code 0 : ℝ), false⟩,
       ⟨(qHi S code 1 : ℝ), false⟩,
       ⟨(qHi S code 2 : ℝ), false⟩] := by
    simp [prefixSlots, upperSlot, hm0, hm1, hm2, qHi, qCellHi_cast]
  refine ⟨Q.beta_pos, Q.delta_pos, ?_, ?_, ?_, ?_, ?_, hmarks, ?_, ?_, hbuffered⟩
  · exact_mod_cast (show (Q.delta : ℝ) < 1 / 100000 by linarith)
  · exact_mod_cast hthird
  · have hm : (qHi S code 0 : ℝ) ≤ (25 : ℝ) / 128 := by
      dsimp [mu] at h2
      linarith
    exact_mod_cast hm
  · have hloR : (Q.lo 0 : ℝ) ≤ qLo S code 0 := by exact_mod_cast hlo0
    have hord : (qHi S code 1 : ℝ) ≤ qLo S code 0 := by linarith
    exact_mod_cast hord
  · have hloR : (Q.lo 1 : ℝ) ≤ qLo S code 1 := by exact_mod_cast hlo1
    have hord : (qHi S code 2 : ℝ) ≤ qLo S code 1 := by linarith
    exact_mod_cast hord
  · refine ⟨by linarith, htop.le, ?_, ?_, ?_⟩
    · change cellUpper S mesh (code 0).1 +
        3 * cellUpper S mesh (code 1).1 < baselineCap rho
      rw [← qCellHi_cast S mesh (code 0).1,
        ← qCellHi_cast S mesh (code 1).1]
      change (qHi S code 0 : ℝ) + 3 * qHi S code 1 < baselineCap rho
      linarith
    · simpa [hslots] using hplain
    · simpa [hslots, selectedWord, remainingWord] using hplain
  · dsimp [A] at h10 ⊢
    linarith

-- This is a local receiver, before any global common-mesh or wall budget.
-- It supplies the exact original table entry, not merely a new predicate.
theorem refined_cell_actual_W_row (S : CompactStart) {rho : ℝ}
    (Q : LocalWBox S rho) {mesh : ℕ} (code : Code mesh)
    (href : CellRefines Q code)
    (hmarks : ∀ i : Fin 5, i.val < 3 → (code i).2 = false) :
    (WThirdTable S rho Q.beta Q.delta).row 3 code =
      some (wCap S code Q.beta, wQueryLower S code Q.beta) := by
  exact WThirdTable_row S rho Q.beta Q.delta code
    (refined_cell_WBoxCheck S Q code href hmarks)

end
end ImbalancedChen.P2OriginalLocalWBoxMeshLicence
