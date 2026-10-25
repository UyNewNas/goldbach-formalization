import ImbalancedChen.P1LiteralVariableFifthCompactSupplier
import ImbalancedChen.P1CorrectedFifthDensityDictionary
import ImbalancedChen.P1OriginalHistoricalFifthOwnCubeAffineGates
import ImbalancedChen.P1ActualVariableFifthProfiles

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_CREDIT.

The literal fifteen-mask fourth envelope plus W is an UPPER bound for
the actual variable original-fourth profile on a genuine selected fifth
joint cell, provided every licensed fourth row has its primitive Geometry.
Equality of these old profiles is neither required nor asserted.

The seed comparison is proved from the actual selected original Gamma box,
its mesh membership and the original joint-region order. Its -2e buffer is
preserved throughout. Every admitted fourth row supplies a nonempty actual
mask and hence one of the fifteen tents. Every eligible fifth row still
participates in the actual new maximum. Canonical gated-profile monotonicity
then gives a conservative literal-row gain bound with all strict gates.

This does not verify whole-table geometry, dynamic owner/cell licences,
saved costs, numerical gains, history realizations or certificate replay.
-/

namespace ImbalancedChen.P1OriginalOld15Majorant

noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1CorrectedFifthDensityDictionary


abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

/-- The fifteen-mask maximum contains every genuinely nonempty fourth mask. -/
theorem nonempty_tent_le_rawFourth (I : Finset (Fin 4)) (hI : I.Nonempty) (t : Point5) :
    v (P1LiteralVariableFifthCompactSupplier.oldSubsetSum I t) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t := by
  apply finiteMax_row_le P1LiteralVariableFifthCompactSupplier.oldMasks (fun _ => True)
    (fun I => v (P1LiteralVariableFifthCompactSupplier.oldSubsetSum I t)) (B (t 2)) I
  · exact Finset.mem_erase.mpr ⟨hI.ne_empty, Finset.mem_univ I⟩
  · trivial

/-- The complete six-term original third envelope occurs in max15+W. -/
theorem rawSix_le_rawFourth (t : Point5) :
    six (t 0) (t 1) (t 2) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t := by
  have h0 : v (t 0) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t := by
    simpa [P1LiteralVariableFifthCompactSupplier.oldSubsetSum] using
      (nonempty_tent_le_rawFourth {0} (by simp) t)
  have h01 : v (t 0 + t 1) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t := by
    simpa [P1LiteralVariableFifthCompactSupplier.oldSubsetSum] using
      (nonempty_tent_le_rawFourth {0,1} (by simp) t)
  have h012 : v (t 0 + t 1 + t 2) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t := by
    simpa [P1LiteralVariableFifthCompactSupplier.oldSubsetSum, add_assoc] using
      (nonempty_tent_le_rawFourth {0,1,2} (by simp) t)
  have hB : B (t 2) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t := finiteMax_seed_le _ _ _ _
  have h02 : v (t 0 + t 2) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t := by
    simpa [P1LiteralVariableFifthCompactSupplier.oldSubsetSum] using
      (nonempty_tent_le_rawFourth {0,2} (by simp) t)
  have h12 : v (t 1 + t 2) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t := by
    simpa [P1LiteralVariableFifthCompactSupplier.oldSubsetSum] using
      (nonempty_tent_le_rawFourth {1,2} (by simp) t)
  exact max_le h0 (max_le h01 (max_le h012 (max_le hB (max_le h02 h12))))

theorem originalEndpoint_le_rawFourth (t : Point5)
    (hz : 0 ≤ t 2) (hzy : t 2 ≤ t 1) (hyx : t 1 ≤ t 0) :
    HistoricalThirdCoarse.endpoint (t 0) (t 1) (t 2) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t := by
  unfold HistoricalThirdCoarse.endpoint
  split_ifs with hx
  · rw [original_eq_six ⟨hz, hzy, hyx, hx⟩]
    exact rawSix_le_rawFourth t
  · simpa [P1LiteralVariableFifthCompactSupplier.oldSubsetSum] using
      (nonempty_tent_le_rawFourth {0} (by simp) t)

/-- Geometry's actual masks9..15 all select original processing slot3.
No table-wide mask claim or unchecked raw record is used. -/
theorem geometry_selected_nonempty (r : ProducerRow) (hr : r.Geometry) : r.selected.Nonempty := by
  have hm0 := hr.1
  have hm1 := hr.2.1
  have hm : r.mask = 9 ∨ r.mask = 10 ∨ r.mask = 11 ∨ r.mask = 12 ∨
      r.mask = 13 ∨ r.mask = 14 ∨ r.mask = 15 := by omega
  rcases hm with h | h | h | h | h | h | h <;>
    exact ⟨(3 : Fin 4), by simp [ProducerRow.selected, h]⟩

/-- A genuine licensed fourth candidate is one of the literal fifteen
buffered tents. Both sides retain exactly the same -2e. -/
theorem bufferedCandidate_le_old15 (r : ProducerRow) (hr : r.Geometry) (e : ℝ) (t : Point5) :
    r.bufferedCandidate e (historicalPrefixProject (by omega : 4 ≤ 5) t) ≤ P1LiteralVariableFifthCompactSupplier.old5 e t := by
  have h := nonempty_tent_le_rawFourth r.selected (geometry_selected_nonempty r hr) t
  rw [ProducerRow.bufferedCandidate, ProducerRow.candidate_eq]
  change v (∑ i ∈ r.selected, historicalPrefixProject (by omega : 4 ≤ 5) t i) - 2 * e ≤
    P1LiteralVariableFifthCompactSupplier.rawFourth t - 2 * e
  apply sub_le_sub_right
  simpa only [P1LiteralVariableFifthCompactSupplier.oldSubsetSum, historicalPrefixProject] using h

/-- No seed-majorant assumption: the original Gamma endpoint comparison
is derived on the selected third ancestor of this exact fifth mesh owner. -/
theorem selected_currentExponent_le_old15
    (e : ℚ) (he : 0 ≤ (e : ℝ)) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (t : Point5) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hjoint : t ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion (e : ℝ) chi m omega j) :
    HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent (e : ℝ) chi m omega j t ≤ P1LiteralVariableFifthCompactSupplier.old5 (e : ℝ) t := by
  have howner : HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j ∈ HistoricalThirdCoarse.cells (e : ℝ) chi m :=
    ((P1OriginalCoarseFifthContinuation.mem_selectedFifthCells e chi m omega J5 j).mp hj).2.1
  have hselected := (HistoricalThirdCoarse.mem_cells (e : ℝ) chi m _).mp howner
  have ht3 := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) ht
  have hbox : (HistoricalThirdCoarse.box m (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j)).InBox (t 0) (t 1) (t 2) := by
    simpa only [HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner, historicalPrefixProject] using
      (HistoricalThirdCoarse.inBox_of_cell ht3)
  have hz : 0 ≤ t 2 := by
    have hl : (0 : ℝ) ≤ (HistoricalThirdCoarse.box m (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j)).lz := by
      exact_mod_cast hselected.2.1
    exact hl.trans hbox.2.2.2.2.1
  have hsort := ((HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_jointRegion (e : ℝ) chi m omega j t).mp hjoint).2.1
  have hzy : t 2 ≤ t 1 := (hsort (by omega : (1 : Fin 5) < 2)).le
  have hyx : t 1 ≤ t 0 := (hsort (by omega : (0 : Fin 5) < 1)).le
  have hg := HistoricalThirdCoarse.gamma_le_endpoint (e : ℝ)
    (HistoricalThirdCoarse.box m (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j)) he hbox hz hzy hyx
  rw [P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    e chi m omega J5 j hj ht]
  change (HistoricalThirdCoarse.gamma (e : ℝ) (HistoricalThirdCoarse.box m (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j)) : ℝ) -
      2 * (e : ℝ) ≤ P1LiteralVariableFifthCompactSupplier.rawFourth t - 2 * (e : ℝ)
  exact sub_le_sub_right (hg.trans (originalEndpoint_le_rawFourth t hz hzy hyx)) _

/-- The actual original variable fourth profile is bounded above by the
literal old15 profile on the original selected joint cell. The primitive
licence hypothesis is per actual fourth row; the inherited seed is proved. -/
theorem actualOriginalFourth_le_old15
    (e : ℚ) (he : 0 ≤ (e : ℝ)) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (t : Point5) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hjoint : t ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion (e : ℝ) chi m omega j) :
    originalVariableFourthProfile e chi omega m j rows4 licensed4 t ≤ P1LiteralVariableFifthCompactSupplier.old5 (e : ℝ) t := by
  unfold originalVariableFourthProfile profile4
  apply finiteMax_le
  · exact selected_currentExponent_le_old15 e he chi m omega J5 j hj t ht hjoint
  · intro r hr her
    exact bufferedCandidate_le_old15 r (hgeometry r hr her.1) (e : ℝ) t

/-- A particular genuinely eligible fifth row supplies a conservative gain
against literal old15. Actual next5 still keeps every eligible fifth row.
All four displayed own-cube inequalities are strict, at their own levels.
Only canonical lower-profile monotonicity is used, not signed finite sums. -/
theorem actual_fifth_kernel_ge_literal_row
    (e : ℚ) (he : 0 ≤ (e : ℝ)) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (J5 : Finset (Label5 m))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))
    (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (r : P1OriginalVariableFifthContinuation.FifthRow m) (hr : r ∈ rows5)
    (hcell : r.cell = j) (hgate : P1OriginalVariableFifthContinuation.gateCheck e m r = true)
    (t : Point5) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hjoint : t ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion (e : ℝ) chi m omega j) (hpos : ∀ i, 0 < t i) :
    ((if primeTupleOwnCubeForm t < P1LiteralVariableFifthCompactSupplier.M r.selected t - 2 * (e : ℝ)
        then primeTupleMinusProfile (P1LiteralVariableFifthCompactSupplier.M r.selected t - 2 * (e : ℝ)) t else 0) -
      (if primeTupleOwnCubeForm t < P1LiteralVariableFifthCompactSupplier.old5 (e : ℝ) t
        then primeTupleMinusProfile (P1LiteralVariableFifthCompactSupplier.old5 (e : ℝ) t) t else 0)) * (∏ i, 1 / t i) ≤
    ((if primeTupleOwnCubeForm t <
          P1ActualVariableFifthProfiles.actualNext5 e chi m omega j rows4 licensed4 rows5 t
        then primeTupleMinusProfile
          (P1ActualVariableFifthProfiles.actualNext5 e chi m omega j rows4 licensed4 rows5 t) t else 0) -
      (if primeTupleOwnCubeForm t < originalVariableFourthProfile e chi omega m j rows4 licensed4 t
        then primeTupleMinusProfile
          (originalVariableFourthProfile e chi omega m j rows4 licensed4 t) t else 0)) * (∏ i, 1 / t i) := by
  have hold := actualOriginalFourth_le_old15 e he chi m omega rows4 licensed4 hgeometry J5 j hj t ht hjoint
  have hnew : P1LiteralVariableFifthCompactSupplier.M r.selected t - 2 * (e : ℝ) ≤
      P1ActualVariableFifthProfiles.actualNext5 e chi m omega j rows4 licensed4 rows5 t := by
    exact finiteMax_row_le rows5 (P1ActualVariableFifthProfiles.ownerEligible e m j)
      (fun r => P1OriginalVariableFifthContinuation.candidate (e : ℝ) r.selected t)
      (originalVariableFourthProfile e chi omega m j rows4 licensed4 t) r hr ⟨hcell, hgate⟩
  change (primeOwnCubeGatedProfile (P1LiteralVariableFifthCompactSupplier.M r.selected t - 2 * (e : ℝ)) t -
      primeOwnCubeGatedProfile (P1LiteralVariableFifthCompactSupplier.old5 (e : ℝ) t) t) * (∏ i, 1 / t i) ≤
    (primeOwnCubeGatedProfile
        (P1ActualVariableFifthProfiles.actualNext5 e chi m omega j rows4 licensed4 rows5 t) t -
      primeOwnCubeGatedProfile (originalVariableFourthProfile e chi omega m j rows4 licensed4 t) t) *
        (∏ i, 1 / t i)
  apply mul_le_mul_of_nonneg_right
  · exact sub_le_sub
      (p1PrimeOwnCubeGatedProfile_mono t (hpos (Fin.last 4)) hnew)
      (p1PrimeOwnCubeGatedProfile_mono t (hpos (Fin.last 4)) hold)
  · exact Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (hpos i).le)

end
end ImbalancedChen.P1OriginalOld15Majorant
