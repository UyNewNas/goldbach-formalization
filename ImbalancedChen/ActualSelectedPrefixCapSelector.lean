import ImbalancedChen.SelectedPrefixRationalMesh
import ImbalancedChen.PrimeHistoryLogCoordinates
import ImbalancedChen.FrozenRosserPolicy
import ImbalancedChen.RosserShortPrefixAdmissibility

/-!
# A finite box selector on actual prime histories

The adopted cells are explicit finite data. Their half-open ownership
makes the cap constant on each adopted cell, and the old cap is used
outside their union. The selector never tests membership in an arbitrary
compact set. It reads the actual reversed prime history through logarithmic
coordinates and freezes that decision at the selected ancestor.

Whole-cell checks imply the literal integer square gates and a level at
least the old level. No density monotonicity, certificate coverage or
signed distribution theorem is asserted here.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open VariableEnvelope

/-- Finite cell lookup written as a sum. Uniqueness of half-open cell
ownership leaves exactly one increment on an adopted cell, and zero
increments outside the union. -/
def selectedPrefixMeshCap {d : ℕ} (I : Finset (Fin d)) (old nu a b : ℚ)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1))) (t : Fin d → ℝ) : ℚ :=
  old + ∑ j ∈ J, if t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j then
    selectedBoxCap I old nu (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) - old
  else 0

theorem selectedPrefixMeshCap_on_cell {d : ℕ} (I : Finset (Fin d))
    (old nu a b : ℚ) (hab : a ≤ b) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) (t : Fin d → ℝ)
    (j : Fin d → Fin (m + 1)) (hj : j ∈ J)
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    selectedPrefixMeshCap I old nu a b m J t =
      selectedBoxCap I old nu (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  unfold selectedPrefixMeshCap
  rw [Finset.sum_eq_single_of_mem j hj]
  · rw [if_pos ht]
    ring
  · intro k _hk hkj
    apply if_neg
    intro htk
    exact hkj (logPrimeMeshCell_unique habR htk ht)

theorem selectedPrefixMeshCap_outside {d : ℕ} (I : Finset (Fin d))
    (old nu a b : ℚ) (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (t : Fin d → ℝ)
    (ht : ∀ j ∈ J, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    selectedPrefixMeshCap I old nu a b m J t = old := by
  unfold selectedPrefixMeshCap
  rw [Finset.sum_eq_zero (fun j hj => if_neg (ht j hj)), add_zero]

/-- The old cap is a global lower bound, including outside the selected
region. The successful stored checks, not an assumed property of the
lookup function, supply this fact. -/
theorem selectedPrefixMeshCap_ge_old {d : ℕ} (I : Finset (Fin d))
    (old nu a b : ℚ) (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (t : Fin d → ℝ) : old ≤ selectedPrefixMeshCap I old nu a b m J t := by
  unfold selectedPrefixMeshCap
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · apply sub_nonneg.mpr
    exact (selectedCapLower_old_le I old _).trans
      (selectedBoxCap_between I old nu _ _ (hchecks j hj)).1.le
  · exact le_rfl

/-- Every strict exponent license holds throughout each adopted cell for
the actual finite lookup, with no extra membership filter. -/
theorem selectedPrefixMeshCap_on_cell_sound {d : ℕ} (I : Finset (Fin d))
    (old nu a b : ℚ) (hab : a ≤ b) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (t : Fin d → ℝ) (j : Fin d → Fin (m + 1)) (hj : j ∈ J)
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    (old : ℝ) < selectedPrefixMeshCap I old nu a b m J t ∧
      (selectedPrefixMeshCap I old nu a b m J t : ℝ) < nu ∧
      (1 / 2 : ℝ) < selectedPrefixMeshCap I old nu a b m J t ∧
      (∀ i, prefixSquareExpr t i < selectedPrefixMeshCap I old nu a b m J t) ∧
      (∀ i ∉ I, selectedSquareExpr I t i < selectedPrefixMeshCap I old nu a b m J t) ∧
      (selectedPrefixMeshCap I old nu a b m J t : ℝ) < v (∑ i ∈ I, t i) := by
  rw [selectedPrefixMeshCap_on_cell I old nu a b hab m J t j hj ht]
  apply selectedBoxCapCheck_sound I old nu _ _ (hchecks j hj) t
  · intro i
    rw [congrFun (cast_qLogPrimeMeshLo a b m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).1
  · intro i
    rw [congrFun (cast_qLogPrimeMeshHi a b m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).2.le

/-- One fixed finite adopted family covers the entire licensed compact
set. Its actual lookup strictly raises the old cap at every point of that
set. The mesh and family are chosen before any target or prime history. -/
theorem exists_selectedPrefixMeshCap_cover {d : ℕ} (I : Finset (Fin d))
    (old nu a b : ℚ) (hab : a ≤ b) (S : Set (Fin d → ℝ))
    (hS : IsCompact S)
    (hbox : S ⊆ logPrimeBox (fun _ => (a : ℝ)) (fun _ => (b : ℝ)))
    (hlicense : ∀ t ∈ S, SelectedPrefixLicense I old nu t) :
    ∃ (m : ℕ) (J : Finset (Fin d → Fin (m + 1))),
      (∀ j ∈ J, selectedBoxCapCheck I old nu
        (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) ∧
      (∀ t ∈ S, ∃! j, j ∈ J ∧ t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) ∧
      (∀ t ∈ S, old < selectedPrefixMeshCap I old nu a b m J t) := by
  obtain ⟨m, hm⟩ := exists_selectedPrefixMeetingCells_check_threshold
    I old nu a b hab S hS hlicense
  let J := selectedPrefixMeetingCells a b m S
  have hc : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true := hm m le_rfl
  refine ⟨m, J, hc, ?_, ?_⟩
  · intro t ht
    exact selectedPrefixMeetingCells_unique_cover a b hab m S hbox ht
  · intro t ht
    obtain ⟨j, hj, _⟩ := selectedPrefixMeetingCells_unique_cover a b hab m S hbox ht
    have hs := selectedPrefixMeshCap_on_cell_sound I old nu a b hab m J hc t j hj.1 hj.2
    exact_mod_cast hs.1

/-- A literal level selected from the logarithms of the actual history.
It depends on the target and selected primes, not on the receiver whose
divisibility polynomial is later evaluated. -/
def actualSelectedPrefixLevel {d : ℕ} (N : ℝ) (I : Finset (Fin d))
    (old nu a b : ℚ) (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (history : List ℕ) : ℝ :=
  N ^ (selectedPrefixMeshCap I old nu a b m J
    (primeHistoryLogCoordinates N d history) : ℝ)

theorem actualSelectedPrefixLevel_ge_old {d : ℕ} (N : ℝ) (hN : 1 < N)
    (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (history : List ℕ) :
    N ^ (old : ℝ) ≤ actualSelectedPrefixLevel N I old nu a b m J history := by
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  exact_mod_cast selectedPrefixMeshCap_ge_old I old nu a b m J hchecks
    (primeHistoryLogCoordinates N d history)

theorem actualSelectedPrefixLevel_gt_one {d : ℕ} (N : ℝ) (hN : 1 < N)
    (I : Finset (Fin d)) (old nu a b : ℚ) (hold : 0 < old) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (history : List ℕ) : 1 < actualSelectedPrefixLevel N I old nu a b m J history := by
  have ho : (0 : ℝ) < old := by exact_mod_cast hold
  have hp : 1 < N ^ (old : ℝ) := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hN ho
  exact hp.trans_le (actualSelectedPrefixLevel_ge_old N hN I old nu a b m J hchecks history)

theorem actualSelectedPrefixLevel_outside {d : ℕ} (N : ℝ)
    (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) (history : List ℕ)
    (ht : ∀ j ∈ J, primeHistoryLogCoordinates N d history ∉
      logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    actualSelectedPrefixLevel N I old nu a b m J history = N ^ (old : ℝ) := by
  unfold actualSelectedPrefixLevel
  rw [selectedPrefixMeshCap_outside I old nu a b m J _ ht]

/-- Old inherited prefix tests remain valid at this actual selected level;
admissibility at the new level is a conclusion. -/
theorem actualSelectedPrefixLevel_inherited_admissible {d : ℕ}
    (N : ℝ) (hN : 1 < N) (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (lower : Bool) (parent history : List ℕ)
    (hparent : ordinaryRosserPrefixAdmissible lower (N ^ (old : ℝ)) parent) :
    ordinaryRosserPrefixAdmissible lower
      (actualSelectedPrefixLevel N I old nu a b m J history) parent :=
  ordinaryRosserPrefixAdmissible_mono lower parent
    (actualSelectedPrefixLevel_ge_old N hN I old nu a b m J hchecks history) hparent

/-- The square gates concern the actual natural history entries in
processing order, with the exact preceding and selected subproducts. -/
theorem actualSelectedPrefixLevel_square_gates {d : ℕ}
    (N : ℝ) (hN : 1 < N) (I : Finset (Fin d)) (old nu a b : ℚ)
    (hab : a ≤ b) (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (history : List ℕ) (hlen : history.length = d)
    (hpos : ∀ p ∈ history, 0 < p)
    (j : Fin d → Fin (m + 1)) (hj : j ∈ J)
    (ht : primeHistoryLogCoordinates N d history ∈
      logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    (∀ i, ((∏ k ∈ Finset.univ.filter (fun k => k < i),
        primeHistoryTuple d history k : ℕ) : ℝ) *
      (primeHistoryTuple d history i : ℝ) ^ 2 <
        actualSelectedPrefixLevel N I old nu a b m J history) ∧
    (∀ i ∉ I, ((∏ k ∈ I, primeHistoryTuple d history k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k => k < i ∧ k ∉ I),
        primeHistoryTuple d history k : ℕ) : ℝ) *
      (primeHistoryTuple d history i : ℝ) ^ 2 <
        actualSelectedPrefixLevel N I old nu a b m J history) := by
  have hs := selectedPrefixMeshCap_on_cell_sound I old nu a b hab m J hchecks
    (primeHistoryLogCoordinates N d history) j hj ht
  have hp : ∀ i, (primeHistoryTuple d history i : ℝ) ≤
      N ^ primeHistoryLogCoordinates N d history i := by
    intro i
    rw [rpow_primeHistoryLogCoordinates N hN hlen hpos i]
  exact ⟨fun i => prefixSquareExpr_actual_gate N hN _ _ hp i (hs.2.2.2.1 i),
    fun i hi => selectedSquareExpr_actual_gate I N hN _ _ hp i (hs.2.2.2.2.1 i hi)⟩

/-- Freeze the concrete cell lookup at the actual selected ancestor. -/
def actualSelectedPrefixFrozenLevel {d : ℕ} (N : ℝ) (I : Finset (Fin d))
    (old nu a b : ℚ) (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (history : List ℕ) : ℝ :=
  actualSelectedPrefixLevel N I old nu a b m J (rosserAncestor d history)

theorem actualSelectedPrefixFrozenLevel_append {d : ℕ} (N : ℝ)
    (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) (later history : List ℕ)
    (hlen : d ≤ history.length) :
    actualSelectedPrefixFrozenLevel N I old nu a b m J (later ++ history) =
      actualSelectedPrefixFrozenLevel N I old nu a b m J history := by
  unfold actualSelectedPrefixFrozenLevel
  rw [rosserAncestor_append d later history hlen]

theorem actualSelectedPrefixFrozenLevel_at_rank {d : ℕ} (N : ℝ)
    (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) (history : List ℕ)
    (hlen : history.length = d) :
    actualSelectedPrefixFrozenLevel N I old nu a b m J history =
      actualSelectedPrefixLevel N I old nu a b m J history := by
  unfold actualSelectedPrefixFrozenLevel
  rw [rosserAncestor_self_of_length d history hlen]

end

end ImbalancedChen
