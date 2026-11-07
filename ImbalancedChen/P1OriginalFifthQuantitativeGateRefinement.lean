import ImbalancedChen.P1OriginalPrefixRowDecodeSoundness

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Quantitative rank-five refinement for the ACTUAL variable-fifth gateCheck.
No table, numerical passing witness, history licence, or mean is imported.
The selected and unselected preceding slots are disjoint: their total
coefficient count is at most five. Thus the upper-endpoint square-gate
loss is at most 7h, and the tent interval loss is at most 15h/2.
A strict 16h margin suffices. All original masks retain their slot order.
-/

namespace ImbalancedChen.P1OriginalFifthQuantitativeGateRefinement

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P1OriginalVariableFifthContinuation
open P1OriginalPrefixRowDecodeSoundness

/-- Uniform coordinate perturbation, with the actual rank-five count. -/
theorem sum_le_sum_add_five (S : Finset (Fin 5)) (l u : Fin 5 → ℚ)
    (h : ℚ) (hh : 0 ≤ h) (hwidth : ∀ i, u i ≤ l i + h) :
    (∑ i ∈ S, u i) ≤ (∑ i ∈ S, l i) + 5 * h := by
  have hcard : S.card ≤ 5 := by
    simpa using (Finset.card_le_card (Finset.subset_univ S))
  calc
    (∑ i ∈ S, u i) ≤ ∑ i ∈ S, (l i + h) :=
      Finset.sum_le_sum (fun i _ => hwidth i)
    _ = (∑ i ∈ S, l i) + (S.card : ℚ) * h := by
      simp [Finset.sum_add_distrib]
    _ ≤ (∑ i ∈ S, l i) + 5 * h := by
      have hc : (S.card : ℚ) ≤ 5 := by exact_mod_cast hcard
      exact add_le_add_left (mul_le_mul_of_nonneg_right hc hh) _

theorem prefixSquareExpr_upper_loss (l u : Fin 5 → ℚ) (h : ℚ)
    (hh : 0 ≤ h) (hwidth : ∀ i, u i ≤ l i + h) (j : Fin 5) :
    prefixSquareExpr u j ≤ prefixSquareExpr l j + 7 * h := by
  have hs := sum_le_sum_add_five
    (Finset.univ.filter (fun i : Fin 5 => i < j)) l u h hh hwidth
  dsimp [prefixSquareExpr]
  linarith [hwidth j]

/-- The two finite sums use disjoint processing slots. Counting them
separately would introduce an incorrect dimension-ten loss. -/
theorem selectedSquareExpr_upper_loss (I : Finset (Fin 5))
    (l u : Fin 5 → ℚ) (h : ℚ) (hh : 0 ≤ h)
    (hwidth : ∀ i, u i ≤ l i + h) (j : Fin 5) :
    selectedSquareExpr I u j ≤ selectedSquareExpr I l j + 7 * h := by
  let P : Finset (Fin 5) := Finset.univ.filter (fun i => i < j ∧ i ∉ I)
  have hd : Disjoint I P := by
    apply Finset.disjoint_left.mpr
    intro i hi hp
    exact (Finset.mem_filter.mp hp).2.2 hi
  have hs := sum_le_sum_add_five (I ∪ P) l u h hh hwidth
  rw [Finset.sum_union hd, Finset.sum_union hd] at hs
  change (∑ i ∈ I, u i) + (∑ i ∈ P, u i) + 2 * u j ≤
    (∑ i ∈ I, l i) + (∑ i ∈ P, l i) + 2 * l j + 7 * h
  linarith [hwidth j]

/-- Endpoint inflation of the exact finite maximum consumed by gateCheck. -/
theorem selectedCapLower_upper_loss (I : Finset (Fin 5))
    (l u : Fin 5 → ℚ) (h : ℚ) (hh : 0 ≤ h)
    (hwidth : ∀ i, u i ≤ l i + h) :
    selectedCapLower I 0 u ≤ selectedCapLower I 0 l + 7 * h := by
  apply Finset.max'_le
  intro a ha
  simp only [selectedCapLowerSet, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image] at ha
  rcases ha with rfl | rfl | ⟨j, _, rfl⟩ | ⟨j, hj, rfl⟩
  · linarith [selectedCapLower_old_le I 0 l]
  · linarith [selectedCapLower_half_le I 0 l]
  · linarith [prefixSquareExpr_upper_loss l u h hh hwidth j,
      selectedCapLower_prefix_le I 0 l j]
  · have hjI := (Finset.mem_sdiff.mp hj).2
    linarith [selectedSquareExpr_upper_loss I l u h hh hwidth j,
      selectedCapLower_selected_le I 0 l j hjI]

/-- No monotone-branch assumption on the tent is needed, even when the
selected interval crosses its peak. -/
theorem qVLo_lower_loss (I : Finset (Fin 5)) (l u : Fin 5 → ℚ)
    (h : ℚ) (hh : 0 ≤ h) (hwidth : ∀ i, u i ≤ l i + h) :
    qV (∑ i ∈ I, l i) - (15 / 2) * h ≤
      qVLo (∑ i ∈ I, l i) (∑ i ∈ I, u i) := by
  have hs := sum_le_sum_add_five I l u h hh hwidth
  have ha := min_le_left (qA (∑ i ∈ I, l i)) (qC (∑ i ∈ I, l i))
  have hc := min_le_right (qA (∑ i ∈ I, l i)) (qC (∑ i ∈ I, l i))
  unfold qVLo
  apply le_min
  · change min (qA (∑ i ∈ I, l i)) (qC (∑ i ∈ I, l i)) -
      (15 / 2) * h ≤ qA (∑ i ∈ I, l i)
    linarith
  · unfold qV qC at *
    linarith

/-- Individual literal lower-endpoint gates imply the finite-max margin.
The zero member is discharged by the half gate, not by positivity of t. -/
theorem selectedCapLower_margin_of_individual (e delta : ℚ)
    (I : Finset (Fin 5)) (l : Fin 5 → ℚ)
    (hhalf : 1 / 2 + delta ≤ qV (∑ i ∈ I, l i) - 2 * e)
    (hprefix : ∀ j, prefixSquareExpr l j + delta ≤ qV (∑ i ∈ I, l i) - 2 * e)
    (hselected : ∀ j ∉ I,
      selectedSquareExpr I l j + delta ≤ qV (∑ i ∈ I, l i) - 2 * e) :
    selectedCapLower I 0 l + delta ≤ qV (∑ i ∈ I, l i) - 2 * e := by
  have hm : selectedCapLower I 0 l ≤ qV (∑ i ∈ I, l i) - 2 * e - delta := by
    apply Finset.max'_le
    intro a ha
    simp only [selectedCapLowerSet, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at ha
    rcases ha with rfl | rfl | ⟨j, _, rfl⟩ | ⟨j, hj, rfl⟩
    · linarith
    · linarith
    · linarith [hprefix j]
    · linarith [hselected j (Finset.mem_sdiff.mp hj).2]
  linarith

/-- Quantitative endpoint inequality for arbitrary rational boxes. This is
the very inequality in the actual variable-fifth gateCheck. -/
theorem endpoint_gate_of_margin (e delta h : ℚ) (I : Finset (Fin 5))
    (l u : Fin 5 → ℚ) (hh : 0 ≤ h) (hsmall : 16 * h < delta)
    (hwidth : ∀ i, u i ≤ l i + h)
    (hmargin : selectedCapLower I 0 l + delta ≤ qV (∑ i ∈ I, l i) - 2 * e) :
    selectedCapLower I 0 u + 2 * e <
      qVLo (∑ i ∈ I, l i) (∑ i ∈ I, u i) := by
  have hcap := selectedCapLower_upper_loss I l u h hh hwidth
  have htent := qVLo_lower_loss I l u h hh hwidth
  linarith

def meshStepQ (m : ℕ) : ℚ := (19 / 96) / (m + 1 : ℚ)

@[simp] theorem cast_meshStepQ (m : ℕ) :
    (meshStepQ m : ℝ) = logPrimeMeshStep 0 (19 / 96) m := by
  simp [meshStepQ, logPrimeMeshStep]

theorem meshStepQ_pos (m : ℕ) : 0 < meshStepQ m := by
  unfold meshStepQ
  positivity

theorem mesh_upper_eq_lower_add_step (m : ℕ) (j : Label5 m) (i : Fin 5) :
    qLogPrimeMeshHi 0 (19 / 96) m j i =
      qLogPrimeMeshLo 0 (19 / 96) m j i + meshStepQ m := by
  simp only [qLogPrimeMeshHi, qLogPrimeMeshLo, qLogPrimeMeshPoint,
    meshStepQ, Nat.cast_add, Nat.cast_one]
  ring

/-- Every positive rational gate margin admits one threshold for all
subsequent original meshes, before choosing any cells. -/
theorem exists_mesh_threshold (delta : ℚ) (hdelta : 0 < delta) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → 16 * meshStepQ m < delta := by
  have hd : (0 : ℝ) < (delta : ℝ) / 16 := by
    have hdR : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hdelta
    positivity
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19 / 96)).eventually (gt_mem_nhds hd))
  refine ⟨m₀, ?_⟩
  intro m hm
  have h := hm₀ m hm
  have hreal : (16 : ℝ) * (meshStepQ m : ℝ) < (delta : ℝ) := by
    rw [cast_meshStepQ]
    linarith
  exact_mod_cast hreal

/-- Literal lower-endpoint gate margins force the ACTUAL Boolean gate.
Neither row eligibility nor the gate outcome is a premise. -/
theorem gateCheck_eq_true_of_lower_endpoint_margin (e delta : ℚ)
    (m : ℕ) (r : FifthRow m) (hsmall : 16 * meshStepQ m < delta)
    (hhalf : 1 / 2 + delta ≤
      qV (∑ i ∈ r.selected, qLogPrimeMeshLo 0 (19 / 96) m r.cell i) - 2 * e)
    (hprefix : ∀ j,
      prefixSquareExpr (qLogPrimeMeshLo 0 (19 / 96) m r.cell) j + delta ≤
        qV (∑ i ∈ r.selected, qLogPrimeMeshLo 0 (19 / 96) m r.cell i) - 2 * e)
    (hselected : ∀ j ∉ r.selected,
      selectedSquareExpr r.selected (qLogPrimeMeshLo 0 (19 / 96) m r.cell) j + delta ≤
        qV (∑ i ∈ r.selected, qLogPrimeMeshLo 0 (19 / 96) m r.cell i) - 2 * e) :
    gateCheck e m r = true := by
  apply decide_eq_true
  exact endpoint_gate_of_margin e delta (meshStepQ m) r.selected _ _
    (meshStepQ_pos m).le hsmall
    (fun i => (mesh_upper_eq_lower_add_step m r.cell i).le)
    (selectedCapLower_margin_of_individual e delta r.selected _ hhalf hprefix hselected)

/-- Scalar rational endpoint candidate agrees with the actual literal
M_I(t)-2e. This converts a real raw-box margin without changing its mask. -/
theorem cast_lower_candidate (e : ℚ) (I : Finset (Fin 5)) (l : Fin 5 → ℚ) :
    ((qV (∑ i ∈ I, l i) - 2 * e : ℚ) : ℝ) =
      candidate (e : ℝ) I (fun i => (l i : ℝ)) := by
  rw [candidate, envelope_eq_v]
  simp [cast_qV]

/-- A decoded row's actual lower mesh endpoint belongs to the CLOSED raw
box. No lowerpoint membership in a half-open saved box is assumed. -/
theorem decoded_lower_endpoint_mem_closed (raw : FifthWireRow) (m : ℕ)
    (r : FifthRow m) (hr : r ∈ decodeFifthRows raw m) :
    ∀ i, (raw.lower i : ℝ) ≤
        (qLogPrimeMeshLo 0 (19 / 96) m r.cell i : ℝ) ∧
      (qLogPrimeMeshLo 0 (19 / 96) m r.cell i : ℝ) ≤ (raw.upper i : ℝ) := by
  obtain ⟨_, _, j, hj, rfl⟩ := (mem_decodeFifthRows_iff raw m r).mp hr
  intro i
  constructor
  · exact_mod_cast (hj i).1
  · have hlu : qLogPrimeMeshLo 0 (19 / 96) m j i ≤
        qLogPrimeMeshHi 0 (19 / 96) m j i := by
      rw [mesh_upper_eq_lower_add_step]
      linarith [meshStepQ_pos m]
    exact_mod_cast hlu.trans (hj i).2

/-- Uniform real margins on the genuine raw CLOSED box license EVERY
decoded cell at once, including arbitrarily many cells and boundary cells.
These are primitive literal square-gate margins, not checker assumptions. -/
theorem all_decoded_gateCheck_eq_true_of_uniform_margin
    (e delta : ℚ) (raw : FifthWireRow) (m : ℕ)
    (hsmall : 16 * meshStepQ m < delta)
    (hmargin : ∀ t : Fin 5 → ℝ,
      (∀ i, (raw.lower i : ℝ) ≤ t i ∧ t i ≤ (raw.upper i : ℝ)) →
      (1 / 2 : ℝ) + (delta : ℝ) ≤
          candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t ∧
      (∀ j, prefixSquareExpr t j + (delta : ℝ) ≤
          candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t) ∧
      (∀ j ∉ maskSlots 5 raw.mask.toNat,
        selectedSquareExpr (maskSlots 5 raw.mask.toNat) t j + (delta : ℝ) ≤
          candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t)) :
    ∀ r ∈ decodeFifthRows raw m, gateCheck e m r = true := by
  intro r hr
  have hI := decodeFifthRows_selected_eq raw m r hr
  let l := qLogPrimeMeshLo 0 (19 / 96) m r.cell
  obtain ⟨hh, hp, hs⟩ := hmargin (fun i => (l i : ℝ))
    (decoded_lower_endpoint_mem_closed raw m r hr)
  rw [← hI] at hh hp hs
  apply gateCheck_eq_true_of_lower_endpoint_margin e delta m r hsmall
  · have hc := cast_lower_candidate e r.selected l
    rw [← hc] at hh
    exact_mod_cast hh
  · intro j
    have h := hp j
    rw [← cast_lower_candidate e r.selected l,
      ← cast_prefixSquareExpr l j] at h
    exact_mod_cast h
  · intro j hj
    have h := hs j hj
    rw [← cast_lower_candidate e r.selected l,
      ← cast_selectedSquareExpr r.selected l j] at h
    exact_mod_cast h

/-- Once the quantitative refinement applies, filtering the decoded family
by the actual gate is extensionally the identity. -/
theorem checkedFifthRows_eq_decodeFifthRows_of_all_gates
    (e : ℚ) (raw : FifthWireRow) (m : ℕ)
    (hgate : ∀ r ∈ decodeFifthRows raw m, gateCheck e m r = true) :
    checkedFifthRows raw m e = decodeFifthRows raw m := by
  apply Finset.filter_eq_self.mpr
  exact hgate

end
end ImbalancedChen.P1OriginalFifthQuantitativeGateRefinement
