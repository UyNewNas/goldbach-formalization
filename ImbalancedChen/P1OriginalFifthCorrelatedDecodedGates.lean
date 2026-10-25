import ImbalancedChen.P1OriginalFifthQuantitativeGateRefinement
import ImbalancedChen.P1OriginalFifthCorrelatedRawBoxGates

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Composition of a genuine correlated raw-box affine margin with the
quantitative bound for the actual variable-fifth rational gateCheck.
This licenses every contained decoded cell after one mesh threshold;
it does not enumerate the cells, execute any row check, or infer that
the authenticated full saved table passes the correlated check.
-/

namespace ImbalancedChen.P1OriginalFifthCorrelatedDecodedGates

noncomputable section
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthQuantitativeGateRefinement P1OriginalFifthCorrelatedRawBoxGates

/-- Correlated affine lower bounds on the raw closed box imply the actual
endpoint gate for every genuinely contained original-mesh cell. -/
theorem all_decoded_gateCheck_eq_true (e : ℚ) (raw : FifthWireRow) (m : ℕ)
    (hc : correlatedRawBoxGateCheck e raw = true)
    (hsmall : 16 * meshStepQ m < gateMarginQ e raw) :
    ∀ r ∈ decodeFifthRows raw m, gateCheck e m r = true := by
  have hmargin := (correlatedRawBoxGateCheck_uniform_margin e raw hc).2
  exact all_decoded_gateCheck_eq_true_of_uniform_margin e (gateMarginQ e raw)
    raw m hsmall (fun t ht => hmargin t ht)

theorem checkedFifthRows_eq_decodeFifthRows (e : ℚ) (raw : FifthWireRow) (m : ℕ)
    (hc : correlatedRawBoxGateCheck e raw = true)
    (hsmall : 16 * meshStepQ m < gateMarginQ e raw) :
    checkedFifthRows raw m e = decodeFifthRows raw m :=
  checkedFifthRows_eq_decodeFifthRows_of_all_gates e raw m
    (all_decoded_gateCheck_eq_true e raw m hc hsmall)

/-- The mesh threshold is chosen before the cell. There is no finite
cell list or postulated Boolean gate result among the hypotheses. -/
theorem exists_refinement_threshold (e : ℚ) (raw : FifthWireRow)
    (hc : correlatedRawBoxGateCheck e raw = true) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ r ∈ decodeFifthRows raw m, gateCheck e m r = true := by
  obtain ⟨m₀, hm₀⟩ := exists_mesh_threshold (gateMarginQ e raw)
    (gateMarginQ_pos e raw hc)
  exact ⟨m₀, fun m hm => all_decoded_gateCheck_eq_true e raw m hc (hm₀ m hm)⟩

/-- One threshold licenses a finite raw family, retaining each saved
mask and each original contained mesh cell without enumerating either. -/
theorem exists_family_refinement_threshold (e : ℚ) (raws : Finset FifthWireRow)
    (hc : ∀ raw ∈ raws, correlatedRawBoxGateCheck e raw = true) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ raw ∈ raws, ∀ r ∈ decodeFifthRows raw m, gateCheck e m r = true := by
  let M : FifthWireRow → ℕ := fun raw =>
    if hr : raw ∈ raws then
      Classical.choose (exists_refinement_threshold e raw (hc raw hr))
    else 0
  refine ⟨raws.sup M, ?_⟩
  intro m hm raw hr
  have hbound : M raw ≤ m := (Finset.le_sup hr).trans hm
  have hchosen : Classical.choose (exists_refinement_threshold e raw (hc raw hr)) ≤ m := by
    simpa only [M, dif_pos hr] using hbound
  exact Classical.choose_spec (exists_refinement_threshold e raw (hc raw hr)) m hchosen

/-- A positive rational STEP budget for a finite raw family. This can be
combined with an independent rough-cutoff mesh budget or an aligned-grid
construction, without relating the mesh index to an arbitrarily chosen
threshold. The inserted one handles an empty saved family exactly. -/
theorem exists_family_mesh_budget (e : ℚ) (raws : Finset FifthWireRow)
    (hc : ∀ raw ∈ raws, correlatedRawBoxGateCheck e raw = true) :
    ∃ budget : ℚ, 0 < budget ∧ ∀ m : ℕ, meshStepQ m < budget →
      ∀ raw ∈ raws, ∀ r ∈ decodeFifthRows raw m, gateCheck e m r = true := by
  let S : Finset ℚ := insert 1 (raws.image (fun raw => gateMarginQ e raw / 16))
  have hS : S.Nonempty := ⟨1, by simp [S]⟩
  let budget := S.min' hS
  have hb : 0 < budget := by
    have hm : budget ∈ S := Finset.min'_mem S hS
    simp only [S, Finset.mem_insert, Finset.mem_image] at hm
    rcases hm with h1 | ⟨raw, hr, heq⟩
    · rw [h1]
      norm_num
    · rw [← heq]
      exact div_pos (gateMarginQ_pos e raw (hc raw hr)) (by norm_num)
  refine ⟨budget, hb, ?_⟩
  intro m hm raw hr
  have hle : budget ≤ gateMarginQ e raw / 16 := by
    apply Finset.min'_le
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨raw, hr, rfl⟩)
  have hsmall : 16 * meshStepQ m < gateMarginQ e raw := by
    have h := hm.trans_le hle
    linarith
  exact all_decoded_gateCheck_eq_true e raw m (hc raw hr) hsmall

/-- The decoded family's actual selected-owner tests remain explicit.
Once supplied, this produces original eligibility rather than a surrogate
raw-box or stored-parent policy. -/
theorem decoded_original_eligible (e : ℚ) (chi omega : ℝ) (raw : FifthWireRow)
    (m : ℕ) (J5 : Finset (Label5 m)) (r : FifthRow m)
    (hc : correlatedRawBoxGateCheck e raw = true)
    (hsmall : 16 * meshStepQ m < gateMarginQ e raw)
    (hr : r ∈ decodeFifthRows raw m)
    (howner : r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (t : Point5) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    eligible e chi m omega J5 r t :=
  ⟨howner, all_decoded_gateCheck_eq_true e raw m hc hsmall r hr, ht⟩

end
end ImbalancedChen.P1OriginalFifthCorrelatedDecodedGates
