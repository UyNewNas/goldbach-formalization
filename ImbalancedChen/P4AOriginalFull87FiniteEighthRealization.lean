import ImbalancedChen.P4AOriginalFull87FiniteEighthPolicy
import ImbalancedChen.P4AOriginalFull87TrimOmission

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

One pre-N original archive schedule, one exact source trim, one finite
rational eighth-cap alphabet.  The public terminal supplies actual parent
bounds and actual source states internally; it assumes no history/support/
frontier licence.  A finite eighth stage is NOT a finite whole policy.
The volume payment below is NOT a numerical saving or a density reserve.
-/
namespace ImbalancedChen.P4AOriginalFull87FiniteEighthRealization
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim P4AOriginalFull87FiniteEighthCap
open P4AOriginalFull87FiniteEighthPolicy P4AOriginalFull87TrimOmission
open P4AOriginalFull87SevenCubeAdmission (pre point pre_length point_rpow)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalCompleteSixthChronology (currentSixthExponent)
open P4AOriginalFull87HistoryCore (width width_pos)

/-- Both sets of NATURAL square gates hold at this SAME rounded cap.
No new coordinate-domination or square-admissibility input is needed. -/
theorem finiteCap_integer_squares (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (hn : 4 * width n < delta) (N : ℝ) (hN : 1 < N)
    (p : Fin 8 → ℕ) (hp : ∀ i, 0 < p i) (c : Cell)
    (ht : point N p ∈ trim c delta) :
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < N ^ (finiteCap n c (point N p) : ℝ)) ∧
    (∀ j ∉ selected c, ((∏ k ∈ selected c, p k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selected c), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < N ^ (finiteCap n c (point N p) : ℝ)) := by
  have h := finiteCap_licensed n hd hn ht
  have hcoord : ∀ i, (p i : ℝ) ≤ N ^ point N p i :=
    fun i => (point_rpow N hN p hp i).symm.le
  constructor
  · intro j
    apply prefixSquareExpr_actual_gate N hN p (point N p) hcoord j
    have hj := h.2.2.1 j
    linarith
  · intro j hj
    apply selectedSquareExpr_actual_gate (selected c) N hN p (point N p) hcoord j
    have hgate := h.2.2.2.1 j hj
    linarith

/-- A single common source trim and alphabet resolution precede the
original e,q schedule; all precede every arithmetic parameter. The caller
supplies the primitive prime/source-carrier conditions, never a selected
state, an owner, an actual parent bound, or a supported-third witness. -/
theorem exists_shared_finite_eighth_schedule (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ r n0 : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      totalOmitted r (fun _ _ => (1 : ℝ)) < epsilon ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ n : ℕ, n0 ≤ n →
      ∀ omega : ℝ, omega ≤ 1 / 100 → ∀ N : ℕ, 1 < (N : ℝ) →
      ∀ p : Fin 8 → ℕ, (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) →
      ∀ c : Cell, point (N : ℝ) p ∈ trim c (width r) →
        RealizedHistory e q omega (N : ℝ) (pre p) c ∧
        finiteCap n c (point (N : ℝ) p) ∈ alphabet n ∧
        currentSixthExponent e q omega (N : ℝ) (rosserAncestor 6 (pre p)) + width r / 2 <
          (finiteCap n c (point (N : ℝ) p) : ℝ) ∧
        (∀ j, prefixSquareExpr (point (N : ℝ) p) j + width r / 2 <
          (finiteCap n c (point (N : ℝ) p) : ℝ)) ∧
        (∀ j ∉ selected c, selectedSquareExpr (selected c) (point (N : ℝ) p) j + width r / 2 <
          (finiteCap n c (point (N : ℝ) p) : ℝ)) ∧
        (finiteCap n c (point (N : ℝ) p) : ℝ) + width n <
          v (∑ j ∈ selected c, point (N : ℝ) p j) ∧
        selectedCap (width r) n (N : ℝ) (pre p) =
          some (finiteCap n c (point (N : ℝ) p)) ∧
        (∀ cap : ℕ, ∀ w z : ℝ, w ≤ (N : ℝ) ^ (53 / 13824 : ℝ) →
          (N : ℝ)^mu ≤ z → z ≤ (cap : ℝ) → ∀ weight : ℕ → ℝ,
          canonicalState N cap w weight p ∈
            trimmedStates (width r) n e q omega N cap w z weight c) := by
  obtain ⟨r, hr⟩ := exists_common_volume_trim epsilon hepsilon
  have hd := width_pos r
  obtain ⟨n0, hn0⟩ := exists_uniform_cap_resolution (width r) hd
  obtain ⟨e0, he0, hemax, hchoice⟩ :=
    P4AOriginalFull87ActualSourceMembership.exists_cofinal_original_source_membership
      (width r) hd
  refine ⟨r, n0, e0, he0, hemax, hr r le_rfl, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hq⟩ := hchoice e he hee
  refine ⟨q0, hq0, ?_⟩
  intro q hqq n hn omega homega N hN p hp hdelete c ht
  have hs : Source c (point (N : ℝ) p) := trim_subset_source c hd ht
  have hc := trim_subset_core c (width r) ht
  obtain ⟨hhistory, hmember⟩ := hq q hqq omega homega N hN p hp hdelete c hs hc
  have hlicense := finiteCap_licensed n hd (hn0 n hn) ht
  have hparent := hhistory.2.2.2.2
  have hgain := hlicense.2.1
  refine ⟨hhistory, finiteCap_mem_alphabet n hs, ?_, hlicense.2.2.1,
    hlicense.2.2.2.1, hlicense.2.2.2.2.2,
    selectedCap_of_trim (width r) hd n (N : ℝ) (pre p) (pre_length p) c ht, ?_⟩
  · exact (add_le_add_right hparent (width r / 2)).trans_lt hgain
  · intro cap w z hw hz hzcap weight
    exact canonical_mem_trimmedStates (width r) n e q omega N cap w z weight p c ht
      (hmember cap w z hw hz hzcap weight)

end
end ImbalancedChen.P4AOriginalFull87FiniteEighthRealization
