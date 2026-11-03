import ImbalancedChen.P4AOriginalFull87CommonHistoricalMesh
import ImbalancedChen.P4AOriginalFull87CompleteSixthBound
import ImbalancedChen.P4AOriginalFull87CompleteSixthDispatch
import ImbalancedChen.P4AOriginalCommonArchiveSchedule

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The common actual schedule is the UNCHANGED R06 original fourth/fifth bank
and the COMPLETE S09 sixth producer. q precedes omega, N, and every source
label. The actual supported-third predicate is a CONCLUSION, proved from
the original half-open mesh and original rough activation. All four odd
histories lie below its actual lambda3. The old held-eleven bound is never
substituted for the complete current sixth parent.

This does not assert reverse occurrence/frontier membership, full saved
sixth guard coverage, all numerical saving transport, a finite higher-cap
alphabet, compiler reserves, or whole-node verification.
-/
namespace ImbalancedChen.P4AOriginalFull87ActualCommonHistory
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AOriginalFull87SourceDictionary P4AOriginalFull87HistoryCore
open P4AOriginalFull87CommonHistoricalMesh
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology
open P2OriginalSaving16HistoricalMesh (firstThree firstThree_ancestor actual_firstStop_of_joint_cell)

/-- This is a conclusion predicate on the exact schedule, never an input
licence. It uses the original mesh ownership and actual current parent. -/
def RealizedHistory (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ)
    (c : Cell) : Prop :=
  let d := data e q omega
  let t := primeHistoryLogCoordinates N 8 pre
  HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m N (rosserAncestor 1 pre) ∧
  P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
    (rosserAncestor 3 pre) ∧
  (∀ j : Fin 4, oldHistory t j < lambda3 d N (rosserAncestor 4 pre)) ∧
  lambda3 d N (rosserAncestor 4 pre) ≤
    currentSixthExponent e q omega N (rosserAncestor 6 pre) ∧
  currentSixthExponent e q omega N (rosserAncestor 6 pre) ≤ comparison c t

/-- Increasing q preserves the required resolution of the ORIGINAL
m=475*q-1 grid400-aligned mesh; this is not a new mesh constructor. -/
theorem original_mesh_above (m0 q : ℕ) (hq : m0 + 1 ≤ q)
    (e : ℚ) (omega : ℝ) : m0 ≤ (data e q omega).m := by
  change m0 ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q
  unfold P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh
  omega

/-- ONE pre-N schedule realizes every original source in the retained
common carrier. There is no assumed supported predicate, history estimate,
current-parent bound, selected-state membership, or supplied licence. -/
theorem exists_original_common_history (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ omega : ℝ, omega ≤ 1 / 100 → ∀ N : ℝ, 1 < N →
      ∀ pre : List ℕ, pre.length = 8 → (∀ p ∈ pre, 0 < p) →
      ∀ c : Cell, Source c (primeHistoryLogCoordinates N 8 pre) →
      primeHistoryLogCoordinates N 8 pre ∈ core delta →
        RealizedHistory e q omega N pre c := by
  obtain ⟨e0, he0, hmesh⟩ := exists_common_actual_mesh delta hdelta
  refine ⟨e0, he0, ?_⟩
  intro e he hee
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  obtain ⟨m0, hm0⟩ := hmesh (e : ℝ) heR hee ((e : ℝ) / 20)
    (by positivity) (by linarith)
  refine ⟨m0 + 1, by omega, ?_⟩
  intro q hq omega homega N hN pre hlen hpos c hs ht
  let d := data e q omega
  let t := primeHistoryLogCoordinates N 8 pre
  have hdm : m0 ≤ d.m := original_mesh_above m0 q hq e omega
  obtain ⟨j, hj, hjt, hhist, hlo, hup⟩ := hm0 d.m hdm c t hs ht
  have hj' : j ∈ HistoricalThirdCoarse.cells (d.e : ℝ) d.chi d.m := hj
  have hsupport : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre) := by
    refine ⟨P4AOriginalFull87CommonHistoricalMesh.actual_third_active
      omega N hN homega pre hlen hpos c hs, j, hj', ?_⟩
    rw [firstThree_ancestor N pre hlen]
    exact hjt
  have hcap : lambda3 d N (rosserAncestor 4 pre) =
      HistoricalThirdCoarse.exponent (e : ℝ) ((e : ℝ) / 20) d.m (firstThree t) := by
    rw [P4AOriginalFull87CompleteSixthBound.actual_third_eq_original
      d N pre hlen c hs,
      P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hsupport,
      firstThree_ancestor N pre hlen] <;> rfl
  have hparent : lambda3 d N (rosserAncestor 4 pre) ≤
      currentSixthExponent e q omega N (rosserAncestor 6 pre) := by
    have hh := lambda3_le_exponent5 d N (rosserAncestor 5 pre)
    rw [lambda3_ancestor d N 5 (by decide),
      ← lambda3_ancestor d N 4 (by decide) pre] at hh
    have hp := fifth_le_current e q omega N (rosserAncestor 6 pre)
    change exponent5 d N (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _ at hp
    rw [rosserAncestor_nested 5 6 (by decide)] at hp
    exact hh.trans hp
  have hupper := P4AOriginalFull87CompleteSixthBound.source_current_le_comparison
    e q omega N he.le pre hlen c hs hsupport
  have hstop := actual_firstStop_of_joint_cell (d.e : ℝ) d.chi N d.m
    pre hlen j hj' hjt
  refine ⟨hstop, hsupport, ?_, hparent, hupper⟩
  intro k
  rw [hcap]
  exact hhist k

/-- A real original-source residual is derived at the ACTUAL current
sixth parent. It is not substituted by the ideal third or comparison R. -/
theorem realized_actual_residual (e : ℚ) (q : ℕ) (omega N : ℝ)
    (pre : List ℕ) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (hr : RealizedHistory e q omega N pre c) :
    let t := primeHistoryLogCoordinates N 8 pre
    t 7 < currentSixthExponent e q omega N (rosserAncestor 6 pre) - (∑ j, t j) ∧
    currentSixthExponent e q omega N (rosserAncestor 6 pre) < newCap c t := by
  let t := primeHistoryLogCoordinates N 8 pre
  have h7 := hr.2.2.1 (3 : Fin 4)
  have hparent := hr.2.2.2.1
  have horder := (P4AOriginalFull87SourceDictionary.source_basic hs).2.2.2 6
  have hupper := hr.2.2.2.2
  have hgain := (source_improvement_terminal hs).1
  constructor
  · dsimp [oldHistory, P4AOriginalRemainingEighthSources.history] at h7
    norm_num at horder
    dsimp only
    simp only [Fin.sum_univ_succ]
    linarith
  · exact hupper.trans_lt hgain

/-- The exact owner's decision and descendant continuation from the
previous packet are now paired with a DERIVED real schedule. The owner is
obtained from original rows; no arbitrary parent is supplied here. -/
theorem exists_original_history_and_dispatch (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ omega : ℝ, omega ≤ 1 / 100 → ∀ N : ℝ, 1 < N →
      ∀ pre : List ℕ, pre.length = 8 → (∀ p ∈ pre, 0 < p) →
      ∀ c : Cell, Source c (primeHistoryLogCoordinates N 8 pre) →
      primeHistoryLogCoordinates N 8 pre ∈ core delta →
        RealizedHistory e q omega N pre c ∧
        P4AOriginalFull87SourceDispatch.ownerAtPrefix N pre = some c ∧
        (∀ p : ℕ, ∀ later : List ℕ, ∀ positive : Bool,
          P4AOriginalFull87CompleteSixthDispatch.policy e q omega N positive
            ((p :: later) ++ pre) =
          ordinaryParityRosserPolicy false
            (N ^ newCap c (primeHistoryLogCoordinates N 8 pre))
            positive ((p :: later) ++ pre)) := by
  obtain ⟨e0, he0, hchoice⟩ := exists_original_common_history delta hdelta
  refine ⟨e0, he0, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hhistory⟩ := hchoice e he hee
  refine ⟨q0, hq0, ?_⟩
  intro q hq omega homega N hN pre hlen hpos c hs ht
  refine ⟨hhistory q hq omega homega N hN pre hlen hpos c hs ht,
    (P4AOriginalFull87SourceDispatch.ownerAtPrefix_rank_eight N pre hlen c).mpr hs, ?_⟩
  intro p later positive
  exact P4AOriginalFull87CompleteSixthDispatch.policy_on_selected_descendants
    e q omega N c pre later hlen hs p positive

/-- Nonvacuous existence of a legal rational precision and one actual
archive mesh, BOTH fixed before omega, N and every original87 source.
The original common-constructor precision ceiling is retained. -/
theorem exists_concrete_shared_history (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < e ∧ (e : ℝ) ≤ 11 / 64000 ∧ 0 < q ∧
      ∀ omega : ℝ, omega ≤ 1 / 100 → ∀ N : ℝ, 1 < N →
      ∀ pre : List ℕ, pre.length = 8 → (∀ p ∈ pre, 0 < p) →
      ∀ c : Cell, Source c (primeHistoryLogCoordinates N 8 pre) →
      primeHistoryLogCoordinates N 8 pre ∈ core delta →
        RealizedHistory e q omega N pre c := by
  obtain ⟨e0, he0, hchoose⟩ := exists_original_common_history delta hdelta
  have hbound : (0 : ℝ) < min e0 (11 / 64000) := lt_min he0 (by norm_num)
  obtain ⟨e, heR, heupper⟩ := exists_rat_btwn hbound
  have he : (0 : ℚ) < e := by exact_mod_cast heR
  have hee : (e : ℝ) < e0 := heupper.trans_le (min_le_left _ _)
  have hemax : (e : ℝ) ≤ 11 / 64000 :=
    (heupper.trans_le (min_le_right _ _)).le
  obtain ⟨q0, hq0, hh⟩ := hchoose e he hee
  exact ⟨e, q0, he, hemax, hq0, hh q0 le_rfl⟩

end
end ImbalancedChen.P4AOriginalFull87ActualCommonHistory
