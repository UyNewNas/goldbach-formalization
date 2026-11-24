import ImbalancedChen.P1FifthUnitBoxGainDecomposition
import ImbalancedChen.P1OriginalCoarseFifthCellLimit

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual retained fifth raw owner is a saved grid box intersected with the
original selected cell.  On a selected fifth cell its moving part is precisely
the seven historical gates with both initial and third first cubes, provided
the original first-stop predicate holds.  The difference of two such owners
at a fixed cell lies in an explicit crossing of one of those seven bounds.
This is a carrier identity, not a measure estimate or an archived certificate.
-/

namespace ImbalancedChen.P1OriginalFifthActualOwnerGateCrossing

noncomputable section
open Set
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalCoarseFifthContinuation
open P1FifthUnitBoxGainDecomposition

private abbrev Point := Fin 5 → ℝ

def fixedOwnerBase (raw : FifthWireRow) (m : ℕ) (j : Label5 m) : Set Point :=
  raw.originalBox ∩ {t | ∀ i, 0 < t i} ∩
    logPrimeBox (fun _ : Fin 5 => 0) (fun _ => (19 / 96 : ℝ)) ∩
      logPrimeMeshCell 0 (19 / 96) m j

def movingGateCrossing (e₀ e₁ : ℚ) (m : ℕ) (j : Label5 m) : Set Point :=
  {t | ∃ i : Fin 7,
    (historicalUnorderedThirdGateForms i t <
        P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₀ m j i ∧
      P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₁ m j i ≤
        historicalUnorderedThirdGateForms i t) ∨
    (historicalUnorderedThirdGateForms i t <
        P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₁ m j i ∧
      P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₀ m j i ≤
        historicalUnorderedThirdGateForms i t)}

/-- The third seed is independent of the initial first-cube bound. Only the
last three of the seven historical bounds can move with the parent cap. -/
theorem actual_parentBounds_explicit (e : ℚ) (m : ℕ) (j : Label5 m) :
    P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e m j =
      ![0, 0, 0, 0, HistoricalThirdCoarse.initial (e : ℝ),
        HistoricalThirdCoarse.levelExponent (e : ℝ)
          (HistoricalThirdCoarse.box m
            (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j)),
        HistoricalThirdCoarse.levelExponent (e : ℝ)
          (HistoricalThirdCoarse.box m
            (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j))] := by
  rfl

theorem selected_rawOwnerDomain_eq_gate
    (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (hs : P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck
      (e : ℝ) m j = true) :
    rawOwnerDomain raw e chi m omega j =
      fixedOwnerBase raw m j ∩
        primeAffineGateRegion historicalUnorderedThirdGateForms
          (P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e m j) := by
  ext t
  simp only [rawOwnerDomain, P1OriginalFifthUntruncatedIntegral.fullCell,
    P1OriginalFifthLimit.sourceRegion_eq_if e chi m omega J5 j hj,
    if_pos hs, fixedOwnerBase, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

theorem selected_rawOwnerDomain_eq_empty_of_firstStop_false
    (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (hs : P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck
      (e : ℝ) m j = false) :
    rawOwnerDomain raw e chi m omega j = ∅ := by
  ext t
  simp only [rawOwnerDomain, P1OriginalFifthUntruncatedIntegral.fullCell,
    P1OriginalFifthLimit.sourceRegion_eq_if e chi m omega J5 j hj]
  simp [hs]

theorem selected_owner_difference_subset_gate_crossing
    (raw : FifthWireRow) (e₀ e₁ : ℚ) (chi₀ chi₁ : ℝ) (m : ℕ)
    (omega₀ omega₁ : ℝ) (J₀ J₁ : Finset (Label5 m)) (j : Label5 m)
    (hj₀ : j ∈ selectedFifthCells e₀ chi₀ m omega₀ J₀)
    (hj₁ : j ∈ selectedFifthCells e₁ chi₁ m omega₁ J₁)
    (hs₀ : P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck
      (e₀ : ℝ) m j = true)
    (hs₁ : P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck
      (e₁ : ℝ) m j = true) :
    ((rawOwnerDomain raw e₀ chi₀ m omega₀ j \
        rawOwnerDomain raw e₁ chi₁ m omega₁ j) ∪
      (rawOwnerDomain raw e₁ chi₁ m omega₁ j \
        rawOwnerDomain raw e₀ chi₀ m omega₀ j)) ⊆
      fixedOwnerBase raw m j ∩ movingGateCrossing e₀ e₁ m j := by
  intro t ht
  rw [Set.mem_union] at ht
  rw [selected_rawOwnerDomain_eq_gate raw e₀ chi₀ m omega₀ J₀ j hj₀ hs₀,
    selected_rawOwnerDomain_eq_gate raw e₁ chi₁ m omega₁ J₁ j hj₁ hs₁] at ht
  rcases ht with ht | ht
  · rcases ht with ⟨⟨hbase, hgate₀⟩, hnot₁⟩
    change ∀ i, historicalUnorderedThirdGateForms i t <
      P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₀ m j i at hgate₀
    have hnotGate₁ : ¬ t ∈ primeAffineGateRegion historicalUnorderedThirdGateForms
        (P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₁ m j) :=
      fun hgate₁ => hnot₁ ⟨hbase, hgate₁⟩
    change ¬ ∀ i, historicalUnorderedThirdGateForms i t <
      P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₁ m j i at hnotGate₁
    obtain ⟨i, hi⟩ := not_forall.mp hnotGate₁
    exact ⟨hbase, i, Or.inl ⟨hgate₀ i, le_of_not_gt hi⟩⟩
  · rcases ht with ⟨⟨hbase, hgate₁⟩, hnot₀⟩
    change ∀ i, historicalUnorderedThirdGateForms i t <
      P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₁ m j i at hgate₁
    have hnotGate₀ : ¬ t ∈ primeAffineGateRegion historicalUnorderedThirdGateForms
        (P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₀ m j) :=
      fun hgate₀ => hnot₀ ⟨hbase, hgate₀⟩
    change ¬ ∀ i, historicalUnorderedThirdGateForms i t <
      P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds e₀ m j i at hnotGate₀
    obtain ⟨i, hi⟩ := not_forall.mp hnotGate₀
    exact ⟨hbase, i, Or.inr ⟨hgate₁ i, le_of_not_gt hi⟩⟩

end
end ImbalancedChen.P1OriginalFifthActualOwnerGateCrossing
