import ImbalancedChen.P5ZU1011OriginalSixteenAffineState
import ImbalancedChen.P5ZU1011OriginalSixteenMixedGatePrimeTests
import ImbalancedChen.P5ZU1011SelectedLargestAllCellPrimeTests

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Direct actual-prime harmonic limit for every ORIGINAL full sixteen-policy
common state. The six literal ordered-support gates are concatenated with
the241 actual branch/first-failure/H248 state rows. Zero constant rows are
handled by the exact reduction theorem, including impossible W branches.
The original nonlinear finite minimum stays inside the test sum and the
integral. There is no hForms, geometric-subset, cell-mean or convergence
premise. The only argument is the actual finite original state itself.
-/
namespace ImbalancedChen.P5Z.U1011OriginalSixteenCommonStatePrimeTest

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalSixteenEligibilityState
open U1011OriginalSixteenAffineState
open U1011OriginalSixteenMixedGatePrimeTests
open U1011OriginalSixteenStateKernel

/-- Only the original ordered support is reused from the selected-largest
file. Its policy/candidate mean is not used in the sixteen-policy result. -/
def supportGates (i : Fin 6) : MixedGate :=
  ⟨U1011SelectedLargestAllCellPrimeTests.supportForms i,
    U1011SelectedLargestAllCellPrimeTests.supportBounds i,
    !(U1011SelectedLargestAllCellPrimeTests.supportWeak i)⟩

theorem supportGates_dictionary (v : LogFour) :
    (∀ i : Fin 6, (supportGates i).Holds v) ↔ v ∈ originalDomain ∅ := by
  rw [← U1011SelectedLargestAllCellPrimeTests.support_dictionary v]
  constructor
  · intro h i
    have hi := h i
    cases hw : U1011SelectedLargestAllCellPrimeTests.supportWeak i <;>
      simpa [supportGates, MixedGate.Holds, hw] using hi
  · intro h i
    have hi := h i
    cases hw : U1011SelectedLargestAllCellPrimeTests.supportWeak i <;>
      simpa [supportGates, MixedGate.Holds, hw] using hi

abbrev OriginalGateSlot := Fin 6 ⊕ CommonGateSlot

/-- The actual full247-row mixed affine circuit, retaining all zero rows. -/
def originalGates (s : U1011OriginalSixteenAffineState.State) : OriginalGateSlot → MixedGate
  | .inl i => supportGates i
  | .inr k => commonGates s k

theorem originalCell_eq_mixed (s : U1011OriginalSixteenAffineState.State) :
    originalCell ∅ s = mixedRegion (originalGates s) := by
  ext v
  constructor
  · rintro ⟨hv, hs⟩ k
    cases k with
    | inl i => exact (supportGates_dictionary v).2 hv i
    | inr k =>
      have hcell : v ∈ commonAffineCell s := by
        rw [← commonCell_eq_affineCell]
        exact hs
      exact hcell k
  · intro h
    refine ⟨(supportGates_dictionary v).1 (fun i => h (.inl i)), ?_⟩
    rw [commonCell_eq_affineCell]
    exact fun k => h (.inr k)

/-- DIRECT full original bank state PNT. Every affine/properness/state
condition needed by the predecessor is discharged by the actual circuit.
Impossible states contribute exactly zero, rather than a fabricated mean. -/
theorem tendsto_original_sixteen_commonCell
    (s : U1011OriginalSixteenAffineState.State) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
      ((originalCell ∅ s).indicator actualMinimum)) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ∩ originalCell ∅ s,
        actualMinimum v * ∏ i, 1 / v i)) := by
  have hc : ContinuousOn (frozenMinimum (kernelState s))
      (univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))) := by
    apply (continuousOn_frozenMinimum (kernelState s)).mono
    intro v hv
    exact ⟨fun j => (hv j (mem_univ j)).1, fun j => (hv j (mem_univ j)).2⟩
  have hlim := tendsto_actualPrimeBox_mixedRegion (originalGates s)
    (frozenMinimum (kernelState s)) hc
  rw [← originalCell_eq_mixed s] at hlim
  have hpoint (v : LogFour) (hv : v ∈ originalCell ∅ s) :
      actualMinimum v = frozenMinimum (kernelState s) v :=
    actualMinimum_eq_kernel ∅ hv
  have hind : (originalCell ∅ s).indicator actualMinimum =
      (originalCell ∅ s).indicator (frozenMinimum (kernelState s)) := by
    funext v
    by_cases hv : v ∈ originalCell ∅ s
    · simp only [indicator_of_mem hv, hpoint v hv]
    · simp only [indicator_of_notMem hv]
  have hint : (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
      (fun _ => (59 / 250 : ℝ)) ∩ originalCell ∅ s,
      frozenMinimum (kernelState s) v * ∏ i, 1 / v i) =
      ∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ∩ originalCell ∅ s,
        actualMinimum v * ∏ i, 1 / v i := by
    apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter
      (measurableSet_originalCell ∅ MeasurableSet.empty s))
    intro v hv
    rw [hpoint v hv.2]
  rw [hind, ← hint]
  exact hlim

end
end ImbalancedChen.P5Z.U1011OriginalSixteenCommonStatePrimeTest
