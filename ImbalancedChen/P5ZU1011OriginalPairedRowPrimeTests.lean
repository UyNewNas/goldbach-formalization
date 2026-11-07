import ImbalancedChen.P5ZU1011OriginalSixteenCommonStatePrimeTest
import ImbalancedChen.P5ZU1011OriginalSixteenNativeHarmonic
import ImbalancedChen.P1AdoptedE0E1ActualSupport

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The actual adopted paired-v2 mask already has17572 half-open outer rows
with unique owners. No replacement mask or boundary deletion is introduced.
This module attaches each literal row to the ORIGINAL full16 common-state
prime test and proves the exact native last-pair logarithmic pullback.
Native ascending(p3,p4) is read as decreasing(logp4,logp3) exactly once.
Only finite identities below allow arbitrary masks; PNT is supplied here
for the actual fixed finite affine rows, never an arbitrary moving mask.
-/
namespace ImbalancedChen.P5Z.U1011OriginalPairedRowPrimeTests

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open U11Integral U11Canonical U1011AdaptivePrimeError
open U1011OriginalSixteenEligibilityState U1011OriginalSixteenAffineState
open U1011OriginalSixteenStateKernel U1011OriginalSixteenMixedGatePrimeTests
open U1011OriginalSixteenCommonStatePrimeTest U1011OriginalSixteenNativeHarmonic
open Certificates.PairedV2

abbrev Row := FullMask.Row

def outerPair (v : LogFour) : ℝ × ℝ := (v 0, v 1)

def rowRegion (r : Row) : Set LogFour :=
  outerPair ⁻¹' FullMask.P1E0E1.pairCell r

/-- Lower-inclusive and upper-exclusive, in the actual t,u order. -/
def rowGates (r : Row) : Fin 4 → MixedGate :=
  ![⟨-ContinuousLinearMap.proj 0, -(tLower (FullMask.indices r).1 : ℝ), false⟩,
    ⟨ContinuousLinearMap.proj 0, (tUpper (FullMask.indices r).1 : ℝ), true⟩,
    ⟨-ContinuousLinearMap.proj 1, -(uLower (FullMask.indices r).2 : ℝ), false⟩,
    ⟨ContinuousLinearMap.proj 1, (uUpper (FullMask.indices r).2 : ℝ), true⟩]

theorem rowRegion_eq_mixed (r : Row) : rowRegion r = mixedRegion (rowGates r) := by
  ext v
  simp [rowRegion, outerPair, FullMask.P1E0E1.pairCell, mixedRegion,
    rowGates, MixedGate.Holds, Fin.forall_fin_succ, neg_le_neg_iff, and_assoc]

theorem measurableSet_rowRegion (r : Row) : MeasurableSet (rowRegion r) := by
  rw [rowRegion_eq_mixed]
  exact measurableSet_mixedRegion _

theorem rowRegions_unique_owner {r t : Row} {v : LogFour}
    (hr : v ∈ rowRegion r) (ht : v ∈ rowRegion t) : r = t :=
  FullMask.P1E0E1.pairCell_unique_owner hr ht

/-- Additional FIXED mixed affine gates, concatenated after the complete
original circuit. No form-properness input is necessary, even for zero rows. -/
def cutGates {ι : Type*} (s : U1011OriginalSixteenAffineState.State)
    (g : ι → MixedGate) : OriginalGateSlot ⊕ ι → MixedGate
  | .inl k => originalGates s k
  | .inr i => g i

def cutCell {ι : Type*} (s : U1011OriginalSixteenAffineState.State)
    (g : ι → MixedGate) : Set LogFour := originalCell ∅ s ∩ mixedRegion g

theorem cutCell_eq_mixed {ι : Type*} (s : U1011OriginalSixteenAffineState.State)
    (g : ι → MixedGate) : cutCell s g = mixedRegion (cutGates s g) := by
  ext v
  constructor
  · rintro ⟨hs, hg⟩ k
    cases k with
    | inl k =>
      have hh : v ∈ mixedRegion (originalGates s) := by
        rw [← originalCell_eq_mixed]
        exact hs
      exact hh k
    | inr i => exact hg i
  · intro h
    refine ⟨?_, fun i => h (.inr i)⟩
    rw [originalCell_eq_mixed]
    exact fun k => h (.inl k)

theorem tendsto_actual_commonCell_cut {ι : Type*} [Fintype ι]
    (s : U1011OriginalSixteenAffineState.State) (g : ι → MixedGate) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
      ((cutCell s g).indicator actualMinimum)) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ∩ cutCell s g,
        actualMinimum v * ∏ i, 1 / v i)) := by
  have hc : ContinuousOn (frozenMinimum (kernelState s))
      (univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))) := by
    apply (continuousOn_frozenMinimum (kernelState s)).mono
    intro v hv
    exact ⟨fun j => (hv j (mem_univ j)).1, fun j => (hv j (mem_univ j)).2⟩
  have hlim := tendsto_actualPrimeBox_mixedRegion (cutGates s g)
    (frozenMinimum (kernelState s)) hc
  rw [← cutCell_eq_mixed s g] at hlim
  have hpoint (v : LogFour) (hv : v ∈ cutCell s g) :
      actualMinimum v = frozenMinimum (kernelState s) v := actualMinimum_eq_kernel ∅ hv.1
  have hind : (cutCell s g).indicator actualMinimum =
      (cutCell s g).indicator (frozenMinimum (kernelState s)) := by
    funext v
    by_cases hv : v ∈ cutCell s g
    · simp only [indicator_of_mem hv, hpoint v hv]
    · simp only [indicator_of_notMem hv]
  have hmeas : MeasurableSet (cutCell s g) := by
    rw [cutCell_eq_mixed]
    exact measurableSet_mixedRegion _
  have hint : (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
      (fun _ => (59 / 250 : ℝ)) ∩ cutCell s g,
      frozenMinimum (kernelState s) v * ∏ i, 1 / v i) =
      ∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ∩ cutCell s g,
        actualMinimum v * ∏ i, 1 / v i := by
    apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter hmeas)
    intro v hv
    rw [hpoint v hv.2]
  rw [hind, ← hint]
  exact hlim

/-- The actual original row, selected before N, has its direct state PNT.
All four half-open outer walls are retained in the arithmetic test. -/
theorem tendsto_actual_commonCell_row
    (s : U1011OriginalSixteenAffineState.State) (r : Row) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
      ((originalCell ∅ s ∩ rowRegion r).indicator actualMinimum)) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) ∩ (originalCell ∅ s ∩ rowRegion r),
        actualMinimum v * ∏ i, 1 / v i)) := by
  simpa only [cutCell, ← rowRegion_eq_mixed] using
    tendsto_actual_commonCell_cut s (rowGates r)

/-- Exact native last-pair mask. M is already in DECREASING(logp4,logp3)
coordinates; no second swap is applied to the adopted P1 pairRegion. -/
def nativeMask (M : Set (ℝ × ℝ)) (N : ℕ) (p : ℕ × ℕ) : Prop :=
  FullMask.P1E0E1.primePairCoordinates (N : ℝ) p ∈ M

theorem nativeMask_log_dictionary (M : Set (ℝ × ℝ)) (N : ℕ) (p : Fin 4 → ℕ) :
    nativeMask M N (p 1, p 0) ↔ outerPair (actualPrimeTupleLog N p) ∈ M := Iff.rfl

theorem originalDomain_mask_iff (M : Set (ℝ × ℝ)) (v : LogFour) :
    v ∈ originalDomain M ↔ v ∈ originalDomain ∅ ∧ outerPair v ∉ M := by
  simp only [originalDomain, outerPair, mem_setOf_eq, mem_empty_iff_false,
    not_false_eq_true, and_true]
  tauto

/-- A finite identity for ANY M. It is a limit theorem only after the
separate fixed finite-affine mask PNT has been supplied. -/
theorem nativeHarmonicSum_eq_fixedMask_box {N : ℕ} (hN : 1 < N)
    (M : Set (ℝ × ℝ)) (f : LogFour → ℝ) :
    nativeHarmonicSum N (nativeMask M N) f = actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
      ((originalDomain M).indicator f) := by
  rw [nativeHarmonicSum_eq_masked_box hN]
  have hkept (p : Fin 4 → ℕ) : kept N (nativeMask M N) p ↔
      actualPrimeTupleLog N p ∈ originalDomain M := by
    rw [originalDomain_mask_iff]
    exact and_congr_right (fun _ => not_congr (nativeMask_log_dictionary M N p))
  unfold maskedTestSum actualPrimeBoxTestSum
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : actualPrimeTupleLog N p ∈ originalDomain M
  · have hk := (hkept p).2 hp
    simp only [hk, if_true, indicator_of_mem hp]
  · have hk : ¬kept N (nativeMask M N) p := fun hk => hp ((hkept p).1 hk)
    simp only [hk, if_false, indicator_of_notMem hp, mul_zero]

theorem nativeMask_actual_adopted (N : ℕ) :
    nativeMask FullMask.P1E0E1.pairRegion N =
      FullMask.P1E0E1.deletionMask (N : ℝ) := rfl

end
end ImbalancedChen.P5Z.U1011OriginalPairedRowPrimeTests
