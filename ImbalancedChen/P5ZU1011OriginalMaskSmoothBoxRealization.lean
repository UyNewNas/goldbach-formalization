import ImbalancedChen.P5ZU1011AffineSmoothBoxCover
import ImbalancedChen.P5ZU1011SameRhoFixedCellPolyhedralIntegral
import ImbalancedChen.P5ZU1011OriginalPairedFixedMaskHarmonic
import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapCompiler

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual ORIGINAL policy/order states, literal native owner cells, and the
selected17572 half-open paired rectangles receive finite signed sums of
separated FOUR-prime smooth boxes. Native owner mesh m and smoothing mesh n
are distinct: the physical residual row stays frozen at m, before n, delta,
N and every arithmetic tuple. The same original E is retained by exact
row subtraction. This is an atom realization, not a strong-PP conclusion.
-/
namespace ImbalancedChen.P5Z.U1011OriginalMaskSmoothBoxRealization
noncomputable section
open Set Classical
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenAffineState
open U1011OriginalSixteenMixedGatePrimeTests
open U1011OriginalSixteenCommonStatePrimeTest (originalGates OriginalGateSlot)
open U1011OriginalPairedRowPrimeTests (rowRegion rowGates nativeMask)
open U1011OriginalPairedFixedMaskHarmonic (outerUnion keptDomain rowDomain)
open U1011FourDimensionalSmoothBoxAtoms U1011AffineSmoothBoxCover
open Certificates.PairedV2

abbrev Row := FullMask.Row
abbrev State := U1011OriginalSixteenAffineState.State

/-- Actual247 policy/order rows plus EIGHT literal native owner faces. -/
def baseGates (s : State) (m : ℕ) (k : Grid m) :
    OriginalGateSlot ⊕ (Fin 4 × Bool) → U1011OriginalSixteenEligibilityState.MixedGate :=
  U1011SameRhoFixedCellPolyhedralIntegral.cutGates (originalGates s) m k

/-- The four ORIGINAL t,u rectangle faces are added without swapping
prime coordinates or replacing the original outer mask. -/
def removedGates (s : State) (m : ℕ) (k : Grid m) (r : Row) :
    (OriginalGateSlot ⊕ Fin 4) ⊕ (Fin 4 × Bool) →
      U1011OriginalSixteenEligibilityState.MixedGate :=
  U1011SameRhoFixedCellPolyhedralIntegral.cutGates
    (U1011OriginalPairedRowPrimeTests.cutGates s (rowGates r)) m k

theorem base_region (s : State) (m : ℕ) (k : Grid m) :
    mixedRegion (baseGates s m k) = originalCell ∅ s ∩ cell m k := by
  rw [baseGates, ← U1011SameRhoFixedCellPolyhedralIntegral.cut_eq_mixed,
    ← U1011OriginalSixteenCommonStatePrimeTest.originalCell_eq_mixed]

theorem removed_region (s : State) (m : ℕ) (k : Grid m) (r : Row) :
    mixedRegion (removedGates s m k r) = (originalCell ∅ s ∩ rowRegion r) ∩ cell m k := by
  rw [removedGates, ← U1011SameRhoFixedCellPolyhedralIntegral.cut_eq_mixed,
    ← U1011OriginalPairedRowPrimeTests.cutCell_eq_mixed]
  rw [U1011OriginalPairedRowPrimeTests.cutCell,
    ← U1011OriginalPairedRowPrimeTests.rowRegion_eq_mixed]

def retainedIndicator (S : Finset Row) (s : State) (m : ℕ) (k : Grid m) (v : LogFour) : ℝ :=
  if v ∈ originalCell (outerUnion S) s ∩ cell m k then 1 else 0

/-- Exact original same-E subtraction, before any smoothing or estimate.
The proved unique paired-row ownership retains multiplicity exactly one. -/
theorem original_indicator_split (S : Finset Row) (s : State) (m : ℕ) (k : Grid m)
    (v : LogFour) :
    regionIndicator (baseGates s m k) v = retainedIndicator S s m k v +
      ∑ r ∈ S, regionIndicator (removedGates s m k r) v := by
  have h := U1011OriginalPairedFixedMaskHarmonic.kept_indicator_split S (fun _ => (1 : ℝ)) v
  by_cases hc : v ∈ commonCell s
  <;> by_cases hk : v ∈ cell m k
  · simpa [regionIndicator, base_region, removed_region, retainedIndicator, originalCell,
      U1011OriginalPairedFixedMaskHarmonic.originalDomain_outerUnion,
      U1011OriginalPairedFixedMaskHarmonic.domain, rowDomain, Set.indicator_apply, hc, hk,
      and_assoc] using h
  · simp [regionIndicator, base_region, removed_region, retainedIndicator, originalCell, hk]
  · simp [regionIndicator, base_region, removed_region, retainedIndicator, originalCell, hc]
  · simp [regionIndicator, base_region, removed_region, retainedIndicator, originalCell, hc]

/-- A lower expression uses INNER base boxes and OUTER removed boxes;
the upper expression reverses these choices. Every summand is separated. -/
def signedSmoothCover (lowerSide : Bool) (S : Finset Row) (s : State)
    (m : ℕ) (k : Grid m) (n : ℕ) (δ : ℝ) (v : LogFour) : ℝ :=
  smoothCover lowerSide δ
    (if lowerSide then innerCells (baseGates s m k) n else outerCells (baseGates s m k) n) v -
      ∑ r ∈ S, smoothCover (!lowerSide) δ
        (if lowerSide then outerCells (removedGates s m k r) n
          else innerCells (removedGates s m k r) n) v

theorem original_mask_smooth_sandwich (S : Finset Row) (s : State)
    (m : ℕ) (k : Grid m) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {v : LogFour} (hv : v ∈ cube) :
    signedSmoothCover true S s m k n δ v ≤ retainedIndicator S s m k v ∧
      retainedIndicator S s m k v ≤ signedSmoothCover false S s m k n δ v := by
  have hb := smooth_inner_le_region_le_outer (baseGates s m k) n hδ hv
  have hr (r : Row) := smooth_inner_le_region_le_outer (removedGates s m k r) n hδ hv
  have hlo := Finset.sum_le_sum (s := S) (fun r hrS => (hr r).1)
  have hhi := Finset.sum_le_sum (s := S) (fun r hrS => (hr r).2)
  have he := original_indicator_split S s m k v
  simp only [signedSmoothCover, Bool.not_true, Bool.not_false, if_true, if_false]
  constructor <;> linarith

def circuitReserve {ι : Type*} (inner : Bool) (g : ι → U1011OriginalSixteenEligibilityState.MixedGate)
    (n : ℕ) (δ : ℝ) (v : LogFour) : Prop :=
  faceReserve inner δ (if inner then innerCells g n else outerCells g n) v ∨ wallReserve g n v

def originalReserve (lowerSide : Bool) (S : Finset Row) (s : State)
    (m : ℕ) (k : Grid m) (n : ℕ) (δ : ℝ) (v : LogFour) : Prop :=
  circuitReserve lowerSide (baseGates s m k) n δ v ∨
    ∃ r ∈ S, circuitReserve (!lowerSide) (removedGates s m k r) n δ v

theorem circuit_error_supported {ι : Type*}
    (g : ι → U1011OriginalSixteenEligibilityState.MixedGate) (inner : Bool)
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) {v : LogFour} (hv : v ∈ cube)
    (he : smoothCover inner δ (if inner then innerCells g n else outerCells g n) v -
      regionIndicator g v ≠ 0) : circuitReserve inner g n δ v := by
  cases inner with
  | false => exact smooth_outer_error_supported g n hδ hv he
  | true => exact smooth_inner_error_supported g n hδ hv he

/-- This support statement is valid at every literal prime-log point.
The reserve contains policy, order, native-cell and adopted-row walls. -/
theorem original_mask_error_supported (lowerSide : Bool) (S : Finset Row) (s : State)
    (m : ℕ) (k : Grid m) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {v : LogFour} (hv : v ∈ cube)
    (he : signedSmoothCover lowerSide S s m k n δ v - retainedIndicator S s m k v ≠ 0) :
    originalReserve lowerSide S s m k n δ v := by
  by_contra hn
  have hb : smoothCover lowerSide δ
      (if lowerSide then innerCells (baseGates s m k) n else outerCells (baseGates s m k) n) v =
      regionIndicator (baseGates s m k) v := by
    apply sub_eq_zero.mp
    by_contra h
    exact hn (Or.inl (circuit_error_supported _ lowerSide n hδ hv h))
  have hr (r : Row) (hrS : r ∈ S) : smoothCover (!lowerSide) δ
      (if lowerSide then outerCells (removedGates s m k r) n
        else innerCells (removedGates s m k r) n) v = regionIndicator (removedGates s m k r) v := by
    apply sub_eq_zero.mp
    by_contra h
    have herror : circuitReserve (!lowerSide) (removedGates s m k r) n δ v := by
      apply circuit_error_supported _ (!lowerSide) n hδ hv
      cases lowerSide <;> simpa using h
    exact hn (Or.inr ⟨r, hrS, herror⟩)
  have hsum := Finset.sum_congr rfl hr
  have hsplit := original_indicator_split S s m k v
  apply he
  unfold signedSmoothCover
  rw [hb, hsum]
  linarith

/-- All17572 actual selected rows, with their original half-open walls,
are obtained simply by S=univ. No new geometric mask is substituted. -/
theorem actual17572_mask_sandwich (s : State) (m : ℕ) (k : Grid m) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {v : LogFour} (hv : v ∈ cube) :
    signedSmoothCover true Finset.univ s m k n δ v ≤
      (if v ∈ originalCell FullMask.P1E0E1.pairRegion s ∩ cell m k then 1 else 0) ∧
    (if v ∈ originalCell FullMask.P1E0E1.pairRegion s ∩ cell m k then 1 else 0) ≤
      signedSmoothCover false Finset.univ s m k n δ v := by
  simpa [retainedIndicator, U1011OriginalPairedFixedMaskHarmonic.outerUnion_all] using
    original_mask_smooth_sandwich (Finset.univ : Finset Row) s m k n hδ hv

/-- A grouping is a fixed function on the FOUR labels for the WHOLE
smooth box. This is an exact profile identity; admissible merger lengths
and residual coefficient factorization remain separate obligations. -/
theorem whole_atom_fixed_group_profile (inner : Bool) (δ : ℝ) (n : ℕ) (j : Grid n)
    (groups : Fin 4 → Fin 3) (v : LogFour) :
    boxAtom inner δ n j v = ∏ a : Fin 3,
      ∏ i ∈ (Finset.univ : Finset (Fin 4)).filter (fun i => groups i = a),
        U1011CompactLogIntervalSmoothing.weight inner δ
          (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
          (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i) (v i) := by
  exact (Finset.prod_fiberwise Finset.univ groups _).symm

/-- Nonzero inner tensor support lies in the exact owned mesh cell. -/
theorem inner_atom_nonzero_mem {δ : ℝ} (hδ : 0 < δ) {n : ℕ} {j : Grid n}
    {v : LogFour} (ha : boxAtom true δ n j v ≠ 0) : v ∈ cell n j := by
  by_contra hv
  have hzero : boxLiteral n j v = 0 := by rw [boxLiteral_eq_indicator, if_neg hv]
  have hle := inner_box_le_literal hδ n j v
  rw [hzero] at hle
  exact ha (le_antisymm hle (boxAtom_bounds true δ n j v).1)

/-- On every safe inner atom the ORIGINAL native owner cell and its
actual near-cap residual coefficient stay frozen, before arithmetic. -/
theorem original_native_row_on_inner_atom (s : State) (m : ℕ) (k : Grid m) (n N : ℕ)
    (eta : ℚ) {δ : ℝ} (hδ : 0 < δ) {j : Grid n}
    (hj : j ∈ innerCells (baseGates s m k) n) {t : Four}
    (ha : boxAtom true δ n j (coordinates N t) ≠ 0) :
    U1011OriginalSixteenJointNearCapCompiler.support m N eta t =
      U1011OriginalSixteenJointNearCapCompiler.rowSupport
        (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox m k)) (gridBox m k) eta N ∧
    ∀ d, U1011OriginalSixteenJointNearCapCompiler.coefficient m N eta t d =
      U1011OriginalSixteenJointNearCapCompiler.rowCoefficient
        (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox m k)) (gridBox m k) eta N d := by
  have hsafe := (Finset.mem_filter.mp hj).2 _ (inner_atom_nonzero_mem hδ ha)
  rw [base_region] at hsafe
  exact U1011OriginalSixteenJointNearCapCompiler.compiled_static_on_cell m N eta hsafe.2

end
end ImbalancedChen.P5Z.U1011OriginalMaskSmoothBoxRealization
