import ImbalancedChen.Part5OriginalH430NativeQueryPaths
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The O native-query dictionary requires StartMatches for Buchstab domains.
Here the domain is pulled back from the ACTUAL parent argument instead.
No equality to a fixed table-cell start is an input.  Closed knot atoms
and closed moving endpoints are retained exactly.  Replacing this moving
domain by an old fixed-start primitive has a proved absolute L1 cost.

This is a local missing dictionary and error estimate, not a smooth-box
realization of the 441-generation graph.  In particular it does not
identify the primitive L1 budget with the physical graph's localBudget,
license an arithmetic source, or repair the U3 root/full-square mismatch.
-/

namespace ImbalancedChen.Part5OriginalH430MovingBuchstabAtoms

noncomputable section
open Set MeasureTheory Classical
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430AbsoluteQueries Part5OriginalH430NativeQueryPaths
open Part5OriginalUpsilon5CausalDictionary (FloorAtom)

/-- Only the Buchstab integration start changes.  All W1/W2 domains,
densities, profiles, selected-table guards and occurrence labels are the
literal existing ones. -/
def movingDomain (n : PhysicalNode) : (q : FeedbackQuery) → Set (Space q.primitive)
  | .w1 i j => (data (.w1 i j)).domain
  | .w2Singleton j k => (data (.w2Singleton j k)).domain
  | .w2Pair j k => (data (.w2Pair j k)).domain
  | .buchstabUpper _ => buchstabUpperDomain n.argument
  | .buchstabLower _ => buchstabLowerDomain n.argument

theorem movingDomain_measurable (n : PhysicalNode) (q : FeedbackQuery) :
    MeasurableSet (movingDomain n q) := by
  cases q with
  | w1 i j => exact (data (.w1 i j)).domain_measurable
  | w2Singleton j k => exact (data (.w2Singleton j k)).domain_measurable
  | w2Pair j k => exact (data (.w2Pair j k)).domain_measurable
  | buchstabUpper i => exact measurableSet_Icc
  | buchstabLower i => exact measurableSet_Icc

/-- The former StartMatches premise is recovered when it really holds;
it is not required to define or identify an actual local query. -/
theorem movingDomain_eq_fixed {n : PhysicalNode} (q : FeedbackQuery)
    (hs : StartMatches n q) : movingDomain n q = (data q.primitive).domain := by
  cases q with
  | w1 i j => rfl
  | w2Singleton j k => rfl
  | w2Pair j k => rfl
  | buchstabUpper i =>
      change n.argument = upperStart i at hs
      change buchstabUpperDomain n.argument = buchstabUpperDomain (upperStart i)
      rw [hs]
  | buchstabLower i =>
      change n.argument = lowerStart i at hs
      change buchstabLowerDomain n.argument = buchstabLowerDomain (lowerStart i)
      rw [hs]

theorem actual_child_moving_domain {n : PhysicalNode} {z : Point}
    (q : FeedbackQuery) (hz : LocalDomain n q.shape z) :
    q.coordinate n z ∈ movingDomain n q := by
  cases q with
  | w1 i j => exact hz.2.2.1
  | w2Singleton j k => exact hz.2.2.1
  | w2Pair j k => exact hz.2.2.1
  | buchstabUpper i => exact hz.2.2
  | buchstabLower i => exact hz.2.2.2

def movingAtomSet (n : PhysicalNode) (q : FeedbackQuery) (b : FloorAtom) :
    Set (Space q.primitive) :=
  movingDomain n q ∩ tablePullback (data q.primitive).lower (data q.primitive).query b

def movingAtomDensity (n : PhysicalNode) (q : FeedbackQuery) (b : FloorAtom) :
    Space q.primitive → ℝ := (movingAtomSet n q b).indicator (data q.primitive).density

theorem movingAtomSet_measurable (n : PhysicalNode) (q : FeedbackQuery) (b : FloorAtom) :
    MeasurableSet (movingAtomSet n q b) :=
  (movingDomain_measurable n q).inter
    (measurableSet_tablePullback _ (data q.primitive).query_measurable b)

theorem movingAtomDensity_measurable (n : PhysicalNode) (q : FeedbackQuery) (b : FloorAtom) :
    Measurable (movingAtomDensity n q b) :=
  (data q.primitive).density_measurable.indicator (movingAtomSet_measurable n q b)

/-- Every singleton knot is tested at the actual child argument.  There
is no null-knot convention and no fixed-start equality hypothesis. -/
theorem actual_child_moving_atom {n : PhysicalNode} {z : Point}
    (q : FeedbackQuery) (b : FloorAtom) (hz : LocalDomain n q.shape z) :
    q.coordinate n z ∈ movingAtomSet n q b ↔
      (perform n q.shape z).argument ∈ tableAtomSet (data q.primitive).lower b := by
  constructor
  · intro h
    rw [actual_child_query]
    exact h.2
  · intro h
    refine ⟨actual_child_moving_domain q hz, ?_⟩
    change (data q.primitive).query (q.coordinate n z) ∈ _
    rw [← actual_child_query]
    exact h

/-- The input is the existing realized Program prefix at any of its
441 generation labels, not a fresh independent normalized primitive.
The ordinary local-domain predicate is the only admission hypothesis. -/
theorem occurrence_moving_atom_exact {mesh : ℕ} (n : TypedNode)
    (v : GraphVertex mesh 440) (z : Coordinates v.1.val)
    (q : FeedbackQuery) (next : Point) (b : FloorAtom)
    (hz : LocalDomain (realize v.1.val n v.2 z).physical q.shape next) :
    occurrenceInput n v z q next ∈ movingAtomSet (realize v.1.val n v.2 z).physical q b ↔
      (perform (realize v.1.val n v.2 z).physical q.shape next).argument ∈
        tableAtomSet (data q.primitive).lower b :=
  actual_child_moving_atom q b hz

theorem movingAtomDensity_eq_fixed {n : PhysicalNode} (q : FeedbackQuery)
    (hs : StartMatches n q) (b : FloorAtom) :
    movingAtomDensity n q b = atomDensity q.primitive b := by
  unfold movingAtomDensity movingAtomSet atomDensity atomSet
  rw [movingDomain_eq_fixed q hs]

/-- One fixed endpoint and one literal table atom.  This helper is used
only for the actual Buchstab domains below; no arbitrary density or
approximation-error premise is introduced. -/
def startAtomDensity (lower : Bool) (b : FloorAtom) (a : ℝ) : ℝ → ℝ :=
  (Icc a 5 ∩ tableAtomSet lower b).indicator buchstabKernel

theorem startAtomDensity_integrable (lower : Bool) (b : FloorAtom) (a : ℝ) :
    Integrable (startAtomDensity lower b a) := by
  have hi : IntegrableOn buchstabKernel (Icc a 5) :=
    buchstabKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc
  exact (hi.mono_set inter_subset_left).integrable_indicator
    (measurableSet_Icc.inter (measurableSet_tableAtomSet lower b))

theorem moving_upper_density (n : PhysicalNode) (i : Fin 200) (b : FloorAtom) :
    movingAtomDensity n (.buchstabUpper i) b =
      startAtomDensity true b (max 2 (n.argument - 1)) := rfl

theorem moving_lower_density (n : PhysicalNode) (i : Fin 150) (b : FloorAtom) :
    movingAtomDensity n (.buchstabLower i) b =
      startAtomDensity false b (n.argument - 1) := rfl

theorem fixed_upper_density (i : Fin 200) (b : FloorAtom) :
    atomDensity (.buchstabUpper i) b =
      startAtomDensity true b (max 2 (upperStart i - 1)) := rfl

theorem fixed_lower_density (i : Fin 150) (b : FloorAtom) :
    atomDensity (.buchstabLower i) b =
      startAtomDensity false b (lowerStart i - 1) := rfl

/-- The discrepancy is supported only between the two actual starts.
The interval is closed, so this pointwise bound deletes no endpoint or
positive-measure equality stratum. -/
theorem startAtomDensity_difference_le (lower : Bool) (b : FloorAtom) (a c w : ℝ) :
    |startAtomDensity lower b a w - startAtomDensity lower b c w| ≤
      (Icc (min a c) (max a c)).indicator (fun _ : ℝ => (1 : ℝ)) w := by
  by_cases ha : w ∈ Icc a 5 ∩ tableAtomSet lower b
  · by_cases hc : w ∈ Icc c 5 ∩ tableAtomSet lower b
    · by_cases hstrip : w ∈ Icc (min a c) (max a c) <;>
        simp [startAtomDensity, ha, hc, hstrip]
    · have hwc : w < c := by
        by_contra h
        exact hc ⟨⟨le_of_not_gt h, ha.1.2⟩, ha.2⟩
      have hstrip : w ∈ Icc (min a c) (max a c) :=
        ⟨(min_le_left a c).trans ha.1.1, hwc.le.trans (le_max_right a c)⟩
      simpa [startAtomDensity, ha, hc, hstrip,
        abs_of_nonneg (buchstabKernel_nonneg w)] using buchstabKernel_le_one w
  · by_cases hc : w ∈ Icc c 5 ∩ tableAtomSet lower b
    · have hwa : w < a := by
        by_contra h
        exact ha ⟨⟨le_of_not_gt h, hc.1.2⟩, hc.2⟩
      have hstrip : w ∈ Icc (min a c) (max a c) :=
        ⟨(min_le_right a c).trans hc.1.1, hwa.le.trans (le_max_left a c)⟩
      simpa [startAtomDensity, ha, hc, hstrip,
        abs_of_nonneg (buchstabKernel_nonneg w)] using buchstabKernel_le_one w
    · by_cases hstrip : w ∈ Icc (min a c) (max a c) <;>
        simp [startAtomDensity, ha, hc, hstrip]

def startAbsoluteError (lower : Bool) (b : FloorAtom) (a c : ℝ) : ℝ :=
  ∫ w, |startAtomDensity lower b a w - startAtomDensity lower b c w|

theorem startAbsoluteError_integrable (lower : Bool) (b : FloorAtom) (a c : ℝ) :
    Integrable (fun w => |startAtomDensity lower b a w - startAtomDensity lower b c w|) :=
  ((startAtomDensity_integrable lower b a).sub
    (startAtomDensity_integrable lower b c)).abs

/-- A genuine absolute L1 estimate, with integrability proved above.
No atom mass is divided out, and empty or zero-mass atoms cause no exception. -/
theorem startAbsoluteError_bounds (lower : Bool) (b : FloorAtom) (a c : ℝ) :
    0 ≤ startAbsoluteError lower b a c ∧ startAbsoluteError lower b a c ≤ |a - c| := by
  have hi : Integrable ((Icc (min a c) (max a c)).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (continuousOn_const.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have he := integral_mono (startAbsoluteError_integrable lower b a c) hi
    (startAtomDensity_difference_le lower b a c)
  have hlength : volume.real (Icc (min a c) (max a c)) = |a - c| := by
    rcases le_total a c with hac | hca
    · rw [min_eq_left hac, max_eq_right hac, Real.volume_real_Icc_of_le hac,
        abs_of_nonpos (sub_nonpos.mpr hac)]
      ring
    · rw [min_eq_right hca, max_eq_left hca, Real.volume_real_Icc_of_le hca,
        abs_of_nonneg (sub_nonneg.mpr hca)]
  rw [integral_indicator_one measurableSet_Icc, hlength] at he
  exact ⟨integral_nonneg (fun _ => abs_nonneg _), he⟩

/-- The actual moving upper start versus the original fixed primitive.
The max-two start is 1-Lipschitz, including its entire constant branch. -/
theorem actual_upper_start_absolute_error (n : PhysicalNode) (i : Fin 200) (b : FloorAtom) :
    (∫ w, |movingAtomDensity n (.buchstabUpper i) b w -
      atomDensity (.buchstabUpper i) b w|) ≤ |n.argument - upperStart i| := by
  rw [moving_upper_density, fixed_upper_density]
  have h := (startAbsoluteError_bounds true b
    (max 2 (n.argument - 1)) (max 2 (upperStart i - 1))).2
  have hmax : |max 2 (n.argument - 1) - max 2 (upperStart i - 1)| ≤
      |(n.argument - 1) - (upperStart i - 1)| := by
    simpa only [max_comm] using
      abs_max_sub_max_le_abs (n.argument - 1) (upperStart i - 1) 2
  have hs : (n.argument - 1) - (upperStart i - 1) = n.argument - upperStart i := by ring
  exact h.trans (by simpa only [hs] using hmax)

theorem actual_lower_start_absolute_error (n : PhysicalNode) (i : Fin 150) (b : FloorAtom) :
    (∫ w, |movingAtomDensity n (.buchstabLower i) b w -
      atomDensity (.buchstabLower i) b w|) ≤ |n.argument - lowerStart i| := by
  rw [moving_lower_density, fixed_lower_density]
  have h := (startAbsoluteError_bounds false b (n.argument - 1) (lowerStart i - 1)).2
  have hs : (n.argument - 1) - (lowerStart i - 1) = n.argument - lowerStart i := by ring
  simpa only [startAbsoluteError, hs] using h

/-- Equality of starts is unnecessary on the constant upper branch.
This identity retains every knot atom rather than discarding its pullback. -/
theorem upper_constant_start_exact (n : PhysicalNode) (i : Fin 200)
    (hn : n.argument ≤ 3) (hi : upperStart i ≤ 3) (b : FloorAtom) :
    movingAtomDensity n (.buchstabUpper i) b = atomDensity (.buchstabUpper i) b := by
  rw [moving_upper_density, fixed_upper_density,
    max_eq_left (by linarith : n.argument - 1 ≤ 2),
    max_eq_left (by linarith : upperStart i - 1 ≤ 2)]

/-- A fixed-grid lower dictionary alone misses this open strip at start
two.  This is a domain fact, not a claim that every such point belongs to
a licensed H430 arithmetic path.  A transport or a moving-domain mask
must be justified when passing from an actual parent to fixed primitives. -/
theorem lower_start_two_open_strip :
    (Ioo (1 : ℝ) (51 / 50)).Nonempty ∧
      ∀ i : Fin 150, Ioo (1 : ℝ) (51 / 50) ⊆
        buchstabLowerDomain 2 \ (data (.buchstabLower i)).domain := by
  refine ⟨Set.nonempty_Ioo.mpr (by norm_num), ?_⟩
  intro i w hw
  have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hstart : (51 / 50 : ℝ) ≤ lowerStart i - 1 := by
    dsimp [lowerStart]
    linarith
  refine ⟨?_, ?_⟩
  · change 2 - 1 ≤ w ∧ w ≤ 5
    constructor <;> linarith [hw.1, hw.2]
  · intro h
    change lowerStart i - 1 ≤ w ∧ w ≤ 5 at h
    linarith [h.1, hw.2]

end
end ImbalancedChen.Part5OriginalH430MovingBuchstabAtoms
