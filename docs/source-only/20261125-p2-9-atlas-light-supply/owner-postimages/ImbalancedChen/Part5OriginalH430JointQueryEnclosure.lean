import ImbalancedChen.P2OriginalSmoothReadoutCore
import ImbalancedChen.Part5OriginalH430FullMemberMeasurable

/-! Finite smooth lower/upper *functions* for the actual prefix pullback,
not a claim that a partition of unity alone approximates a discontinuity.
The undecided weight is exposed exactly. No boundary is dismissed because
it is called an equality. All upper/lower coefficients are chosen before N.
Source only; no assertion that the original arithmetic controls every mixed box. -/
namespace ImbalancedChen.Part5OriginalH430JointQueryEnclosure
noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalCausalSmoothAtlas
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430NativeQueryPaths Part5OriginalH430FullMemberStrips
open Part5OriginalUpsilon5CausalDictionary

/-- Every actual chronological prefix has precisely the root slot and the
0/1/2 slots of its emitted shapes. Its varying canonical Program is recomputed
on the very same input to every mask; cutoff, clamp and all 401 atoms are literal. -/
def nativeQuery {d : ℕ} (n mesh : ℕ) (k : Root) (tau : ℝ)
    (sh : Fin d → StepShape) (lower : Bool) (b : FloorAtom) :
    Set (NativeSlot sh → ℝ) := {x |
      QueryMember 0 1 (frozenRoot n k tau (nativeRootCoordinate x))
        (nativeProgram mesh sh x) (nativeCoordinates sh x) lower b}

theorem every_native_query (P : Plan) {d : ℕ} (n mesh : ℕ) (k : Root) (tau : ℝ)
    (sh : Fin d → StepShape) (lower : Bool) (b : FloorAtom) :
    let D := nativeQuery n mesh k tau sh lower b
    MeasurableSet D ∧ ContDiff ℝ ∞ (readout P (sure P D)) ∧
      ContDiff ℝ ∞ (readout P (hit P D)) ∧
      ∀ x, Cube x → readout P (sure P D) x ≤ (if x ∈ D then 1 else 0) ∧
        (if x ∈ D then 1 else 0) ≤ readout P (hit P D) x ∧
        readout P (hit P D) x - readout P (sure P D) x = readout P (mixed P D) x := by
  dsimp only
  let D := nativeQuery n mesh k tau sh lower b
  refine ⟨(Part5OriginalH430FullMemberMeasurable.actual_native_QueryMember_measurable
      n mesh k tau sh lower b).2, readout_smooth _ _, readout_smooth _ _, ?_⟩
  intro x hx
  have h := sharp_sandwich P D hx
  exact ⟨h.1,h.2,by linarith only [gap_exact P D x]⟩

end
end ImbalancedChen.Part5OriginalH430JointQueryEnclosure
