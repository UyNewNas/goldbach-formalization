import ImbalancedChen.Part3OriginalSwitchedProjectionMask
import ImbalancedChen.Part3OriginalSwitchedScaleContraction

/-! The actual finite level supports of the two marked traces. -/
namespace ImbalancedChen.Part3.OriginalSwitchedActiveLevels20261113
noncomputable section
open Finset Complex
open scoped BigOperators Classical
open OriginalSwitchedTraceProjection20261113 (all pair E R C H)
open OriginalSwitchedPhysicalWindows20261113 (returnScale six_return)
open OriginalSwitchedLevelIdentity20261113 (levelWeight spectral)
open OriginalSwitchedHolTraceError20261113 (test)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels mem_classicalLevels)
open OriginalSwitchedInitialTraceGeometry20261113 (mark)
open OriginalSameInfinityWeightedHol20261113 (holSum basisTerm)
open OriginalSwitchedMaassExchange20261113 (mass)
open OriginalSameInfinityFixedScalarTrace20261113 (total)
open ActualPrescribedPositiveJ20261112 (positiveWeight exceptionalWeight)
open ActualPositiveNativeDiagonal20261112 (nativeWeight)
open ActualPositiveHolomorphicWeights20261112 (holWeight moment)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open CommonSmoothCutoff (dyadicCutoff dyadicCutoff_tsupport_eq_tight)

def inScale (Q : ℝ) (l : ℕ) := (2:ℝ)^l*Q/4
def inputLevels (Q : ℝ) := (range 4).biUnion (fun l => classicalLevels (inScale Q l))
def outScale (j : ℕ) (Y Q : ℝ) (l : ℕ) := (2:ℝ)^l*returnScale j Y Q/2
def outputLevels (j : ℕ) (Y Q : ℝ) := (range 6).biUnion (fun l => classicalLevels (outScale j Y Q l))

theorem outside_input {Q : ℝ} (qp : 0<Q) (q : ℕ+) (outside : q∉inputLevels Q) : levelWeight Q q=0 := by
  by_contra nz
  have p : dyadicCutoff ((q.val:ℝ)/Q)≠0 := fun h => nz (by simp [levelWeight,h])
  have t := subset_tsupport _ p
  rw [dyadicCutoff_tsupport_eq_tight] at t
  have bounds : Q/2≤(q.val:ℝ) ∧ (q.val:ℝ)≤(5/2)*Q :=
    ⟨by have u := (le_div_iff₀ qp).mp t.1;linarith, (div_le_iff₀ qp).mp t.2⟩
  apply outside
  apply Finset.mem_biUnion.mpr
  by_cases edge : (q.val:ℝ)≤Q/2
  · refine ⟨0,by decide,(mem_classicalLevels _ _).mpr ?_⟩
    dsimp only [inScale]
    constructor <;> norm_num <;> linarith only [edge,bounds.1,qp]
  by_cases lo : (q.val:ℝ)≤Q
  · refine ⟨1,by decide,(mem_classicalLevels _ _).mpr ?_⟩
    dsimp only [inScale]
    constructor <;> norm_num <;> linarith only [lo,not_le.mp edge]
  by_cases mid : (q.val:ℝ)≤2*Q
  · refine ⟨2,by decide,(mem_classicalLevels _ _).mpr ?_⟩
    dsimp only [inScale]
    constructor <;> norm_num <;> linarith only [mid,not_le.mp lo]
  · refine ⟨3,by decide,(mem_classicalLevels _ _).mpr ?_⟩
    dsimp only [inScale]
    constructor <;> norm_num <;> linarith only [bounds.2,not_le.mp mid,qp]

private theorem zero_spectrum (q m n : ℕ+) : spectral q m n (fun _ => 0)=0 := by
  simp [spectral,mass,total,nativeWeight,positiveWeight,exceptionalWeight,holSum,basisTerm,holWeight,moment]

theorem outside_output (j a b : ℕ) (lo : 2^j≤a) (hi : b≤2^(j+1)) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q)
    (d : ℕ+) (outside : d∉outputLevels j Y Q) (ω : ℝ) :
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    all true d ap b Y Q ω=0 := by
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  have mem (m : ↥(Ico a b)) : m.val∈dyadicWindow j :=
    Finset.mem_Ico.mpr ⟨lo.trans (Finset.mem_Ico.mp m.property).1,
      lt_of_lt_of_le (Finset.mem_Ico.mp m.property).2 hi⟩
  have zero (m n : ↥(Ico a b)) : switchedTest Y ((d.val:ℝ)*Q) m.val n.val=fun _ => 0 := by
    funext x
    by_contra nz
    obtain ⟨l,lb,dl⟩ := six_return (mem m) (mem n) yp qp d nz
    exact outside (Finset.mem_biUnion.mpr ⟨l,Finset.mem_range.mpr lb,dl⟩)
  apply sum_eq_zero
  intro m _
  apply sum_eq_zero
  intro n _
  change _*spectral d (mark a ap m) (mark a ap n) (switchedTest Y ((d.val:ℝ)*Q) m.val n.val)=0
  rw [zero,zero_spectrum,mul_zero]

/-- Finite disjointness is unnecessary for a sum of nonnegative costs. -/
theorem charge_union (U : Finset ℕ) (V : ℕ→Finset ℕ+) (f : ℕ+→ℝ) (nn : ∀ q,0≤f q) :
    (∑ q∈U.biUnion V,f q)≤∑ l∈U,∑ q∈V l,f q := by
  classical
  let S := U.biUnion V
  have point (q : ℕ+) (hq : q∈S) : f q≤∑ l∈U,if q∈V l then f q else 0 := by
    obtain ⟨l,hl,hq⟩ := Finset.mem_biUnion.mp hq
    have r := Finset.single_le_sum (f:=fun k : ℕ => if q∈V k then f q else 0)
      (fun k _ => by split_ifs <;> first | exact nn q | exact le_rfl) hl
    simpa only [if_pos hq] using r
  apply (Finset.sum_le_sum point).trans_eq
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro l hl
  rw [←Finset.sum_filter]
  congr 1
  ext q
  exact Finset.mem_filter.trans ⟨And.right,fun h => ⟨Finset.mem_biUnion.mpr ⟨l,hl,h⟩,h⟩⟩

end
end ImbalancedChen.Part3.OriginalSwitchedActiveLevels20261113
