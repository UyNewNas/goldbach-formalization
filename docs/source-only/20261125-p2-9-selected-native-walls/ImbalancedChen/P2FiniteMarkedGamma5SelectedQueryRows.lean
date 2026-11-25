import ImbalancedChen.P2FiniteMarkedGamma5RealSelectedPrefix
import ImbalancedChen.Part5OriginalH430FullMemberStrips

namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedQueryRows
noncomputable section
open Set
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerFinitePhysicalGraph Part5UpperTables
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open Part5OriginalH430NativeQueryPaths Part5OriginalH430ActiveKnotPullbacks
open Part5OriginalH430MemberGateRows Part5OriginalH430FullMemberStrips
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430PrimeChildAdmission
open P2FiniteMarkedGamma5StrictPhysicalChildren
open P2EnhancedLowerPrimeChildCarriers (SingleRule)

/-- The slope is fixed by the preceding shape. The denominator and residual
are physical exponents. Multiplying by the positive denominator preserves
closed knots and strict tests. -/
def represents (p : PhysicalNode) (gain den : ℝ) : Prop :=
  0 < den ∧ den*p.argument = gain*residual p

theorem frozen_root_chart (n : ℕ) (k : Root) (tau x : ℝ)
    (hL : 0 < residual (frozenRoot n k tau x).physical) (ha : 0 < a) :
    let p := (frozenRoot n k tau x).physical
    (residual p ≤ 2*a ∧ represents p 2 (residual p)) ∨
    (2*a < residual p ∧ represents p 1 a) := by
  dsimp only
  let p := (frozenRoot n k tau x).physical
  have arg : p.argument = max 2 (residual p/a) := by
    change _ = max 2 (residual (frozenRoot n k tau x).physical/a)
    rw [frozenRoot_residual]
    rfl
  change (residual p ≤ 2*a ∧ represents p 2 (residual p)) ∨ _
  by_cases h : residual p ≤ 2*a
  · refine Or.inl ⟨h,hL,?_⟩
    rw [arg,max_eq_left ((div_le_iff₀ ha).mpr h),mul_comm]
  · have h' := lt_of_not_ge h
    refine Or.inr ⟨h',ha,?_⟩
    rw [arg,max_eq_right ((le_div_iff₀ ha).mpr h'.le)]
    field_simp

def activeGain : FeedbackQuery → ℝ
  | .w1 _ j => W1Anchor j
  | .w2Singleton j _ => (originalW2At j).s0
  | .w2Pair j piece => if piece.val < 2 then (originalW2At j).s0 else 1
  | .buchstabUpper _ | .buchstabLower _ => 1

/-- Use the existing exact active knot numerator at zero. Thus neither
a new formula for the interpolated table nor a monotonicity is needed. -/
theorem active_chart (p : PhysicalNode) (z : Point) (q : FeedbackQuery)
    (hL : 0 < residual p) (hx : 0 < z 0) :
    represents (perform p q.shape z) (activeGain q) (knotDenominator p z q) := by
  have hd := knotDenominator_pos hL hx q
  have h := query_sub_knot hL hx q 0
  rw [sub_zero,eq_div_iff hd.ne'] at h
  refine ⟨hd,?_⟩
  rw [mul_comm,h]
  cases q with
  | w2Pair j piece =>
    by_cases hpiece : piece.val < 2 <;>
      simp [activeGain,knotNumerator,hpiece,FeedbackQuery.shape,perform] <;> ring
  | _ => simp [activeGain,knotNumerator,FeedbackQuery.shape,perform] <;> ring

theorem compare_chart (p : PhysicalNode) (c : ℝ) (hL : 0 < residual p) :
    represents (compareAt p c) c (residual p) := by
  exact ⟨hL,mul_comm _ _⟩

theorem atom_row_iff {p : PhysicalNode} {g D : ℝ} (h : represents p g D)
    (b : FloorAtom) (lower : Bool) :
    p.argument ∈ tableAtomSet lower b ↔ ∀ r ∈ atomRows lower b,
      if r.strict then 0 < r.query*g*residual p+r.constant*D
      else 0 ≤ r.query*g*residual p+r.constant*D := by
  rw [← atomRows_iff lower b (residual p)]
  apply forall_congr'
  intro r
  apply forall_congr'
  intro hr
  obtain ⟨hz,_⟩ := atomRows_coefficients hr
  have he : r.value (residual p) p.argument*D =
      r.query*g*residual p+r.constant*D := by
    dsimp [GateRow.value]
    rw [hz]
    linear_combination r.query*h.2
  unfold GateRow.accepts
  rw [← he]
  cases r.strict <;> simp [h.1, mul_pos_iff_of_pos_right, mul_nonneg_iff_of_pos_right]

/-- A moving parent Buchstab comparison originally contains the product
of the new prime coordinate and the moving table query. On this chart
it is a single affine test in the prime coordinate and the denominator. -/
theorem buchstab_parent_iff {p : PhysicalNode} {g D x : ℝ} (h : represents p g D)
    (hL : 0 < residual p) :
    x*p.argument ≤ residual p ↔ g*x ≤ D := by
  have he : x*p.argument*D = (g*x)*residual p := by
    linear_combination x*h.2
  rw [← mul_le_mul_iff_of_pos_right h.1,he,mul_comm (residual p) D,
    mul_le_mul_iff_of_pos_right hL]

theorem buchstab_rows_iff (p : PhysicalNode) (up : Bool) (z : Point) {g D : ℝ}
    (h : represents p g D) (hL : 0 < residual p) (hx : 0 < z 0) :
    oneDomain p (.buchstab up p.argument) z ↔
      (if up then D ≤ g*residual p else 2*D ≤ g*residual p) ∧
      (if up then 3*z 0 ≤ residual p else True) ∧
      g*z 0 ≤ D ∧ residual p ≤ 6*z 0 := by
  have hh (c : ℝ) : c ≤ p.argument ↔ c*D ≤ g*residual p := by
    rw [← h.2,mul_comm D p.argument,mul_le_mul_iff_of_pos_right h.1]
  have hb := buchstab_parent_iff h hL (x := z 0)
  cases up
  · change (2 ≤ p.argument ∧ p.argument-1 ≤ residual p/z 0-1 ∧
        residual p/z 0-1 ≤ 5) ↔ _
    simp only [Bool.false_eq_true,if_false,true_and,hh]
    rw [← hb]
    constructor
    · rintro ⟨hs,hl,hu⟩
      exact ⟨hs,by simpa [mul_comm] using (le_div_iff₀ hx).mp (show p.argument ≤ residual p/z 0 by linarith),
        by linarith [(div_le_iff₀ hx).mp (show residual p/z 0 ≤ 6 by linarith)]⟩
    · rintro ⟨hs,hl,hu⟩
      refine ⟨hs,?_,?_⟩
      · linarith [(le_div_iff₀ hx).mpr (show p.argument*z 0 ≤ residual p by simpa [mul_comm] using hl)]
      · linarith [(div_le_iff₀ hx).mpr hu]
  · change (1 ≤ p.argument ∧ max 2 (p.argument-1) ≤ residual p/z 0-1 ∧
        residual p/z 0-1 ≤ 5) ↔ _
    simp only [if_true,max_le_iff,hh,one_mul]
    rw [← hb]
    constructor
    · rintro ⟨hs,⟨hthree,hl⟩,hu⟩
      refine ⟨hs,?_,?_,?_⟩
      · exact (le_div_iff₀ hx).mp (show 3 ≤ residual p/z 0 by linarith)
      · simpa [mul_comm] using (le_div_iff₀ hx).mp (show p.argument ≤ residual p/z 0 by linarith)
      · exact (div_le_iff₀ hx).mp (show residual p/z 0 ≤ 6 by linarith)
    · rintro ⟨hs,hthree,hl,hu⟩
      refine ⟨hs,⟨?_,?_⟩,?_⟩
      · linarith [(le_div_iff₀ hx).mpr hthree]
      · linarith [(le_div_iff₀ hx).mpr (show p.argument*z 0 ≤ residual p by simpa [mul_comm] using hl)]
      · linarith [(div_le_iff₀ hx).mpr hu]

/-- Clearing the denominator of each original active-owner or terminal
atom row preserves its original strict or weak sense. -/
def cleared (g : ℝ) (r : GateRow) : GateRow :=
  ⟨r.strict,r.query*g,r.constant,0⟩

theorem atom_cleared {p : PhysicalNode} {g D : ℝ} (h : represents p g D)
    (lo : Bool) (b : FloorAtom) :
    p.argument ∈ tableAtomSet lo b ↔
      AllRows ((atomRows lo b).map (cleared g)) (residual p) D := by
  rw [atom_row_iff h]
  simp [AllRows,cleared,GateRow.accepts,GateRow.value]

/-- Different points in the same fixed chart and with different atom
membership yield a proper pulled-back row. The inequality of evaluated
values excludes every constant row, including identically-zero knots. -/
theorem changed_atom_cleared {p q : PhysicalNode} {g D E : ℝ}
    (hp : represents p g D) (hq : represents q g E)
    (lo : Bool) (b : FloorAtom)
    (h : ¬ (p.argument ∈ tableAtomSet lo b ↔ q.argument ∈ tableAtomSet lo b)) :
    ∃ r ∈ (atomRows lo b).map (cleared g),
      r.value (residual p) D ≠ r.value (residual q) E ∧
      |r.value (residual p) D| ≤
        |r.level|*|residual p-residual q| + |r.query|*|D-E| := by
  classical
  rw [atom_cleared hp,atom_cleared hq] at h
  by_contra hn
  apply h
  apply forall_congr'
  intro r
  apply forall_congr'
  intro hr
  by_contra hc
  exact hn ⟨r,hr,changed_row_strip r hc⟩

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedQueryRows
