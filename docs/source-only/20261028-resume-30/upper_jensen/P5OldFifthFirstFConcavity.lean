import ImbalancedChen.P5OldFifthPointwiseQ
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The missing local calculus in the original fifth-prefix child bound.
No concavity, monotonicity, integral floor, or final sieve bound is assumed.
The imported pointwise module is a separately pinned source-only dependency.
Install this file as ImbalancedChen/P5OldFifthFirstFConcavity.lean after that
exact dependency has been installed by the compilation owner.
-/

namespace ImbalancedChen.P5OldFifthFirstFConcavity
noncomputable section
open Set
open P5OldFifthPointwiseQ
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity
open scoped BigOperators

/-- The literal derivative of the first-interval Rosser profile. -/
def firstSlope (s : ℝ) : ℝ :=
  (s / (s - 1) - Real.log (s - 1)) / s ^ 2

/-- The second derivative, with a positive denominator on the entire
closed interval [2,4]. -/
def firstCurvature (s : ℝ) : ℝ :=
  (2 * (s - 1) ^ 2 * Real.log (s - 1) -
    2 * s * (s - 1) - s ^ 2) / (s ^ 3 * (s - 1) ^ 2)

theorem hasDerivAt_firstF {s : ℝ} (hs : 1 < s) :
    HasDerivAt firstF (firstSlope s) s := by
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s - 1 ≠ 0 := by linarith
  have h := (((hasDerivAt_id s).sub_const 1).log hs1).div
    (hasDerivAt_id s) hs0
  convert h using 1
  · rfl
  · dsimp [firstSlope]
    field_simp [hs0, hs1]
    <;> ring

theorem hasDerivAt_firstSlope {s : ℝ} (hs : 1 < s) :
    HasDerivAt firstSlope (firstCurvature s) s := by
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s - 1 ≠ 0 := by linarith
  have hquot := (hasDerivAt_id s).div
    ((hasDerivAt_id s).sub_const 1) hs1
  have hlog := ((hasDerivAt_id s).sub_const 1).log hs1
  have h := (hquot.sub hlog).div (hasDerivAt_pow 2 s)
    (pow_ne_zero 2 hs0)
  convert h using 1
  · rfl
  · dsimp [firstCurvature]
    field_simp [hs0, hs1]
    <;> ring

theorem firstCurvature_nonpos {s : ℝ}
    (hs2 : 2 ≤ s) (hs4 : s ≤ 4) : firstCurvature s ≤ 0 := by
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  have hlog : Real.log (s - 1) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos hs1
    linarith
  have hlogMul := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 2 * (s - 1) ^ 2 by positivity)
  have hinterval : (s - 2) * (s - 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hnum : 2 * (s - 1) ^ 2 * Real.log (s - 1) -
      2 * s * (s - 1) - s ^ 2 ≤ -4 := by
    nlinarith [hinterval, hlogMul]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith :
      2 * (s - 1) ^ 2 * Real.log (s - 1) -
        2 * s * (s - 1) - s ^ 2 ≤ 0)
    (by positivity : 0 ≤ s ^ 3 * (s - 1) ^ 2)

/-- This supplies the previously unproved `hconc` input of the actual
strict-gate pointwise Q comparison. Endpoints 2 and 4 are retained. -/
theorem firstF_concaveOn : ConcaveOn ℝ (Icc (2 : ℝ) 4) firstF := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 2 4)
    (f' := firstSlope) (f'' := firstCurvature)
  · intro s hs
    exact (hasDerivAt_firstF (by linarith [hs.1])).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Icc (2 : ℝ) 4 := interior_subset hs
    exact (hasDerivAt_firstF (by linarith [hs'.1])).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Icc (2 : ℝ) 4 := interior_subset hs
    exact (hasDerivAt_firstSlope (by linarith [hs'.1])).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Icc (2 : ℝ) 4 := interior_subset hs
    exact firstCurvature_nonpos hs'.1 hs'.2

/-- The elementary logarithm majorant whose derivative is a square.
It is sharp at 1 and sufficient to fix the sign of firstSlope at 4. -/
def logarithmMajorantGap (x : ℝ) : ℝ :=
  (x - 1 / x) / 2 - Real.log x

theorem hasDerivAt_logarithmMajorantGap {x : ℝ} (hx : 0 < x) :
    HasDerivAt logarithmMajorantGap ((x - 1) ^ 2 / (2 * x ^ 2)) x := by
  have hinv := (hasDerivAt_const x (1 : ℝ)).div
    (hasDerivAt_id x) hx.ne'
  have h := (((hasDerivAt_id x).sub hinv).div_const 2).sub
    (Real.hasDerivAt_log hx.ne')
  convert h using 1
  · rfl
  · field_simp [hx.ne']
    <;> ring

theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - 1 / x) / 2 := by
  have hm : MonotoneOn logarithmMajorantGap (Ici (1 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (f' := fun y : ℝ => (y - 1) ^ 2 / (2 * y ^ 2))
    · intro y hy
      have hy1 : 1 ≤ y := hy
      exact (hasDerivAt_logarithmMajorantGap
        (by linarith)).continuousAt.continuousWithinAt
    · intro y hy
      have hy' : y ∈ Ici (1 : ℝ) := interior_subset hy
      have hy1 : 1 ≤ y := hy'
      exact (hasDerivAt_logarithmMajorantGap
        (by linarith)).hasDerivWithinAt
    · intro y _
      positivity
  have h := hm (show (1 : ℝ) ∈ Ici (1 : ℝ) from le_rfl) hx hx
  have hzero : logarithmMajorantGap 1 = 0 := by
    norm_num [logarithmMajorantGap]
  rw [hzero] at h
  dsimp [logarithmMajorantGap] at h
  linarith

theorem firstSlope_nonneg {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    0 ≤ firstSlope s := by
  have hs1 : 0 < s - 1 := by linarith
  have hlog := log_le_half_sub_inv (show 1 ≤ s - 1 by linarith)
  have hidentity : s / (s - 1) - ((s - 1) - 1 / (s - 1)) / 2 =
      ((s - 1) + 1) * (3 - (s - 1)) / (2 * (s - 1)) := by
    field_simp [hs1.ne']
    <;> ring
  have hcomparison : ((s - 1) - 1 / (s - 1)) / 2 ≤ s / (s - 1) := by
    apply le_of_sub_nonneg
    rw [hidentity]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  exact div_nonneg (sub_nonneg.mpr (hlog.trans hcomparison)) (sq_nonneg s)

theorem firstF_monotoneOn : MonotoneOn firstF (Icc (2 : ℝ) 4) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 2 4)
    (f' := firstSlope)
  · intro s hs
    exact (hasDerivAt_firstF (by linarith [hs.1])).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Icc (2 : ℝ) 4 := interior_subset hs
    exact (hasDerivAt_firstF (by linarith [hs'.1])).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Icc (2 : ℝ) 4 := interior_subset hs
    exact firstSlope_nonneg hs'.1 hs'.2

/-- Convexity is asserted only on the interval licensed by the child
A/B ratio check. In particular this does not extend Q past b-2. -/
theorem Q_convexOn_no_calculus_input {b : ℝ} (hb2 : 2 ≤ b) (hb4 : b ≤ 4) :
    ConvexOn ℝ (Icc (0 : ℝ) (b - 2)) (Q b) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a c ha hc hac
  have hbx : b - x ∈ Icc (2 : ℝ) 4 :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hby : b - y ∈ Icc (2 : ℝ) 4 :=
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h := firstF_concaveOn.2 hbx hby ha hc hac
  simp only [smul_eq_mul] at h ⊢
  have harg : a * (b - x) + c * (b - y) = b - (a * x + c * y) := by
    calc
      _ = (a + c) * b - (a * x + c * y) := by ring
      _ = _ := by rw [hac]; ring
  have hconstant : a * firstF b + c * firstF b = firstF b := by
    rw [← add_mul, hac, one_mul]
  rw [harg] at h
  dsimp [Q]
  nlinarith [h, hconstant]

theorem Q_monotoneOn_no_calculus_input {b : ℝ} (hb2 : 2 ≤ b) (hb4 : b ≤ 4) :
    MonotoneOn (Q b) (Icc (0 : ℝ) (b - 2)) := by
  intro x hx y hy hxy
  have hbx : b - x ∈ Icc (2 : ℝ) 4 :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hby : b - y ∈ Icc (2 : ℝ) 4 :=
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have h := firstF_monotoneOn hby hbx (by linarith)
  exact sub_le_sub_left h (firstF b)

theorem Q_nonneg {b u : ℝ} (hb2 : 2 ≤ b) (hb4 : b ≤ 4)
    (hu : u ∈ Icc (0 : ℝ) (b - 2)) : 0 ≤ Q b u := by
  have hzero : Q b 0 = 0 := by simp [Q]
  have h := Q_monotoneOn_no_calculus_input hb2 hb4
    (show (0 : ℝ) ∈ Icc (0 : ℝ) (b - 2) from ⟨le_rfl, by linarith⟩)
    hu hu.1
  simpa [hzero] using h

/-- The old frozen-parent pointwise theorem, now with the local
concavity obligation discharged rather than passed to the caller. -/
theorem frozenUpperPositiveKernel_ge_Q_no_calculus_input
    (picks : ParentPicks) (raw : FifthWireRow)
    (t : Point) (ht : ∀ i : Fin 5, 0 < t i)
    (b : ℝ) (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : residual (rawCandidate 0 raw t) t ≤ b) :
    (4 / t 4) * (∏ i : Fin 5, 1 / t i) *
        Q b (max 0 (frozenGap picks raw t) / t 4) ≤
      frozenUpperPositiveKernel picks raw t := by
  exact frozenUpperPositiveKernel_ge_Q firstF_concaveOn
    picks raw t ht b hb2 hb4 hnew

end
end ImbalancedChen.P5OldFifthFirstFConcavity
