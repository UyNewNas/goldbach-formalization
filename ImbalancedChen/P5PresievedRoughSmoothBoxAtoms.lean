import ImbalancedChen.P5PresievedRoughGateMeshReserve
import ImbalancedChen.P5ZU1011CompactLogIntervalSmoothing
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Group.Bounded

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Genuine separated smooth atoms at every fixed residual rank. Mesh, width,
rank and all labels precede N. Each atom is compactly supported and has a
proved global full Frechet derivative budget, hence controls every mixed
coordinate jet. Finite inner/outer box sums retain literal arithmetic face
reserves. No norm budget or smooth test is supplied as a premise.
-/
namespace ImbalancedChen.P5Z.PresievedRoughSmoothBoxAtoms
noncomputable section
open Set Classical
open scoped BigOperators
open PresievedRoughGateMeshReserve
open U1011CompactLogIntervalSmoothing

def atom {r : ℕ} (inner : Bool) (δ a b : ℝ) (n : ℕ) (j : Grid r n) (v : Fin r → ℝ) : ℝ :=
  ∏ i : Fin r, weight inner δ (logPrimeMeshLo a b n j i) (logPrimeMeshHi a b n j i) (v i)

def literalAtom {r : ℕ} (a b : ℝ) (n : ℕ) (j : Grid r n) (v : Fin r → ℝ) : ℝ :=
  ∏ i : Fin r, literal (logPrimeMeshLo a b n j i) (logPrimeMeshHi a b n j i) (v i)

def cover {r : ℕ} (inner : Bool) (δ a b : ℝ) {n : ℕ} (J : Finset (Grid r n)) (v : Fin r → ℝ) : ℝ :=
  ∑ j ∈ J, atom inner δ a b n j v

def literalCover {r : ℕ} (a b : ℝ) {n : ℕ} (J : Finset (Grid r n)) (v : Fin r → ℝ) : ℝ :=
  ∑ j ∈ J, literalAtom a b n j v

def faceReserve {r : ℕ} (inner : Bool) (δ a b : ℝ) {n : ℕ}
    (J : Finset (Grid r n)) (v : Fin r → ℝ) : Prop :=
  ∃ j ∈ J, ∃ i : Fin r,
    if inner then innerReserve δ (logPrimeMeshLo a b n j i) (logPrimeMeshHi a b n j i) (v i)
    else outerReserve δ (logPrimeMeshLo a b n j i) (logPrimeMeshHi a b n j i) (v i)

theorem atom_bounds {r : ℕ} (inner : Bool) (δ a b : ℝ) (n : ℕ) (j : Grid r n) (v : Fin r → ℝ) :
    0 ≤ atom inner δ a b n j v ∧ atom inner δ a b n j v ≤ 1 := by
  refine ⟨Finset.prod_nonneg (fun i hi => (bounds inner δ _ _ _).1), ?_⟩
  exact (Finset.prod_le_prod (fun i hi => (bounds inner δ _ _ _).1)
    (fun i hi => (bounds inner δ _ _ _).2)).trans_eq (by simp)

theorem literalAtom_eq_indicator {r n : ℕ} (a b : ℝ) (j : Grid r n) (v : Fin r → ℝ) :
    literalAtom a b n j v = if v ∈ cell a b n j then 1 else 0 := by
  by_cases hv : v ∈ cell a b n j
  · have h := mem_logPrimeMeshCell.mp hv
    simp [literalAtom, literal, h, hv]
  · rw [if_neg hv]
    have hi : ∃ i : Fin r, ¬ (logPrimeMeshLo a b n j i ≤ v i ∧ v i < logPrimeMeshHi a b n j i) := by
      by_contra h
      push_neg at h
      exact hv (mem_logPrimeMeshCell.mpr h)
    obtain ⟨i, hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [literal, hi]

theorem inner_le_literal {r n : ℕ} {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) (j : Grid r n) (v : Fin r → ℝ) :
    atom true δ a b n j v ≤ literalAtom a b n j v :=
  Finset.prod_le_prod (fun i hi => (bounds true δ _ _ _).1)
    (fun i hi => U1011CompactLogIntervalSmoothing.inner_le_literal hδ _ _ _)

theorem literal_le_outer {r n : ℕ} {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) (j : Grid r n) (v : Fin r → ℝ) :
    literalAtom a b n j v ≤ atom false δ a b n j v := by
  apply Finset.prod_le_prod
  · intro i hi
    unfold literal
    split_ifs <;> norm_num
  · intro i hi
    exact U1011CompactLogIntervalSmoothing.literal_le_outer hδ _ _ _

theorem cover_sandwich {r n : ℕ} {δ : ℝ} (hδ : 0 < δ) (a b : ℝ)
    (J : Finset (Grid r n)) (v : Fin r → ℝ) :
    cover true δ a b J v ≤ literalCover a b J v ∧ literalCover a b J v ≤ cover false δ a b J v :=
  ⟨Finset.sum_le_sum (fun j hj => inner_le_literal hδ a b j v),
    Finset.sum_le_sum (fun j hj => literal_le_outer hδ a b j v)⟩

theorem cover_error_face {r n : ℕ} {δ : ℝ} (hδ : 0 < δ) (inner : Bool) (a b : ℝ)
    (J : Finset (Grid r n)) (v : Fin r → ℝ)
    (he : cover inner δ a b J v - literalCover a b J v ≠ 0) : faceReserve inner δ a b J v := by
  by_contra hn
  apply he
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro i hi
  have hnot : ¬ (if inner then innerReserve δ (logPrimeMeshLo a b n j i) (logPrimeMeshHi a b n j i) (v i)
    else outerReserve δ (logPrimeMeshLo a b n j i) (logPrimeMeshHi a b n j i) (v i)) :=
      fun h => hn ⟨j, hj, i, h⟩
  cases inner with
  | false =>
    apply eq_of_sub_eq_zero
    by_contra h
    exact hnot (outer_error_support hδ h)
  | true =>
    apply Eq.symm
    apply eq_of_sub_eq_zero
    by_contra h
    exact hnot (inner_error_support hδ h)

theorem contDiff_atom {r : ℕ} (inner : Bool) (δ a b : ℝ) (n : ℕ) (j : Grid r n) :
    ContDiff ℝ ∞ (atom inner δ a b n j) := by
  unfold atom
  apply contDiff_prod
  intro i hi
  exact (contDiff_weight inner δ _ _).comp (contDiff_apply ℝ ℝ i)

theorem hasCompactSupport_atom {r : ℕ} {δ : ℝ} (hδ : 0 < δ) (inner : Bool)
    (a b : ℝ) (n : ℕ) (j : Grid r n) : HasCompactSupport (atom inner δ a b n j) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ_pi (fun i : Fin r => (isCompact_Icc : IsCompact
      (Icc (logPrimeMeshLo a b n j i - δ) (logPrimeMeshHi a b n j i + δ)))))
  intro v hv
  intro i hi
  have hfac : weight inner δ (logPrimeMeshLo a b n j i) (logPrimeMeshHi a b n j i) (v i) ≠ 0 := by
    intro hz
    exact hv (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  have hcoord : ∀ {x l u : ℝ}, weight inner δ l u x ≠ 0 → x ∈ Icc (l - δ) (u + δ) := by
    intro x l u hx
    have hs : 0 ≤ shift inner δ := by cases inner <;> simp [shift, hδ.le]
    have hl := P4B.smoothGateUpperStep_nonzero_support hδ (mul_ne_zero_iff.mp hx).1
    have hu := P4B.smoothGateUpperStep_nonzero_support hδ (mul_ne_zero_iff.mp hx).2
    constructor <;> linarith
  exact hcoord hfac

/-- Genuine all-direction derivative budget at each fixed atom. The
constant precedes N and every prime tuple; no derivative-bound premise is
present. The operator norm controls all mixed partial applications. -/
theorem exists_atom_derivative_budget {r : ℕ} {δ : ℝ} (hδ : 0 < δ) (inner : Bool)
    (a b : ℝ) (n : ℕ) (j : Grid r n) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin r → ℝ, ‖iteratedFDeriv ℝ k (atom inner δ a b n j) v‖ ≤ C := by
  let f := iteratedFDeriv ℝ k (atom inner δ a b n j)
  have hcont : Continuous f :=
    ((contDiff_atom inner δ a b n j).of_le (by simp : (k : ℕ∞) ≤ ∞)).continuous_iteratedFDeriv'
  have hcompact : HasCompactSupport f := (hasCompactSupport_atom hδ inner a b n j).iteratedFDeriv k
  have hK : IsCompact (tsupport f) := hcompact
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro v
  by_cases hv : v ∈ tsupport f
  · exact (hB v hv).trans (le_max_left _ _)
  · have hz : f v = 0 := by
      by_contra hn
      exact hv (subset_closure hn)
    simpa only [hz, norm_zero] using (le_max_right B 0)

/-- Exact native original-prime substitution: this is a separated weight
in the original slot primes at complete scale N, including rough rank0. -/
theorem native_atom_separated {r : ℕ} (inner : Bool) (δ a b : ℝ) (n N : ℕ)
    (j : Grid r n) (p : Fin r → ℕ) :
    atom inner δ a b n j (actualPrimeTupleLog N p) =
      ∏ i : Fin r, weight inner δ (logPrimeMeshLo a b n j i) (logPrimeMeshHi a b n j i)
        (Real.log (p i : ℝ) / Real.log (N : ℝ)) := rfl

end
end ImbalancedChen.P5Z.PresievedRoughSmoothBoxAtoms
