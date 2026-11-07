import ImbalancedChen.P4BSmoothStepDerivativeBudget
import ImbalancedChen.P4BSmoothProfileFirstDerivativeBudget
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Calculus.MeanValue

/-!
# All fixed orders along real lines in the actual physical smooth profile

SOURCE ONLY / YELLOW / UNCOMPILED (2026-10-25).

The project imports are future normal imports of companion drafts. The
physical wall dictionary and its operator-norm bound are reused from the
first-derivative companion. No first-order Frechet proof is duplicated.

At fixed k and b, one constant controls all positive widths, N >= 2,
cutoff offsets T, base points and directions. The bound displays exactly
width^-k and the actual physical log N wall scale. The proof uses actual
scalar derivative bounds, exact affine composition and the genuine
binomial Leibniz identity. No higher derivative budget is a premise.
This is quantitative smooth-profile algebra, not a P3/PP estimate or
licensing conclusion.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped BigOperators ContDiff

/-- A finite derivative envelope for the genuine scalar step, with the
constant chosen before width. Each j-th order retains its exact width^-j. -/
theorem exists_smoothGateUpperStep_finite_derivative_budget
    (k : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : ℕ, j ≤ k → ∀ width : ℝ, 0 < width → ∀ y : ℝ,
      |iteratedDeriv j (smoothGateUpperStep width) y| ≤ B / width ^ j := by
  induction k with
  | zero =>
    refine ⟨1, le_rfl, ?_⟩
    intro j hj width hwidth y
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simp only [iteratedDeriv_zero]
    rw [abs_of_nonneg (smoothGateUpperStep_nonneg width y)]
    simpa only [pow_zero, div_one] using smoothGateUpperStep_le_one width y
  | succ k ih =>
    obtain ⟨B, hB, hbound⟩ := ih
    obtain ⟨C, _hC, htop⟩ := exists_smoothGateUpperStep_derivative_budget (k + 1)
    refine ⟨max B C, hB.trans (le_max_left _ _), ?_⟩
    intro j hj width hwidth y
    rcases lt_or_eq_of_le hj with hlt | heq
    · exact (hbound j (by omega) width hwidth y).trans
        (div_le_div_of_nonneg_right (le_max_left _ _)
          (pow_nonneg hwidth.le j))
    · subst j
      exact (htop width hwidth y).trans
        (div_le_div_of_nonneg_right (le_max_right _ _)
          (pow_nonneg hwidth.le (k + 1)))

/-- Exact iterated chain rule for one real affine argument. -/
theorem iteratedDeriv_comp_real_affine
    (k : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (offset slope x : ℝ) :
    iteratedDeriv k (fun t => f (offset + slope * t)) x =
      slope ^ k * iteratedDeriv k f (offset + slope * x) := by
  have hg : ContDiff ℝ k (fun y => f (offset + y)) :=
    (hf.of_le (by simp)).comp (contDiff_const.add contDiff_id)
  have hscale := congrFun (iteratedDeriv_comp_const_mul hg slope) x
  have hshift := congrFun (iteratedDeriv_comp_const_add k f offset) (slope * x)
  exact hscale.trans (congrArg (fun z : ℝ => slope ^ k * z) hshift)

/-- Binomial Leibniz payment at one point, with a common nonnegative
derivative scale R. It also covers R=0 and k=0 without division. -/
theorem abs_iteratedDeriv_two_mul_le
    (k : ℕ) (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x R Cf Cg : ℝ) (hR : 0 ≤ R) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hleft : ∀ j : ℕ, j ≤ k → |iteratedDeriv j f x| ≤ Cf * R ^ j)
    (hright : ∀ j : ℕ, j ≤ k → |iteratedDeriv j g x| ≤ Cg * R ^ j) :
    |iteratedDeriv k (fun t => f t * g t) x| ≤ Cf * Cg * (2 * R) ^ k := by
  have hfK : ContDiffAt ℝ k f x := (hf.of_le (by simp)).contDiffAt
  have hgK : ContDiffAt ℝ k g x := (hg.of_le (by simp)).contDiffAt
  have hsum : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  change |iteratedDeriv k (f * g) x| ≤ Cf * Cg * (2 * R) ^ k
  rw [iteratedDeriv_mul hfK hgK]
  calc
    |∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * iteratedDeriv j f x * iteratedDeriv (k - j) g x| ≤
        ∑ j ∈ Finset.range (k + 1),
          |(k.choose j : ℝ) * iteratedDeriv j f x * iteratedDeriv (k - j) g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (Cf * Cg * R ^ k) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hproduct : |iteratedDeriv j f x| * |iteratedDeriv (k - j) g x| ≤
          (Cf * R ^ j) * (Cg * R ^ (k - j)) :=
        mul_le_mul (hleft j hjk) (hright (k - j) (Nat.sub_le k j))
          (abs_nonneg _) (mul_nonneg hCf (pow_nonneg hR j))
      calc
        |(k.choose j : ℝ) * iteratedDeriv j f x * iteratedDeriv (k - j) g x| =
            (k.choose j : ℝ) *
              (|iteratedDeriv j f x| * |iteratedDeriv (k - j) g x|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (k.choose j))]
          ring
        _ ≤ (k.choose j : ℝ) * ((Cf * R ^ j) * (Cg * R ^ (k - j))) :=
          mul_le_mul_of_nonneg_left hproduct (Nat.cast_nonneg _)
        _ = (k.choose j : ℝ) * (Cf * Cg * (R ^ j * R ^ (k - j))) := by ring
        _ = (k.choose j : ℝ) * (Cf * Cg * R ^ k) := by
          rw [← pow_add, Nat.add_sub_of_le hjk]
    _ = 2 ^ k * (Cf * Cg * R ^ k) := by rw [← Finset.sum_mul, hsum]
    _ = Cf * Cg * (2 * R) ^ k := by rw [mul_pow]; ring

/-- Four genuine smooth factors retain exactly k powers of their common
directional scale, rather than a larger power that would fail at h=0. -/
theorem abs_iteratedDeriv_four_gate_product_le
    (k : ℕ) (f : Fin 4 → ℝ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hfactor : ∀ i : Fin 4, ∀ j : ℕ, j ≤ k →
      |iteratedDeriv j (f i) x| ≤ B * R ^ j) :
    |iteratedDeriv k (fun t => ∏ i : Fin 4, f i t) x| ≤ B ^ 4 * (4 * R) ^ k := by
  let g0 : ℝ → ℝ := fun t => f 0 t * f 1 t
  let g1 : ℝ → ℝ := fun t => f 2 t * f 3 t
  have hg0 : ContDiff ℝ ∞ g0 := (hf 0).mul (hf 1)
  have hg1 : ContDiff ℝ ∞ g1 := (hf 2).mul (hf 3)
  have hpair0 (j : ℕ) (hj : j ≤ k) :
      |iteratedDeriv j g0 x| ≤ (B * B) * (2 * R) ^ j :=
    abs_iteratedDeriv_two_mul_le j (f 0) (f 1) (hf 0) (hf 1)
      x R B B hR hB hB
      (fun i hi => hfactor 0 i (hi.trans hj))
      (fun i hi => hfactor 1 i (hi.trans hj))
  have hpair1 (j : ℕ) (hj : j ≤ k) :
      |iteratedDeriv j g1 x| ≤ (B * B) * (2 * R) ^ j :=
    abs_iteratedDeriv_two_mul_le j (f 2) (f 3) (hf 2) (hf 3)
      x R B B hR hB hB
      (fun i hi => hfactor 2 i (hi.trans hj))
      (fun i hi => hfactor 3 i (hi.trans hj))
  have hprod : (fun t => ∏ i : Fin 4, f i t) = fun t => g0 t * g1 t := by
    funext t
    rw [Fin.prod_univ_four]
    dsimp [g0, g1]
    ring
  rw [hprod]
  have hfinal := abs_iteratedDeriv_two_mul_le k g0 g1 hg0 hg1
    x (2 * R) (B * B) (B * B) (mul_nonneg (by norm_num) hR)
    (mul_nonneg hB hB) (mul_nonneg hB hB) hpair0 hpair1
  simpa only [show (B * B) * (B * B) = B ^ 4 by ring,
    show (2 : ℝ) * (2 * R) = 4 * R by ring] using hfinal

/-- The actual profile restricted to an arbitrary real affine line. -/
def smoothPhysicalProfileLine (b : ℝ) (N : ℕ) (T width : ℝ)
    (x h : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  smoothPhysicalProfile b N T width (x + t • h)

/-- Exact four-affine-wall line dictionary, using the companion's actual
row maps. In particular T and x affect only the offsets. -/
theorem smoothPhysicalProfileLine_eq_affine_gate_product
    (b : ℝ) (N : ℕ) (T width : ℝ) (x h : Fin 2 → ℝ) :
    smoothPhysicalProfileLine b N T width x h = fun t =>
      ∏ i : Fin 4, smoothGateUpperStep width
        (smoothPhysicalProfileMargin b N T x i + smoothPhysicalWallRow b N i h * t) := by
  funext t
  unfold smoothPhysicalProfileLine smoothPhysicalProfile
  apply Finset.prod_congr rfl
  intro i _hi
  rw [smoothPhysicalProfileMargin_line b N T x h t i]
  rw [mul_comm t (smoothPhysicalWallRow b N i h)]

/-- The full genuine directional derivative budget. Constants are chosen
after k,b and before width,N,T,x,h. Offsets require no range restriction.
Exactly k powers of inverse width and norm h remain, including k=0. -/
theorem exists_smoothPhysicalProfile_directional_derivative_budget
    (k : ℕ) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ width : ℝ, 0 < width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ,
      ∀ x h : Fin 2 → ℝ,
        |iteratedDeriv k (smoothPhysicalProfileLine b N T width x h) 0| ≤
          (C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k * ‖h‖ ^ k := by
  obtain ⟨B, hB, hscalar⟩ :=
    exists_smoothGateUpperStep_finite_derivative_budget k
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hcb : 0 ≤ 2 + |b| := by linarith [abs_nonneg b]
  let C : ℝ := B ^ 4 * (4 * (2 + |b|)) ^ k
  refine ⟨C, mul_nonneg (pow_nonneg hB0 4)
    (pow_nonneg (mul_nonneg (by norm_num) hcb) k), ?_⟩
  intro width hwidth N hN T x h
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ N by omega)
  let R : ℝ := (((2 + |b|) * (1 + Real.log (N : ℝ))) * ‖h‖) / width
  have hR : 0 ≤ R :=
    div_nonneg (mul_nonneg (mul_nonneg hcb (by linarith)) (norm_nonneg h)) hwidth.le
  let f : Fin 4 → ℝ → ℝ := fun i t => smoothGateUpperStep width
    (smoothPhysicalProfileMargin b N T x i + smoothPhysicalWallRow b N i h * t)
  have hstep : ContDiff ℝ ∞ (smoothGateUpperStep width) :=
    contDiff_smoothGateUpperStep width
  have hf (i : Fin 4) : ContDiff ℝ ∞ (f i) :=
    hstep.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hfactor (i : Fin 4) (j : ℕ) (hj : j ≤ k) :
      |iteratedDeriv j (f i) 0| ≤ B * R ^ j := by
    change |iteratedDeriv j (fun t => smoothGateUpperStep width
      (smoothPhysicalProfileMargin b N T x i + smoothPhysicalWallRow b N i h * t)) 0| ≤ _
    rw [iteratedDeriv_comp_real_affine j (smoothGateUpperStep width) hstep
      (smoothPhysicalProfileMargin b N T x i) (smoothPhysicalWallRow b N i h) 0,
      abs_mul, abs_pow]
    calc
      |smoothPhysicalWallRow b N i h| ^ j *
          |iteratedDeriv j (smoothGateUpperStep width)
            (smoothPhysicalProfileMargin b N T x i + smoothPhysicalWallRow b N i h * 0)| ≤
          |smoothPhysicalWallRow b N i h| ^ j * (B / width ^ j) :=
        mul_le_mul_of_nonneg_left (hscalar j hj width hwidth _)
          (pow_nonneg (abs_nonneg _) j)
      _ ≤ (((2 + |b|) * (1 + Real.log (N : ℝ))) * ‖h‖) ^ j *
            (B / width ^ j) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _)
            (smoothPhysicalWallRow_apply_abs_le b N hN i h) j)
          (div_nonneg hB0 (pow_nonneg hwidth.le j))
      _ = B * R ^ j := by
        dsimp only [R]
        rw [div_pow]
        ring
  rw [smoothPhysicalProfileLine_eq_affine_gate_product]
  have hfour := abs_iteratedDeriv_four_gate_product_le k f hf 0 R B hR hB0 hfactor
  have hscale : B ^ 4 * (4 * R) ^ k =
      (C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k * ‖h‖ ^ k := by
    dsimp [C, R]
    simp only [mul_pow, div_pow]
    ring
  exact hfour.trans_eq hscale

/-- The first derivative bound of the actual four-gate profile yields a
global two-point estimate on its continuous domain. Its constant is chosen
before every physical width, target, cutoff and pair of points. -/
theorem exists_smoothPhysicalProfile_Lipschitz_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ b width : ℝ, 0 < width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ x y : Fin 2 → ℝ,
        |smoothPhysicalProfile b N T width x -
          smoothPhysicalProfile b N T width y| ≤
          ((4 * C1 * (2 + |b|) / width) * (1 + Real.log (N : ℝ))) * ‖x - y‖ := by
  obtain ⟨C1, hC1, hderiv⟩ := exists_smoothPhysicalProfile_first_derivative_budget
  refine ⟨C1, hC1, ?_⟩
  intro b width hwidth N hN T x y
  have hcont : ContDiff ℝ 1 (smoothPhysicalProfile b N T width) :=
    contDiff_smoothPhysicalProfile b N T width
  have h := (convex_univ : Convex ℝ (Set.univ : Set (Fin 2 → ℝ))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _hz => hcont.differentiable_one z)
    (fun z _hz => hderiv b width hwidth N hN T z)
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

end

end ImbalancedChen.P4B
