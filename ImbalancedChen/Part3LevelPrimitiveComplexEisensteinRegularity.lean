import ImbalancedChen.Part3LevelPrimitiveComplexEisenstein
import ImbalancedChen.Part3PrimitiveEisensteinHorizontalContinuity

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_CREDIT.

Parameter holomorphy and horizontal continuity/periodicity for the actual
level-N complex primitive series AND its genuine GammaInfinity\Gamma0
coset realization. The primitive index retains gcd(c,d)=1 and N|c.

The actual subseries inherits the summable lattice and neighboring-exponent
derivative bounds, not an assumed convergence or regularity property. The
period matrix belongs to actual Gamma0(N) at every N. Only Re(s)>1 is claimed.
-/

namespace ImbalancedChen.Part3.LevelPrimitiveComplexEisensteinRegularity

noncomputable section

open Set Filter Topology Complex Metric UpperHalfPlane EisensteinSeries
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinHorizontalContinuity
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein

def levelComplexSeedDerivative (N : ℕ) (z : ℍ) (v : LevelPrimitiveRow N) (s : ℂ) : ℂ :=
  complexSeedDerivative z (toPrimitiveRow N v) s

theorem levelComplexSeed_hasDerivAt (N : ℕ) (z : ℍ) (v : LevelPrimitiveRow N) (s : ℂ) :
    HasDerivAt (levelComplexSeed N z v) (levelComplexSeedDerivative N z v s) s :=
  complexSeed_hasDerivAt z (toPrimitiveRow N v) s

/-- Actual level subseries uniformly converges on every bounded real-part slab. -/
theorem levelComplexSeed_tendstoUniformlyOn (N : ℕ) (z : ℍ)
    (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    TendstoUniformlyOn
      (fun F : Finset (LevelPrimitiveRow N) => fun s : ℂ => ∑ v ∈ F, levelComplexSeed N z v s)
      (fun s : ℂ => ∑' v : LevelPrimitiveRow N, levelComplexSeed N z v s)
      atTop {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  apply tendstoUniformlyOn_tsum
    (((seed_summable a ha z).subtype _).add ((seed_summable b hb z).subtype _))
  intro v s hs
  exact norm_complexSeed_le_endpoint_seeds z (toPrimitiveRow N v) a b s hs.1 hs.2

theorem levelDerivativeMajorant_summable (N : ℕ) (z : ℍ) (a b epsilon : ℝ)
    (ha : 1 < a - epsilon) (hb : 1 < b + epsilon) :
    Summable (fun v : LevelPrimitiveRow N =>
      (seed (a - epsilon) z v.1 + seed (b + epsilon) z v.1) / epsilon) :=
  (((seed_summable (a - epsilon) ha z).subtype _).add
    ((seed_summable (b + epsilon) hb z).subtype _)).div_const epsilon

theorem levelComplexSeedDerivative_norm_le (N : ℕ) (z : ℍ)
    (a b epsilon : ℝ) (hepsilon : 0 < epsilon) (v : LevelPrimitiveRow N)
    (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖levelComplexSeedDerivative N z v s‖ ≤
      (seed (a - epsilon) z v.1 + seed (b + epsilon) z v.1) / epsilon :=
  complexSeedDerivative_norm_le z a b epsilon hepsilon (toPrimitiveRow N v) s ha hb

theorem levelComplexSeedDerivative_tendstoUniformlyOn
    (N : ℕ) (z : ℍ) (a b epsilon : ℝ) (hepsilon : 0 < epsilon)
    (ha : 1 < a - epsilon) (hb : 1 < b + epsilon) :
    TendstoUniformlyOn
      (fun F : Finset (LevelPrimitiveRow N) => fun s : ℂ =>
        ∑ v ∈ F, levelComplexSeedDerivative N z v s)
      (fun s : ℂ => ∑' v : LevelPrimitiveRow N, levelComplexSeedDerivative N z v s)
      atTop {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  apply tendstoUniformlyOn_tsum (levelDerivativeMajorant_summable N z a b epsilon ha hb)
  intro v s hs
  exact levelComplexSeedDerivative_norm_le N z a b epsilon hepsilon v s hs.1 hs.2

/-- Differentiation of the true level-N primitive series, supplied by a
proved uniform summable derivative bound on a complex ball around s. -/
theorem level_primitive_tsum_hasDerivAt_parameter (N : ℕ) (z : ℍ)
    (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (fun w : ℂ => ∑' v : LevelPrimitiveRow N, levelComplexSeed N z v w)
      (∑' v : LevelPrimitiveRow N, levelComplexSeedDerivative N z v s) s := by
  let r : ℝ := (s.re - 1) / 4
  let a : ℝ := s.re - r
  let b : ℝ := s.re + r
  have hr : 0 < r := by dsimp [r]; linarith
  have ha : 1 < a - r := by dsimp [a, r]; linarith
  have hb : 1 < b + r := by dsimp [b, r]; linarith
  let u : LevelPrimitiveRow N → ℝ := fun v =>
    (seed (a - r) z v.1 + seed (b + r) z v.1) / r
  have hu : Summable u := levelDerivativeMajorant_summable N z a b r ha hb
  have hsball : s ∈ ball s r := mem_ball_self hr
  refine hasDerivAt_tsum_of_isPreconnected (u := u) (t := ball s r)
    hu isOpen_ball (convex_ball s r).isPreconnected
    (fun v w _hw => levelComplexSeed_hasDerivAt N z v w) ?_
    hsball (levelComplexSeed_summable N z s hs) hsball
  intro v w hw
  have hnorm : ‖w - s‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
  have hre0 : |w.re - s.re| ≤ ‖w - s‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - s)
  obtain ⟨hl, hu⟩ := abs_le.mp (hre0.trans hnorm.le)
  exact levelComplexSeedDerivative_norm_le N z a b r hr v w
    (by dsimp [a]; linarith) (by dsimp [b]; linarith)

theorem levelPrimitiveComplexEisenstein_hasDerivAt (N : ℕ) (z : ℍ)
    (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (fun w : ℂ => levelPrimitiveComplexEisenstein N w z)
      ((1 / 2 : ℂ) * ∑' v : LevelPrimitiveRow N, levelComplexSeedDerivative N z v s) s :=
  (level_primitive_tsum_hasDerivAt_parameter N z s hs).const_mul (1 / 2 : ℂ)

theorem levelPrimitiveComplexEisenstein_analyticOnNhd (N : ℕ) (z : ℍ) :
    AnalyticOnNhd ℂ (fun s : ℂ => levelPrimitiveComplexEisenstein N s z) {s : ℂ | 1 < s.re} := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => levelPrimitiveComplexEisenstein N s z)
      {s : ℂ | 1 < s.re} := by
    intro s hs
    exact (levelPrimitiveComplexEisenstein_hasDerivAt N z s hs).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re)

/-- Holomorphy is also supplied for the genuine parabolic COSSET sum,
using its proved half-pair identity on the actual open half plane. -/
theorem actualComplexParabolicEisenstein_analyticOnNhd (N : ℕ) (z : ℍ) :
    AnalyticOnNhd ℂ (fun s : ℂ => actualComplexParabolicEisenstein N s z) {s : ℂ | 1 < s.re} := by
  apply AnalyticOnNhd.congr (isOpen_Ioi.preimage Complex.continuous_re)
    (levelPrimitiveComplexEisenstein_analyticOnNhd N z)
  intro s hs
  exact (actualComplexParabolicEisenstein_eq_half_pair_sum N s hs z).symm

/-- Explicit summable compact horizontal majorant for the true level rows. -/
def levelHorizontalMajorant (N : ℕ) (s : ℂ) (y : ℝ) (hy : 0 < y) (A : ℝ)
    (v : LevelPrimitiveRow N) : ℝ :=
  (y ^ s.re * EisensteinSeries.r ⟨⟨A, y⟩, hy⟩ ^ (-(2 * s.re))) *
    ‖v.1‖ ^ (-(2 * s.re))

theorem levelHorizontalMajorant_summable (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (A : ℝ) : Summable (levelHorizontalMajorant N s y hy A) := by
  exact ((EisensteinSeries.summable_one_div_norm_rpow
    (by linarith : 2 < 2 * s.re)).subtype _).mul_left
      (y ^ s.re * EisensteinSeries.r ⟨⟨A, y⟩, hy⟩ ^ (-(2 * s.re)))

theorem levelComplexSeed_horizontal_strip_bound (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (A : ℝ) (v : LevelPrimitiveRow N) {x : ℝ} (hx : |x| ≤ A) :
    ‖levelComplexSeed N (horizontalPoint y hy x) v s‖ ≤ levelHorizontalMajorant N s y hy A v :=
  complexSeed_horizontal_strip_bound s hs y hy A (toPrimitiveRow N v) hx

theorem levelComplexSeed_horizontal_tendstoUniformlyOn
    (N : ℕ) (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) (A : ℝ) :
    TendstoUniformlyOn
      (fun F : Finset (LevelPrimitiveRow N) => fun x : ℝ =>
        ∑ v ∈ F, levelComplexSeed N (horizontalPoint y hy x) v s)
      (fun x : ℝ => ∑' v : LevelPrimitiveRow N, levelComplexSeed N (horizontalPoint y hy x) v s)
      atTop (Icc (-A) A) := by
  apply tendstoUniformlyOn_tsum (levelHorizontalMajorant_summable N s hs y hy A)
  intro v x hx
  exact levelComplexSeed_horizontal_strip_bound N s hs y hy A v (abs_le.mpr hx)

theorem level_primitive_tsum_horizontal_continuousOn
    (N : ℕ) (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) (A : ℝ) :
    ContinuousOn (fun x : ℝ => ∑' v : LevelPrimitiveRow N,
      levelComplexSeed N (horizontalPoint y hy x) v s) (Icc (-A) A) := by
  apply (levelComplexSeed_horizontal_tendstoUniformlyOn N s hs y hy A).continuousOn
  apply Frequently.of_forall
  intro F
  exact continuousOn_finsetSum F (fun v _ =>
    (complexSeed_horizontal_continuous y hy (toPrimitiveRow N v) s).continuousOn)

theorem levelPrimitiveComplexEisenstein_horizontal_continuous
    (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    Continuous (fun x : ℝ => levelPrimitiveComplexEisenstein N s (horizontalPoint y hy x)) := by
  have hsum : Continuous (fun x : ℝ => ∑' v : LevelPrimitiveRow N,
      levelComplexSeed N (horizontalPoint y hy x) v s) := by
    rw [continuous_iff_continuousAt]
    intro x
    let A : ℝ := |x| + 1
    have hleft : -A < x := by dsimp [A]; linarith [neg_abs_le x]
    have hright : x < A := by dsimp [A]; linarith [le_abs_self x]
    exact (level_primitive_tsum_horizontal_continuousOn N s hs y hy A).continuousAt
      (Icc_mem_nhds hleft hright)
  exact continuous_const.mul hsum

/-- This period matrix is an actual member of Gamma0(N), at every level. -/
def translationGamma0 (N : ℕ) : CongruenceSubgroup.Gamma0 N :=
  ⟨ModularGroup.T, by simpa only [zpow_one] using translation_mem_gamma0 N 1⟩

theorem levelPrimitiveComplexEisenstein_horizontal_periodic
    (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    Function.Periodic (fun x : ℝ => levelPrimitiveComplexEisenstein N s (horizontalPoint y hy x)) 1 := by
  intro x
  rw [horizontalPoint_add_one]
  exact levelPrimitiveComplexEisenstein_Gamma0_invariant N s hs (translationGamma0 N)
    (horizontalPoint y hy x)

theorem actualComplexParabolicEisenstein_horizontal_continuous
    (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    Continuous (fun x : ℝ => actualComplexParabolicEisenstein N s (horizontalPoint y hy x)) := by
  have heq : (fun x : ℝ => actualComplexParabolicEisenstein N s (horizontalPoint y hy x)) =
      (fun x : ℝ => levelPrimitiveComplexEisenstein N s (horizontalPoint y hy x)) :=
    funext (fun x => actualComplexParabolicEisenstein_eq_half_pair_sum N s hs (horizontalPoint y hy x))
  rw [heq]
  exact levelPrimitiveComplexEisenstein_horizontal_continuous N y hy s hs

theorem actualComplexParabolicEisenstein_horizontal_periodic
    (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    Function.Periodic (fun x : ℝ => actualComplexParabolicEisenstein N s (horizontalPoint y hy x)) 1 := by
  intro x
  rw [actualComplexParabolicEisenstein_eq_half_pair_sum N s hs,
    actualComplexParabolicEisenstein_eq_half_pair_sum N s hs]
  exact levelPrimitiveComplexEisenstein_horizontal_periodic N y hy s hs x

theorem actualComplexParabolicEisenstein_horizontal_endpoints
    (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    actualComplexParabolicEisenstein N s (horizontalPoint y hy 0) =
      actualComplexParabolicEisenstein N s (horizontalPoint y hy 1) := by
  simpa only [zero_add] using (actualComplexParabolicEisenstein_horizontal_periodic N y hy s hs 0).symm

end
end ImbalancedChen.Part3.LevelPrimitiveComplexEisensteinRegularity
