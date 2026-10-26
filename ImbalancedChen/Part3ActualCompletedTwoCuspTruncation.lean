import ImbalancedChen.Part3ActualHighCuspRadialLifts
import ImbalancedChen.Part3ActualCompletedGamma0SideCancellation
import ImbalancedChen.Part3ActualGamma0MaassDescent
import ImbalancedChen.Part3PrimeTwoCuspCompactCover

/-! Literal two-cusp truncation of the actual completed Eisenstein field.
The finite completed constants retain their regularized central value.
Their positive-height continuity is derived from the actual smooth
constant and finite oldform terms. The actual quotient function is
measurable and equals the exact physical remainder on each strict cusp,
and the original field on the full compact complement, including boundary.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a
open ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.ContinuedFourierSpatialSmooth
open ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeTwoCuspCompactCover20261026b
open ImbalancedChen.Part3.ActualHighCuspRadialLifts20261026b

namespace ImbalancedChen.Part3.ActualCompletedTwoCuspTruncation20261026b

private theorem scaled_constant_continuousOn (s : ℂ) (a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun y : ℝ => completedConstant (a * y) s) (Ioi 0) := by
  have hm : Continuous (fun y : ℝ => ((0 : ℝ), a * y)) := by fun_prop
  exact (completedConstant_contDiffOn_infty s).continuousOn.comp hm.continuousOn
    (fun y hy => mul_pos ha hy)

private theorem finite_constants_continuousOn (T : List (ℕ+ × ℂ)) (s : ℂ)
    (a : ℕ+ → ℝ) (ha : ∀ n, 0 < a n) :
    ContinuousOn (fun y : ℝ => (T.map
      (fun t => t.2 * completedConstant (a t.1 * y) s)).sum) (Ioi 0) := by
  induction T with
  | nil => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) (Ioi 0))
  | cons t T ih =>
      simpa only [List.map_cons, List.sum_cons] using
        ((scaled_constant_continuousOn s (a t.1) (ha t.1)).const_mul t.2).add ih

theorem completedInfinityConstant_continuousOn (N : ℕ) (s : ℂ) :
    ContinuousOn (completedInfinityConstant N s) (Ioi 0) := by
  exact (finite_constants_continuousOn (oldformTerms (canonicalPrimeList N) s) s
    (fun n => (n : ℝ)) (fun n => by exact_mod_cast n.pos)).div_const _

theorem completedReflectedConstant_continuousOn (N : ℕ) (hN : 0 < N) (s : ℂ) :
    ContinuousOn (completedReflectedConstant N s) (Ioi 0) := by
  exact (finite_constants_continuousOn (oldformTerms (canonicalPrimeList N) s) s
    (fun n => (N : ℝ) / (n : ℝ)) (fun n => div_pos (by exact_mod_cast hN)
      (by exact_mod_cast n.pos))).div_const _

/-- Only positive native heights are used. The arbitrary nonpositive
totalization is zero and never enters a cusp value. -/
def positiveProfile (k : ℝ → ℂ) : ℝ → ℂ := (Ioi 0).indicator k

theorem positiveProfile_measurable (k : ℝ → ℂ) (hk : ContinuousOn k (Ioi 0)) :
    Measurable (positiveProfile k) := by
  classical
  exact hk.measurable_piecewise continuousOn_const measurableSet_Ioi

theorem positiveProfile_pos (k : ℝ → ℂ) (y : ℝ) (hy : 0 < y) :
    positiveProfile k y = k y := Set.indicator_of_mem hy k

theorem completedLevelOldform_continuous (N : ℕ) (s : ℂ) :
    Continuous (completedLevelOldform N s) := by
  have hc : Continuous (fun z : UpperHalfPlane => completedComplexField N s z) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (completedComplexField_contDiffAt N s z).continuousAt.comp z
      UpperHalfPlane.continuous_coe.continuousAt
  simpa only [completedComplexField_eq_native] using hc

def quotientCompleted (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs : s ∈ completedRegularDomain N) : Gamma0OrbitSpace N → ℂ :=
  quotientInvariantFunction N (completedLevelOldform N s)
    (completedLevelOldform_Gamma0_invariant N hN s hs)

@[simp] theorem quotientCompleted_projection (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs : s ∈ completedRegularDomain N) (z : UpperHalfPlane) :
    quotientCompleted N hN s hs (orbitProjection N z) = completedLevelOldform N s z := rfl

theorem quotientCompleted_measurable (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs : s ∈ completedRegularDomain N) : Measurable (quotientCompleted N hN s hs) :=
  measurable_from_quotient.mpr (completedLevelOldform_continuous N s).measurable

theorem quotientCompleted_continuous (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs : s ∈ completedRegularDomain N) : Continuous (quotientCompleted N hN s hs) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact completedLevelOldform_continuous N s

def infinityConstantLift (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ) :
    Gamma0OrbitSpace N → ℂ :=
  infinityRadialLift N Y hY (positiveProfile (completedInfinityConstant N s))

def zeroConstantLift (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ) :
    Gamma0OrbitSpace p → ℂ :=
  zeroRadialLift p hp Y hY (positiveProfile (completedReflectedConstant p s))

theorem infinityConstantLift_measurable (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ) :
    Measurable (infinityConstantLift N Y hY s) :=
  infinityRadialLift_measurable N Y hY _
    (positiveProfile_measurable _ (completedInfinityConstant_continuousOn N s))

theorem zeroConstantLift_measurable (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ) :
    Measurable (zeroConstantLift p hp Y hY s) :=
  zeroRadialLift_measurable p hp Y hY _
    (positiveProfile_measurable _ (completedReflectedConstant_continuousOn p hp.pos s))

/-- Actual completed truncation: two literal parabolic constant terms
are subtracted in their disjoint strict high charts. -/
def truncatedCompleted (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) (s : ℂ)
    (hs : s ∈ completedRegularDomain p) : Gamma0OrbitSpace p → ℂ :=
  quotientCompleted p hp.pos s hs - infinityConstantLift p Y hY s -
    zeroConstantLift p hp Y hY s

theorem truncatedCompleted_measurable (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (s : ℂ) (hs : s ∈ completedRegularDomain p) :
    Measurable (truncatedCompleted p hp Y hY s hs) :=
  ((quotientCompleted_measurable p hp.pos s hs).sub
    (infinityConstantLift_measurable p Y hY s)).sub
      (zeroConstantLift_measurable p hp Y hY s)

theorem truncatedCompleted_infinity (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (s : ℂ) (hs : s ∈ completedRegularDomain p) (z : UpperHalfPlane) (hz : Y < z.im) :
    truncatedCompleted p hp Y hY s hs (orbitProjection p z) =
      completedLevelOldform p s z - completedInfinityConstant p s z.im := by
  change quotientCompleted p hp.pos s hs (orbitProjection p z) -
    infinityRadialLift p Y hY _ (orbitProjection p z) -
      zeroRadialLift p hp Y hY _ (orbitProjection p z) = _
  rw [quotientCompleted_projection, infinityRadialLift_high p Y hY _ z hz,
    zeroRadialLift_at_infinity p hp Y hY _ z hz, sub_zero,
    positiveProfile_pos _ _ z.im_pos]

theorem truncatedCompleted_zero (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (s : ℂ) (hs : s ∈ completedRegularDomain p) (z : UpperHalfPlane) (hz : Y < z.im) :
    truncatedCompleted p hp Y hY s hs (orbitProjection p (frickeSL p hp.pos • z)) =
      completedLevelOldform p s (frickeSL p hp.pos • z) -
        completedReflectedConstant p s z.im := by
  change quotientCompleted p hp.pos s hs (orbitProjection p (frickeSL p hp.pos • z)) -
    infinityRadialLift p Y hY _ (orbitProjection p (frickeSL p hp.pos • z)) -
      zeroRadialLift p hp Y hY _ (orbitProjection p (frickeSL p hp.pos • z)) = _
  rw [quotientCompleted_projection, infinityRadialLift_at_zero p hp Y hY _ z hz,
    zeroRadialLift_high p hp Y hY _ z hz, sub_zero, positiveProfile_pos _ _ z.im_pos]

theorem truncatedCompleted_on_core (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (s : ℂ) (hs : s ∈ completedRegularDomain p) (q : Gamma0OrbitSpace p)
    (hq : q ∈ twoCuspTruncation p hp Y) :
    truncatedCompleted p hp Y hY s hs q = quotientCompleted p hp.pos s hs q := by
  have hi : q ∉ infinityHighNeighborhood p Y := fun h => hq (Or.inl h)
  have hz : q ∉ zeroHighNeighborhood p hp Y := fun h => hq (Or.inr h)
  change quotientCompleted p hp.pos s hs q - infinityRadialLift p Y hY _ q -
    zeroRadialLift p hp Y hY _ q = _
  rw [infinityRadialLift_off p Y hY _ q hi, zeroRadialLift_off p hp Y hY _ q hz,
    sub_zero, sub_zero]

end ImbalancedChen.Part3.ActualCompletedTwoCuspTruncation20261026b
