import ImbalancedChen.Part3FiniteOldformHeightRemainders
import ImbalancedChen.Part3ActualPrimeHorizontalGreenFlux
import ImbalancedChen.Part3LevelOldformFrickeIdentity
import ImbalancedChen.Part3PrimeScatteringLocalIdentities

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Both LITERAL physical cusp fields: the existing completedLevelChart and
its actual normalized Fricke pullback. Their constants are the EXISTING
completedInfinityConstant and completedReflectedConstant, not prescribed
coefficients. Actual complementary positive integer oldform indices give
the second chart's finite jet/tail representation. Both subtracted fields
and first-height jets have honest zero means and explicit exponential
bounds. The prime constants and their actual first jets are displayed
using the exact two full-level completed constants, including the center.
No flagged16 functional-equation source or held8a4 side source is used.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteOldformHeightRemainders20261026b
open ImbalancedChen.Part3.IntegerDilatedEisensteinHeightJets20261026b
open ImbalancedChen.Part3.FiniteCompletedOldformSpatial20261026a
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.LevelOldformFricke20261026a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinSpatialMaass
open ImbalancedChen.Part3.CompletedEisensteinCuspTail20261025a
open ImbalancedChen.Part3.ActualEisensteinHeightDerivativeTail20261026b
open ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b
open ImbalancedChen.Part3.PrimeExplicitCosetGreenTrace20261026b
open ImbalancedChen.Part3.ActualPrimeHorizontalGreenFlux20261026b
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.PrimeScatteringLocal20261026b
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.ActualTwoCuspHeightRemainders20261026b

/-- The reflected indices are genuine positive integers N/n, with their
divisibility witnesses taken from the ORIGINAL canonical oldform list. -/
def reflectedIntegerTerms (N : ℕ) (hN : 0 < N) (s : ℂ) : List (ℕ+ × ℂ) :=
  (oldformTerms (canonicalPrimeList N) s).attach.map fun t =>
    (complementaryIndex N hN t.val.1 (canonical_oldform_index_dvd N hN s t.val t.property), t.val.2)

def physicalCuspTerms (N : ℕ) (hN : 0 < N) (s : ℂ) (atZero : Bool) : List (ℕ+ × ℂ) :=
  if atZero then reflectedIntegerTerms N hN s else oldformTerms (canonicalPrimeList N) s

def physicalCuspChart (N : ℕ) (hN : 0 < N) (s : ℂ) (atZero : Bool) (p : ℝ × ℝ) : ℂ :=
  if atZero then frickeField N hN (completedComplexField N s) ⟨p.1, p.2⟩
  else completedLevelChart N s p

def physicalCuspConstant (N : ℕ) (s : ℂ) (atZero : Bool) (y : ℝ) : ℂ :=
  if atZero then completedReflectedConstant N s y else completedInfinityConstant N s y

def physicalCuspConstantFirst (N : ℕ) (hN : 0 < N) (s : ℂ) (atZero : Bool) (y : ℝ) : ℂ :=
  constantFirstSum (physicalCuspTerms N hN s atZero) s y /
    oldformNormalization (canonicalPrimeList N) s

def physicalCuspRemainder (N : ℕ) (hN : 0 < N) (s : ℂ) (atZero : Bool) (y x : ℝ) : ℂ :=
  physicalCuspChart N hN s atZero (x, y) - physicalCuspConstant N s atZero y

def physicalCuspRemainderY (N : ℕ) (hN : 0 < N) (s : ℂ) (atZero : Bool) (y x : ℝ) : ℂ :=
  deriv (fun v : ℝ => physicalCuspChart N hN s atZero (x, v)) y -
    deriv (physicalCuspConstant N s atZero) y

def physicalCuspMass (N : ℕ) (hN : 0 < N) (s : ℂ) (atZero : Bool) : ℝ :=
  coefficientMass (physicalCuspTerms N hN s atZero) /
    ‖oldformNormalization (canonicalPrimeList N) s‖

def physicalCuspFirstMass (N : ℕ) (hN : 0 < N) (s : ℂ) (atZero : Bool) : ℝ :=
  firstHeightMass (physicalCuspTerms N hN s atZero) /
    ‖oldformNormalization (canonicalPrimeList N) s‖

theorem physicalCuspMass_nonneg (N : ℕ) (hN : 0 < N) (s : ℂ) (b : Bool) :
    0 ≤ physicalCuspMass N hN s b :=
  div_nonneg (coefficientMass_nonneg _) (norm_nonneg _)

theorem physicalCuspFirstMass_nonneg (N : ℕ) (hN : 0 < N) (s : ℂ) (b : Bool) :
    0 ≤ physicalCuspFirstMass N hN s b :=
  div_nonneg (firstHeightMass_nonneg _) (norm_nonneg _)

theorem reflectedIntegerTerms_native_sum (N : ℕ) (hN : 0 < N) (s : ℂ)
    (z : UpperHalfPlane) :
    ((reflectedIntegerTerms N hN s).map
      (fun t => t.2 * completedActualEisenstein s (pnatDilate t.1 z))).sum =
      reflectedCompletedNumerator N hN s z := by
  unfold reflectedIntegerTerms reflectedCompletedNumerator
  rw [List.map_map]
  apply congrArg List.sum
  calc
    _ = (oldformTerms (canonicalPrimeList N) s).attach.map (fun t =>
        t.val.2 * completedActualEisenstein s (reflectedDilation N hN t.val.1 z)) := by
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply]
      rw [reflectedDilation_eq_integer N hN t.val.1
        (canonical_oldform_index_dvd N hN s t.val t.property)]
    _ = _ := List.attach_map_val

theorem physicalCuspChart_eq_finite (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) (x y : ℝ) (hy : 0 < y) :
    physicalCuspChart N hN s b (x, y) =
      completedTermsChart (physicalCuspTerms N hN s b) s (x, y) /
        oldformNormalization (canonicalPrimeList N) s := by
  cases b with
  | false => rfl
  | true =>
      change frickeField N hN (completedComplexField N s) (horizontalPoint y hy x) = _
      rw [frickeField, slMap_eq_action, completedComplexField_eq_native,
        completedLevelOldform_fricke N hN s hs0 hs1]
      change reflectedCompletedNumerator N hN s (horizontalPoint y hy x) / _ = _
      rw [← reflectedIntegerTerms_native_sum N hN s (horizontalPoint y hy x),
        ← completedTermsChart_eq_native]
      rfl

theorem physicalCuspConstant_eq_finite (N : ℕ) (hN : 0 < N) (s : ℂ)
    (b : Bool) (y : ℝ) :
    physicalCuspConstant N s b y = constantSum (physicalCuspTerms N hN s b) s y /
      oldformNormalization (canonicalPrimeList N) s := by
  cases b with
  | false => rfl
  | true =>
      unfold physicalCuspConstant physicalCuspTerms constantSum reflectedIntegerTerms
      simp only [Bool.true_eq_true, ↓reduceIte, List.map_map, scaledConstant]
      unfold completedReflectedConstant
      congr 1
      apply congrArg List.sum
      symm
      calc
        _ = (oldformTerms (canonicalPrimeList N) s).attach.map (fun t =>
            t.val.2 * completedConstant (((N : ℝ) / (t.val.1 : ℝ)) * y) s) := by
          apply List.map_congr_left
          intro t ht
          simp only [Function.comp_apply, complementaryIndex_real]
        _ = _ := List.attach_map_val

theorem physicalCuspChart_eq_native (N : ℕ) (hN : 0 < N) (s : ℂ)
    (b : Bool) (z : UpperHalfPlane) :
    physicalCuspChart N hN s b (z.re, z.im) =
      if b then completedLevelOldform N s (frickeSL N hN • z) else completedLevelOldform N s z := by
  cases b with
  | false => exact completedLevelChart_eq_native N s z
  | true =>
      change completedComplexField N s (slMap (frickeSL N hN) (z : ℂ)) = _
      rw [slMap_eq_action, completedComplexField_eq_native]

theorem physicalCuspConstant_hasDerivAt (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (physicalCuspConstant N s b) (physicalCuspConstantFirst N hN s b y) y := by
  have he : physicalCuspConstant N s b = fun v : ℝ =>
      constantSum (physicalCuspTerms N hN s b) s v / oldformNormalization (canonicalPrimeList N) s :=
    funext (physicalCuspConstant_eq_finite N hN s b)
  rw [he]
  exact (constantSum_hasDerivAt _ s hs0 hs1 hy).div_const _

theorem physicalCuspChart_hasDerivAt_y (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun v : ℝ => physicalCuspChart N hN s b (x, v))
      ((constantFirstSum (physicalCuspTerms N hN s b) s y +
        remainderFirstSum (physicalCuspTerms N hN s b) s y x) /
          oldformNormalization (canonicalPrimeList N) s) y := by
  have he : (fun v : ℝ => physicalCuspChart N hN s b (x, v)) =ᶠ[𝓝 y]
      (fun v : ℝ => completedTermsChart (physicalCuspTerms N hN s b) s (x, v) /
        oldformNormalization (canonicalPrimeList N) s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with v hv
    exact physicalCuspChart_eq_finite N hN s hs0 hs1 b x v hv
  exact ((completedTermsChart_hasDerivAt_y _ s hs0 hs1 hy x).div_const _)
    .congr_of_eventuallyEq he

theorem physicalCuspRemainder_eq_finite (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    physicalCuspRemainder N hN s b y x =
      remainderSum (physicalCuspTerms N hN s b) s y x /
        oldformNormalization (canonicalPrimeList N) s := by
  rw [physicalCuspRemainder, physicalCuspChart_eq_finite N hN s hs0 hs1 b x y hy,
    physicalCuspConstant_eq_finite N hN s b y, completedTermsChart_eq_constant_remainder]
  ring

theorem physicalCuspRemainderY_eq_finite (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    physicalCuspRemainderY N hN s b y x =
      remainderFirstSum (physicalCuspTerms N hN s b) s y x /
        oldformNormalization (canonicalPrimeList N) s := by
  rw [physicalCuspRemainderY, (physicalCuspChart_hasDerivAt_y N hN s hs0 hs1 b hy x).deriv,
    (physicalCuspConstant_hasDerivAt N hN s hs0 hs1 b hy).deriv]
  unfold physicalCuspConstantFirst
  ring

theorem physicalCuspRemainder_continuous_x (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) {y : ℝ} (hy : 0 < y) :
    Continuous (physicalCuspRemainder N hN s b y) := by
  simp_rw [physicalCuspRemainder_eq_finite N hN s hs0 hs1 b hy]
  exact (remainderSum_continuous_x _ s hy).div_const _

theorem physicalCuspRemainderY_continuous_x (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) {y : ℝ} (hy : 0 < y) :
    Continuous (physicalCuspRemainderY N hN s b y) := by
  simp_rw [physicalCuspRemainderY_eq_finite N hN s hs0 hs1 b hy]
  exact (remainderFirstSum_continuous_x _ s hs0 hs1 hy).div_const _

theorem physicalCuspRemainder_mean_zero (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, physicalCuspRemainder N hN s b y x) = 0 := by
  simp_rw [physicalCuspRemainder_eq_finite N hN s hs0 hs1 b hy]
  rw [intervalIntegral.integral_div, remainderSum_mean_zero _ s hs0 hs1 hy, zero_div]

theorem physicalCuspRemainderY_mean_zero (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, physicalCuspRemainderY N hN s b y x) = 0 := by
  simp_rw [physicalCuspRemainderY_eq_finite N hN s hs0 hs1 b hy]
  rw [intervalIntegral.integral_div, remainderFirstSum_mean_zero _ s hs0 hs1 hy, zero_div]

theorem physicalCusp_first_height_mean (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (b : Bool) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, deriv (fun v : ℝ => physicalCuspChart N hN s b (x, v)) y) =
      physicalCuspConstantFirst N hN s b y := by
  simp_rw [(physicalCuspChart_hasDerivAt_y N hN s hs0 hs1 b hy _).deriv]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
    ((remainderFirstSum_continuous_x _ s hs0 hs1 hy).intervalIntegrable 0 1),
    remainderFirstSum_mean_zero _ s hs0 hs1 hy]
  simp [physicalCuspConstantFirst]

theorem physicalCuspRemainder_bound (N : ℕ) (hN : 0 < N) (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (b : Bool) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖physicalCuspRemainder N hN s b y x‖ ≤
      (physicalCuspMass N hN s b * cuspTailConstant M) * Real.exp (-(Real.pi / 2) * y) := by
  rw [physicalCuspRemainder_eq_finite N hN s hs0 hs1 b (by linarith) x, norm_div]
  calc
    _ ≤ ((coefficientMass (physicalCuspTerms N hN s b) * cuspTailConstant M) *
        Real.exp (-(Real.pi / 2) * y)) / ‖oldformNormalization (canonicalPrimeList N) s‖ :=
      div_le_div_of_nonneg_right (remainderSum_bound _ M hs hy x) (norm_nonneg _)
    _ = _ := by unfold physicalCuspMass; ring

theorem physicalCuspRemainderY_bound (N : ℕ) (hN : 0 < N) (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (b : Bool) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖physicalCuspRemainderY N hN s b y x‖ ≤
      (physicalCuspFirstMass N hN s b * derivativeTailConstant M) * Real.exp (-(Real.pi / 2) * y) := by
  rw [physicalCuspRemainderY_eq_finite N hN s hs0 hs1 b (by linarith) x, norm_div]
  calc
    _ ≤ ((firstHeightMass (physicalCuspTerms N hN s b) * derivativeTailConstant M) *
        Real.exp (-(Real.pi / 2) * y)) / ‖oldformNormalization (canonicalPrimeList N) s‖ :=
      div_le_div_of_nonneg_right (remainderFirstSum_bound _ M hs hs0 hs1 hy x) (norm_nonneg _)
    _ = _ := by unfold physicalCuspFirstMass; ring

/-- Direct native pointwise supplier for genuine infinity/Fricke cusp tails. -/
theorem actual_native_two_cusp_remainder_bound (N : ℕ) (hN : 0 < N) (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (b : Bool) (z : UpperHalfPlane) (hz : 1 ≤ z.im) :
    ‖(if b then completedLevelOldform N s (frickeSL N hN • z) else completedLevelOldform N s z) -
        physicalCuspConstant N s b z.im‖ ≤
      (physicalCuspMass N hN s b * cuspTailConstant M) * Real.exp (-(Real.pi / 2) * z.im) := by
  rw [← physicalCuspChart_eq_native N hN s b z]
  exact physicalCuspRemainder_bound N hN M hs hs0 hs1 b hz z.re

/-- Literal prime completed constants, valid also at the removable center. -/
theorem prime_infinity_constant (p : ℕ) (hp : p.Prime) (s : ℂ) (y : ℝ) :
    completedInfinityConstant p s y =
      (completedConstant ((p : ℝ) * y) s - (p : ℂ) ^ (-s) * completedConstant y s) /
        ((p : ℂ) ^ s - (p : ℂ) ^ (-s)) := by
  simp [completedInfinityConstant, canonicalPrimeList_prime hp, oldformTerms,
    oldformNormalization, primeProduct, hp.not_dvd_one, primePNat, sub_eq_add_neg]

theorem prime_fricke_constant (p : ℕ) (hp : p.Prime) (s : ℂ) (y : ℝ) :
    completedReflectedConstant p s y =
      (completedConstant y s - (p : ℂ) ^ (-s) * completedConstant ((p : ℝ) * y) s) /
        ((p : ℂ) ^ s - (p : ℂ) ^ (-s)) := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  simp [completedReflectedConstant, canonicalPrimeList_prime hp, oldformTerms,
    oldformNormalization, primeProduct, hp.not_dvd_one, primePNat, sub_eq_add_neg, hpR]

theorem prime_infinity_constant_first (p : ℕ) (hp : p.Prime) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    physicalCuspConstantFirst p hp.pos s false y =
      ((p : ℝ) • completedFirst s ((p : ℝ) * y) - (p : ℂ) ^ (-s) * completedFirst s y) /
        ((p : ℂ) ^ s - (p : ℂ) ^ (-s)) := by
  have hnew : HasDerivAt (physicalCuspConstant p s false)
      (((p : ℝ) • completedFirst s ((p : ℝ) * y) - (p : ℂ) ^ (-s) * completedFirst s y) /
        ((p : ℂ) ^ s - (p : ℂ) ^ (-s))) y := by
    have he : physicalCuspConstant p s false = fun v : ℝ =>
        (completedConstant ((p : ℝ) * v) s - (p : ℂ) ^ (-s) * completedConstant v s) /
          ((p : ℂ) ^ s - (p : ℂ) ^ (-s)) := funext (prime_infinity_constant p hp s)
    rw [he]
    simpa only [scaledConstant, scaledConstantFirst] using
      ((scaledConstant_hasDerivAt ⟨p, hp.pos⟩ s hs0 hs1 hy).sub
        ((completedConstant_hasDerivAt s hs0 hs1 hy).const_mul ((p : ℂ) ^ (-s)))).div_const _
  exact (physicalCuspConstant_hasDerivAt p hp.pos s hs0 hs1 false hy).unique hnew

theorem prime_fricke_constant_first (p : ℕ) (hp : p.Prime) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    physicalCuspConstantFirst p hp.pos s true y =
      (completedFirst s y - (p : ℂ) ^ (-s) * ((p : ℝ) • completedFirst s ((p : ℝ) * y))) /
        ((p : ℂ) ^ s - (p : ℂ) ^ (-s)) := by
  have hnew : HasDerivAt (physicalCuspConstant p s true)
      ((completedFirst s y - (p : ℂ) ^ (-s) * ((p : ℝ) • completedFirst s ((p : ℝ) * y))) /
        ((p : ℂ) ^ s - (p : ℂ) ^ (-s))) y := by
    have he : physicalCuspConstant p s true = fun v : ℝ =>
        (completedConstant v s - (p : ℂ) ^ (-s) * completedConstant ((p : ℝ) * v) s) /
          ((p : ℂ) ^ s - (p : ℂ) ^ (-s)) := funext (prime_fricke_constant p hp s)
    rw [he]
    simpa only [scaledConstant, scaledConstantFirst] using
      ((completedConstant_hasDerivAt s hs0 hs1 hy).sub
        ((scaledConstant_hasDerivAt ⟨p, hp.pos⟩ s hs0 hs1 hy).const_mul ((p : ℂ) ^ (-s)))).div_const _
  exact (physicalCuspConstant_hasDerivAt p hp.pos s hs0 hs1 true hy).unique hnew

end ImbalancedChen.Part3.ActualTwoCuspHeightRemainders20261026b
