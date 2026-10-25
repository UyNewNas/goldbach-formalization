import ImbalancedChen.Part3MaassFiniteCoreL2Graph
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

First-order distribution tests for the actual hyperbolic form. Its inputs
are in canonical y⁻² L²; its finiteDx and finiteDy are in ordinary coordinate
Lebesgue L². The test on the canonical side is therefore y²∂jφ.

The proved sequential endpoint says that the L² limit of a core gradient
annihilates every actual compact smooth tensor when the input tends to zero.
OPEN: density of these positive-height tests and elimination of the lower
half-plane component are still needed for zero-gradient uniqueness and
closability. No density, closedness, or self-adjointness premise is supplied.
-/

namespace ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a

noncomputable section
open MeasureTheory Filter
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreResolventCoercivity20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a

private theorem first_continuous (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    Continuous (deriv f) := by
  have hs : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by simpa using hf
  exact (contDiff_succ_iff_deriv.mp hs).2.2.continuous

/-- True first-order integration by parts on the real line. -/
theorem integral_first_star_mul (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    (∫ x : ℝ, star (deriv f x) * g x) =
      -(∫ x : ℝ, star (f x) * deriv g x) := by
  have hi₁ : Integrable (fun x : ℝ => star (f x) * deriv g x) :=
    (hf.continuous.star.mul (first_continuous g hg)).integrable_of_hasCompactSupport
      hgc.deriv.mul_left
  have hi₂ : Integrable (fun x : ℝ => star (deriv f x) * g x) :=
    ((first_continuous f hf).star.mul hg.continuous).integrable_of_hasCompactSupport
      hgc.mul_left
  have hi₀ : Integrable (fun x : ℝ => star (f x) * g x) :=
    (hf.continuous.star.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => star (f x)) (v := g)
    (u' := fun x : ℝ => star (deriv f x)) (v' := deriv g)
    (fun x _ => ((hf.differentiable (by norm_num)) x).hasDerivAt.star)
    (fun x _ => ((hg.differentiable (by norm_num)) x).hasDerivAt)
    hi₁ hi₂ hi₀
  calc
    _ = -(-(∫ x : ℝ, star (deriv f x) * g x)) := by simp
    _ = _ := congrArg Neg.neg h.symm

private theorem pair_integrable (u v a b : ℝ → ℂ)
    (hu : Continuous u) (hv : Continuous v) (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) :
    Integrable (fun p : ℝ × ℝ =>
      star (tensorFunction u v p) * tensorFunction a b p) := by
  have hx : Integrable (fun x : ℝ => star (u x) * a x) :=
    (hu.star.mul ha).integrable_of_hasCompactSupport hac.mul_left
  have hy : Integrable (fun y : ℝ => star (v y) * b y) :=
    (hv.star.mul hb).integrable_of_hasCompactSupport hbc.mul_left
  apply (hx.mul_prod hy).congr
  exact Eventually.of_forall fun p => by simp only [tensorFunction, star_mul]; ring

private theorem pair_integral (u v a b : ℝ → ℂ) :
    (∫ p : ℝ × ℝ, star (tensorFunction u v p) * tensorFunction a b p) =
      (∫ x : ℝ, star (u x) * a x) * (∫ y : ℝ, star (v y) * b y) := by
  calc
    _ = ∫ p : ℝ × ℝ,
        (star (u p.1) * a p.1) * (star (v p.2) * b p.2) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by simp only [tensorFunction, star_mul]; ring
    _ = _ := by rw [integral_prod_mul]

/-- False is the horizontal, true the vertical actual coordinate derivative. -/
def tensorGradient (vertical : Bool) (T : CompactTensor) : ℝ × ℝ → ℂ :=
  if vertical then tensorDy T else tensorDx T

def finiteGradient {ι : Type*} (vertical : Bool) (s : Finset ι)
    (T : ι → CompactTensor) (p : ℝ × ℝ) : ℂ :=
  ∑ i ∈ s, tensorGradient vertical (T i) p

theorem finiteGradient_eq_actual {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) :
    finiteGradient false s T = finiteDx s T ∧
      finiteGradient true s T = finiteDy s T := by
  constructor <;> rfl

private theorem tensorGradient_pair_integrable (vertical : Bool) (T U : CompactTensor) :
    Integrable (fun p : ℝ × ℝ => star (tensorGradient vertical T p) *
      tensorFunction U.horizontal U.vertical p) ∧
    Integrable (fun p : ℝ × ℝ => star (tensorFunction T.horizontal T.vertical p) *
      tensorGradient vertical U p) := by
  cases vertical
  · exact ⟨pair_integrable _ _ _ _
        (first_continuous _ T.horizontal_smooth) T.vertical_smooth.continuous
        U.horizontal_smooth.continuous U.vertical_smooth.continuous
        U.horizontal_compact U.vertical_compact,
      pair_integrable _ _ _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
        (first_continuous _ U.horizontal_smooth) U.vertical_smooth.continuous
        U.horizontal_compact.deriv U.vertical_compact⟩
  · exact ⟨pair_integrable _ _ _ _ T.horizontal_smooth.continuous
        (first_continuous _ T.vertical_smooth) U.horizontal_smooth.continuous
        U.vertical_smooth.continuous U.horizontal_compact U.vertical_compact,
      pair_integrable _ _ _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
        U.horizontal_smooth.continuous (first_continuous _ U.vertical_smooth)
        U.horizontal_compact U.vertical_compact.deriv⟩

theorem tensorGradient_green (vertical : Bool) (T U : CompactTensor) :
    (∫ p : ℝ × ℝ, star (tensorGradient vertical T p) *
        tensorFunction U.horizontal U.vertical p) =
      -(∫ p : ℝ × ℝ, star (tensorFunction T.horizontal T.vertical p) *
        tensorGradient vertical U p) := by
  cases vertical
  · change (∫ p : ℝ × ℝ,
        star (tensorFunction (deriv T.horizontal) T.vertical p) *
          tensorFunction U.horizontal U.vertical p) =
      -(∫ p : ℝ × ℝ, star (tensorFunction T.horizontal T.vertical p) *
          tensorFunction (deriv U.horizontal) U.vertical p)
    rw [pair_integral, pair_integral,
      integral_first_star_mul _ _ T.horizontal_smooth U.horizontal_smooth
        U.horizontal_compact]
    ring
  · change (∫ p : ℝ × ℝ,
        star (tensorFunction T.horizontal (deriv T.vertical) p) *
          tensorFunction U.horizontal U.vertical p) =
      -(∫ p : ℝ × ℝ, star (tensorFunction T.horizontal T.vertical p) *
          tensorFunction U.horizontal (deriv U.vertical) p)
    rw [pair_integral, pair_integral,
      integral_first_star_mul _ _ T.vertical_smooth U.vertical_smooth
        U.vertical_compact]
    ring

/-- The exact density-cancelling test, on canonical upper-half-plane volume. -/
def heightSquaredLift (φ : ℝ × ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  (z.im : ℂ)^2 * φ (Complex.measurableEquivRealProd (z : ℂ))

theorem canonical_heightSquared_pairing (F φ : ℝ × ℝ → ℂ)
    (hφ : ∀ p ∉ upperChart, φ p = 0) :
    (∫ z : UpperHalfPlane,
      star (F (Complex.measurableEquivRealProd (z : ℂ))) * heightSquaredLift φ z) =
      ∫ p : ℝ × ℝ, star (F p) * φ p := by
  change (∫ z : UpperHalfPlane,
    (fun p : ℝ × ℝ => star (F p) * ((p.2 : ℂ)^2 * φ p))
      (Complex.measurableEquivRealProd (z : ℂ))) = _
  rw [canonical_integral_eq_chart_integral]
  unfold chartMeasure
  rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
  calc
    _ = ∫ p in upperChart, star (F p) * φ p := by
      apply setIntegral_congr_fun upperChart_measurable
      intro p hp
      have hy : p.2 ≠ 0 := ne_of_gt hp
      simp only [NNReal.smul_def, Complex.real_smul]
      change (((p.2⁻¹)^2 : ℝ) : ℂ) *
        (star (F p) * ((p.2 : ℂ)^2 * φ p)) = _
      have hc : (((p.2⁻¹)^2 : ℝ) : ℂ) * (p.2 : ℂ)^2 = 1 := by
        have hr : (p.2⁻¹)^2 * p.2^2 = (1 : ℝ) := by
          rw [← mul_pow, inv_mul_cancel₀ hy, one_pow]
        exact_mod_cast hr
      calc
        _ = star (F p) *
            ((((p.2⁻¹)^2 : ℝ) : ℂ) * (p.2 : ℂ)^2) * φ p := by ring
        _ = _ := by rw [hc]; ring
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hφ p hp, mul_zero])

private theorem tensorGradient_zero_nonpositive (vertical : Bool) (U : CompactTensor)
    (p : ℝ × ℝ) (hp : p ∉ upperChart) : tensorGradient vertical U p = 0 := by
  have hv : U.vertical p.2 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hp (U.vertical_positive h))
  have hdv : deriv U.vertical p.2 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hp (U.vertical_positive (tsupport_deriv_subset h)))
  cases vertical <;> simp [tensorGradient, tensorDx, tensorDy, hv, hdv]

/-- Genuine first-order weak action of the actual finite gradient. -/
theorem finiteGradient_green {ι : Type*} (vertical : Bool)
    (s : Finset ι) (T : ι → CompactTensor) (U : CompactTensor) :
    (∫ p : ℝ × ℝ, star (finiteGradient vertical s T p) *
        tensorFunction U.horizontal U.vertical p) =
      -(∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) *
        heightSquaredLift (tensorGradient vertical U) z) := by
  have hcanonical := canonical_heightSquared_pairing (finiteChartFunction s T)
    (tensorGradient vertical U) (tensorGradient_zero_nonpositive vertical U)
  have hcanonical' :
      (∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) *
        heightSquaredLift (tensorGradient vertical U) z) =
      ∫ p : ℝ × ℝ, star (finiteChartFunction s T p) *
        tensorGradient vertical U p := by
    simpa only [finiteCoreFunction_eq_chart] using hcanonical
  rw [hcanonical']
  simp only [finiteGradient, finiteChartFunction, star_sum, Finset.sum_mul]
  rw [integral_finsetSum s (fun i _ =>
    (tensorGradient_pair_integrable vertical (T i) U).1)]
  rw [integral_finsetSum s (fun i _ =>
    (tensorGradient_pair_integrable vertical (T i) U).2)]
  simp_rw [tensorGradient_green]
  simp only [Finset.sum_neg_distrib]

/-- Plane L² membership of a separated compact continuous function. -/
theorem separated_plane_memLp (u v : ℝ → ℂ) (hu : Continuous u) (hv : Continuous v)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v) :
    MemLp (tensorFunction u v) 2 (volume : Measure (ℝ × ℝ)) := by
  have hu2 : MemLp u 2 (volume : Measure ℝ) := hu.memLp_of_hasCompactSupport huc
  have hv2 : MemLp v 2 (volume : Measure ℝ) := hv.memLp_of_hasCompactSupport hvc
  have hx := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu2
  have hy := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv2
  have hc : Continuous (tensorFunction u v) :=
    (hu.comp continuous_fst).mul (hv.comp continuous_snd)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
  simpa only [tensorFunction, norm_mul, mul_pow] using hx.mul_prod hy

theorem tensorGradient_memLp (vertical : Bool) (T : CompactTensor) :
    MemLp (tensorGradient vertical T) 2 (volume : Measure (ℝ × ℝ)) := by
  cases vertical
  · exact separated_plane_memLp _ _ (first_continuous _ T.horizontal_smooth)
      T.vertical_smooth.continuous T.horizontal_compact.deriv T.vertical_compact
  · exact separated_plane_memLp _ _ T.horizontal_smooth.continuous
      (first_continuous _ T.vertical_smooth) T.horizontal_compact T.vertical_compact.deriv

theorem finiteGradient_memLp {ι : Type*} (vertical : Bool)
    (s : Finset ι) (T : ι → CompactTensor) :
    MemLp (finiteGradient vertical s T) 2 (volume : Measure (ℝ × ℝ)) :=
  memLp_finsetSum s (fun i _ => tensorGradient_memLp vertical (T i))

theorem liftedGradient_memLp (vertical : Bool) (T : CompactTensor) :
    MemLp (heightSquaredLift (tensorGradient vertical T)) 2
      (volume : Measure UpperHalfPlane) := by
  cases vertical
  · have h := separated_memLp (deriv T.horizontal)
      (fun y : ℝ => (y : ℂ)^2 * T.vertical y)
      (first_continuous _ T.horizontal_smooth)
      ((Complex.continuous_ofReal.pow 2).mul T.vertical_smooth.continuous)
      T.horizontal_compact.deriv T.vertical_compact.mul_left
      (tsupport_mul_subset_right.trans T.vertical_positive)
    convert h using 1
    funext z
    simp [heightSquaredLift, tensorGradient, tensorDx, tensorFunctionH,
      tensorFunction, Complex.measurableEquivRealProd_apply] <;> ring
  · have h := separated_memLp T.horizontal
      (fun y : ℝ => (y : ℂ)^2 * deriv T.vertical y)
      T.horizontal_smooth.continuous
      ((Complex.continuous_ofReal.pow 2).mul (first_continuous _ T.vertical_smooth))
      T.horizontal_compact T.vertical_compact.deriv.mul_left
      (tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans T.vertical_positive))
    convert h using 1
    funext z
    simp [heightSquaredLift, tensorGradient, tensorDy, tensorFunctionH,
      tensorFunction, Complex.measurableEquivRealProd_apply] <;> ring

abbrev PlaneL2 := Lp ℂ 2 (volume : Measure (ℝ × ℝ))

def gradientL2 {ι : Type*} (vertical : Bool) (s : Finset ι)
    (T : ι → CompactTensor) : PlaneL2 :=
  (finiteGradient_memLp vertical s T).toLp (finiteGradient vertical s T)

def testL2 (U : CompactTensor) : PlaneL2 :=
  (separated_plane_memLp U.horizontal U.vertical U.horizontal_smooth.continuous
    U.vertical_smooth.continuous U.horizontal_compact U.vertical_compact).toLp
    (tensorFunction U.horizontal U.vertical)

def liftedGradientL2 (vertical : Bool) (U : CompactTensor) : HyperbolicL2 :=
  (liftedGradient_memLp vertical U).toLp (heightSquaredLift (tensorGradient vertical U))

private theorem toLp_inner_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, star (f x) * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply', Complex.star_def]

theorem gradientL2_green {ι : Type*} (vertical : Bool)
    (s : Finset ι) (T : ι → CompactTensor) (U : CompactTensor) :
    inner ℂ (gradientL2 vertical s T) (testL2 U) =
      -inner ℂ (finiteCoreL2 s T) (liftedGradientL2 vertical U) := by
  unfold gradientL2 testL2 finiteCoreL2 liftedGradientL2
  rw [toLp_inner_integral, toLp_inner_integral]
  exact finiteGradient_green vertical s T U

/-- A genuine C∞ compact tensor test, retaining the actual core's data. -/
def SmoothCompactTest := {U : CompactTensor //
  ContDiff ℝ ∞ U.horizontal ∧ ContDiff ℝ ∞ U.vertical}

/-- Sequential distribution limit: convergence in the two actual L² spaces
forces the limiting gradient to annihilate each concrete compact test. -/
theorem gradient_limit_annihilates_compact_tests (vertical : Bool)
    (k : ℕ → ℕ) (T : (n : ℕ) → Fin (k n) → CompactTensor) (G : PlaneL2)
    (hinput : Tendsto (fun n => finiteCoreL2 Finset.univ (T n)) atTop (nhds 0))
    (hgradient : Tendsto (fun n => gradientL2 vertical Finset.univ (T n))
      atTop (nhds G)) (U : CompactTensor) :
    inner ℂ G (testL2 U) = 0 := by
  have hleft : Tendsto
      (fun n => inner ℂ (gradientL2 vertical Finset.univ (T n)) (testL2 U))
      atTop (nhds (inner ℂ G (testL2 U))) :=
    hgradient.inner tendsto_const_nhds
  have hright : Tendsto
      (fun n => -inner ℂ (finiteCoreL2 Finset.univ (T n))
        (liftedGradientL2 vertical U)) atTop (nhds 0) := by
    simpa using (hinput.inner (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => liftedGradientL2 vertical U) atTop
        (nhds (liftedGradientL2 vertical U)))).neg
  have heq : (fun n => inner ℂ (gradientL2 vertical Finset.univ (T n)) (testL2 U)) =
      (fun n => -inner ℂ (finiteCoreL2 Finset.univ (T n))
        (liftedGradientL2 vertical U)) := by
    funext n
    exact gradientL2_green vertical Finset.univ (T n) U
  rw [← heq] at hright
  exact tendsto_nhds_unique hleft hright

theorem gradient_limit_annihilates_smooth_tests (vertical : Bool)
    (k : ℕ → ℕ) (T : (n : ℕ) → Fin (k n) → CompactTensor) (G : PlaneL2)
    (hinput : Tendsto (fun n => finiteCoreL2 Finset.univ (T n)) atTop (nhds 0))
    (hgradient : Tendsto (fun n => gradientL2 vertical Finset.univ (T n))
      atTop (nhds G)) (U : SmoothCompactTest) :
    inner ℂ G (testL2 U.val) = 0 :=
  gradient_limit_annihilates_compact_tests vertical k T G hinput hgradient U.val

end
end ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
