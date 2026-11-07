import ImbalancedChen.Part3CompactProductBochnerAEJoin
import ImbalancedChen.Part3WeakH1ProductMollifierDerivative
import ImbalancedChen.Part3CompactTensorFirstJetL2Error
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Full value/first-gradient test-jet density for a genuinely compact H1 jet
at positive height. Each of its three L2 components has actual compact
support; these are geometric support inputs, not approximation premises.
The weak derivative is the literal distributional test definition. Actual
product smoothing, its proved Bochner/scalar AE identification, and the
actual common-support finite-tensor supplier give an explicit diagonal
sequence of finite smooth tensors. The conclusion is native L2 jet
convergence and closure membership, with no hDensity/hJoin hypothesis.
No H1 regularity of an actual Gamma adjoint vector is inferred.
-/

namespace ImbalancedChen.Part3.SupportedH1FiniteTensorDensity20261026a
noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
open CompactProductKernelSixJet20261025a
open CompactC2ProductMollifier20261026a
open CompactC2FiniteTensorApproximation20261026a
open CompactTensorFirstJetL2Error20261026a
open ProductKernelL2TranslationAverage20261026a
open CompactProductBochnerAEJoin20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz

def firstIndex : Fin 3 → JetIndex :=
  ![⟨(0, 0), by norm_num⟩, ⟨(1, 0), by norm_num⟩, ⟨(0, 1), by norm_num⟩]

def component (J : CompactH1Jet) : Fin 3 → Plane → ℂ := ![J.value, J.dx, J.dy]

theorem component_memLp (J : CompactH1Jet) (i : Fin 3) :
    MemLp (component J i) 2 volume := by
  fin_cases i
  · exact J.value_memLp
  · exact J.dx_memLp
  · exact J.dy_memLp

def h1JetClass (J : CompactH1Jet) : Fin 3 → PlaneL2 :=
  fun i => (component_memLp J i).toLp (component J i)

theorem partial_memLp {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (ij : JetIndex) :
    MemLp (fun p => partialJet ij F p) 2 volume := by
  have heq : (fun p => partialJet ij F p) = mixedJet F ij :=
    funext (partialJet_eq_mixedJet hF ij)
  rw [heq]
  exact (mixedJet_smooth hF ij).continuous.memLp_of_hasCompactSupport
    (mixedJet_compact hc ij)

def smoothJetClass {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : Fin 3 → PlaneL2 :=
  fun i => (partial_memLp hF hc (firstIndex i)).toLp (fun p => partialJet (firstIndex i) F p)

theorem norm_sq_integral (u : PlaneL2) :
    ‖u‖ ^ 2 = ∫ p, ‖u p‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner u u)]
  apply integral_congr_ae
  exact Eventually.of_forall fun p =>
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (u p)).symm

theorem toLp_sub_norm_sq {f g : Plane → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ p, ‖f p - g p‖ ^ 2 := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp,
    hg.coeFn_toLp] with p hp hf' hg'
  rw [hp, hf', hg']

theorem smoothing_firstJet {J : CompactH1Jet} (r : ℝ) (hr : 0 < r)
    (i : Fin 3) (p : Plane) :
    partialJet (firstIndex i) (productSmoothing r hr J.value) p =
      productSmoothing r hr (component J i) p := by
  have hF := compactH1_productSmoothing_smooth J r hr
  obtain ⟨hx, hy⟩ := compactH1_productSmoothing_gradient J r hr
  fin_cases i
  · rfl
  · rw [partialJet_eq_mixedJet hF]
    exact congrFun hx p
  · rw [partialJet_eq_mixedJet hF]
    exact congrFun hy p

theorem component_compact (J : CompactH1Jet) (hx : HasCompactSupport J.dx)
    (hy : HasCompactSupport J.dy) (i : Fin 3) : HasCompactSupport (component J i) := by
  fin_cases i
  · exact J.value_compact
  · exact hx
  · exact hy

theorem smoothing_jetClass_eq (J : CompactH1Jet) (hx : HasCompactSupport J.dx)
    (hy : HasCompactSupport J.dy) (r : ℝ) (hr : 0 < r) (i : Fin 3) :
    smoothJetClass (compactH1_productSmoothing_smooth J r hr)
      (smoothing_compact J.value_compact r hr) i =
      productAverage r hr (h1JetClass J i) := by
  rw [h1JetClass, productAverage_eq_scalar_toLp (component_memLp J i)
    (component_compact J hx hy i) r hr]
  apply Lp.ext
  filter_upwards [(partial_memLp (compactH1_productSmoothing_smooth J r hr)
      (smoothing_compact J.value_compact r hr) (firstIndex i)).coeFn_toLp,
    (smoothing_memLp (component_memLp J i) (component_compact J hx hy i) r hr).coeFn_toLp]
    with p hp hq
  rw [hp, hq]
  exact smoothing_firstJet r hr i p

/-- The geometric positive rectangle is preserved under a small genuine
product convolution, uniformly in its shrinking radius. -/
theorem smoothing_support_box {F : Plane → ℂ} {A a b r : ℝ}
    (hF : tsupport F ⊆ planeBox A a b) (hr : 0 < r)
    (hr1 : r ≤ 1) (hra : r ≤ a / 2) :
    tsupport (productSmoothing r hr F) ⊆ planeBox (A + 1) (a / 2) (b + 1) := by
  apply closure_minimal ?_ (isCompact_planeBox _ _ _).isClosed
  intro p hp
  obtain ⟨u, hu, v, hv, rfl⟩ := support_convolution_subset
    (ContinuousLinearMap.mul ℝ ℂ) hp
  have huk : u ∈ Function.support (realProductKernel r hr) := by
    intro hz
    apply hu
    rw [complexProductKernel_eq, hz]
    rfl
  have hun := Metric.mem_ball.mp (realProductKernel_support r hr huk)
  rw [dist_zero_right, Prod.norm_def] at hun
  have hux : |u.1| < r := by
    simpa only [Real.norm_eq_abs] using (lt_of_le_of_lt (le_max_left _ _) hun)
  have huy : |u.2| < r := by
    simpa only [Real.norm_eq_abs] using (lt_of_le_of_lt (le_max_right _ _) hun)
  have hv' := hF (subset_closure hv)
  rcases abs_lt.mp hux with ⟨hux₁, hux₂⟩
  rcases abs_lt.mp huy with ⟨huy₁, huy₂⟩
  change (-(A + 1) ≤ u.1 + v.1 ∧ u.1 + v.1 ≤ A + 1) ∧
    (a / 2 ≤ u.2 + v.2 ∧ u.2 + v.2 ≤ b + 1)
  change (-A ≤ v.1 ∧ v.1 ≤ A) ∧ (a ≤ v.2 ∧ v.2 ≤ b) at hv'
  constructor <;> constructor <;> linarith [hv'.1.1, hv'.1.2, hv'.2.1, hv'.2.2]

def finiteTensorJetSet : Set (Fin 3 → PlaneL2) :=
  {v | ∃ (F : Plane → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F),
    (∃ (ι : Type) (s : Finset ι) (T : ι → SmoothCompactTensor),
      F = finiteChartFunction s (fun t => (T t).toCompactTensor)) ∧
    v = smoothJetClass hF hc}

/-- Explicit finite-tensor diagonal approximation for a genuinely compact
positive-height H1 jet. There is no test-jet-density hypothesis. -/
theorem compactH1_mem_finiteTensorJet_closure (J : CompactH1Jet)
    (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (A a b : ℝ) (ha : 0 < a) (hs : tsupport J.value ⊆ planeBox A a b) :
    h1JetClass J ∈ closure finiteTensorJetSet := by
  have hsmall : ∀ᶠ n in atTop, radius n < min 1 (a / 2) :=
    radius_tendsto.eventually (gt_mem_nhds (lt_min (by norm_num) (half_pos ha)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  let r (n : ℕ) := radius (n + N)
  have hr (n : ℕ) : 0 < r n := radius_pos _
  have hr1 (n : ℕ) : r n ≤ 1 :=
    ((hN (n + N) (Nat.le_add_left N n)).trans_le (min_le_left _ _)).le
  have hra (n : ℕ) : r n ≤ a / 2 :=
    ((hN (n + N) (Nat.le_add_left N n)).trans_le (min_le_right _ _)).le
  let F (n : ℕ) := productSmoothing (r n) (hr n) J.value
  have hF (n : ℕ) : ContDiff ℝ ∞ (F n) := compactH1_productSmoothing_smooth J _ _
  have hFc (n : ℕ) : HasCompactSupport (F n) := smoothing_compact J.value_compact _ _
  have hFs (n : ℕ) : tsupport (F n) ⊆ planeBox (A + 1) (a / 2) (b + 1) :=
    smoothing_support_box hs (hr n) (hr1 n) (hra n)
  let P (n : ℕ) : CompactC2TensorApproximation (F n) (A + 1) (a / 2) (b + 1) (radius n) :=
    Classical.choice (exists_compactC2TensorApproximation (hF n) (hFc n)
      (A + 1) (a / 2) (b + 1) (half_pos ha) (hFs n) (radius n) (radius_pos n))
  let G (n : ℕ) := approximatingFunction (P n)
  have hG (n : ℕ) : ContDiff ℝ ∞ (G n) :=
    finiteSmoothChart_contDiff (P n).indices (P n).tensors
  have hGc (n : ℕ) : HasCompactSupport (G n) :=
    HasCompactSupport.of_support_subset_isCompact
      (commonBox_isCompact (A + 1) (a / 2) (b + 1))
      (subset_closure.trans (P n).common_support)
  let V (n : ℕ) := smoothJetClass (hG n) (hGc n)
  have hmem (n : ℕ) : V n ∈ finiteTensorJetSet :=
    ⟨G n, hG n, hGc n, ⟨planeBox (A + 1) (a / 2) (b + 1),
      (P n).indices, (P n).tensors, rfl⟩, rfl⟩
  have htN : Tendsto (fun n : ℕ => n + N) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n N) tendsto_id
  have hlim : Tendsto V atTop (𝓝 (h1JetClass J)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hsmooth : Tendsto (fun n => smoothJetClass (hF n) (hFc n) i)
        atTop (𝓝 (h1JetClass J i)) := by
      have h := (productAverage_tendsto (h1JetClass J i)).comp htN
      simpa only [← smoothing_jetClass_eq J hx hy] using h
    have hb (n : ℕ) : ‖V n i - smoothJetClass (hF n) (hFc n) i‖ ^ 2 ≤
        (radius n) ^ 2 * (volume : Measure Plane).real
          (commonBox (A + 1) (a / 2) (b + 1)) := by
      rw [toLp_sub_norm_sq]
      exact jetError_integral_norm_sq_le (P n) (radius_pos n) (firstIndex i)
    have hsq : Tendsto (fun n => ‖V n i - smoothJetClass (hF n) (hFc n) i‖ ^ 2)
        atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _) hb
        (by simpa using (radius_tendsto.pow 2).mul_const
          ((volume : Measure Plane).real (commonBox (A + 1) (a / 2) (b + 1))))
    have hnorm := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
    have hdiff : Tendsto (fun n => V n i - smoothJetClass (hF n) (hFc n) i)
        atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hnorm
    simpa only [sub_add_cancel, zero_add] using hdiff.add hsmooth
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hmem)

end
end ImbalancedChen.Part3.SupportedH1FiniteTensorDensity20261026a
