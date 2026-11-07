import ImbalancedChen.Part3CompactC2LocalizedTensorApproximation
import ImbalancedChen.Part3SupportedH1FiniteTensorDensity
import ImbalancedChen.Part3Gamma0ActualAdjointInteriorWeakEquation

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Support-preserving finite tensor approximation of a genuine compact H1
jet. All factors lie in the SAME prescribed open rectangle. The only
regularity data are the literal weak first derivatives of CompactH1Jet.
The unfinished predecessor's L2-budget idea is proved here as an internal
lemma; that unfinished source is not imported or treated as a supplier.
-/
namespace ImbalancedChen.Part3.LocalH1Tests20261026b
noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution UpperHalfPlane
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open CompactC2FiniteTensorApproximation20261026a
open CompactC2LocalizedTensorApproximation20261026a
open SupportedH1FiniteTensorDensity20261026a
open ProductKernelL2TranslationAverage20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a

def rect (L R a b : ℝ) : Set Plane := Icc L R ×ˢ Icc a b

def openRect (L R a b : ℝ) : Set Plane := Ioo L R ×ˢ Ioo a b

theorem finiteTensor_tsupport_rect {ι : Type*} (s : Finset ι)
    (T : ι → SmoothCompactTensor) (L R a b : ℝ)
    (hs : ∀ t, tsupport (T t).horizontal ⊆ Icc L R ∧
      tsupport (T t).vertical ⊆ Icc a b) :
    tsupport (finiteChartFunction s (fun t => (T t).toCompactTensor)) ⊆ rect L R a b := by
  apply closure_minimal ?_ (isClosed_Icc.prod isClosed_Icc)
  intro p hp
  by_contra hn
  apply hp
  change (∑ t ∈ s, (T t).horizontal p.1 * (T t).vertical p.2) = 0
  apply Finset.sum_eq_zero
  intro t ht
  by_cases hx : p.1 ∈ tsupport (T t).horizontal
  · have hy : p.2 ∉ tsupport (T t).vertical := by
      intro hy
      exact hn ⟨(hs t).1 hx, (hs t).2 hy⟩
    simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem localized_tsupport {F : Plane → ℂ} {L R a b ε : ℝ}
    (P : LocalizedC2Approximation F L R a b 0 ε) :
    tsupport (finiteChartFunction P.indices (fun t => (P.tensors t).toCompactTensor)) ⊆
      rect L R a b := by
  apply finiteTensor_tsupport_rect
  intro t
  obtain ⟨hx, hy⟩ := P.factor_supports_open t
  constructor
  · simpa only [add_zero, sub_zero] using hx.trans Ioo_subset_Icc_self
  · simpa only [add_zero, sub_zero] using hy.trans Ioo_subset_Icc_self

theorem localized_compact {F : Plane → ℂ} {L R a b ε : ℝ}
    (P : LocalizedC2Approximation F L R a b 0 ε) :
    HasCompactSupport (finiteChartFunction P.indices
      (fun t => (P.tensors t).toCompactTensor)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
    (subset_closure.trans (localized_tsupport P))

/-- Uniform C2 error on one bounded chart gives a genuine global L2
error because both jets vanish outside that SAME closed rectangle. -/
theorem localized_error_L2 {F : Plane → ℂ} {L R a b ε : ℝ}
    (P : LocalizedC2Approximation F L R a b 0 ε)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ rect L R a b) (ij : JetIndex) :
    (∫ p : Plane, ‖partialJet ij
      (finiteChartFunction P.indices (fun t => (P.tensors t).toCompactTensor)) p -
        partialJet ij F p‖ ^ 2) ≤ ε ^ 2 * (volume : Measure Plane).real (rect L R a b) := by
  let G := finiteChartFunction P.indices (fun t => (P.tensors t).toCompactTensor)
  have hG := finiteSmoothChart_contDiff P.indices P.tensors
  have he := (partial_memLp hG (localized_compact P) ij).sub (partial_memLp hF hc ij)
  have hi : Integrable (fun p => ‖partialJet ij G p - partialJet ij F p‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he
  have hz (p : Plane) (hp : p ∉ rect L R a b) :
      partialJet ij G p - partialJet ij F p = 0 := by
    rw [image_eq_zero_of_notMem_tsupport
      (fun h => hp (localized_tsupport P (partialJet_tsupport_subset hG ij h))),
      image_eq_zero_of_notMem_tsupport
      (fun h => hp (hs (partialJet_tsupport_subset hF ij h))), sub_self]
  have hset : (∫ p in rect L R a b, ‖partialJet ij G p - partialJet ij F p‖ ^ 2) =
      ∫ p, ‖partialJet ij G p - partialJet ij F p‖ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [hz p hp]
    norm_num
  rw [← hset]
  calc
    _ ≤ ∫ _p in rect L R a b, ε ^ 2 := by
      apply integral_mono_ae hi.integrableOn
        (integrableOn_const.mpr (Or.inr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne))
      exact Eventually.of_forall fun p => by
        have hb := (P.uniform_sixJet_error p ij).le
        simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hb
    _ = _ := by rw [setIntegral_const]; simp only [smul_eq_mul, mul_comm]

/-- Actual convolution support geometry, with an arbitrarily small
prescribed expansion. This does not use H1 approximation as a premise. -/
theorem smoothing_tsupport_rect {F : Plane → ℂ} {L R a b r δ : ℝ}
    (hs : tsupport F ⊆ rect L R a b) (hr : 0 < r) (hrδ : r ≤ δ) :
    tsupport (productSmoothing r hr F) ⊆ rect (L - δ) (R + δ) (a - δ) (b + δ) := by
  apply closure_minimal ?_ (isClosed_Icc.prod isClosed_Icc)
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
    simpa only [Real.norm_eq_abs] using lt_of_le_of_lt (le_max_left _ _) hun
  have huy : |u.2| < r := by
    simpa only [Real.norm_eq_abs] using lt_of_le_of_lt (le_max_right _ _) hun
  have h := hs (subset_closure hv)
  obtain ⟨hx₁, hx₂⟩ := abs_lt.mp hux
  obtain ⟨hy₁, hy₂⟩ := abs_lt.mp huy
  change (L - δ ≤ u.1 + v.1 ∧ u.1 + v.1 ≤ R + δ) ∧
    (a - δ ≤ u.2 + v.2 ∧ u.2 + v.2 ≤ b + δ)
  constructor <;> constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]

def localFiniteTensorJets (L R a b : ℝ) : Set (Fin 3 → PlaneL2) :=
  {v | ∃ (ι : Type) (s : Finset ι) (T : ι → SmoothCompactTensor)
    (hc : HasCompactSupport (finiteChartFunction s (fun t => (T t).toCompactTensor))),
    (∀ t, tsupport (T t).horizontal ⊆ Ioo L R ∧
      tsupport (T t).vertical ⊆ Ioo a b) ∧
    v = smoothJetClass (finiteSmoothChart_contDiff s T) hc}

/-- Support-preserving H1 jet density, proved by genuine product
mollification followed by the SAME-open-rectangle finite tensor supplier.
Every factor lies strictly inside the originally allowed chart. -/
theorem compactH1_mem_localFiniteTensorJets_closure (J : CompactH1Jet)
    (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (uL uR vL vR : ℝ) (hvL : 0 < vL) (hu : uL < uR) (hv : vL < vR)
    (hs : tsupport J.value ⊆ openRect uL uR vL vR) :
    h1JetClass J ∈ closure (localFiniteTensorJets uL uR vL vR) := by
  obtain ⟨L,R,a,b,ρ,hLR,ha,hab,hρ,hxL,hxR,hyL,hyR,hinner⟩ :=
    exists_inner_rectangle_slack J.value_compact uL uR vL vR 0 (le_refl 0) hvL
      (by simpa using hu) (by simpa using hv) (by simpa [openRect] using hs)
  have hsmall : ∀ᶠ n in atTop, radius n < ρ / 2 :=
    radius_tendsto.eventually (gt_mem_nhds (half_pos hρ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsmall
  let r (n : ℕ) := radius (n + N)
  have hr (n : ℕ) : 0 < r n := radius_pos _
  have hrρ (n : ℕ) : r n ≤ ρ / 2 := (hN (n + N) (Nat.le_add_left N n)).le
  let F (n : ℕ) := productSmoothing (r n) (hr n) J.value
  have hF (n : ℕ) : ContDiff ℝ ∞ (F n) := compactH1_productSmoothing_smooth J _ _
  have hFc (n : ℕ) : HasCompactSupport (F n) := smoothing_compact J.value_compact _ _
  have hFs (n : ℕ) : tsupport (F n) ⊆ openRect uL uR vL vR := by
    intro p hp
    have h := smoothing_tsupport_rect hinner (hr n) (hrρ n) hp
    change (uL < p.1 ∧ p.1 < uR) ∧ (vL < p.2 ∧ p.2 < vR)
    constructor <;> constructor <;>
      linarith [h.1.1,h.1.2,h.2.1,h.2.2]
  let P (n : ℕ) : LocalizedC2Approximation (F n) uL uR vL vR 0 (radius n) :=
    Classical.choice (exists_sameOpenRectangle_C2Approximation (hF n) (hFc n)
      uL uR vL vR 0 (le_refl 0) hvL (by simpa using hu) (by simpa using hv)
      (by simpa [openRect] using hFs n) (radius n) (radius_pos n))
  let G (n : ℕ) := finiteChartFunction (P n).indices (fun t => ((P n).tensors t).toCompactTensor)
  have hG (n : ℕ) : ContDiff ℝ ∞ (G n) := finiteSmoothChart_contDiff (P n).indices (P n).tensors
  have hGc (n : ℕ) : HasCompactSupport (G n) := localized_compact (P n)
  let V (n : ℕ) := smoothJetClass (hG n) (hGc n)
  have hmem (n : ℕ) : V n ∈ localFiniteTensorJets uL uR vL vR := by
    refine ⟨planeBox (P n).A (P n).a (P n).b, (P n).indices, (P n).tensors, hGc n, ?_, rfl⟩
    intro t
    simpa only [add_zero, sub_zero] using (P n).factor_supports_open t
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
        (radius n) ^ 2 * (volume : Measure Plane).real (rect uL uR vL vR) := by
      rw [toLp_sub_norm_sq]
      exact localized_error_L2 (P n) (hF n) (hFc n)
        ((hFs n).trans (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)) (firstIndex i)
    have hsq : Tendsto (fun n => ‖V n i - smoothJetClass (hF n) (hFc n) i‖ ^ 2)
        atTop (𝓝 0) := squeeze_zero (fun n => sq_nonneg _) hb
      (by simpa using (radius_tendsto.pow 2).mul_const
        ((volume : Measure Plane).real (rect uL uR vL vR)))
    have hnorm := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
    have hdiff : Tendsto (fun n => V n i - smoothJetClass (hF n) (hFc n) i)
        atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hnorm
    simpa only [sub_add_cancel, zero_add] using hdiff.add hsmooth
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hmem)

/-- The full CLOSED factor supports used by the original Gamma weak
identity lie inside the actual reduced carrier, not just the support of
their sum. Cancellation in a finite sum therefore causes no support gap. -/
theorem finiteTensorSupportK_subset_reducedCarrier (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → SmoothCompactTensor) (L R a b : ℝ)
    (hU : ∀ z : UpperHalfPlane, z.re ∈ Ioo L R → z.im ∈ Ioo a b →
      z ∈ reducedCarrier N)
    (hs : ∀ t, tsupport (T t).horizontal ⊆ Ioo L R ∧
      tsupport (T t).vertical ⊆ Ioo a b) :
    finiteCompactTensorSupportK s (fun t => (T t).toCompactTensor) ⊆ reducedCarrier N := by
  intro z hz
  obtain ⟨t, ht⟩ := mem_iUnion.mp hz
  exact hU z ((hs t).1 ht.1) ((hs t).2 ht.2)

end
end ImbalancedChen.Part3.LocalH1Tests20261026b
