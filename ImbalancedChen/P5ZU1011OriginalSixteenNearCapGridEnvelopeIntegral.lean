import ImbalancedChen.P5ZU1011OriginalSixteenNearCapGridProfiles
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual near-cap native grid envelope: one-sided original integral bound

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

M(n), eta(n), all original15/W native parameters, and the certified bank
are fixed by the rational box before N and every tuple. Only actual
WholeBoxEligibleTest-certified native costs occur; all other tags read
the unchanged actual switched fallback. Finite Ico ownership makes this
a measurable fixed-cell native program.

The actual buffer data have already been constructed without a buffer
premise. ALL16 separate tests eventually equal actual eligibility, and
the exact native/safephysical profile dictionary gives eventual pointwise
agreement with that constructed buffered envelope. Correct high-knot
nullity and the genuine weighted switched domination then prove positive
weighted native excess integral->0. Hence nativeIntegral<=original+eps
eventually. The full clamp, including raw ratio2, is retained. No
absolute/equality clamp limit, H248 density licence, AP or count theorem
is asserted.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenNearCapGridEnvelopeIntegral

noncomputable section

open Set MeasureTheory Filter Topology U11Integral U11Canonical Part5UpperTables
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSixteenTightGridLocalGeometry
open U1011OriginalSixteenNearCapGridBufferData U1011OriginalSixteenNearCapGridProfiles
open BufferedOrdinaryOffKnots
open OriginalSixteenEnvelopeBoxBounds (actualEnvelope)
open scoped BigOperators
open Classical

def switched : LogFour → ℝ := switchedKernel currentK LiLiuPrereqBuchstab.buchstab

def policyNativeCost (n : ℕ) (p : Policy) (v : LogFour) : ℝ := switched v +
  ∑ j : Index (meshLevel n), if Certified n p j then
    (cell (meshLevel n) j).indicator
      (fun w => U1011OriginalSixteenNearCapBoxProfiles.nativeCost p (box n j) (eta n) - switched w) v
    else 0

def nativeKernel (n j : ℕ) (v : LogFour) : ℝ :=
  if hj : j < 16 then policyNativeCost n ⟨j, hj⟩ v else switched v
def nativeCandidate (n : ℕ) : ℕ → LogFour → ℝ := guarded eligible switched (nativeKernel n)
def nativeEnvelope (n : ℕ) : LogFour → ℝ := envelope bank (nativeCandidate n)
def nativeExcess (n : ℕ) (v : LogFour) : ℝ := max 0 (nativeEnvelope n v - actualEnvelope v)
def weightedNativeExcess (n : ℕ) (v : LogFour) : ℝ := nativeExcess n v * harmonicDensity v
def nativeIntegral (n : ℕ) : ℝ := ∫ v in originalDomain ∅, nativeEnvelope n v * harmonicDensity v

theorem original_point_in_cube {v : LogFour} (hv : v ∈ originalDomain ∅) : v ∈ cube := by
  have h := U1011OriginalSixteenFullHarmonic.domain_subset_box hv
  simpa only [U1011OriginalSixteenFullHarmonic.box, cube, a, b] using h

theorem policyNativeCost_eq_owner (n : ℕ) (p : Policy) {v : LogFour} (hv : v ∈ cube) :
    policyNativeCost n p v = if Certified n p (owner (meshLevel n) v) then
      U1011OriginalSixteenNearCapBoxProfiles.nativeCost p (box n (owner (meshLevel n) v)) (eta n)
      else switched v := by
  unfold policyNativeCost
  rw [Finset.sum_eq_single (owner (meshLevel n) v)]
  · by_cases ht : Certified n p (owner (meshLevel n) v)
    · simp only [if_pos ht, indicator_of_mem (owner_mem _ hv)]
      ring
    · simp only [if_neg ht, add_zero]
  · intro j hj hne
    have hnot : v ∉ cell (meshLevel n) j := fun h => hne (owner_unique _ hv h)
    by_cases ht : Certified n p j <;> simp only [ht, if_true, if_false, indicator_of_notMem hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem measurable_policyNativeCost (n : ℕ) (p : Policy) : Measurable (policyNativeCost n p) := by
  have hs : Measurable switched :=
    measurable_switchedKernel currentK _ LiLiuPrereqBuchstab.continuous_buchstab.measurable
  apply hs.add
  apply Finset.measurable_sum
  intro j hj
  by_cases ht : Certified n p j
  · simpa only [if_pos ht] using (measurable_const.sub hs).indicator (cell_measurable _ j)
  · simp only [if_neg ht]
    exact measurable_const

theorem measurable_nativeKernel (n j : ℕ) : Measurable (nativeKernel n j) := by
  by_cases hj : j < 16
  · simpa only [nativeKernel, dif_pos hj] using measurable_policyNativeCost n ⟨j, hj⟩
  · simpa only [nativeKernel, dif_neg hj] using
      measurable_switchedKernel currentK _ LiLiuPrereqBuchstab.continuous_buchstab.measurable

theorem measurable_nativeEnvelope (n : ℕ) : Measurable (nativeEnvelope n) := by
  apply measurable_envelope
  apply measurable_guarded
  · intro j hj
    exact measurableSet_eligible j
  · exact measurable_switchedKernel currentK _ LiLiuPrereqBuchstab.continuous_buchstab.measurable
  · intro j hj
    exact measurable_nativeKernel n j

theorem nativeCost_nonneg (n : ℕ) (p : Policy) (j : Index (meshLevel n)) (ht : Certified n p j) :
    0 ≤ U1011OriginalSixteenNearCapBoxProfiles.nativeCost p (box n j) (eta n) := by
  have hR : (0 : ℝ) < (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p (box n j) (eta n) : ℝ) := by
    have hh := (certified_profile_floors n p j ht).1
    have hhR : (a : ℝ) ≤ (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p (box n j) (eta n) : ℝ) := by
      exact_mod_cast hh
    exact lt_of_lt_of_le (by norm_num [a]) hhR
  have hH := H248_bounds ((U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p (box n j) (eta n) : ℝ) /
    (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p (box n j) (eta n) : ℝ))
  exact div_nonneg (by linarith only [hH.2]) hR.le

theorem nativeKernel_nonneg (n j : ℕ) {v : LogFour} (hv : v ∈ originalDomain ∅) : 0 ≤ nativeKernel n j v := by
  have hs : 0 ≤ switched v := canonical_switched_nonneg ∅ currentK (by norm_num [currentK]) v hv
  by_cases hj : j < 16
  · simp only [nativeKernel, dif_pos hj]
    rw [policyNativeCost_eq_owner _ _ (original_point_in_cube hv)]
    by_cases ht : Certified n (⟨j, hj⟩ : Policy) (owner (meshLevel n) v)
    · rw [if_pos ht]
      exact nativeCost_nonneg n _ _ ht
    · rw [if_neg ht]
      exact hs
  · simpa only [nativeKernel, dif_neg hj] using hs

theorem nativeEnvelope_bounds (n : ℕ) {v : LogFour} (hv : v ∈ originalDomain ∅) :
    0 ≤ nativeEnvelope n v ∧ nativeEnvelope n v ≤ switched v := by
  apply guarded_envelope_bounds (originalDomain ∅) bank eligible switched (nativeKernel n)
  · exact canonical_switched_nonneg ∅ currentK (by norm_num [currentK])
  · intro j hj w hw he
    exact nativeKernel_nonneg n j hw
  · exact hv

/-- The certified bank eventually equals the actual bank at the SAME
point, and every retained fixed native profile is the exact constructed
physical profile. There is no supplied agreement predicate. -/
theorem eventually_nativeEnvelope_eq_actual_physical {v : LogFour} (hv : v ∈ cube) :
    ∀ᶠ n : ℕ in atTop, nativeEnvelope n v =
      U1011OriginalSixteenBufferedEnvelopeIntegral.physicalEnvelope actualBufferData n v := by
  filter_upwards [eventually_all_actual_wholeBox_tests hv] with n hbank
  have hcandidate (c : ℕ) (hc : c ∈ tags bank) : nativeCandidate n c v =
      U1011OriginalSixteenBufferedEnvelopeIntegral.physicalCandidate actualBufferData n c v := by
    rcases Finset.mem_insert.mp hc with hzero | hc
    · subst c
      rfl
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
      have hj16 : j < 16 := Finset.mem_range.mp hj
      let p : Policy := ⟨j, hj16⟩
      by_cases he : eligible j v
      · have heP : TypedEligible p v := by simpa only [eligible, dif_pos hj16] using he
        have ht := (hbank p).mpr heP
        have hprofile : policyNativeCost n p v =
            U1011OriginalSixteenBufferedEnvelopeIntegral.physicalOrdinary actualBufferData n p v := by
          rw [policyNativeCost_eq_owner n p hv, if_pos ht]
          exact nativeCost_eq_actual_physical n p hv ht
        simpa only [nativeCandidate, nativeKernel,
          U1011OriginalSixteenBufferedEnvelopeIntegral.physicalCandidate,
          U1011OriginalSixteenBufferedEnvelopeIntegral.physicalKernel,
          guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_pos he, dif_pos hj16] using hprofile
      · simpa only [nativeCandidate, U1011OriginalSixteenBufferedEnvelopeIntegral.physicalCandidate,
          guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_neg he] using
          (rfl : switched v = U1011OriginalSixteenBufferedEnvelopeIntegral.switched v)
  unfold nativeEnvelope U1011OriginalSixteenBufferedEnvelopeIntegral.physicalEnvelope envelope
  apply congrArg sInf
  ext q
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, (hcandidate c hc).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, hcandidate c hc⟩

theorem nativeExcess_bounds (n : ℕ) {v : LogFour} (hv : v ∈ originalDomain ∅) :
    0 ≤ nativeExcess n v ∧ nativeExcess n v ≤ switched v := by
  have hp := nativeEnvelope_bounds n hv
  have ho : 0 ≤ actualEnvelope v := (U1011OriginalSixteenReassembly.actualMinimum_bounds ∅ v hv).1
  exact ⟨le_max_left _ _, max_le (by linarith only [hp.1, hp.2]) (by linarith only [hp.2, ho])⟩

theorem nativeExcess_tendsto_zero {v : LogFour} (hv : v ∈ originalDomain ∅)
    (hknots : ∀ p : Policy, HighOffKnots (typedResidual p v / v 3)) :
    Tendsto (fun n => nativeExcess n v) atTop (𝓝 0) := by
  have ht := U1011OriginalSixteenBufferedEnvelopeIntegral.envelopeExcess_tendsto_zero actualBufferData hv hknots
  apply ht.congr'
  filter_upwards [eventually_nativeEnvelope_eq_actual_physical (original_point_in_cube hv)] with n hn
  simp only [nativeExcess, U1011OriginalSixteenBufferedEnvelopeIntegral.envelopeExcess, hn]

theorem measurable_weightedNativeExcess (n : ℕ) : Measurable (weightedNativeExcess n) := by
  have he : Measurable (nativeExcess n) := measurable_const.max
    ((measurable_nativeEnvelope n).sub U1011OriginalSixteenReassembly.measurable_actualMinimum)
  exact he.mul (by unfold harmonicDensity; fun_prop)

theorem weightedNativeExcess_domination (n : ℕ) {v : LogFour} (hv : v ∈ originalDomain ∅) :
    0 ≤ weightedNativeExcess n v ∧ weightedNativeExcess n v ≤ harmonicDensity v * switched v := by
  have he := nativeExcess_bounds n hv
  have hd := U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hv
  exact ⟨mul_nonneg he.1 hd, by simpa only [weightedNativeExcess, mul_comm] using
    mul_le_mul_of_nonneg_right he.2 hd⟩

theorem weightedNativeExcess_integrable (n : ℕ) :
    IntegrableOn (weightedNativeExcess n) (originalDomain ∅) volume := by
  apply (integrableOn_original_weighted_switched ∅ currentK).mono_nonneg
    (measurable_weightedNativeExcess n).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
    exact (weightedNativeExcess_domination n hv).1
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
    exact (weightedNativeExcess_domination n hv).2

theorem tendsto_integral_actual_native_positive_excess :
    Tendsto (fun n => ∫ v in originalDomain ∅, weightedNativeExcess n v) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (originalDomain ∅)) (fun v => harmonicDensity v * switched v)
    (fun n => (measurable_weightedNativeExcess n).aestronglyMeasurable)
    (integrableOn_original_weighted_switched ∅ currentK)
    (fun n => by
      filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (weightedNativeExcess_domination n hv).1]
      exact (weightedNativeExcess_domination n hv).2)
    (show ∀ᵐ v ∂volume.restrict (originalDomain ∅),
      Tendsto (fun n => weightedNativeExcess n v) atTop (𝓝 0) from by
      filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty),
        ae_restrict_of_ae U1011OriginalSixteenBufferedEnvelopeIntegral.ae_highOffKnots] with v hv hn
      have hw : v 3 ≠ 0 := (originalDomain_denominators_pos ∅ v hv).1.ne'
      simpa only [weightedNativeExcess, zero_mul] using
        (nativeExcess_tendsto_zero hv (fun p => hn p hw)).mul_const (harmonicDensity v))
  simpa only [integral_zero] using ht

theorem native_weighted_integrable (n : ℕ) :
    IntegrableOn (fun v => nativeEnvelope n v * harmonicDensity v) (originalDomain ∅) volume := by
  have hm : Measurable (fun v => nativeEnvelope n v * harmonicDensity v) :=
    (measurable_nativeEnvelope n).mul (by unfold harmonicDensity; fun_prop)
  apply (integrableOn_original_weighted_switched ∅ currentK).mono_nonneg hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
    exact mul_nonneg (nativeEnvelope_bounds n hv).1
      (U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hv)
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (nativeEnvelope_bounds n hv).2
      (U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hv)

/-- The actual fixed native-grid caller, with NO artificial buffer data
premise, has the correct one-sided original target integral bound. -/
theorem eventually_actual_nativeIntegral_le_original (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, nativeIntegral n ≤
      U1011OriginalSixteenRationalIntegralCertificates.fullIntegral + epsilon := by
  have hO := U1011OriginalSixteenReassembly.integrableOn_weighted_actualMinimum ∅ measurableSet_empty
  filter_upwards [tendsto_integral_actual_native_positive_excess.eventually (gt_mem_nhds hepsilon)] with n hn
  have hE := weightedNativeExcess_integrable n
  have hle := setIntegral_mono_on (native_weighted_integrable n) (hO.add hE)
    (measurableSet_originalDomain ∅ measurableSet_empty) (fun v hv => by
      have he := le_max_right 0 (nativeEnvelope n v - actualEnvelope v)
      have hc : nativeEnvelope n v ≤ actualEnvelope v + nativeExcess n v := by linarith only [he]
      have hd := U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hv
      simpa only [weightedNativeExcess, add_mul] using mul_le_mul_of_nonneg_right hc hd)
  rw [integral_add hO hE] at hle
  have htarget := U1011OriginalSixteenBufferedEnvelopeIntegral.originalIntegral_eq_actual_fullIntegral
  change nativeIntegral n ≤ U1011OriginalSixteenBufferedEnvelopeIntegral.originalIntegral +
    ∫ v in originalDomain ∅, weightedNativeExcess n v at hle
  rw [htarget] at hle
  exact hle.trans (add_le_add_left hn.le _)

end

end ImbalancedChen.P5Z.U1011OriginalSixteenNearCapGridEnvelopeIntegral
