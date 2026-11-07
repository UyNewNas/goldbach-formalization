import ImbalancedChen.P5ZU1011OriginalSixteenBufferedCandidate
import ImbalancedChen.P5ZU1011OriginalSixteenTightOrdinaryEndpointLimits
import ImbalancedChen.P5ZU1011OriginalSixteenRationalIntegralCertificates
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# One-sided physical-to-original integral transport for actual original16

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Measurable geometric buffers may vary with the actual point. Their
primitive data are only measurability, nonnegativity and size<=1/(n+1).
The original eligibility is frozen. All16 physical ordinary costs and
the unchanged actual switched fallback enter ONE actual finite minimum.

Only the positive excess over the ORIGINAL minimum is transported.
An attained original winner bounds that excess by its physical ordinary
positive excess, or by zero for the switched winner. Proper actual query
walls51..200 are null; the full clamp including raw ratio2 is retained.
The actual integrable weighted switched fallback supplies domination.

The positive weighted excess integral tends zero, hence the physical
integral is eventually at most originalFullIntegral+epsilon. No absolute
clamp-cost convergence, boundary/error/mean estimate or desired cost
convergence is assumed as a supplier.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenBufferedEnvelopeIntegral

noncomputable section

open Set MeasureTheory Filter Topology U11Integral U11Canonical Part5UpperTables
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenBufferedCandidate
open BufferedOrdinaryOffKnots U1011OriginalSixteenResidualWalls
open U1011OriginalSixteenTightOrdinaryEndpointLimits (exists_actual_cap_branch)
open OriginalSixteenEnvelopeBoxBounds (actualEnvelope)
open Classical

/-- Point-dependent primitive geometric buffer data. These fields contain
no cost inequality, asymptotic mean, boundary mass or convergence target. -/
structure GeometricBufferData where
  tau : ℕ → Policy → LogFour → ℝ
  xi : ℕ → Policy → LogFour → ℝ
  rho : ℕ → Policy → LogFour → ℝ
  measurable_tau : ∀ n p, Measurable (tau n p)
  measurable_xi : ∀ n p, Measurable (xi n p)
  measurable_rho : ∀ n p, Measurable (rho n p)
  tau_mem : ∀ n p v, tau n p v ∈ Icc 0 (bufferRate n)
  xi_mem : ∀ n p v, xi n p v ∈ Icc 0 (bufferRate n)
  rho_mem : ∀ n p v, rho n p v ∈ Icc 0 (bufferRate n)

def GeometricBufferData.atPoint (B : GeometricBufferData) (v : LogFour) : BufferData where
  tau := fun n p => B.tau n p v
  xi := fun n p => B.xi n p v
  rho := fun n p => B.rho n p v
  tau_mem := fun n p => B.tau_mem n p v
  xi_mem := fun n p => B.xi_mem n p v
  rho_mem := fun n p => B.rho_mem n p v

def physicalOrdinary (B : GeometricBufferData) (n : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  U1011OriginalSixteenBufferedCandidate.physicalOrdinary (B.atPoint v) n p v

theorem measurable_physicalOrdinary (B : GeometricBufferData) (n : ℕ) (p : Policy) :
    Measurable (physicalOrdinary B n p) := by
  have hR : Measurable (fun v => max clip (typedResidual p v - B.tau n p v)) :=
    measurable_const.max
      ((((continuous_cap p).sub U11SelectedLargest.continuous_prefixSum).measurable).sub (B.measurable_tau n p))
  have hw : Measurable (fun v => max clip (v 3 - B.xi n p v)) :=
    measurable_const.max ((measurable_pi_apply 3).sub (B.measurable_xi n p))
  exact (measurable_const.mul (measurable_const.sub
    (measurable_H248.comp ((measurable_const.add (B.measurable_rho n p)).max (hR.div hw))))).div hR

def switched : LogFour → ℝ := switchedKernel currentK LiLiuPrereqBuchstab.buchstab
def physicalKernel (B : GeometricBufferData) (n j : ℕ) (v : LogFour) : ℝ :=
  if hj : j < 16 then physicalOrdinary B n ⟨j, hj⟩ v else 0
def physicalCandidate (B : GeometricBufferData) (n : ℕ) : ℕ → LogFour → ℝ :=
  guarded eligible switched (physicalKernel B n)
def originalCandidate : ℕ → LogFour → ℝ := guarded eligible switched (ordinaryKernel H248 residual)
def physicalEnvelope (B : GeometricBufferData) (n : ℕ) : LogFour → ℝ := envelope bank (physicalCandidate B n)
def envelopeExcess (B : GeometricBufferData) (n : ℕ) (v : LogFour) : ℝ :=
  max 0 (physicalEnvelope B n v - actualEnvelope v)
def weightedExcess (B : GeometricBufferData) (n : ℕ) (v : LogFour) : ℝ :=
  envelopeExcess B n v * harmonicDensity v
def physicalIntegral (B : GeometricBufferData) (n : ℕ) : ℝ :=
  ∫ v in originalDomain ∅, physicalEnvelope B n v * harmonicDensity v
def originalIntegral : ℝ := ∫ v in originalDomain ∅, actualEnvelope v * harmonicDensity v

theorem physicalKernel_nonneg (B : GeometricBufferData) (n j : ℕ) (v : LogFour) :
    0 ≤ physicalKernel B n j v := by
  by_cases hj : j < 16
  · simpa only [physicalKernel, dif_pos hj, physicalOrdinary] using
      (physicalOrdinary_bounds (B.atPoint v) n ⟨j, hj⟩ v).1
  · simp only [physicalKernel, dif_neg hj, le_refl]

theorem measurable_physicalKernel (B : GeometricBufferData) (n j : ℕ) :
    Measurable (physicalKernel B n j) := by
  by_cases hj : j < 16
  · simpa only [physicalKernel, dif_pos hj] using measurable_physicalOrdinary B n ⟨j, hj⟩
  · simp only [physicalKernel, dif_neg hj]
    exact measurable_const

theorem measurable_physicalEnvelope (B : GeometricBufferData) (n : ℕ) :
    Measurable (physicalEnvelope B n) := by
  apply measurable_envelope
  apply measurable_guarded
  · intro j hj
    exact measurableSet_eligible j
  · exact measurable_switchedKernel currentK _ LiLiuPrereqBuchstab.continuous_buchstab.measurable
  · intro j hj
    exact measurable_physicalKernel B n j

theorem physicalEnvelope_bounds (B : GeometricBufferData) (n : ℕ) {v : LogFour}
    (hv : v ∈ originalDomain ∅) : 0 ≤ physicalEnvelope B n v ∧ physicalEnvelope B n v ≤ switched v := by
  apply guarded_envelope_bounds (originalDomain ∅) bank eligible switched (physicalKernel B n)
  · exact canonical_switched_nonneg ∅ currentK (by norm_num [currentK])
  · intro j hj w hw he
    exact physicalKernel_nonneg B n j w
  · exact hv

theorem envelopeExcess_bounds (B : GeometricBufferData) (n : ℕ) {v : LogFour}
    (hv : v ∈ originalDomain ∅) : 0 ≤ envelopeExcess B n v ∧ envelopeExcess B n v ≤ switched v := by
  have hp := physicalEnvelope_bounds B n hv
  have ho : 0 ≤ actualEnvelope v := (U1011OriginalSixteenReassembly.actualMinimum_bounds ∅ v hv).1
  exact ⟨le_max_left _ _, max_le ((by linarith only [hp.1, hp.2])) (by linarith only [hp.2, ho])⟩

theorem envelopeExcess_explicit_bound (B : GeometricBufferData) (n : ℕ) {v : LogFour}
    (hv : v ∈ originalDomain ∅) : envelopeExcess B n v ≤ currentK / a := by
  have h := abs_canonical_switched_le ∅ currentK v hv
  have hK : 0 ≤ currentK := by norm_num [currentK]
  rw [abs_of_nonneg hK] at h
  have hs : switched v ≤ currentK / a := by
    exact (le_abs_self _).trans (by simpa only [switched, a] using h)
  exact (envelopeExcess_bounds B n hv).2.trans hs

theorem measurable_weightedExcess (B : GeometricBufferData) (n : ℕ) :
    Measurable (weightedExcess B n) := by
  have hE : Measurable (envelopeExcess B n) := measurable_const.max
    ((measurable_physicalEnvelope B n).sub U1011OriginalSixteenReassembly.measurable_actualMinimum)
  have hD : Measurable harmonicDensity := by unfold harmonicDensity; fun_prop
  exact hE.mul hD

abbrev HighQueryIndex := Policy × Bool × Fin 150
def highQueryForms (t : HighQueryIndex) : LogFour →L[ℝ] ℝ :=
  queryGate t.1 t.2.1 (Part5OriginalUpsilon5CausalDictionary.floorGrid (51 + t.2.2.val))
def highQueryBounds (t : HighQueryIndex) : ℝ := -capOffset t.1 t.2.1

theorem highQueryForms_ne_zero (t : HighQueryIndex) : highQueryForms t ≠ 0 := queryGate_ne_zero _ _ _

/-- ONLY51..200 are removed as null equality surfaces. Raw query2 and
the entire positive-measure clamp half-space remain in the pointwise theorem. -/
theorem ae_highOffKnots : ∀ᵐ v : LogFour ∂volume,
    ∀ p : Policy, v 3 ≠ 0 → HighOffKnots (typedResidual p v / v 3) := by
  filter_upwards [ae_primeAffineGate_no_wall highQueryForms highQueryBounds highQueryForms_ne_zero] with v hv
  intro p hw j heq
  obtain ⟨left, hleft⟩ := exists_actual_cap_branch p v
  have hres := (div_eq_iff hw).mp heq
  have hwall := (queryGate_eq_dictionary p left
    (Part5OriginalUpsilon5CausalDictionary.floorGrid (51 + j.val)) v hleft).mp hres
  exact hv (p, left, j) hwall

/-- An attained ORIGINAL winner is compared with its buffered candidate.
This preserves the actual nonlinear minimum and proves only its positive excess. -/
theorem envelopeExcess_tendsto_zero (B : GeometricBufferData) {v : LogFour}
    (hv : v ∈ originalDomain ∅) (hn : ∀ p : Policy, HighOffKnots (typedResidual p v / v 3)) :
    Tendsto (fun n => envelopeExcess B n v) atTop (𝓝 0) := by
  obtain ⟨c, hc, hwin⟩ := exists_winner (originalDomain ∅) bank originalCandidate v hv
  have heq : originalCandidate c v = actualEnvelope v := hwin.2.1
  have hup (n : ℕ) : physicalEnvelope B n v ≤ physicalCandidate B n c v :=
    envelope_le bank (physicalCandidate B n) v c hc
  rcases Finset.mem_insert.mp hc with hzero | hc
  · subst c
    have heq0 : switched v = actualEnvelope v := by simpa only [originalCandidate, guarded, if_pos rfl] using heq
    have hz (n : ℕ) : envelopeExcess B n v = 0 := by
      have hu : physicalEnvelope B n v ≤ switched v := by simpa only [physicalCandidate, guarded, if_pos rfl] using hup n
      exact max_eq_left (by linarith only [hu, heq0])
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    have hj16 : j < 16 := Finset.mem_range.mp hj
    let p : Policy := ⟨j, hj16⟩
    by_cases he : eligible j v
    · have heP : TypedEligible p v := by simpa only [eligible, dif_pos hj16] using he
      have hEq : originalOrdinary p v = actualEnvelope v := by
        simpa only [originalCandidate, guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ,
          if_pos he, originalOrdinary] using heq
      have hUp (n : ℕ) : physicalEnvelope B n v ≤ physicalOrdinary B n p v := by
        simpa only [physicalCandidate, guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ,
          if_pos he, physicalKernel, dif_pos hj16] using hup n
      have ht := positiveExcess_tendsto_zero (B.atPoint v) p hv heP (hn p)
      apply squeeze_zero (g := fun n => positiveExcess (B.atPoint v) n p v)
      · intro n
        exact le_max_left _ _
      · intro n
        apply max_le_max le_rfl
        change physicalEnvelope B n v - actualEnvelope v ≤ physicalOrdinary B n p v - originalOrdinary p v
        rw [hEq]
        exact sub_le_sub_right (hUp n) _
      · exact ht
    · have hEq : switched v = actualEnvelope v := by
        simpa only [originalCandidate, guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_neg he] using heq
      have hz (n : ℕ) : envelopeExcess B n v = 0 := by
        have hUp : physicalEnvelope B n v ≤ switched v := by
          simpa only [physicalCandidate, guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_neg he] using hup n
        exact max_eq_left (by linarith only [hEq, hUp])
      simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem weightedExcess_domination (B : GeometricBufferData) (n : ℕ) {v : LogFour}
    (hv : v ∈ originalDomain ∅) : 0 ≤ weightedExcess B n v ∧
      weightedExcess B n v ≤ harmonicDensity v * switched v := by
  have hE := envelopeExcess_bounds B n hv
  have hD := U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hv
  exact ⟨mul_nonneg hE.1 hD, by simpa only [weightedExcess, mul_comm] using
    mul_le_mul_of_nonneg_right hE.2 hD⟩

theorem weightedExcess_integrable (B : GeometricBufferData) (n : ℕ) :
    IntegrableOn (weightedExcess B n) (originalDomain ∅) volume := by
  apply (integrableOn_original_weighted_switched ∅ currentK).mono_nonneg
    (measurable_weightedExcess B n).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
    exact (weightedExcess_domination B n hv).1
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
    exact (weightedExcess_domination B n hv).2

theorem tendsto_integral_positive_weighted_excess (B : GeometricBufferData) :
    Tendsto (fun n => ∫ v in originalDomain ∅, weightedExcess B n v) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (originalDomain ∅)) (fun v => harmonicDensity v * switched v)
    (fun n => (measurable_weightedExcess B n).aestronglyMeasurable)
    (integrableOn_original_weighted_switched ∅ currentK)
    (fun n => by
      filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (weightedExcess_domination B n hv).1]
      exact (weightedExcess_domination B n hv).2)
    (show ∀ᵐ v ∂volume.restrict (originalDomain ∅),
      Tendsto (fun n => weightedExcess B n v) atTop (𝓝 0) from by
      filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty),
        ae_restrict_of_ae ae_highOffKnots] with v hv hn
      have hw : v 3 ≠ 0 := (originalDomain_denominators_pos ∅ v hv).1.ne'
      simpa only [weightedExcess, zero_mul] using
        (envelopeExcess_tendsto_zero B hv (fun p => hn p hw)).mul_const (harmonicDensity v))
  simpa only [integral_zero] using ht

theorem physical_weighted_integrable (B : GeometricBufferData) (n : ℕ) :
    IntegrableOn (fun v => physicalEnvelope B n v * harmonicDensity v) (originalDomain ∅) volume := by
  have hm : Measurable (fun v => physicalEnvelope B n v * harmonicDensity v) :=
    (measurable_physicalEnvelope B n).mul (by unfold harmonicDensity; fun_prop)
  apply (integrableOn_original_weighted_switched ∅ currentK).mono_nonneg hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
    exact mul_nonneg (physicalEnvelope_bounds B n hv).1
      (U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hv)
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain ∅ measurableSet_empty)] with v hv
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (physicalEnvelope_bounds B n hv).2
      (U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hv)

theorem physicalIntegral_le_original_add_excess (B : GeometricBufferData) (n : ℕ) :
    physicalIntegral B n ≤ originalIntegral + ∫ v in originalDomain ∅, weightedExcess B n v := by
  have hO := U1011OriginalSixteenReassembly.integrableOn_weighted_actualMinimum ∅ measurableSet_empty
  have hE := weightedExcess_integrable B n
  have hle := setIntegral_mono_on (physical_weighted_integrable B n) (hO.add hE)
    (measurableSet_originalDomain ∅ measurableSet_empty) (fun v hv => by
      have hcost : physicalEnvelope B n v ≤ actualEnvelope v + envelopeExcess B n v := by
        have hh := le_max_right 0 (physicalEnvelope B n v - actualEnvelope v)
        linarith only [hh]
      have hd := U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hv
      have hh := mul_le_mul_of_nonneg_right hcost hd
      simpa only [weightedExcess, add_mul] using hh)
  rw [integral_add hO hE] at hle
  exact hle

theorem originalIntegral_eq_actual_fullIntegral : originalIntegral =
    U1011OriginalSixteenRationalIntegralCertificates.fullIntegral := by
  simp only [originalIntegral, U1011OriginalSixteenRationalIntegralCertificates.fullIntegral,
    U1011OriginalSourceGeometryMesh.sourceDomain,
    U1011OriginalSixteenRationalIntegralCertificates.weightedKernel,
    U1011OriginalSixteenRationalIntegralCertificates.weight,
    U1011OriginalSixteenFullHarmonic.harmonicDensity_eq_prod]

/-- Correct ONE-SIDED target integral transport. The complete original
clamp is retained, and no absolute/equality clamp limit is asserted. -/
theorem eventually_physicalIntegral_le_actual_original_add (B : GeometricBufferData)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, physicalIntegral B n ≤
      U1011OriginalSixteenRationalIntegralCertificates.fullIntegral + epsilon := by
  filter_upwards [(tendsto_integral_positive_weighted_excess B).eventually (gt_mem_nhds hepsilon)] with n hn
  have hle := physicalIntegral_le_original_add_excess B n
  rw [originalIntegral_eq_actual_fullIntegral] at hle
  exact hle.trans (add_le_add_left hn.le _)

end

end ImbalancedChen.P5Z.U1011OriginalSixteenBufferedEnvelopeIntegral
