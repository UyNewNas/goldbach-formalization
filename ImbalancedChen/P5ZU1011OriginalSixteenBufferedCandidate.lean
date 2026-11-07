import ImbalancedChen.P5ZU1011BufferedOrdinaryUpperApprox
import ImbalancedChen.P5ZU1011OriginalSixteenReassembly

/-!
# One-sided buffered physical ordinary candidates for actual original16

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The three small buffers are primitive scalar geometric data, uniformly
in the actual sixteen policies. Their only constraints are nonnegativity
and size at most1/(n+1). The original eligibility is frozen at the actual
point. Physical residual and w are safely clipped below at a/2.

The physical candidate is globally nonnegative and bounded by8/a. At an
actually eligible original point, its POSITIVE excess over the original
ordinary cost tends zero under the literal high-knot exclusion51..200.
The entire clamp, including raw query2, is retained by the scalar proof.
No absolute/equality convergence of the clamped cost is asserted.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenBufferedCandidate

noncomputable section

open Set MeasureTheory Filter Topology U11Integral Part5UpperTables
open U1011OriginalSixteenPolicyBank BufferedOrdinaryClamp BufferedOrdinaryUpperApprox
open BufferedOrdinaryOffKnots
open Classical

def a : ℝ := 417 / 5000
def clip : ℝ := a / 2
def bufferRate (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Genuine buffer geometry; no cost or convergence conclusion is a
field. Buffers are scalar for each actual policy, hence measurable. -/
structure BufferData where
  tau : ℕ → Policy → ℝ
  xi : ℕ → Policy → ℝ
  rho : ℕ → Policy → ℝ
  tau_mem : ∀ n p, tau n p ∈ Icc 0 (bufferRate n)
  xi_mem : ∀ n p, xi n p ∈ Icc 0 (bufferRate n)
  rho_mem : ∀ n p, rho n p ∈ Icc 0 (bufferRate n)

theorem clip_pos : 0 < clip := by norm_num [clip, a]

theorem buffers_eventually_small (B : BufferData) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Policy,
      B.tau n p < eta ∧ B.xi n p < eta ∧ B.rho n p < eta := by
  have ht : Tendsto bufferRate atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds heta)] with n hn
  intro p
  exact ⟨((B.tau_mem n p).2).trans_lt hn, ((B.xi_mem n p).2).trans_lt hn,
    ((B.rho_mem n p).2).trans_lt hn⟩

def physicalResidual (B : BufferData) (n : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  max clip (typedResidual p v - B.tau n p)
def physicalW (B : BufferData) (n : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  max clip (v 3 - B.xi n p)
def physicalOrdinary (B : BufferData) (n : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  4 * (1 - H248 (max (2 + B.rho n p) (physicalResidual B n p v / physicalW B n p v))) /
    physicalResidual B n p v
def originalOrdinary (p : Policy) (v : LogFour) : ℝ := ordinaryKernel H248 residual p.val v
def positiveExcess (B : BufferData) (n : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  max 0 (physicalOrdinary B n p v - originalOrdinary p v)
def eligibleExcess (B : BufferData) (n : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  if TypedEligible p v then positiveExcess B n p v else 0

theorem physicalOrdinary_bounds (B : BufferData) (n : ℕ) (p : Policy) (v : LogFour) :
    0 ≤ physicalOrdinary B n p v ∧ physicalOrdinary B n p v ≤ 8 / a := by
  have hR : clip ≤ physicalResidual B n p v := le_max_left _ _
  have hRp : 0 < physicalResidual B n p v := clip_pos.trans_le hR
  have hH := H248_bounds (max (2 + B.rho n p) (physicalResidual B n p v / physicalW B n p v))
  have hN0 : 0 ≤ 4 * (1 - H248 (max (2 + B.rho n p)
      (physicalResidual B n p v / physicalW B n p v))) := by linarith only [hH.2]
  have hN4 : 4 * (1 - H248 (max (2 + B.rho n p)
      (physicalResidual B n p v / physicalW B n p v))) ≤ 4 := by linarith only [hH.1]
  refine ⟨div_nonneg hN0 hRp.le, ?_⟩
  have hh := (div_le_div_of_nonneg_right hN4 hRp.le).trans
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) clip_pos hR)
  have hclip : (4 : ℝ) / clip = 8 / a := by norm_num [clip, a]
  simpa only [physicalOrdinary, hclip] using hh

theorem originalOrdinary_eq_scalar (p : Policy) (v : LogFour) :
    originalOrdinary p v = originalCost (typedResidual p v) (v 3) := by
  simp only [originalOrdinary, ordinaryKernel, residual, dif_pos p.isLt, originalCost]

theorem eligibleExcess_bounds (B : BufferData) (n : ℕ) (p : Policy) {v : LogFour}
    (hv : v ∈ originalDomain ∅) : 0 ≤ eligibleExcess B n p v ∧ eligibleExcess B n p v ≤ 8 / a := by
  by_cases he : TypedEligible p v
  · have h0 : 0 ≤ originalOrdinary p v :=
      (ordinary_actual_bounds ∅ p.val v hv (by simpa [eligible, dif_pos p.isLt] using he)).1
    have hP := physicalOrdinary_bounds B n p v
    simp only [eligibleExcess, if_pos he, positiveExcess]
    exact ⟨le_max_left _ _, max_le (by norm_num [a]) (by linarith only [h0, hP.2])⟩
  · simp only [eligibleExcess, if_neg he, le_refl]
    norm_num [a]

theorem measurable_physicalOrdinary (B : BufferData) (n : ℕ) (p : Policy) :
    Measurable (physicalOrdinary B n p) := by
  have hR : Measurable (physicalResidual B n p) := by
    unfold physicalResidual typedResidual
    exact measurable_const.max
      ((((continuous_cap p).sub U11SelectedLargest.continuous_prefixSum).measurable).sub measurable_const)
  have hw : Measurable (physicalW B n p) :=
    measurable_const.max ((measurable_pi_apply 3).sub measurable_const)
  exact (measurable_const.mul (measurable_const.sub
    (measurable_H248.comp (measurable_const.max (hR.div hw))))).div hR

theorem measurable_eligibleExcess (B : BufferData) (n : ℕ) (p : Policy) :
    Measurable (eligibleExcess B n p) := by
  have hO : Measurable (originalOrdinary p) :=
    measurable_ordinaryKernel H248 residual p.val measurable_H248 (measurable_residual p.val)
  have hP : Measurable (positiveExcess B n p) :=
    measurable_const.max ((measurable_physicalOrdinary B n p).sub hO)
  exact Measurable.ite (measurableSet_typedEligible p) hP measurable_const

/-- One-sided pointwise transport, including the ENTIRE actual clamp.
The only knot exclusion is the literal high-knot predicate51..200. -/
theorem positiveExcess_tendsto_zero (B : BufferData) (p : Policy) {v : LogFour}
    (hv : v ∈ originalDomain ∅) (he : TypedEligible p v)
    (hknots : HighOffKnots (typedResidual p v / v 3)) :
    Tendsto (fun n => positiveExcess B n p v) atTop (𝓝 0) := by
  have hw : 0 < v 3 := (originalDomain_denominators_pos ∅ v hv).1
  have hR : 0 < typedResidual p v := hw.trans (typedEligible_residual_gt_smallest p v he)
  have hbase : a ≤ v 3 := hv.1
  have hwclip : clip < v 3 := by norm_num [clip, a] at hbase ⊢; linarith only [hbase]
  have hRclip : clip < typedResidual p v := hwclip.trans (typedEligible_residual_gt_smallest p v he)
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨eta, heta, hupper⟩ := exists_physical_upper_scale (typedResidual p v) (v 3)
    hR hw hknots (eps / 2) (by positivity)
  let theta := min eta (min (typedResidual p v - clip) (v 3 - clip))
  have htheta : 0 < theta := lt_min heta (lt_min (sub_pos.mpr hRclip) (sub_pos.mpr hwclip))
  filter_upwards [buffers_eventually_small B theta htheta] with n hn
  have hnt := hn p
  have htEta : B.tau n p < eta := hnt.1.trans_le (min_le_left _ _)
  have hxEta : B.xi n p < eta := hnt.2.1.trans_le (min_le_left _ _)
  have hrEta : B.rho n p < eta := hnt.2.2.trans_le (min_le_left _ _)
  have htClip : clip ≤ typedResidual p v - B.tau n p := by
    have hh := hnt.1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [hh]
  have hxClip : clip ≤ v 3 - B.xi n p := by
    have hh := hnt.2.1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith only [hh]
  have hcost := hupper (B.tau n p) (B.xi n p) (B.rho n p)
    (B.tau_mem n p).1 htEta (B.xi_mem n p).1 hxEta (B.rho_mem n p).1 hrEta
  have heq : physicalOrdinary B n p v =
      physicalCost (typedResidual p v) (v 3) (B.tau n p) (B.xi n p) (B.rho n p) := by
    simp only [physicalOrdinary, physicalResidual, physicalW, max_eq_right htClip,
      max_eq_right hxClip, physicalCost, physicalQuery]
  rw [← heq, ← originalOrdinary_eq_scalar] at hcost
  have hpos : positiveExcess B n p v ≤ eps / 2 :=
    max_le (by positivity) (by dsimp only [positiveExcess]; linarith only [hcost])
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _)]
  exact hpos.trans_lt (by linarith only [heps])

end

end ImbalancedChen.P5Z.U1011OriginalSixteenBufferedCandidate
