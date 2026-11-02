import Mathlib
import ImbalancedChen.Part3TwoLongN2FourierDecay
import ImbalancedChen.Part3TwoLongThreeBrunInternalP2

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual D transition is multiplied by the literal Mellin phase and,
when the original HB role is logarithm, by log U + log x. Constants are
fixed before delta, U, the frequency cube, labels and Brun divisors.
No profile norm, Fourier decay, P1 or P2 estimate is a premise.
-/
namespace ImbalancedChen.Part3.TwoLongTransitionMellinN2
noncomputable section
open Classical Set Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b
open ImbalancedChen.Part3.TwoLongLiteralMellinModes (N2)
open ImbalancedChen.Part3.TwoLongQuantitativeTransitionProfiles
open ImbalancedChen.Part3.TwoLongN2FourierDecay

def window : Set ℝ := Icc (1/2 : ℝ) (5/2)

theorem compact_of_support {f : ℝ → ℂ} (hs : Function.support f ⊆ window) :
    HasCompactSupport f := by
  change IsCompact (closure (Function.support f))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal hs isClosed_Icc)

/- The following product lemma is calculus, not an analytic estimate
interface. Both its factors are independently defined below. -/
theorem second_deriv_mul {f g : ℝ → ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    deriv (deriv (fun y => f y * g y)) x =
      deriv (deriv f) x * g x + 2 * deriv f x * deriv g x +
        f x * deriv (deriv g) x := by
  have hf1 := hf.derivWithin (m := 1) (by simp)
  have hg1 := hg.derivWithin (m := 1) (by simp)
  have hlf := (hf.of_le (m := 1) (by simp)).eventually (by norm_num)
  have hlg := (hg.of_le (m := 1) (by simp)).eventually (by norm_num)
  have he : deriv (fun y => f y * g y) =ᶠ[𝓝 x]
      (fun y => deriv f y * g y + f y * deriv g y) := by
    filter_upwards [hlf, hlg] with y hyf hyg
    exact ((hyf.differentiableAt (by simp)).hasDerivAt.mul
      (hyg.differentiableAt (by simp)).hasDerivAt).deriv
  have hd := ((hf1.differentiableAt (by simp)).hasDerivAt.mul
      (hg.differentiableAt (by simp)).hasDerivAt).add
    ((hf.differentiableAt (by simp)).hasDerivAt.mul
      (hg1.differentiableAt (by simp)).hasDerivAt)
  convert (hd.congr_of_eventuallyEq he).deriv using 1 <;> ring

def twisted (f : ℝ → ℂ) (t x : ℝ) : ℂ := f x * phase t x

theorem twisted_support (f : ℝ → ℂ) (t : ℝ)
    (hs : Function.support f ⊆ window) : Function.support (twisted f t) ⊆ window := by
  intro x hx
  apply hs
  intro hz
  exact hx (by simp [twisted, hz])

theorem phase_smoothAt (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (phase t) x := by
  have hl := Real.contDiffAt_log.mpr hx
  have hc : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
  exact (hc.const_mul (Complex.I * (t : ℂ))).cexp

theorem twisted_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ window) (t : ℝ) : ContDiff ℝ ∞ (twisted f t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have he : twisted f t =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2)] with y hy
      have hz : f y = 0 := by
        by_contra hn
        have h := (hs hn).1
        change 1/2 ≤ y at h
        linarith
      simp [twisted, hz]
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) 0).
      congr_of_eventuallyEq he
  · exact hf.contDiffAt.mul (phase_smoothAt t hx)

theorem phase_second {t x : ℝ} (hx : 0 < x) :
    deriv (deriv (phase t)) x = phase t x *
      ((Complex.I * (t : ℂ))^2 - Complex.I * (t : ℂ)) / (x : ℂ)^2 := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hi : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have hq := (hasDerivAt_const x (Complex.I * (t : ℂ))).div hi hxC
  have hd := (phase_hasDerivAt t hx).mul hq
  have he : deriv (phase t) =ᶠ[𝓝 x]
      (fun y => phase t y * (Complex.I * (t : ℂ) / (y : ℂ))) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (phase_hasDerivAt t hy).deriv
  convert (hd.congr_of_eventuallyEq he).deriv using 1 <;>
    field_simp [hxC] <;> ring

theorem reciprocal_window {x : ℝ} (hx : x ∈ window) :
    0 < x ∧ 1/x ≤ 2 ∧ 1/x^2 ≤ 4 := by
  have hx0 : 0 < x := by have h := hx.1; change 1/2 ≤ x at h; linarith
  refine ⟨hx0, (div_le_iff₀ hx0).2 (by have h := hx.1; change 1/2 ≤ x at h; linarith), ?_⟩
  apply (div_le_iff₀ (pow_pos hx0 2)).2
  have h := hx.1
  change 1/2 ≤ x at h
  nlinarith [sq_nonneg (x-1/2)]

theorem phase_jet_bounds (t : ℝ) {x : ℝ} (hx : x ∈ window) :
    ‖deriv (phase t) x‖ ≤ 2*|t| ∧
      ‖deriv (deriv (phase t)) x‖ ≤ 4*(|t|^2+|t|) := by
  obtain ⟨hx0, hr, hr2⟩ := reciprocal_window hx
  have hc : ‖Complex.I * (t : ℂ)‖ = |t| := by simp
  constructor
  · rw [(phase_hasDerivAt t hx0).deriv, norm_mul, phase_norm, one_mul,
      norm_div, hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    simpa only [div_eq_mul_inv, one_div, mul_comm] using
      mul_le_mul_of_nonneg_left hr (abs_nonneg t)
  · rw [phase_second hx0, norm_div, norm_mul, phase_norm, one_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have hnum : ‖(Complex.I*(t : ℂ))^2-Complex.I*(t : ℂ)‖ ≤ |t|^2+|t| := by
      exact (norm_sub_le _ _).trans_eq (by rw [norm_pow, hc])
    calc
      _ ≤ (|t|^2+|t|)/x^2 := div_le_div_of_nonneg_right hnum (sq_nonneg x)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ |t|^2+|t|)
        simpa only [div_eq_mul_inv, one_div, mul_comm] using h

/-- Fixed second-derivative budget from genuine local ordinary jets. -/
theorem twisted_N2_le {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ window) {M0 M1 M2 : ℝ}
    (h0 : ∀ x ∈ window, ‖f x‖ ≤ M0)
    (h1 : ∀ x ∈ window, ‖deriv f x‖ ≤ M1)
    (h2 : ∀ x ∈ window, ‖deriv (deriv f) x‖ ≤ M2) (t : ℝ) :
    N2 (twisted f t) ≤ 2*M0 + 2*(M2+4*M1*|t|+4*M0*(|t|^2+|t|)) := by
  have hmem : (1 : ℝ) ∈ window := by constructor <;> norm_num
  have hM0 : 0 ≤ M0 := (norm_nonneg _).trans (h0 1 hmem)
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans (h1 1 hmem)
  have hM2 : 0 ≤ M2 := (norm_nonneg _).trans (h2 1 hmem)
  have hsm := twisted_smooth hf hs t
  have hsup := twisted_support f t hs
  have hc := compact_of_support hsup
  have hi := hsm.continuous.integrable_of_hasCompactSupport hc
  have hd1 := (contDiff_infty_iff_deriv.mp hsm).2
  have hd2 := (contDiff_infty_iff_deriv.mp hd1).2
  have hi2 := hd2.continuous.integrable_of_hasCompactSupport hc.deriv.deriv
  have hsup2 : Function.support (deriv (deriv (twisted f t))) ⊆ window :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans
      (closure_minimal hsup isClosed_Icc))
  have hmass := norm_integral_le_two hi hsup M0 (fun x hx => by
    simpa only [twisted, norm_mul, phase_norm, mul_one] using h0 x hx)
  have hsecond := norm_integral_le_two hi2 hsup2
    (M2+4*M1*|t|+4*M0*(|t|^2+|t|)) (fun x hx => by
      obtain ⟨hp1, hp2⟩ := phase_jet_bounds t hx
      have hx0 := (reciprocal_window hx).1
      rw [twisted, second_deriv_mul hf.contDiffAt (phase_smoothAt t hx0.ne')]
      calc
        _ ≤ ‖deriv (deriv f) x‖*‖phase t x‖ +
            2*‖deriv f x‖*‖deriv (phase t) x‖ +
            ‖f x‖*‖deriv (deriv (phase t)) x‖ := by
          simpa only [norm_mul, norm_ofNat] using
            (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
        _ ≤ M2*1 + 2*M1*(2*|t|) + M0*(4*(|t|^2+|t|)) := by
          rw [phase_norm]
          gcongr
          · exact h2 x hx
          · exact h1 x hx
          · exact hp1
          · exact h0 x hx
          · exact hp2
        _ = _ := by ring)
  exact add_le_add hmass hsecond

/- Actual scalar logarithm; false is the genuine HB one-slot. -/
def logFactor (isLog : Bool) (U x : ℝ) : ℝ :=
  if isLog then Real.log U + Real.log x else 1

theorem log_abs_window {x : ℝ} (hx : x ∈ window) : |Real.log x| ≤ 2 := by
  have hx0 := (reciprocal_window hx).1
  have hupper := Real.log_le_sub_one_of_pos hx0
  have hlower := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
  rw [Real.log_inv] at hlower
  have hinv := (reciprocal_window hx).2.1
  rw [one_div] at hinv
  rw [abs_le]
  have hxhi := hx.2
  change x ≤ 5/2 at hxhi
  constructor <;> linarith

def logSize (U : ℝ) : ℝ := 3 + |Real.log U|

theorem logSize_one_le (U : ℝ) : 1 ≤ logSize U := by
  unfold logSize
  linarith [abs_nonneg (Real.log U)]

theorem logFactor_smoothAt (isLog : Bool) (U : ℝ) {x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (logFactor isLog U) x := by
  cases isLog
  · exact contDiffAt_const
  · exact contDiffAt_const.add (Real.contDiffAt_log.mpr hx)

theorem logFactor_first (isLog : Bool) (U : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (logFactor isLog U) x = if isLog then x⁻¹ else 0 := by
  cases isLog
  · simp [logFactor]
  · exact ((Real.hasDerivAt_log hx).const_add (Real.log U)).deriv

theorem logFactor_second (isLog : Bool) (U : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv (logFactor isLog U)) x = if isLog then -(x^2)⁻¹ else 0 := by
  cases isLog
  · simp [logFactor]
  · have he : deriv (logFactor true U) =ᶠ[𝓝 x] (fun y => y⁻¹) := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      exact logFactor_first true U hy
    simpa using
      (((hasDerivAt_id x).inv hx).congr_of_eventuallyEq he).deriv

theorem logFactor_bounds (isLog : Bool) (U : ℝ) {x : ℝ} (hx : x ∈ window) :
    |logFactor isLog U x| ≤ logSize U ∧
    |deriv (logFactor isLog U) x| ≤ 2 ∧
    |deriv (deriv (logFactor isLog U)) x| ≤ 4 := by
  obtain ⟨hx0, hr1, hr2⟩ := reciprocal_window hx
  rw [logFactor_first isLog U hx0.ne', logFactor_second isLog U hx0.ne']
  cases isLog
  · simp only [logFactor, Bool.false_eq_true, if_false, abs_one, abs_zero]
    exact ⟨logSize_one_le U, by norm_num, by norm_num⟩
  · simp only [logFactor, if_true, abs_neg, abs_inv,
      abs_of_pos hx0, abs_of_pos (pow_pos hx0 2)]
    refine ⟨?_, by simpa only [one_div] using hr1, by simpa only [one_div] using hr2⟩
    exact (abs_add _ _).trans (by
      have h := log_abs_window hx
      unfold logSize
      linarith)

/- One actual selector suffices for both left/right three-Brun labels. -/
def transition (isGap : Bool) (delta : ℝ) : ℝ → ℝ :=
  if isGap then gap delta else upper delta

theorem transition_smooth (isGap : Bool) (delta : ℝ) :
    ContDiff ℝ ∞ (transition isGap delta) := by
  cases isGap <;> simp only [transition, Bool.false_eq_true, if_false, if_true]
  · exact upper_smooth delta
  · exact gap_smooth delta

theorem transition_support (isGap : Bool) {delta : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) :
    Function.support (transition isGap delta) ⊆ window := by
  cases isGap
  · exact upper_support hd hs
  · exact gap_support hd hs

theorem gap_first_bound {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    |deriv (gap delta) x| ≤ 4*B 1/delta := by
  have hL := doubleStep_smooth delta (1-delta) (1+delta)
  have hR := doubleStep_smooth delta (2-delta) (2+delta)
  rw [show deriv (gap delta) x = deriv (endpoint delta 1) x + deriv (endpoint delta 2) x from
    (((hL.differentiable (by simp) x).hasDerivAt).add
      ((hR.differentiable (by simp) x).hasDerivAt)).deriv]
  exact (abs_add _ _).trans ((add_le_add
    (doubleStep_deriv_bound hd (1-delta) (1+delta) x)
    (doubleStep_deriv_bound hd (2-delta) (2+delta) x)).trans_eq (by ring))

theorem transition_bounds (isGap : Bool) {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    |transition isGap delta x| ≤ 2 ∧
    |deriv (transition isGap delta) x| ≤ 4*B 1/delta ∧
    |deriv (deriv (transition isGap delta)) x| ≤ 2*D/delta^2 := by
  cases isGap
  · refine ⟨(upper_abs_le_one delta x).trans (by norm_num), ?_, ?_⟩
    · exact (doubleStep_deriv_bound hd 1 2 x).trans (by
        have h := B_nonneg 1
        gcongr <;> linarith)
    · exact (doubleStep_second_bound hd 1 2 x).trans (by
        have h := D_nonneg
        gcongr <;> linarith)
  · exact ⟨gap_abs_le_two delta x, gap_first_bound hd x, gap_second_bound hd x⟩

def amplitude (isGap isLog : Bool) (delta U x : ℝ) : ℂ :=
  ((transition isGap delta x * logFactor isLog U x : ℝ) : ℂ)

theorem amplitude_support (isGap isLog : Bool) {delta : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (U : ℝ) :
    Function.support (amplitude isGap isLog delta U) ⊆ window := by
  intro x hx
  apply transition_support isGap hd hs
  intro hz
  exact hx (by simp [amplitude, hz])

theorem amplitude_smooth (isGap isLog : Bool) {delta : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (U : ℝ) :
    ContDiff ℝ ∞ (amplitude isGap isLog delta U) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have he : amplitude isGap isLog delta U =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2)] with y hy
      have hz : transition isGap delta y = 0 := by
        by_contra hn
        have h := (transition_support isGap hd hs hn).1
        change 1/2 ≤ y at h
        linarith
      simp [amplitude, hz]
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) 0).
      congr_of_eventuallyEq he
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((transition_smooth isGap delta).contDiffAt.mul (logFactor_smoothAt isLog U hx))

def firstCost : ℝ := 4*B 1+4
def secondCost : ℝ := 2*D+16*B 1+8
def profileConstant : ℝ := 36+8*firstCost+2*secondCost

theorem costs_nonneg : 0 ≤ firstCost ∧ 0 ≤ secondCost ∧ 0 ≤ profileConstant := by
  have hB := B_nonneg 1
  have hD := D_nonneg
  unfold firstCost secondCost profileConstant
  exact ⟨by positivity, by positivity, by positivity⟩

/-- All three ordinary jets are derived from the actual transition and
actual HB numerator logarithm. No norm estimate is stored in a family. -/
theorem amplitude_bounds (isGap isLog : Bool) {delta : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (U : ℝ) {x : ℝ} (hx : x ∈ window) :
    ‖amplitude isGap isLog delta U x‖ ≤ 2*logSize U ∧
    ‖deriv (amplitude isGap isLog delta U) x‖ ≤ firstCost*logSize U/delta ∧
    ‖deriv (deriv (amplitude isGap isLog delta U)) x‖ ≤ secondCost*logSize U/delta^2 := by
  let f := transition isGap delta
  let g := logFactor isLog U
  obtain ⟨h0, h1, h2⟩ := transition_bounds isGap hd x
  obtain ⟨hg0, hg1, hg2⟩ := logFactor_bounds isLog U hx
  have hx0 := (reciprocal_window hx).1
  have hf := transition_smooth isGap delta
  have hg := logFactor_smoothAt isLog U hx0.ne'
  have hL := logSize_one_le U
  have hB := B_nonneg 1
  have hD := D_nonneg
  have hdle : delta ≤ 1 := by linarith
  have hd2le : delta^2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdle) (by linarith : 0 ≤ 1+delta)]
  have hd2pos : 0 < delta^2 := pow_pos hd 2
  have hfC : ContDiffAt ℝ ∞ (fun y => (f y : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp hf).contDiffAt
  have hgC : ContDiffAt ℝ ∞ (fun y => (g y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hg
  have hderiv : deriv (amplitude isGap isLog delta U) x =
      (deriv f x : ℂ)*(g x : ℂ)+(f x : ℂ)*(deriv g x : ℂ) := by
    simpa only [amplitude, Complex.ofReal_mul] using
      (((hf.differentiable (by simp) x).hasDerivAt.ofReal_comp).mul
        ((hg.differentiableAt (by simp)).hasDerivAt.ofReal_comp)).deriv
  have hsecond : deriv (deriv (amplitude isGap isLog delta U)) x =
      (deriv (deriv f) x : ℂ)*(g x : ℂ)+
        2*(deriv f x : ℂ)*(deriv g x : ℂ)+(f x : ℂ)*(deriv (deriv g) x : ℂ) := by
    have hdg : deriv (fun y => (g y : ℂ)) =ᶠ[𝓝 x] (fun y => (deriv g y : ℂ)) := by
      filter_upwards [(hg.of_le (m := 1) (by simp)).eventually (by norm_num)] with y hy
      exact ((hy.differentiableAt (by simp)).hasDerivAt.ofReal_comp).deriv
    have hdg2 : deriv (deriv (fun y => (g y : ℂ))) x = (deriv (deriv g) x : ℂ) := by
      exact ((((hg.derivWithin (m := 1) (by simp)).differentiableAt (by simp)).hasDerivAt.ofReal_comp).
        congr_of_eventuallyEq hdg).deriv
    simp only [amplitude, Complex.ofReal_mul]
    rw [second_deriv_mul hfC hgC, ofReal_secondDeriv hf, hdg2,
      ((hf.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv,
      ((hg.differentiableAt (by simp)).hasDerivAt.ofReal_comp).deriv]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [amplitude, Complex.norm_real, Real.norm_eq_abs, abs_mul] using
      mul_le_mul h0 hg0 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  · rw [hderiv]
    calc
      _ ≤ |deriv f x|*|g x|+|f x|*|deriv g x| := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using norm_add_le _ _
      _ ≤ (4*B 1/delta)*logSize U+2*2 := by gcongr
      _ ≤ firstCost*logSize U/delta := by
        apply (le_div_iff₀ hd).2
        unfold firstCost
        field_simp [hd.ne']
        nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sub_nonneg.mpr hL)]
  · rw [hsecond]
    calc
      _ ≤ |deriv (deriv f) x|*|g x| +
          2*|deriv f x|*|deriv g x|+|f x|*|deriv (deriv g) x| := by
        simpa only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs] using
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ (2*D/delta^2)*logSize U+2*(4*B 1/delta)*2+2*4 := by gcongr
      _ ≤ secondCost*logSize U/delta^2 := by
        apply (le_div_iff₀ hd2pos).2
        unfold secondCost
        field_simp [hd.ne']
        have hBD := mul_le_mul_of_nonneg_left hdle (by positivity : 0 ≤ 16*B 1)
        have hBL := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 16*B 1)
        nlinarith

def profile (isGap isLog : Bool) (delta U t : ℝ) : ℝ → ℂ :=
  twisted (amplitude isGap isLog delta U) t

theorem profile_support (isGap isLog : Bool) {delta : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (U t : ℝ) :
    Function.support (profile isGap isLog delta U t) ⊆ window :=
  twisted_support _ _ (amplitude_support isGap isLog hd hs U)

theorem profile_smooth (isGap isLog : Bool) {delta : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (U t : ℝ) :
    ContDiff ℝ ∞ (profile isGap isLog delta U t) :=
  twisted_smooth (amplitude_smooth isGap isLog hd hs U)
    (amplitude_support isGap isLog hd hs U) t

/-- The constant precedes every parameter. The logarithm is log U,
not log(U/d): all positive Brun divisors have the SAME profile budget. -/
theorem profile_N2_cube (isGap isLog : Bool) {delta H t : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (hH : 0 ≤ H) (ht : |t| ≤ H) (U : ℝ) :
    N2 (profile isGap isLog delta U t) ≤
      profileConstant*logSize U*(1+H)^2/delta^2 := by
  have h := twisted_N2_le (amplitude_smooth isGap isLog hd hs U)
    (amplitude_support isGap isLog hd hs U)
    (fun x hx => (amplitude_bounds isGap isLog hd hs U hx).1)
    (fun x hx => (amplitude_bounds isGap isLog hd hs U hx).2.1)
    (fun x hx => (amplitude_bounds isGap isLog hd hs U hx).2.2) t
  have hL : 0 ≤ logSize U := zero_le_one.trans (logSize_one_le U)
  have hC1 := costs_nonneg.1
  have hC2 := costs_nonneg.2.1
  have hdle : delta ≤ 1 := by linarith
  have hd2le : delta^2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdle) (by linarith : 0 ≤ 1+delta)]
  have hunit : (1 : ℝ) ≤ (1+H)^2 := by nlinarith
  have hlin : |t| ≤ (1+H)^2 := by nlinarith [abs_nonneg t]
  have hquad : |t|^2+|t| ≤ 2*(1+H)^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr ht) (add_nonneg hH (abs_nonneg t))
    nlinarith
  apply h.trans
  apply (le_div_iff₀ (pow_pos hd 2)).2
  have hbase := mul_le_mul_of_nonneg_left hd2le (by positivity : 0 ≤ 4*logSize U)
  have hbase2 := mul_le_mul_of_nonneg_left hunit (by positivity : 0 ≤ 4*logSize U)
  have hsec := mul_le_mul_of_nonneg_left hunit (by positivity : 0 ≤ 2*secondCost*logSize U)
  have hlin1 := mul_le_mul_of_nonneg_left hdle (by positivity : 0 ≤ 8*firstCost*logSize U*|t|)
  have hlin2 := mul_le_mul_of_nonneg_left hlin (by positivity : 0 ≤ 8*firstCost*logSize U)
  have hquad1 := mul_le_mul_of_nonneg_left hd2le
    (by positivity : 0 ≤ 16*logSize U*(|t|^2+|t|))
  have hquad2 := mul_le_mul_of_nonneg_left hquad (by positivity : 0 ≤ 16*logSize U)
  unfold profileConstant
  field_simp [hd.ne']
  nlinarith only [hbase, hbase2, hsec, hlin1, hlin2, hquad1, hquad2]

def profileSchwartz (isGap isLog : Bool) {delta : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (U t : ℝ) : 𝓢(ℝ, ℂ) :=
  (compact_of_support (profile_support isGap isLog hd hs U t)).toSchwartzMap
    (profile_smooth isGap isLog hd hs U t)

@[simp] theorem profileSchwartz_coe (isGap isLog : Bool) {delta : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (U t : ℝ) :
    (profileSchwartz isGap isLog hd hs U t : ℝ → ℂ) = profile isGap isLog delta U t := rfl

theorem profile_fourier_decay (isGap isLog : Bool) {delta H t : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (hH : 0 ≤ H) (ht : |t| ≤ H) (U s : ℝ) :
    ‖(𝓕 (profileSchwartz isGap isLog hd hs U t)) s‖ ≤
      fourierDecayConstant*(profileConstant*logSize U*(1+H)^2/delta^2)/(1+|s|)^2 := by
  apply (norm_fourier_le_N2 (profileSchwartz isGap isLog hd hs U t) s).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (profile_N2_cube isGap isLog hd hs hH ht U)
    fourierDecayConstant_pos.le

end
end ImbalancedChen.Part3.TwoLongTransitionMellinN2

