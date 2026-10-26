import ImbalancedChen.Part3ImaginaryRadialCutoffEnergy
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual L2 radial solutions have an L2 derivative on a smaller tail

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The genuine smoothTransition cutoff is zero at a and b+1 and one on
[a+1,b]. Its derivative has a uniform bound derived from the actual
smoothTransition derivative theorem. Native cutoff Caccioppoli therefore
bounds every finite derivative-square integral by the input's own L2
mass. The native improper-integrability theorem exhausts those intervals.
No derivative-L2, energy, basis, or limit-point hypothesis is assumed.
-/

namespace ImbalancedChen.Part3.ImaginaryRadialTailDerivativeL220261026b

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ImaginaryRadialCutoffEnergy20261026b

private def intervalCutoff (a b r : ℝ) : ℝ :=
  Real.smoothTransition (r-a) * Real.smoothTransition (b+1-r)

private theorem intervalCutoff_smooth (a b : ℝ) :
    ContDiff ℝ 1 (intervalCutoff a b) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

private theorem intervalCutoff_range (a b r : ℝ) :
    0 ≤ intervalCutoff a b r ∧ intervalCutoff a b r ≤ 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)

private theorem intervalCutoff_left (a b : ℝ) : intervalCutoff a b a = 0 := by
  simp only [intervalCutoff, sub_self, Real.smoothTransition.zero, zero_mul]

private theorem intervalCutoff_right (a b : ℝ) : intervalCutoff a b (b+1) = 0 := by
  simp only [intervalCutoff, sub_self, Real.smoothTransition.zero, mul_zero]

private theorem intervalCutoff_one {a b r : ℝ} (hr : r ∈ Icc (a+1) b) :
    intervalCutoff a b r = 1 := by
  rw [intervalCutoff, Real.smoothTransition.one_of_one_le (by linarith [hr.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hr.2]), one_mul]

private theorem intervalCutoff_deriv (a b r : ℝ) :
    deriv (intervalCutoff a b) r =
      deriv Real.smoothTransition (r-a)*Real.smoothTransition (b+1-r) -
        Real.smoothTransition (r-a)*deriv Real.smoothTransition (b+1-r) := by
  have hs : Differentiable ℝ Real.smoothTransition :=
    Real.smoothTransition.contDiff.differentiable (by norm_num : (1 : ℕ∞) ≤ 1)
  have hleft := (hs (r-a)).hasDerivAt.comp r
    ((hasDerivAt_id r).sub_const a)
  have hright := (hs (b+1-r)).hasDerivAt.comp r
    ((hasDerivAt_const r (b+1)).sub (hasDerivAt_id r))
  simpa only [intervalCutoff, Function.comp_def, mul_one, sub_self, zero_sub,
    mul_neg_one, sub_eq_add_neg] using (hleft.mul hright).deriv

private theorem intervalCutoff_deriv_bound {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ r : ℝ, |deriv Real.smoothTransition r| ≤ C)
    (a b r : ℝ) : |deriv (intervalCutoff a b) r| ≤ 2*C := by
  rw [intervalCutoff_deriv]
  calc
    _ ≤ |deriv Real.smoothTransition (r-a)*Real.smoothTransition (b+1-r)| +
        |Real.smoothTransition (r-a)*deriv Real.smoothTransition (b+1-r)| := abs_sub _ _
    _ = |deriv Real.smoothTransition (r-a)|*Real.smoothTransition (b+1-r) +
        Real.smoothTransition (r-a)*|deriv Real.smoothTransition (b+1-r)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _),
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
    _ ≤ C*1+1*C := add_le_add
      (mul_le_mul (hbound _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) hC)
      (mul_le_mul (Real.smoothTransition.le_one _) (hbound _)
        (abs_nonneg _) (by norm_num))
    _ = _ := by ring

private theorem tail_continuity {tau R : ℝ} {u : ℝ → ℂ}
    (hu : TailSolution tau R u) :
    ContinuousOn u (Ioi R) ∧ ContinuousOn (deriv u) (Ioi R) := by
  exact ⟨fun r hr => (hu r hr).1.continuousAt.continuousWithinAt,
    fun r hr => (hu r hr).2.continuousAt.continuousWithinAt⟩

/-- A uniform finite derivative-energy bound, with its constant obtained
from the actual smooth cutoff and the native ODE estimate. -/
private theorem finite_derivative_bound {tau R a C : ℝ} {u : ℝ → ℂ}
    (hu : TailSolution tau R u) (hRa : R < a) (hC : 0 ≤ C)
    (hCbound : ∀ r : ℝ, |deriv Real.smoothTransition r| ≤ C)
    (hL2 : MemLp u 2 (volume.restrict (Ioi R)))
    {b : ℝ} (hab : a+1 ≤ b) :
    (∫ r in (a+1)..b, Complex.normSq (deriv u r)) ≤
      (16*C^2+2*tau^2)*(∫ r in Ioi R, Complex.normSq (u r)) := by
  let eta := intervalCutoff a b
  have hab1 : a ≤ b+1 := by linarith
  obtain ⟨hK,hErr,hM⟩ := cutoff_terms_integrable hu hab1 hRa eta (intervalCutoff_smooth a b)
  have hU := (tail_continuity hu).1
  have hUsq : ContinuousOn (fun r => Complex.normSq (u r)) (Ioi R) := by
    simpa only [Complex.normSq_apply, pow_two] using (hU.re.pow 2).add (hU.im.pow 2)
  have hIntU : IntegrableOn (fun r => Complex.normSq (u r)) (Ioi R) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
  have hlocalU : IntervalIntegrable (fun r => Complex.normSq (u r)) volume a (b+1) :=
    (hUsq.mono (by
      intro r hr
      have hr' : r ∈ Icc a (b+1) := by simpa only [uIcc_of_le hab1] using hr
      exact hRa.trans_le hr'.1)).intervalIntegrable
  have hmass : (∫ r in a..(b+1), Complex.normSq (u r)) ≤
      ∫ r in Ioi R, Complex.normSq (u r) := by
    rw [intervalIntegral.integral_of_le hab1]
    exact setIntegral_mono_set hIntU (Eventually.of_forall (fun r => Complex.normSq_nonneg _))
      (Eventually.of_forall (fun r hr => hRa.trans hr.1))
  have hErrBound : (∫ r in a..(b+1), (deriv eta r)^2*Complex.normSq (u r)) ≤
      4*C^2*(∫ r in a..(b+1), Complex.normSq (u r)) := by
    calc
      _ ≤ ∫ r in a..(b+1), (4*C^2)*Complex.normSq (u r) := by
        apply intervalIntegral.integral_mono_on hab1 hErr (hlocalU.const_mul _)
        intro r _
        apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
        have hd := intervalCutoff_deriv_bound hC hCbound a b r
        change |deriv eta r| ≤ 2*C at hd
        nlinarith [sq_abs (deriv eta r), abs_nonneg (deriv eta r)]
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hMassBound : (∫ r in a..(b+1), eta r^2*Complex.normSq (u r)) ≤
      ∫ r in a..(b+1), Complex.normSq (u r) := by
    apply intervalIntegral.integral_mono_on hab1 hM hlocalU
    intro r _
    have hr := intervalCutoff_range a b r
    have hs : eta r^2 ≤ 1 := by dsimp [eta]; nlinarith [hr.1,hr.2]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (Complex.normSq_nonneg (u r))
  have hPlateau : (∫ r in (a+1)..b, Complex.normSq (deriv u r)) =
      ∫ r in (a+1)..b, eta r^2*Complex.normSq (deriv u r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (a+1) b := by simpa only [uIcc_of_le hab] using hr
    simp only [eta, intervalCutoff_one hr', one_pow, one_mul]
  have hEnlarge : (∫ r in (a+1)..b, eta r^2*Complex.normSq (deriv u r)) ≤
      ∫ r in a..(b+1), eta r^2*Complex.normSq (deriv u r) :=
    intervalIntegral.integral_mono_interval (by linarith) hab (by linarith)
      (Eventually.of_forall (fun r => mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))) hK
  have hEnergy := tail_cutoff_Caccioppoli hu hab1 hRa eta (intervalCutoff_smooth a b)
    (intervalCutoff_left a b) (intervalCutoff_right a b)
  rw [hPlateau]
  calc
    _ ≤ ∫ r in a..(b+1), eta r^2*Complex.normSq (deriv u r) := hEnlarge
    _ ≤ 4*(∫ r in a..(b+1), (deriv eta r)^2*Complex.normSq (u r)) +
        2*tau^2*(∫ r in a..(b+1), eta r^2*Complex.normSq (u r)) := hEnergy
    _ ≤ 4*(4*C^2*(∫ r in a..(b+1), Complex.normSq (u r))) +
        2*tau^2*(∫ r in a..(b+1), Complex.normSq (u r)) :=
      add_le_add (mul_le_mul_of_nonneg_left hErrBound (by norm_num))
        (mul_le_mul_of_nonneg_left hMassBound (by positivity))
    _ = (16*C^2+2*tau^2)*(∫ r in a..(b+1), Complex.normSq (u r)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

/-- Every genuine L2 tail solution of the imaginary-order radial ODE
has a genuine L2 native derivative after moving the endpoint a fixed
distance into the ODE domain. The conclusion follows from actual smooth
cutoffs and improper integrability, not a supplied energy hypothesis. -/
theorem derivative_memLp_two_smaller_tail {tau R : ℝ} {u : ℝ → ℂ}
    (hu : TailSolution tau R u)
    (hL2 : MemLp u 2 (volume.restrict (Ioi R))) :
    MemLp (deriv u) 2 (volume.restrict (Ioi (R+2))) := by
  obtain ⟨C,hC1,hCb⟩ := ImbalancedChen.P4B.exists_smoothTransition_global_derivative_bound 1
  have hC : 0 ≤ C := by linarith
  have hCbound : ∀ r : ℝ, |deriv Real.smoothTransition r| ≤ C := by
    simpa only [iteratedDeriv_one] using hCb
  let endpoint (n : ℕ) : ℝ := R+2+(n : ℝ)
  have hend (n : ℕ) : R+2 ≤ endpoint n := by
    dsimp [endpoint]
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hcont : ContinuousOn (fun r => Complex.normSq (deriv u r)) (Ioi R) := by
    have hc := (tail_continuity hu).2
    simpa only [Complex.normSq_apply,pow_two] using (hc.re.pow 2).add (hc.im.pow 2)
  have hfi (n : ℕ) : IntegrableOn (fun r => Complex.normSq (deriv u r))
      (Ioc (R+2) (endpoint n)) := by
    have hc : ContinuousOn (fun r => Complex.normSq (deriv u r))
        (Icc (R+2) (endpoint n)) := hcont.mono (by intro r hr; change R < r; linarith [hr.1])
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have he : Tendsto endpoint atTop atTop :=
    tendsto_atTop_add_const_left _ (R+2) tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      (∫ r in (R+2)..endpoint n, ‖Complex.normSq (deriv u r)‖) ≤
        (16*C^2+2*tau^2)*(∫ r in Ioi R, Complex.normSq (u r)) := by
    apply Eventually.of_forall
    intro n
    simp only [Real.norm_eq_abs,abs_of_nonneg (Complex.normSq_nonneg _)]
    have hN := finite_derivative_bound hu (a := R+1) (by linarith) hC hCbound hL2
      (b := endpoint n) (by linarith [hend n])
    simpa only [show R+1+1 = R+2 by ring] using hN
  have hInt := integrableOn_Ioi_of_intervalIntegral_norm_bounded
    ((16*C^2+2*tau^2)*(∫ r in Ioi R, Complex.normSq (u r))) (R+2) hfi he hbound
  have hD : AEStronglyMeasurable (deriv u) (volume.restrict (Ioi (R+2))) :=
    ((tail_continuity hu).2.mono (by intro r hr; change R < r; linarith)).aestronglyMeasurable
      measurableSet_Ioi
  apply (memLp_two_iff_integrable_sq_norm hD).mpr
  simpa only [Complex.normSq_eq_norm_sq] using hInt

end
end ImbalancedChen.Part3.ImaginaryRadialTailDerivativeL220261026b

