import ImbalancedChen.Part3ActualExceptionalJSmallKernel
import ImbalancedChen.Part3ActualJSecondMixedDerivative
import ImbalancedChen.Part3ActualRealOrderJLargeQ
import Mathlib.Tactic

/-!
M source candidate. UNCOMPILED; no kernel or production credit.

The actual positive-sign symmetric numerator, including its removable
order-zero value, solves the homogeneous ordinary Bessel equation. Its
radial energy is decreasing. Compactness is used only for native order
derivatives at the single positive point 1/256, before choosing alpha.
The resulting estimate is uniform in alpha, unlike division of separate
J_alpha and J_minusalpha bounds by sin(pi*alpha/2).

This file is the kernel supplier. Decay of the integrated smooth physical
test is a separate, necessary step; it is not a consequence of a bare
pointwise O(q^(-1/2)) estimate alone.
-/

namespace ImbalancedChen.Part3.ActualExceptionalJLargeKernel20261102

noncomputable section
open Complex Set Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly ActualJLocalOrderHolomorphic20261026a
open ActualJFirstOrderJet20261026b ActualJSecondOrderJet20261026b
open ActualJFirstMixedDerivative20261026b ActualJSecondMixedDerivative20261026b
open ActualRealOrderJRadialJet20261026b ActualRealOrderJLargeQ20261026b
open ActualExceptionalJSmallKernel20261102

def positiveSignFirst (alpha q : ℝ) : ℂ :=
  if alpha = 0 then 2 * actualJFirstOrderDerivative 0 q
  else ((Real.pi : ℂ) / (2 * (Real.sin (Real.pi * alpha / 2) : ℂ))) *
    (generalJFirst (alpha : ℂ) q - generalJFirst (-(alpha : ℂ)) q)

def positiveSignSecond (alpha q : ℝ) : ℂ :=
  if alpha = 0 then 2 * actualJSecondOrderDerivative 0 q
  else ((Real.pi : ℂ) / (2 * (Real.sin (Real.pi * alpha / 2) : ℂ))) *
    (generalJSecond (alpha : ℂ) q - generalJSecond (-(alpha : ℂ)) q)

private theorem orders_lower {alpha : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    -1 < (alpha : ℂ).re ∧ -1 < (-(alpha : ℂ)).re := by
  simp only [Complex.ofReal_re, Complex.neg_re]
  norm_num [exceptionalCap] at ha
  constructor <;> linarith

theorem positiveSignKernel_hasDerivAt {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    HasDerivAt (positiveSignKernel alpha) (positiveSignFirst alpha q) q := by
  by_cases hz : alpha = 0
  · subst alpha
    simpa only [positiveSignKernel, positiveSignFirst, if_pos rfl] using
      (actualJOrderDerivative_q_hasDerivAt
        (nu := (0 : ℂ)) (by norm_num [orderHalfPlane]) hq).const_mul 2
  · obtain ⟨hp, hn⟩ := orders_lower ha0 ha
    simpa only [positiveSignKernel, positiveSignFirst, if_neg hz] using
      ((generalJ_hasDerivAt hp hq).sub (generalJ_hasDerivAt hn hq)).const_mul
        ((Real.pi : ℂ) / (2 * (Real.sin (Real.pi * alpha / 2) : ℂ)))

theorem positiveSignFirst_hasDerivAt {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    HasDerivAt (positiveSignFirst alpha) (positiveSignSecond alpha q) q := by
  by_cases hz : alpha = 0
  · subst alpha
    simpa only [positiveSignFirst, positiveSignSecond, if_pos rfl] using
      (actualJFirstOrderDerivative_q_hasDerivAt
        (nu := (0 : ℂ)) (by norm_num [orderHalfPlane]) hq).const_mul 2
  · obtain ⟨hp, hn⟩ := orders_lower ha0 ha
    simpa only [positiveSignFirst, positiveSignSecond, if_neg hz] using
      ((generalJFirst_hasDerivAt hp hq).sub
        (generalJFirst_hasDerivAt hn hq)).const_mul
          ((Real.pi : ℂ) / (2 * (Real.sin (Real.pi * alpha / 2) : ℂ)))

/-- The order derivative forcing 2*nu*J_nu vanishes at nu=0.
Thus the removable kernel has the SAME homogeneous equation. -/
theorem positiveSign_jet_equation {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    (q : ℂ)^2 * positiveSignSecond alpha q +
      (q : ℂ) * positiveSignFirst alpha q +
        ((q : ℂ)^2 - (alpha : ℂ)^2) * positiveSignKernel alpha q = 0 := by
  by_cases hz : alpha = 0
  · subst alpha
    have h := generalJ_order_jet_equation (0 : ℂ) hq
    simp only [positiveSignKernel, positiveSignFirst, positiveSignSecond,
      if_pos rfl, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero]
    linear_combination 2 * h
  · obtain ⟨hp, hn⟩ := orders_lower ha0 ha
    have h1 := generalJ_jet_equation hp hq
    have h2 := generalJ_jet_equation hn hq
    simp only [neg_sq] at h2
    simp only [positiveSignKernel, positiveSignFirst, positiveSignSecond, if_neg hz]
    linear_combination
      ((Real.pi : ℂ) / (2 * (Real.sin (Real.pi * alpha / 2) : ℂ))) * h1 -
      ((Real.pi : ℂ) / (2 * (Real.sin (Real.pi * alpha / 2) : ℂ))) * h2

theorem positiveSignSecond_eq {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    positiveSignSecond alpha q =
      -positiveSignFirst alpha q / (q : ℂ) -
        (1 - (alpha : ℂ)^2 / (q : ℂ)^2) * positiveSignKernel alpha q := by
  have h := positiveSign_jet_equation ha0 ha hq
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  apply (mul_left_cancel₀ (pow_ne_zero 2 hqC))
  field_simp [hqC]
  linear_combination h

def radialKernel (alpha q : ℝ) : ℂ :=
  (Real.sqrt q : ℂ) * positiveSignKernel alpha q

def radialKernelFirst (alpha q : ℝ) : ℂ :=
  (Real.sqrt q : ℂ) * positiveSignFirst alpha q +
    ((1 / (2 * Real.sqrt q) : ℝ) : ℂ) * positiveSignKernel alpha q

theorem radialKernel_hasDerivAt {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    HasDerivAt (radialKernel alpha) (radialKernelFirst alpha q) q := by
  have h := (Real.hasDerivAt_sqrt hq.ne').ofReal_comp.mul
    (positiveSignKernel_hasDerivAt ha0 ha hq)
  convert h using 1 <;> unfold radialKernel radialKernelFirst <;> ring

private theorem half_inverse_sqrt_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => 1 / (2 * Real.sqrt x))
      (-(1 / (4 * Real.sqrt q ^ 3))) q := by
  have hs := (Real.sqrt_pos.2 hq).ne'
  have h := ((Real.hasDerivAt_sqrt hq.ne').const_mul 2).inv
    (mul_ne_zero (by norm_num) hs)
  convert h using 1
  · funext x; exact one_div _
  · field_simp [hs] <;> ring

theorem radialKernelFirst_hasDerivAt {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    HasDerivAt (radialKernelFirst alpha)
      (-(realRadialPotential alpha q) • radialKernel alpha q) q := by
  have hsC : (Real.sqrt q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hq).ne'
  have hsq : (Real.sqrt q : ℂ)^2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  have h := ((Real.hasDerivAt_sqrt hq.ne').ofReal_comp.mul
    (positiveSignFirst_hasDerivAt ha0 ha hq)).add
      ((half_inverse_sqrt_hasDerivAt hq).ofReal_comp.mul
        (positiveSignKernel_hasDerivAt ha0 ha hq))
  convert h using 1
  · rfl
  · rw [positiveSignSecond_eq ha0 ha hq]
    unfold realRadialPotential realRadialCoefficient radialKernel
    simp only [Complex.real_smul]
    push_cast
    rw [← hsq]
    field_simp [hsC] <;> ring

def kernelEnergy (alpha q : ℝ) : ℝ :=
  ‖radialKernelFirst alpha q‖^2 +
    realRadialPotential alpha q * ‖radialKernel alpha q‖^2

private theorem alpha_half {alpha : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) : |alpha| ≤ 1/2 := by
  rw [abs_of_nonneg ha0]
  exact ha.trans (by norm_num [exceptionalCap])

theorem kernelEnergy_hasDerivAt {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    HasDerivAt (kernelEnergy alpha)
      (-(2 * realRadialCoefficient alpha * ‖radialKernel alpha q‖^2 / q^3)) q := by
  have h := ((radialKernelFirst_hasDerivAt ha0 ha hq).norm_sq).add
    ((realRadialPotential_hasDerivAt alpha hq).mul
      ((radialKernel_hasDerivAt ha0 ha hq).norm_sq))
  convert h using 1
  · rfl
  · simp only [inner_smul_right]
    rw [real_inner_comm (radialKernel alpha q) (radialKernelFirst alpha q)]
    ring

theorem kernelEnergy_antitoneOn {alpha : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    AntitoneOn (kernelEnergy alpha) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ))
  · intro q hq
    exact (kernelEnergy_hasDerivAt ha0 ha hq).continuousAt.continuousWithinAt
  · intro q hq
    exact (kernelEnergy_hasDerivAt ha0 ha (interior_subset hq)).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq0 : 0 < q := interior_subset hq
    rw [(kernelEnergy_hasDerivAt ha0 ha hq0).deriv]
    apply neg_nonpos.mpr
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (realRadialCoefficient_nonneg (alpha_half ha0 ha))) (sq_nonneg _)) (by positivity)

/-- Holomorphic cancellation on a fixed compact order segment. This is
ordinary mean-value calculus, not an assumed special-function bound. -/
def symmetricOrderDifference (F : ℂ → ℂ) (alpha : ℝ) : ℂ :=
  if alpha = 0 then 2 * deriv F 0 else
    ((Real.pi : ℂ) / (2 * (Real.sin (Real.pi * alpha / 2) : ℂ))) *
      (F (alpha : ℂ) - F (-(alpha : ℂ)))

theorem exists_symmetricOrderDifference_bound (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F orderHalfPlane) :
    ∃ B : ℝ, 0 < B ∧ ∀ alpha : ℝ,
      0 ≤ alpha → alpha ≤ exceptionalCap → ‖symmetricOrderDifference F alpha‖ ≤ B := by
  have hd : ContinuousOn (fun nu : ℝ => deriv F (nu : ℂ))
      (Icc (-exceptionalCap) exceptionalCap) := by
    intro nu hnu
    have hh := hF.analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (real_order_mem (abs_le.mpr hnu)))
    exact (hh.deriv.continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨D0, hD0⟩ := (isCompact_Icc : IsCompact
    (Icc (-exceptionalCap) exceptionalCap)).exists_bound_of_continuousOn hd
  let D : ℝ := |D0| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hDb (nu : ℝ) (hnu : |nu| ≤ exceptionalCap) : ‖deriv F (nu : ℂ)‖ ≤ D :=
    (hD0 nu (abs_le.mp hnu)).trans (by dsimp [D]; linarith [le_abs_self D0])
  refine ⟨Real.pi * D, mul_pos Real.pi_pos hD, ?_⟩
  intro alpha ha0 ha
  by_cases hz : alpha = 0
  · subst alpha
    have hb := hDb 0 (by norm_num [exceptionalCap])
    simp only [symmetricOrderDifference, if_pos rfl, norm_mul, norm_ofNat]
    calc
      2 * ‖deriv F 0‖ ≤ 2 * D := by simpa using mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ Real.pi * D := mul_le_mul_of_nonneg_right Real.two_le_pi hD.le
  · have hp : 0 < alpha := lt_of_le_of_ne ha0 (Ne.symm hz)
    have hs : 0 < Real.sin (Real.pi * alpha / 2) := hp.trans_le (alpha_le_sin ha0 ha)
    have hm := (convex_Icc (-alpha) alpha).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun nu hnu => ((hF.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (real_order_mem ((abs_le.mpr hnu).trans ha)))).hasDerivAt.comp_ofReal).hasDerivWithinAt)
      (fun nu hnu => hDb nu ((abs_le.mpr hnu).trans ha))
      (show -alpha ∈ Icc (-alpha) alpha from ⟨le_rfl, by linarith⟩)
      (show alpha ∈ Icc (-alpha) alpha from ⟨by linarith, le_rfl⟩)
    have hl : ‖alpha - -alpha‖ = 2 * alpha := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; ring
    rw [hl, Complex.ofReal_neg] at hm
    have hb : ‖F (alpha : ℂ) - F (-(alpha : ℂ))‖ ≤
        2 * D * Real.sin (Real.pi * alpha / 2) := by
      calc
        _ ≤ D * (2 * alpha) := hm
        _ ≤ D * (2 * Real.sin (Real.pi * alpha / 2)) := by
          gcongr; exact alpha_le_sin ha0 ha
        _ = _ := by ring
    simp only [symmetricOrderDifference, if_neg hz, norm_mul, norm_div,
      norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hs]
    calc
      _ ≤ Real.pi / (2 * Real.sin (Real.pi * alpha / 2)) *
          (2 * D * Real.sin (Real.pi * alpha / 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by field_simp [hs.ne']; ring

def initialPoint : ℝ := 1 / 256

theorem exists_uniform_initial_jets :
    ∃ B : ℝ, 0 < B ∧ ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ exceptionalCap →
      ‖positiveSignKernel alpha initialPoint‖ ≤ B ∧
      ‖positiveSignFirst alpha initialPoint‖ ≤ B := by
  have hq : 0 < initialPoint := by norm_num [initialPoint]
  obtain ⟨B0, hB0, hb0⟩ := exists_symmetricOrderDifference_bound
    (fun nu => generalJ nu initialPoint)
    (fun nu hnu => (generalJ_order_hasDerivAt hnu hq).differentiableAt.differentiableWithinAt)
  obtain ⟨B1, hB1, hb1⟩ := exists_symmetricOrderDifference_bound
    (fun nu => generalJFirst nu initialPoint)
    (fun nu hnu => (generalJFirst_order_hasDerivAt hnu hq).differentiableAt.differentiableWithinAt)
  have hz : (0 : ℂ) ∈ orderHalfPlane := by norm_num [orderHalfPlane]
  refine ⟨B0 + B1, by linarith, ?_⟩
  intro alpha ha0 ha
  have h0 := hb0 alpha ha0 ha
  have h1 := hb1 alpha ha0 ha
  have he0 : positiveSignKernel alpha initialPoint =
      symmetricOrderDifference (fun nu => generalJ nu initialPoint) alpha := by
    unfold positiveSignKernel symmetricOrderDifference
    rw [(generalJ_order_hasDerivAt hz hq).deriv]
  have he1 : positiveSignFirst alpha initialPoint =
      symmetricOrderDifference (fun nu => generalJFirst nu initialPoint) alpha := by
    unfold positiveSignFirst symmetricOrderDifference
    rw [(generalJFirst_order_hasDerivAt hz hq).deriv]
  rw [he0, he1]
  exact ⟨h0.trans (by linarith), h1.trans (by linarith)⟩

def initialJetBound : ℝ := exists_uniform_initial_jets.choose
theorem initialJetBound_pos : 0 < initialJetBound := exists_uniform_initial_jets.choose_spec.1

/-- Large enough to bound both initial radial jets and their energy.
The generous fixed constant has no alpha, q, packet or mode dependence. -/
def largeKernelConstant : ℝ := 1024 * initialJetBound

theorem largeKernelConstant_pos : 0 < largeKernelConstant := by
  have h := initialJetBound_pos
  unfold largeKernelConstant
  positivity

theorem initial_energy_le {alpha : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    kernelEnergy alpha initialPoint ≤ largeKernelConstant^2 := by
  obtain ⟨h0, h1⟩ := exists_uniform_initial_jets.choose_spec.2 alpha ha0 ha
  have hB := initialJetBound_pos
  have hs : Real.sqrt initialPoint = 1/16 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num [initialPoint]) (by norm_num)).mpr
    norm_num [initialPoint]
  have hR : ‖radialKernel alpha initialPoint‖ ≤ initialJetBound / 16 := by
    simp only [radialKernel, hs, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num
    nlinarith
  have hR1 : ‖radialKernelFirst alpha initialPoint‖ ≤ 9 * initialJetBound := by
    apply (norm_add_le _ _).trans
    simp only [hs, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num
    nlinarith
  have hV : realRadialPotential alpha initialPoint ≤ 16385 := by
    unfold realRadialPotential realRadialCoefficient initialPoint
    norm_num
    nlinarith [sq_nonneg alpha]
  have h0sq : ‖radialKernel alpha initialPoint‖^2 ≤ (initialJetBound/16)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hR 2
  have h1sq : ‖radialKernelFirst alpha initialPoint‖^2 ≤ (9*initialJetBound)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hR1 2
  have hmul := mul_le_mul hV h0sq (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 16385)
  unfold kernelEnergy largeKernelConstant
  nlinarith [h1sq, hmul]

/-- Uniform actual symmetric-numerator estimate, with its alpha=0 value.
This includes the transition range needed by every Y>1/16 packet. -/
theorem positiveSignKernel_large_bound {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : initialPoint ≤ q) :
    ‖positiveSignKernel alpha q‖ ≤ largeKernelConstant / Real.sqrt q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num [initialPoint]) hq
  have hE := kernelEnergy_antitoneOn ha0 ha
    (show initialPoint ∈ Ioi 0 by norm_num [initialPoint]) hq0 hq
  have hpot := mul_le_mul_of_nonneg_right
    (realRadialPotential_ge_one (alpha_half ha0 ha) q) (sq_nonneg ‖radialKernel alpha q‖)
  have hR : ‖radialKernel alpha q‖^2 ≤ kernelEnergy alpha q := by
    unfold kernelEnergy
    nlinarith [sq_nonneg ‖radialKernelFirst alpha q‖]
  have hb : ‖radialKernel alpha q‖ ≤ largeKernelConstant := by
    have hs := hR.trans (hE.trans (initial_energy_le ha0 ha))
    nlinarith [norm_nonneg (radialKernel alpha q), largeKernelConstant_pos]
  rw [radialKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg q)] at hb
  apply (le_div_iff₀ (Real.sqrt_pos.2 hq0)).mpr
  simpa only [mul_comm] using hb

theorem positiveSignKernel_transition_bound {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : initialPoint ≤ q) :
    ‖positiveSignKernel alpha q‖ ≤ 16 * largeKernelConstant := by
  have hs : (1/16 : ℝ) ≤ Real.sqrt q := by
    have h := Real.sqrt_le_sqrt hq
    have he : Real.sqrt initialPoint = 1/16 := by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num [initialPoint]) (by norm_num)).mpr
      norm_num [initialPoint]
    simpa only [he] using h
  apply (positiveSignKernel_large_bound ha0 ha hq).trans
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/16) hs)).mpr
  have hB := largeKernelConstant_pos
  nlinarith

end
end ImbalancedChen.Part3.ActualExceptionalJLargeKernel20261102
