import ImbalancedChen.Part3ActualExceptionalJAllScaleBudget
import ImbalancedChen.Part3OriginalRetainedPhaseOriginalScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pay the genuine fourth-weight J debit. This file does not manufacture the
missing arithmetic-row -> Kuznetsov/ABL PacketData dictionary. The physical
caller below invokes the actual M theorem and retains exactly its completed
energy. In particular a coefficient-energy estimate is never a premise.

The scale estimates use the full 4*pi normalization. A nonempty positive
integer interval supplies the lower bounds on U and V; there is no assumption
that Y is large. Constants and finite selectable loss orders precede eta.
-/

namespace ImbalancedChen.Part3.ActualExceptionalJSelectableEta20261102

noncomputable section
open Classical Set MeasureTheory Filter
open scoped BigOperators Topology
open P3ActualLiteralPacketIntegralSourceOnly
open P3ActualWeightedSpectralBudgetSourceOnly
open ActualPoissonNormalizedFSourceOnly (spectralScale)
open ActualExceptionalPhysicalNormalization20261102 (physicalScalePacket)
open ActualExceptionalJSmallKernel20261102
open ActualExceptionalJSmallPacketBudget20261102
open ActualExceptionalJLargeTransform20261102
open ActualExceptionalJPacketAdapter20261102
open ActualExceptionalJAllScaleBudget20261102
open ImbalancedChen.Part3
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalActualPoissonTightH20261028
open ImbalancedChen.Part3.OriginalActualAbelPrefixCost20261028
open ImbalancedChen.Part3.OriginalRetainedPhaseOriginalScale20261102

variable {ι : Type*}

/-- The loose native chart (-32,32) suffices: a positive integer in
that chart forces its actual physical length to exceed 1/32. -/
theorem length_lower_of_positive_integer {L : ℝ} (hL : 0 < L)
    (n : ℕ) (hn : 1 ≤ n) (hchart : (n : ℝ)/L < 32) :
    (1 : ℝ)/32 ≤ L := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hh := (div_lt_iff₀ hL).mp hchart
  linarith

theorem packet_V_lower (P : PacketData ι) (m : ℕ)
    (hm : m ∈ P.mCarrier) (hm1 : 1 ≤ m) : (1 : ℝ)/32 ≤ P.V :=
  length_lower_of_positive_integer P.V_pos m hm1 (P.m_normalized m hm).2

theorem packet_U_lower (P : PacketData ι) (j : ι) (hj : j ∈ P.rows)
    (n : ℕ) (hn : n ∈ P.nCarrier j)
    (hn1 : 1 ≤ (P.packet j).multiplier*n) : (1 : ℝ)/32 ≤ P.U :=
  length_lower_of_positive_integer P.U_pos ((P.packet j).multiplier*n)
    hn1 (P.n_normalized j hj n hn).2

/-- Derived inverse scale, with no small/large-Y restriction. B is a
fixed polynomial scale order, not a selectable small exponent. -/
theorem inverse_physical_scale_le {A V U Z C x B : ℝ}
    (hA : 1 ≤ A) (hV : (1 : ℝ)/32 ≤ V) (hU : (1 : ℝ)/32 ≤ U)
    (hZ : 0 < Z) (hC : 0 < C) (hx : 1 ≤ x) (hB : 0 ≤ B)
    (hCx : C ≤ x^B) (hZx : Z ≤ x^B) :
    1 / spectralScale A V U Z C ≤ 64*x^(2*B) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hV0 : 0 < V := by linarith
  have hU0 : 0 < U := by linarith
  have havu : (1 : ℝ)/1024 ≤ A*V*U := by
    have hvu := mul_le_mul hV hU (by norm_num : (0 : ℝ) ≤ 1/32) hV0.le
    have hh := mul_le_mul_of_nonneg_right hA (mul_nonneg hV0.le hU0.le)
    nlinarith
  have hs : (1 : ℝ)/32 ≤ Real.sqrt (A*V*U) := by
    have hp := Real.sqrt_nonneg (A*V*U)
    have he := Real.sq_sqrt (show 0 ≤ A*V*U by positivity)
    nlinarith
  have hsZ : Real.sqrt Z ≤ 1+Z := by
    have hp := Real.sqrt_nonneg Z
    have he := Real.sq_sqrt hZ.le
    nlinarith [sq_nonneg (Real.sqrt Z-1)]
  have hp : 1 ≤ 4*Real.pi := by linarith [Real.pi_gt_three]
  have hden : (1 : ℝ)/32 ≤ 4*Real.pi*Real.sqrt (A*V*U) := by
    have hh := mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (A*V*U))
    linarith
  have hinv : 1 / spectralScale A V U Z C ≤ 32*C*(1+Z) := by
    have he : 1 / spectralScale A V U Z C =
        (C*Real.sqrt Z)/(4*Real.pi*Real.sqrt (A*V*U)) := by
      unfold spectralScale
      field_simp [hC.ne', (Real.sqrt_pos.mpr hZ).ne',
        (Real.sqrt_pos.mpr (show 0 < A*V*U by positivity)).ne', Real.pi_ne_zero]
      <;> ring
    rw [he]
    apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ C*Real.sqrt Z)
      (by norm_num : (0 : ℝ) < 1/32) hden).trans
    have hh := mul_le_mul_of_nonneg_left hsZ (show 0 ≤ 32*C by positivity)
    convert hh using 1 <;> ring
  have hxp : 1 ≤ x^B := Real.one_le_rpow hx hB
  have hupper : C*(1+Z) ≤ 2*(x^B)^2 := by
    have hh := mul_le_mul hCx (show 1+Z ≤ 2*x^B by linarith)
      (by positivity : 0 ≤ 1+Z) (Real.rpow_nonneg hx0.le B)
    nlinarith
  calc
    _ ≤ 32*C*(1+Z) := hinv
    _ ≤ 64*(x^B)^2 := by nlinarith
    _ = 64*x^(2*B) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 2
      ring

/-- The true small-Y logarithm. Even when C/D<1/2, the scale comes
from a nonempty actual integer interval, not that comparison point. -/
theorem physical_log_le {A V U Z C x B : ℝ}
    (hA : 1 ≤ A) (hV : (1 : ℝ)/32 ≤ V) (hU : (1 : ℝ)/32 ≤ U)
    (hZ : 0 < Z) (hC : 0 < C) (hx : 1 ≤ x) (hB : 0 ≤ B)
    (hCx : C ≤ x^B) (hZx : Z ≤ x^B) :
    Real.log (2+1/spectralScale A V U Z C) ≤
      Real.log 66 + 2*B*Real.log x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hV0 : 0 < V := by linarith
  have hU0 : 0 < U := by linarith
  have hY : 0 < spectralScale A V U Z C := by
    unfold spectralScale
    positivity
  have hi := inverse_physical_scale_le hA hV hU hZ hC hx hB hCx hZx
  have hxp : 1 ≤ x^(2*B) := Real.one_le_rpow hx (by positivity)
  have hh : 2+1/spectralScale A V U Z C ≤ 66*x^(2*B) := by linarith
  apply (Real.log_le_log (by positivity) hh).trans_eq
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne',
    Real.log_rpow hx0]

/-- The literal original return uses C=N*R*S and Z=S^2. The first
original range N^2*S*R^2 <= x already gives the polynomial order THREE;
neither the two other saving inequalities nor Eq24 is needed here. -/
theorem original_literal_scale_polynomial {N M R S x : ℝ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hx : x = N*M) (hrange : N^2*S*R^2 ≤ x) :
    1 ≤ x ∧ N*R*S ≤ x^(3 : ℕ) ∧ S^2 ≤ x^(3 : ℕ) := by
  have hN0 : 0 ≤ N := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hN2 : 1 ≤ N^2 := by nlinarith [sq_nonneg (N-1)]
  have hR2 : 1 ≤ R^2 := by nlinarith [sq_nonneg (R-1)]
  have hNR : 1 ≤ N^2*S := by
    nlinarith [mul_le_mul_of_nonneg_left hS (sq_nonneg N)]
  have hx1 : 1 ≤ x := by
    rw [hx]
    nlinarith [mul_le_mul_of_nonneg_left hM hN0]
  have hNx : N ≤ x := by
    rw [hx]
    nlinarith [mul_le_mul_of_nonneg_left hM hN0]
  have hSx : S ≤ x := by
    have ha : S ≤ N^2*S := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hN2 hS0
    have hb : N^2*S ≤ N^2*S*R^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hR2 (mul_nonneg (sq_nonneg N) hS0)]
    exact (ha.trans hb).trans hrange
  have hRx : R ≤ x := by
    have ha : R ≤ R^2 := by
      nlinarith [mul_nonneg hR0 (sub_nonneg.mpr hR)]
    have hb : R^2 ≤ N^2*S*R^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hNR (sq_nonneg R)]
    exact (ha.trans hb).trans hrange
  refine ⟨hx1,?_,?_⟩
  · calc
      N*R*S ≤ x*x*x := by gcongr
      _ = x^(3 : ℕ) := by ring
  · have hh := pow_le_pow_left₀ hS0 hSx 2
    have hx3 : x^2 ≤ x^(3 : ℕ) := by
      nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
    exact hh.trans hx3

/-- Actual original formula, with the small U lower bound derived
from its positive integer coordinate. This is scale geometry only; it
does not identify an arbitrary arithmetic source with a spectral packet. -/
theorem original_literal_scale_log {A V N M R S x : ℝ}
    (hA : 1 ≤ A) (hV : (1 : ℝ)/32 ≤ V)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hx : x = N*M) (hrange : N^2*S*R^2 ≤ x)
    (n : ℕ) (hn : 1 ≤ n)
    (hchart : (n : ℝ)/(N*R^2*S^3/M) < 32) :
    Real.log (2+1/spectralScale A V (N*R^2*S^3/M) (S^2) (N*R*S)) ≤
      Real.log 66+6*Real.log x := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := by linarith
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  have hU : 0 < N*R^2*S^3/M := by positivity
  have hUlow := length_lower_of_positive_integer hU n hn hchart
  obtain ⟨hx1,hCx,hZx⟩ := original_literal_scale_polynomial hN hM hR hS hx hrange
  have hh := physical_log_le (B := 3) hA hV hUlow (by positivity) (by positivity)
    hx1 (by norm_num) (by simpa only [Real.rpow_natCast] using hCx)
      (by simpa only [Real.rpow_natCast] using hZx)
  simpa only [show (2 : ℝ)*3 = 6 by norm_num] using hh

def logarithmConstant (B : ℝ) : ℝ :=
  1 + |Real.log 16| + |Real.log 66| + 2*B

def transformConstant (B : ℝ) : ℝ :=
  (510*smallKernelConstant*(16 : ℝ)^exceptionalCap)*logarithmConstant B +
    largeTransformConstant

theorem transformConstant_pos {B : ℝ} (hB : 0 ≤ B) :
    0 < transformConstant B := by
  have hs := smallKernelConstant_pos
  have hl := largeTransformConstant_pos
  unfold transformConstant logarithmConstant
  positivity

/-- A genuine all-scale estimate of M's actual weight. Its entire
small-Y logarithm is derived above; the denominator 1+Y is preserved. -/
theorem allScaleTransformBudget_original_scale_le {A V U Z C x B : ℝ}
    (hA : 1 ≤ A) (hV : (1 : ℝ)/32 ≤ V) (hU : (1 : ℝ)/32 ≤ U)
    (hZ : 0 < Z) (hC : 0 < C) (hx : 1 ≤ x) (hB : 0 ≤ B)
    (hCx : C ≤ x^B) (hZx : Z ≤ x^B) :
    allScaleTransformBudget (spectralScale A V U Z C) ≤
      transformConstant B * (1+Real.log x) /
        (1+spectralScale A V U Z C) := by
  let Y := spectralScale A V U Z C
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hV0 : 0 < V := by linarith
  have hU0 : 0 < U := by linarith
  have hY : 0 < Y := by dsimp [Y,spectralScale]; positivity
  have hlogx := Real.log_nonneg hx
  have hs := smallKernelConstant_pos
  have hl := largeTransformConstant_pos
  have hK := transformConstant_pos hB
  have hc : 0 ≤ 510*smallKernelConstant*(16 : ℝ)^exceptionalCap := by positivity
  have hL : 0 ≤ logarithmConstant B := by unfold logarithmConstant; positivity
  have hlog := physical_log_le hA hV hU hZ hC hx hB hCx hZx
  change Real.log (2+1/Y) ≤ _ at hlog
  unfold allScaleTransformBudget
  change (if Y ≤ 1/16 then smallTransformBudget Y else largeTransformConstant/(1+Y)) ≤ _
  split_ifs with hsmall
  · have hYs : Y/16 ≤ 1 := by linarith
    have hlogY : |Real.log (Y/16)| = Real.log 16 - Real.log Y := by
      rw [abs_of_nonpos (Real.log_nonpos (by positivity) hYs),
        Real.log_div hY.ne' (by norm_num)]
      ring
    have hli : -Real.log Y ≤ Real.log (2+1/Y) := by
      have hh := Real.log_le_log (show 0 < 1/Y by positivity)
        (show 1/Y ≤ 2+1/Y by linarith)
      simpa only [one_div, Real.log_inv] using hh
    have hsmallLog : 1+|Real.log (Y/16)| ≤
        logarithmConstant B*(1+Real.log x) := by
      rw [hlogY]
      unfold logarithmConstant
      have hp := mul_nonneg
        (show 0 ≤ 1+|Real.log 16|+|Real.log 66| by positivity) hlogx
      nlinarith [le_abs_self (Real.log 16), le_abs_self (Real.log 66)]
    unfold smallTransformBudget
    apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 1+Y)
    have hh := mul_le_mul_of_nonneg_left hsmallLog hc
    have hrest : 0 ≤ largeTransformConstant*(1+Real.log x) := by positivity
    unfold transformConstant
    nlinarith only [hh,hrest]
  · apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 1+Y)
    have hh : largeTransformConstant ≤ transformConstant B := by
      unfold transformConstant
      nlinarith [mul_nonneg hc hL]
    exact hh.trans (le_mul_of_one_le_right hK.le (by linarith))

theorem log_power_eventually_le_rpow (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log x^n ≤ x^δ := by
  have hh := (Real.isLittleO_log_rpow_rpow_atTop (n : ℝ) hδ).eventuallyLE
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with x hx hx1
  simpa only [Real.rpow_natCast,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.log_nonneg hx1) n),
    abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx1) δ)] using hx

theorem one_add_log_sq_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, (1+Real.log x)^2 ≤ 4*x^δ := by
  filter_upwards [log_power_eventually_le_rpow 2 hδ,
    eventually_ge_atTop (Real.exp 1)] with x hx hxE
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxE
  have hl : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxE
  nlinarith

/-- Original caller weight after an arbitrary fixed finite additional
selectable cost q*eta. The actual M fourth-weight theorem is used, and
the same completedEnergy, same source rows and same interval survive.
The output is NOT Eq24 or a spectral norm theorem. -/
theorem exists_physical_J_caller_constant (B q δ : ℝ)
    (hB : 0 ≤ B) (hq : 0 ≤ q) (hδ : 0 < δ) :
    ∃ K X : ℝ, 0 < K ∧ ∀ (P : PacketData ι) (A C D x eta alpha : ℝ)
      (hA : 0 < A) (hC : 0 < C),
      1 ≤ A → (1 : ℝ)/32 ≤ P.V → (1 : ℝ)/32 ≤ P.U →
      0 < D → 1 ≤ x → X ≤ x → 0 ≤ eta →
      C ≤ x^B → P.Z ≤ x^B → P.V ≤ x^eta*C/D → |P.sigma| ≤ 1 →
      0 ≤ alpha → alpha ≤ exceptionalCap →
      x^(q*eta) *
        ‖∫ t : ℝ, positivePhysical (physicalScalePacket P A C D hA hC) alpha t‖^2 ≤
      K*x^((28+q)*eta+δ) *
        (((1+1/spectralScale A P.V P.U P.Z C)^alpha) /
          (1+spectralScale A P.V P.U P.Z C))^2 *
        completedEnergy (physicalScalePacket P A C D hA hC) := by
  obtain ⟨K0,hK0,hM⟩ :=
    exists_physical_positive_all_scale_smoothing_constant (ι := ι)
  have hKB := transformConstant_pos hB
  obtain ⟨X,hX⟩ := eventually_atTop.mp (one_add_log_sq_eventually hδ)
  refine ⟨4*K0*(transformConstant B)^2,X,by positivity,?_⟩
  intro P A C D x eta alpha hA hC hA1 hV hU hD hx hxX heta hCx hZx hcut hsigma ha0 ha
  let Y := spectralScale A P.V P.U P.Z C
  let Q := physicalScalePacket P A C D hA hC
  let w := (1+1/Y)^alpha/(1+Y)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hY : 0 < Y := by dsimp [Y,spectralScale]; positivity
  have he := completedEnergy_nonneg Q
  have hlocal := hM P A C D x eta alpha hA hC hD hx heta hcut hsigma ha0 ha
  have ht := allScaleTransformBudget_original_scale_le hA1 hV hU
    P.Z_pos hC hx hB hCx hZx
  have ht0 := allScaleTransformBudget_nonneg hY
  have hw0 : 0 ≤ (1+1/Y)^alpha := Real.rpow_nonneg (by positivity) _
  have htsq :
      (allScaleTransformBudget Y*(1+1/Y)^alpha)^2 ≤
        (transformConstant B)^2*(1+Real.log x)^2*w^2 := by
    have hh := pow_le_pow_left₀ (mul_nonneg ht0 hw0)
      (mul_le_mul_of_nonneg_right ht hw0) 2
    apply hh.trans_eq
    dsimp [w]
    ring
  have hlog := hX x hxX
  have hsq : (allScaleTransformBudget Y*(1+1/Y)^alpha)^2 ≤
      4*(transformConstant B)^2*x^δ*w^2 := by
    apply htsq.trans
    have hh := mul_le_mul_of_nonneg_left hlog (sq_nonneg (transformConstant B))
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg w)
    nlinarith only [hh']
  have hh := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ K0*x^((28 : ℝ)*eta) by positivity)
  have hh' := mul_le_mul_of_nonneg_right hh he
  have hfull := mul_le_mul_of_nonneg_left (hlocal.trans hh')
    (Real.rpow_nonneg hx0.le (q*eta))
  apply hfull.trans_eq
  have hp : x^(q*eta)*x^(28*eta)*x^δ = x^((28+q)*eta+δ) := by
    rw [← Real.rpow_add hx0,← Real.rpow_add hx0]
    congr 1
    ring
  calc
    _ = (4*K0*(transformConstant B)^2)*
        (x^(q*eta)*x^(28*eta)*x^δ)*w^2*completedEnergy Q := by ring
    _ = _ := by rw [hp]; rfl

/-- A fully explicit narrowing after the finite loss order q is fixed.
The 29 denominator deliberately leaves strict room beyond 28+q. -/
def allowance (epsilon sigma : ℝ) : ℝ := min epsilon (sigma/10)
def selectedEta (epsilon sigma q : ℝ) : ℝ :=
  allowance epsilon sigma / (4*(29+q))
def logarithmicAllowance (epsilon sigma : ℝ) : ℝ := allowance epsilon sigma/4

theorem selectedEta_with_cutoff_cost (epsilon sigma : ℝ) :
    selectedEta epsilon sigma 2 = min epsilon (sigma/10)/124 := by
  norm_num only [selectedEta,allowance]

theorem selectable_hierarchy {epsilon sigma q : ℝ}
    (hε : 0 < epsilon) (hσ : 0 < sigma) (hq : 0 ≤ q) :
    0 < selectedEta epsilon sigma q ∧
    0 < logarithmicAllowance epsilon sigma ∧
    selectedEta epsilon sigma q ≤ epsilon ∧
    (28+q)*selectedEta epsilon sigma q + logarithmicAllowance epsilon sigma ≤
      allowance epsilon sigma/2 ∧
    allowance epsilon sigma/2 ≤ epsilon/2 ∧
    allowance epsilon sigma/2 ≤ sigma/20 := by
  have ha : 0 < allowance epsilon sigma := lt_min hε (by positivity)
  have haε : allowance epsilon sigma ≤ epsilon := min_le_left _ _
  have haσ : allowance epsilon sigma ≤ sigma/10 := min_le_right _ _
  have hd : 0 < 4*(29+q) := by positivity
  have heq : selectedEta epsilon sigma q*(4*(29+q)) = allowance epsilon sigma := by
    unfold selectedEta
    exact div_mul_cancel₀ _ hd.ne'
  have he : 0 < selectedEta epsilon sigma q := div_pos ha hd
  have hqe : 0 ≤ q*selectedEta epsilon sigma q := mul_nonneg hq he.le
  refine ⟨he,div_pos ha (by norm_num),?_,?_,?_,?_⟩ <;>
    unfold logarithmicAllowance <;> nlinarith

/-- The selected parameter is actually fed to the M physical J caller.
Every scale and packet occurs after its uniform constant and threshold.
No old order-zero / x^(12 eta) caller is used. -/
theorem exists_selected_physical_J_caller (B epsilon sigma q : ℝ)
    (hB : 0 ≤ B) (hε : 0 < epsilon) (hσ : 0 < sigma) (hq : 0 ≤ q) :
    ∃ K X : ℝ, 0 < K ∧ ∀ (P : PacketData ι) (A C D x alpha : ℝ)
      (hA : 0 < A) (hC : 0 < C),
      1 ≤ A → (1 : ℝ)/32 ≤ P.V → (1 : ℝ)/32 ≤ P.U →
      0 < D → 1 ≤ x → X ≤ x → C ≤ x^B → P.Z ≤ x^B →
      P.V ≤ x^(selectedEta epsilon sigma q)*C/D → |P.sigma| ≤ 1 →
      0 ≤ alpha → alpha ≤ exceptionalCap →
      x^(q*selectedEta epsilon sigma q) *
        ‖∫ t : ℝ, positivePhysical (physicalScalePacket P A C D hA hC) alpha t‖^2 ≤
      K*x^(allowance epsilon sigma/2) *
        (((1+1/spectralScale A P.V P.U P.Z C)^alpha) /
          (1+spectralScale A P.V P.U P.Z C))^2 *
        completedEnergy (physicalScalePacket P A C D hA hC) := by
  obtain ⟨he,hδ,_,hcost,_,_⟩ := selectable_hierarchy hε hσ hq
  obtain ⟨K,X,hK,hcaller⟩ := exists_physical_J_caller_constant (ι := ι)
    B q (logarithmicAllowance epsilon sigma) hB hq hδ
  refine ⟨K,X,hK,?_⟩
  intro P A C D x alpha hA hC hA1 hV hU hD hx hxX hCx hZx hcut hsigma ha0 ha
  have hh := hcaller P A C D x (selectedEta epsilon sigma q) alpha hA hC
    hA1 hV hU hD hx hxX he.le hCx hZx hcut hsigma ha0 ha
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (completedEnergy_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx hcost) hK.le

/-- The once-only retained phase is paid at the same ordered hierarchy.
This is the actual original E3 theorem, with its original prefix envelope;
no association between that envelope and a spectral energy is asserted. -/
theorem exists_selected_original_E3_threshold (epsilon sigma : ℝ)
    (hε : 0 < epsilon) (hσ : 0 < sigma) :
    ∃ X : ℝ, ∀ (b : ℕ) (σ κ c0 : ℝ)
      (atom : MediumAtom) (z y : ℝ) (k : Key)
      (hA : MediumAdmissible b σ κ c0 atom)
      (hκ : 0 ≤ κ) (Csep : ℕ) (j : Fin 3) (small : ℕ)
      (hd : small ∈ activeD atom k)
      (negative : Bool), X ≤ atom.scale →
      let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
      let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
      ‖B.E3‖ ≤ actualPrefixEnvelope T *
          (retainedConstant * atom.scale^(5*κ+logarithmicAllowance epsilon sigma)) := by
  have hδ : 0 < logarithmicAllowance epsilon sigma :=
    (selectable_hierarchy hε hσ (show (0 : ℝ) ≤ 0 from le_rfl)).2.1
  exact ImbalancedChen.Part3.OriginalRetainedPhaseOriginalScale20261102.actual_E3_original_scale_epsilon
    (logarithmicAllowance epsilon sigma) hδ

theorem combined_selectable_cost {epsilon sigma q : ℝ}
    (hε : 0 < epsilon) (hσ : 0 < sigma) (hq : 0 ≤ q) :
    (28+q)*selectedEta epsilon sigma q+2*logarithmicAllowance epsilon sigma ≤
      3*allowance epsilon sigma/4 ∧
    3*allowance epsilon sigma/4 ≤ 3*epsilon/4 ∧
    3*allowance epsilon sigma/4 ≤ 3*sigma/40 := by
  obtain ⟨_,_,_,hcost,_,_⟩ := selectable_hierarchy hε hσ hq
  have hεa : allowance epsilon sigma ≤ epsilon := min_le_left _ _
  have hσa : allowance epsilon sigma ≤ sigma/10 := min_le_right _ _
  unfold logarithmicAllowance at *
  constructor
  · linarith
  constructor <;> linarith

/-- Both printed original saving exponents retain a margin stronger
than sigma/2. This includes the full J squared loss as a conservative
debit; subsequent square/fourth roots only improve that payment. -/
theorem original_two_saving_margins {epsilon sigma kappa q : ℝ}
    (hε : 0 < epsilon) (hσ : 0 < sigma) (hq : 0 ≤ q)
    (hκ : kappa ≤ sigma/100) :
    -4*sigma+5*kappa+
      ((28+q)*selectedEta epsilon sigma q+2*logarithmicAllowance epsilon sigma)
        ≤ -sigma/2 ∧
    -15*sigma/4+21*kappa/4+
      ((28+q)*selectedEta epsilon sigma q+2*logarithmicAllowance epsilon sigma)
        ≤ -sigma/2 := by
  obtain ⟨hcost,_,hbudget⟩ := combined_selectable_cost hε hσ hq
  constructor <;> linarith

end
end ImbalancedChen.Part3.ActualExceptionalJSelectableEta20261102
