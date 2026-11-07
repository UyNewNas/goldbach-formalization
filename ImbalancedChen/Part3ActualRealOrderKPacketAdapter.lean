import ImbalancedChen.Part3RealOrderKExceptional
import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.  This selects the actual integral
realization of real-order K_α(q)/q for an exceptional packet.  The order
bound is explicit; the original packet's fields and physical region are
retained.  There is no asserted equality to a full exceptional Kuznetsov
kernel or to its missing spectral normalization.
-/

namespace ImbalancedChen.Part3.ActualRealOrderKPacketAdapterSourceOnly
noncomputable section

open Classical Set MeasureTheory Filter
open scoped BigOperators Topology
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
  (point4 actualCoeff spectralTest spectralMode chi chi_mul_actual)
open ImbalancedChen.Part3.ActualNormalizedSmoothF (normalizedF)
open RealOrderKExceptionalSourceOnly
open ActualCommonHeightKGramSourceOnly (completedPacketSum)

variable {ι : Type*}

/-- The exceptional real-order K/q kernel on a strictly positive half-line. -/
def halfLineRealOrderKernel (a : ℝ) (ha : 0 < a) (α : ℝ)
    (hα : |α| ≤ (7/32 : ℝ)) : C(Ici a, ℂ) where
  toFun q := (realOrderK α (q : ℝ) : ℂ) / ((q : ℝ) : ℂ)
  continuous_toFun := by
    have hαsub : α ∈ Icc (-(7/32 : ℝ)) (7/32 : ℝ) :=
      abs_le.mp hα
    have hpair : Continuous
        (fun q : Ici a =>
          ((⟨α, hαsub⟩ : Icc (-(7/32 : ℝ)) (7/32 : ℝ)), q)) := by
      fun_prop
    have hK : Continuous (fun q : Ici a => (realOrderK α (q : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((realOrderK_joint_continuous a ha).comp hpair)
    have hq : Continuous (fun q : Ici a => ((q : ℝ) : ℂ)) := by
      fun_prop
    exact hK.div hq (fun q => Complex.ofReal_ne_zero.mpr
      (lt_of_lt_of_le ha q.property).ne')

def extendedRealOrderKernel (a : ℝ) (ha : 0 < a) (α : ℝ)
    (hα : |α| ≤ (7/32 : ℝ)) : C(ℝ, ℂ) :=
  extendKernelFromHalfLine a (halfLineRealOrderKernel a ha α hα)

theorem extendedRealOrderKernel_eq (a : ℝ) (ha : 0 < a)
    (α q : ℝ) (hα : |α| ≤ (7/32 : ℝ)) (hq : a ≤ q) :
    extendedRealOrderKernel a ha α hα q =
      (realOrderK α q : ℂ) / (q : ℂ) := by
  exact extendKernelFromHalfLine_eq a
    (halfLineRealOrderKernel a ha α hα) q hq

theorem extendedRealOrderKernel_eq_on_region (P : PacketData ι)
    (α q : ℝ) (hα : |α| ≤ (7/32 : ℝ)) (hq : q ∈ P.region) :
    extendedRealOrderKernel (P.Y0/32)
        (by have h := P.Y0_pos; positivity) α hα q =
      (realOrderK α q : ℂ) / (q : ℂ) := by
  apply extendedRealOrderKernel_eq
  change P.Y0/16 ≤ q ∧ q ≤ 16*P.Y0 at hq
  linarith [P.Y0_pos]

/-- The common L1 envelope integrates exactly to `exp(8/a)` on u>0. -/
private lemma realOrderEnvelope_integral {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi (0 : ℝ), Real.exp (8/a) * Real.exp (-u)) =
      Real.exp (8/a) := by
  rw [integral_const_mul]
  have he := integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have he' : (∫ u in Ioi (0 : ℝ), Real.exp (-u)) = 1 := by
    simpa using he
  rw [he', mul_one]

theorem realOrderK_abs_le (α : ℝ) {a q : ℝ}
    (ha : 0 < a) (hq : a ≤ q) (hα : |α| ≤ (7/32 : ℝ)) :
    |realOrderK α q| ≤ Real.exp (8/a) := by
  calc
    |realOrderK α q| = ‖∫ u in Ioi (0 : ℝ), realOrderIntegrand α q u‖ := by
      rw [Real.norm_eq_abs]
      rfl
    _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (8/a) * Real.exp (-u) := by
      apply norm_integral_le_of_norm_le (RealOrderKExceptionalSourceOnly.realOrderEnvelope_integrable ha)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact realOrderIntegrand_norm_le ha hq hα hu.le
    _ = Real.exp (8/a) := realOrderEnvelope_integral ha

/-- An explicit (conservative) physical-region sup budget for K_α(q)/q. -/
theorem extendedRealOrderKernel_norm_le_on_region (P : PacketData ι)
    (α q : ℝ) (hα : |α| ≤ (7/32 : ℝ)) (hq : q ∈ P.region) :
    ‖extendedRealOrderKernel (P.Y0/32)
      (by have h := P.Y0_pos; positivity) α hα q‖ ≤
      Real.exp (8/(P.Y0/32)) / (P.Y0/32) := by
  rw [extendedRealOrderKernel_eq_on_region P α q hα hq]
  have ha : 0 < P.Y0/32 := by
    have h := P.Y0_pos
    positivity
  have hqlo : P.Y0/32 ≤ q := by
    change P.Y0/16 ≤ q ∧ q ≤ 16*P.Y0 at hq
    linarith [P.Y0_pos]
  have hqpos : 0 < q := lt_of_lt_of_le ha hqlo
  calc
    ‖(realOrderK α q : ℂ)/(q : ℂ)‖ = |realOrderK α q|/q := by
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
    _ ≤ Real.exp (8/(P.Y0/32))/q :=
      div_le_div_of_nonneg_right (realOrderK_abs_le α ha hqlo hα) hqpos.le
    _ ≤ Real.exp (8/(P.Y0/32))/(P.Y0/32) := by
      gcongr

def restrictedRealOrderKernel (P : PacketData ι) (α : ℝ)
    (hα : |α| ≤ (7/32 : ℝ)) : C(P.region, ℂ) :=
  (extendedRealOrderKernel (P.Y0/32)
    (by have h := P.Y0_pos; positivity) α hα).comp
      ⟨Subtype.val, continuous_subtype_val⟩

theorem restrictedRealOrderKernel_eq (P : PacketData ι) (α : ℝ)
    (hα : |α| ≤ (7/32 : ℝ)) (q : P.region) :
    restrictedRealOrderKernel P α hα q =
      (realOrderK α (q : ℝ) : ℂ)/((q : ℝ) : ℂ) := by
  change extendedRealOrderKernel (P.Y0/32)
    (by have h := P.Y0_pos; positivity) α hα (q : ℝ) = _
  exact extendedRealOrderKernel_eq_on_region P α (q : ℝ) hα q.property

theorem restrictedRealOrderKernel_norm_le (P : PacketData ι) (α : ℝ)
    (hα : |α| ≤ (7/32 : ℝ)) :
    ‖restrictedRealOrderKernel P α hα‖ ≤
      Real.exp (8/(P.Y0/32)) / (P.Y0/32) := by
  apply (ContinuousMap.norm_le _ (by
    have h := P.Y0_pos
    positivity)).mpr
  intro q
  exact extendedRealOrderKernel_norm_le_on_region P α (q : ℝ) hα q.property

/-- Replace only the original kernel field; every packet and carrier is kept. -/
def withRealOrderKKernel (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ)
    (hα : ∀ j m n, |α j m n| ≤ (7/32 : ℝ)) : PacketData ι :=
  { P with
    kernel := fun j m n =>
      extendedRealOrderKernel (P.Y0/32)
        (by have h := P.Y0_pos; positivity) (α j m n) (hα j m n) }

theorem withRealOrderKKernel_restrictedKernel (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ)
    (hα : ∀ j m n, |α j m n| ≤ (7/32 : ℝ))
    (j : ι) (m n : ℕ) :
    (withRealOrderKKernel P α hα).restrictedKernel j m n =
      restrictedRealOrderKernel P (α j m n) (hα j m n) := by
  rfl

theorem withRealOrderKKernel_restrictedKernel_apply (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ)
    (hα : ∀ j m n, |α j m n| ≤ (7/32 : ℝ))
    (j : ι) (m n : ℕ) (q : P.region) :
    (withRealOrderKKernel P α hα).restrictedKernel j m n q =
      (realOrderK (α j m n) (q : ℝ) : ℂ)/((q : ℝ) : ℂ) := by
  rw [withRealOrderKKernel_restrictedKernel]
  exact restrictedRealOrderKernel_eq P (α j m n) (hα j m n) q

theorem withRealOrderKKernel_restrictedKernel_norm_le (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ)
    (hα : ∀ j m n, |α j m n| ≤ (7/32 : ℝ))
    (j : ι) (m n : ℕ) :
    ‖(withRealOrderKKernel P α hα).restrictedKernel j m n‖ ≤
      Real.exp (8/(P.Y0/32)) / (P.Y0/32) := by
  rw [withRealOrderKKernel_restrictedKernel]
  exact restrictedRealOrderKernel_norm_le P (α j m n) (hα j m n)

/-- The literal physical packet after replacing its q kernel by real-order K. -/
def realOrderPhysical (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ) (q : ℝ) : ℂ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    signedCoefficient P.negativeCusp (P.packet j) n *
      ((realOrderK (α j m n) q : ℂ)/(q : ℂ)) *
      normalizedF P.rho P.sigma
        (point4 (q/P.Y0) ((m : ℝ)/P.V)
          ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
          (((P.packet j).level : ℝ)/P.Z))

def realOrderModeFunction (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) (q : ℝ) : ℂ :=
  spectralTest k P.Y0 q *
    (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
      (P.completed k).weight m *
        signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
          ((realOrderK (α j m n) q : ℂ)/(q : ℂ)))

private lemma realOrderPhysical_zero_off (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ) (q : ℝ) (hq : q ∉ P.region) :
    realOrderPhysical P α q = 0 := by
  have hF (v w z : ℝ) :
      normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) = 0 := by
    have hh := chi_mul_actual P.rho P.sigma (point4 (q/P.Y0) v w z)
    change (chi (q/P.Y0) : ℂ) *
      normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) =
        normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) at hh
    rw [P.chi_scaled_zero_off q hq] at hh
    simpa only [Complex.ofReal_zero, zero_mul] using hh.symm
  simp only [realOrderPhysical, hF, mul_zero, Finset.sum_const_zero]

theorem withRealOrderKKernel_physical (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ)
    (hα : ∀ j m n, |α j m n| ≤ (7/32 : ℝ)) :
    (withRealOrderKKernel P α hα).physical = realOrderPhysical P α := by
  funext q
  by_cases hq : q ∈ P.region
  · change
      (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
        signedCoefficient P.negativeCusp (P.packet j) n *
          extendedRealOrderKernel (P.Y0/32)
            (by have h := P.Y0_pos; positivity) (α j m n) (hα j m n) q *
          normalizedF P.rho P.sigma
            (point4 (q/P.Y0) ((m : ℝ)/P.V)
              ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
              (((P.packet j).level : ℝ)/P.Z))) = realOrderPhysical P α q
    unfold realOrderPhysical
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    rw [extendedRealOrderKernel_eq_on_region P (α j m n) q (hα j m n) hq]
  · rw [(withRealOrderKKernel P α hα).physical_zero_off q hq,
      realOrderPhysical_zero_off P α q hq]

theorem withRealOrderKKernel_modeFunction (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ)
    (hα : ∀ j m n, |α j m n| ≤ (7/32 : ℝ))
    (k : D4 → ℤ) :
    (withRealOrderKKernel P α hα).modeFunction k =
      realOrderModeFunction P α k := by
  funext q
  change spectralTest k P.Y0 q *
    (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
      (P.completed k).weight m *
        signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
          extendedRealOrderKernel (P.Y0/32)
            (by have h := P.Y0_pos; positivity) (α j m n) (hα j m n) q) =
      realOrderModeFunction P α k q
  unfold realOrderModeFunction
  by_cases hq : q ∈ P.region
  · apply congrArg (fun z : ℂ => spectralTest k P.Y0 q * z)
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    rw [extendedRealOrderKernel_eq_on_region P (α j m n) q (hα j m n) hq]
  · simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
      Complex.ofReal_zero, zero_mul]

theorem realOrderPhysical_integrable (P : PacketData ι)
    (α : ι → ℕ → ℕ → ℝ)
    (hα : ∀ j m n, |α j m n| ≤ (7/32 : ℝ)) :
    Integrable (realOrderPhysical P α) := by
  rw [← withRealOrderKKernel_physical P α hα]
  exact (withRealOrderKKernel P α hα).physical_integrable

/-- Common real order across the entire finite packet. -/
def commonRealOrder (α : ℝ) : ι → ℕ → ℕ → ℝ := fun _ _ _ => α

def realOrderTestTransform (P : PacketData ι) (k : D4 → ℤ)
    (α : ℝ) : ℂ :=
  ∫ q : ℝ, spectralTest k P.Y0 q *
    ((realOrderK α q : ℂ)/(q : ℂ))

theorem realOrderTestTransform_integrable (P : PacketData ι)
    (k : D4 → ℤ) (α : ℝ) (hα : |α| ≤ (7/32 : ℝ)) :
    Integrable (fun q : ℝ => spectralTest k P.Y0 q *
      ((realOrderK α q : ℂ)/(q : ℂ))) := by
  let K : C(ℝ, ℂ) := extendedRealOrderKernel (P.Y0/32)
    (by have h := P.Y0_pos; positivity) α hα
  have hc : Continuous (fun q : ℝ => spectralTest k P.Y0 q * K q) :=
    (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous.mul
      K.continuous
  have hi : Integrable (fun q : ℝ => spectralTest k P.Y0 q * K q) := by
    apply hc.integrable_of_hasCompactSupport
    apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
    intro q hq
    by_contra hn
    apply hq
    simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hn,
      Complex.ofReal_zero, zero_mul]
  have he : (fun q : ℝ => spectralTest k P.Y0 q * K q) =
      (fun q : ℝ => spectralTest k P.Y0 q *
        ((realOrderK α q : ℂ)/(q : ℂ))) := by
    funext q
    by_cases hq : q ∈ P.region
    · change spectralTest k P.Y0 q *
        extendedRealOrderKernel (P.Y0/32)
          (by have h := P.Y0_pos; positivity) α hα q = _
      rw [extendedRealOrderKernel_eq_on_region P α q hα hq]
    · simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
        Complex.ofReal_zero, zero_mul]
  rw [← he]
  exact hi

theorem common_realOrder_mode_integrable (P : PacketData ι)
    (k : D4 → ℤ) (α : ℝ) (hα : |α| ≤ (7/32 : ℝ)) :
    Integrable (realOrderModeFunction P (commonRealOrder α) k) := by
  rw [← withRealOrderKKernel_modeFunction P (commonRealOrder α)
    (fun _ _ _ => hα) k]
  have hc : Continuous
      ((withRealOrderKKernel P (commonRealOrder α) (fun _ _ _ => hα)).modeFunction k) := by
    have hs :=
      (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous
    unfold PacketData.modeFunction PacketData.modeCore
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  apply hq
  change spectralTest k P.Y0 q * _ = 0
  simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hn,
    Complex.ofReal_zero, zero_mul]

theorem common_realOrder_mode_factorization (P : PacketData ι)
    (k : D4 → ℤ) (α q : ℝ) :
    realOrderModeFunction P (commonRealOrder α) k q =
      (spectralTest k P.Y0 q * ((realOrderK α q : ℂ)/(q : ℂ))) *
        completedPacketSum P k := by
  unfold realOrderModeFunction commonRealOrder completedPacketSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem actual_common_realOrder_modeIntegral (P : PacketData ι)
    (k : D4 → ℤ) (α : ℝ) :
    (∫ q : ℝ, realOrderModeFunction P (commonRealOrder α) k q) =
      realOrderTestTransform P k α * completedPacketSum P k := by
  calc
    (∫ q : ℝ, realOrderModeFunction P (commonRealOrder α) k q) =
        ∫ q : ℝ, (spectralTest k P.Y0 q *
          ((realOrderK α q : ℂ)/(q : ℂ))) * completedPacketSum P k := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun q => common_realOrder_mode_factorization P k α q)
    _ = realOrderTestTransform P k α * completedPacketSum P k := by
      exact integral_mul_const (completedPacketSum P k) _

end
end ImbalancedChen.Part3.ActualRealOrderKPacketAdapterSourceOnly
