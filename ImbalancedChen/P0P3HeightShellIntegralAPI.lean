import ImbalancedChen.P0HeightPublicAPI
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED / 20261024z-P0. No acceptance credit.
P0HeightPublicAPI denotes the proposed module placement of the sibling draft.
All height measures below are ordinary unweighted Lebesgue measure on a finite
closed interval. No automorphic measure or Plancherel identity is introduced.
-/

namespace ImbalancedChen.Part3.P0P3HeightShellIntegralAPISourceOnly
noncomputable section

open Set MeasureTheory Filter
open scoped Topology BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode)
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly
open ImaginaryOrderKHeightDecaySourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open P0HeightPublicAPISourceOnly

variable {ι : Type*}

/-- The transform is literally its supported physical-q integral. -/
theorem kTestTransform_eq_setIntegral (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k t = ∫ q in P.region,
      spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ)/(q : ℂ)) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
    Complex.ofReal_zero, zero_mul]

/-- A fixed supported q lies on the proved positive-axis continuity domain. -/
theorem testKIntegrand_height_continuous (P : PacketData ι) (k : D4 → ℤ)
    (q : ℝ) (hq : q ∈ P.region) :
    Continuous (fun t : ℝ =>
      spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ)/(q : ℂ))) := by
  have hqp : 0 < q := by
    have hl : P.Y0/16 ≤ q := hq.1
    linarith [P.Y0_pos]
  have hpair : Continuous (fun t : ℝ =>
      (t, (⟨q, le_rfl⟩ : Ici q))) := by fun_prop
  have hK : Continuous (fun t : ℝ => (imaginaryOrderK t q : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((imaginaryOrderK_joint_continuous q hqp).comp hpair)
  exact continuous_const.mul (hK.div_const (q : ℂ))

/-- A genuine continuity proof for the actual transform; its dominating
constant is the existing all-height bound on the finite physical region. -/
theorem kTestTransform_continuous (P : PacketData ι) (k : D4 → ℤ) :
    Continuous (kTestTransform P k) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  change Tendsto (fun r : ℝ => kTestTransform P k r) (𝓝 t)
    (𝓝 (kTestTransform P k t))
  simp_rw [kTestTransform_eq_setIntegral P k]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _q : ℝ => 512/P.Y0^2)
  · apply Eventually.of_forall
    intro r
    exact (kTestTransform_integrable P k r).aestronglyMeasurable.restrict
  · apply Eventually.of_forall
    intro r
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    rw [← spectralTest_mul_extendedKKernel P k r q, norm_mul]
    calc
      ‖spectralTest k P.Y0 q‖ *
          ‖extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) r q‖ ≤
        1 * (512/P.Y0^2) :=
          mul_le_mul (spectralTest_norm_le_one P k q)
            (extendedKKernel_norm_le_on_region P r q hq)
            (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  · exact continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    exact (testKIntegrand_height_continuous P k q hq).continuousAt

/-- Exact existing factorization supplies continuity of the integrated row. -/
theorem common_height_modeIntegral_continuous (P : PacketData ι) (k : D4 → ℤ) :
    Continuous (fun t : ℝ => ∫ q : ℝ, kModeFunction P (commonHeight t) k q) := by
  have heq : (fun t : ℝ => ∫ q : ℝ, kModeFunction P (commonHeight t) k q) =
      (fun t : ℝ => kTestTransform P k t * completedPacketSum P k) :=
    funext (actual_common_height_modeIntegral P k)
  rw [heq]
  exact (kTestTransform_continuous P k).mul continuous_const

/-- Finite-interval norm-square integration, with all well-definedness and
positivity facts included. Concrete actual-K consumers below discharge hB. -/
theorem compact_energy_budget {f : ℝ → ℂ} (hf : Continuous f)
    {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc a b, ‖f t‖ ≤ B) :
    IntegrableOn (fun t => ‖f t‖^2) (Icc a b) ∧
      0 ≤ (∫ t in Icc a b, ‖f t‖^2) ∧
      (∫ t in Icc a b, ‖f t‖^2) ≤ B^2 * (b-a) := by
  refine ⟨(hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc,
    integral_nonneg (fun t => sq_nonneg _), ?_⟩
  calc
    (∫ t in Icc a b, ‖f t‖^2) ≤ ‖∫ t in Icc a b, ‖f t‖^2‖ :=
      le_abs_self _
    _ ≤ B^2 * (volume : Measure ℝ).real (Icc a b) := by
      apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
      intro t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := hbound t ht
      nlinarith [norm_nonneg (f t)]
    _ = B^2 * (b-a) := by rw [Real.volume_real_Icc_of_le hab]

/-- An arbitrary finite closed subinterval of a positive absolute-height
shell. Its integral is ordinary dt and its length is exactly b-a. -/
theorem kTestTransform_shell_energy_budget (P : PacketData ι) (k : D4 → ℤ)
    {a b T : ℝ} (hab : a ≤ b) (hT : 0 < T)
    (hshell : ∀ t ∈ Icc a b, T ≤ |t|) :
    IntegrableOn (fun t => ‖kTestTransform P k t‖^2) (Icc a b) ∧
      0 ≤ (∫ t in Icc a b, ‖kTestTransform P k t‖^2) ∧
      (∫ t in Icc a b, ‖kTestTransform P k t‖^2) ≤
        (40800/(P.Y0*T^2))^2 * (b-a) := by
  exact compact_energy_budget (kTestTransform_continuous P k) hab
    (by have h := P.Y0_pos; positivity)
    (fun t ht => kTestTransform_norm_le_on_shell P k hT (hshell t ht))

/-- The integrated actual mode keeps its complete frozen coefficient energy. -/
theorem common_height_modeIntegral_shell_energy_budget (P : PacketData ι)
    (k : D4 → ℤ) {a b T : ℝ} (hab : a ≤ b) (hT : 0 < T)
    (hshell : ∀ t ∈ Icc a b, T ≤ |t|) :
    IntegrableOn (fun t => ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2)
      (Icc a b) ∧
      0 ≤ (∫ t in Icc a b,
        ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) ∧
      (∫ t in Icc a b, ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) ≤
        (40800/(P.Y0*T^2))^2 * ‖completedPacketSum P k‖^2 * (b-a) := by
  have h := compact_energy_budget (common_height_modeIntegral_continuous P k)
    hab (B := (40800/(P.Y0*T^2)) * ‖completedPacketSum P k‖)
    (by have hY := P.Y0_pos; positivity) (by
      intro t ht
      rw [actual_common_height_modeIntegral, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (kTestTransform_norm_le_on_shell P k hT (hshell t ht)) (norm_nonneg _))
  simpa only [mul_pow, mul_assoc] using h

/-- Convenient positive-shell specialization; no quantified shell proof
or nonzero-height proof is required from this consumer. -/
theorem positive_shell_modeIntegral_energy_budget (P : PacketData ι)
    (k : D4 → ℤ) {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    IntegrableOn (fun t => ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2)
      (Icc T U) ∧
      0 ≤ (∫ t in Icc T U,
        ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) ∧
      (∫ t in Icc T U, ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) ≤
        (40800/(P.Y0*T^2))^2 * ‖completedPacketSum P k‖^2 * (U-T) := by
  exact common_height_modeIntegral_shell_energy_budget P k hTU hT
    (fun t ht => ht.1.trans (le_abs_self t))

/-- Fixed-q raw rows reuse the FullGram continuity theorem directly. -/
theorem modeRow_shell_energy_budget (P : PacketData ι) (k : D4 → ℤ)
    (q : ℝ) (hq : q ∈ P.region) {a b T : ℝ} (hab : a ≤ b) (hT : 0 < T)
    (hshell : ∀ t ∈ Icc a b, T ≤ |t|) :
    IntegrableOn (fun t => ‖modeRow P k q t‖^2) (Icc a b) ∧
      0 ≤ (∫ t in Icc a b, ‖modeRow P k q t‖^2) ∧
      (∫ t in Icc a b, ‖modeRow P k q t‖^2) ≤
        ((2560/(P.Y0^2*T^2)) * ‖completedPacketSum P k‖)^2 * (b-a) := by
  have hqp : 0 < q := by
    have hl : P.Y0/16 ≤ q := hq.1
    linarith [P.Y0_pos]
  apply compact_energy_budget (modeRow_continuous P k hqp) hab
    (by positivity)
  intro t ht
  have htn : t ≠ 0 := by
    intro hz
    have hs := hshell t ht
    simp only [hz, abs_zero] at hs
    exact (not_le_of_gt hT) hs
  have hsquare : T^2 ≤ t^2 := by
    have hs := hshell t ht
    nlinarith [sq_abs t, abs_nonneg t]
  rw [modeRow_eq_actual, common_height_mode_factorization, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (testKIntegrand_norm_le_quadratic P k htn q hq).trans
    (div_le_div_of_nonneg_left (by norm_num) (by have hY := P.Y0_pos; positivity)
      (mul_le_mul_of_nonneg_left hsquare (sq_nonneg P.Y0)))

end
end ImbalancedChen.Part3.P0P3HeightShellIntegralAPISourceOnly

