import ImbalancedChen.Part3ActualFullPacketModeL2
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED, 2026-10-24.  The Fourier series here is the
literal normalizedF reconstruction of the actual finite physical packet.
The q amplitudes have exactly the original rows, m interval and signed
coprime coefficients. The final tail norm uses ordinary raw-height
Plancherel and the actual coefficient L1 series; no spectral saving occurs.
-/

namespace ImbalancedChen.Part3.ActualFullPacketFourierTailL2SourceOnly
noncomputable section
open Classical Set MeasureTheory Filter
open scoped BigOperators FourierTransform Topology
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
  (point4 actualCoeff spectralTest actual_global_separation_hasSum)
open ImbalancedChen.Part3.ActualNormalizedSmoothF (normalizedF)
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open ActualFullPacketFourierBridgeSourceOnly
open ActualFullPacketRawHeightEnergySourceOnly
open ActualFullPacketModeL2SourceOnly
open ActualKTransformFourier20261024z
open ActualKFullHeightEnergy20261024z
open ActualKHeightFourierTail20261024z

variable {ι : Type*}

/-- Actual Fourier-mode q amplitude after the completed m sum and original
modulated coprime packet have been collected. -/
def modeAmplitude (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) : ℂ :=
  actualCoeff P.rho P.sigma k * actualKAmplitude P k q *
    completedPacketSum P k

theorem modeAmplitude_physical (P : PacketData ι) (k : D4 → ℤ) :
    PhysicalAmplitude P (modeAmplitude P k) := by
  constructor
  · unfold modeAmplitude
    exact continuous_const.mul
      ((actualKAmplitude_physical P k).1.mul continuous_const)
  · intro q hq
    simp only [modeAmplitude, (actualKAmplitude_physical P k).2 q hq,
      mul_zero, zero_mul]

/-- Pointwise Fourier reconstruction of the q amplitude.  This consumes
the actual four-coordinate normalizedF separation, before K is inserted. -/
theorem modeAmplitude_hasSum (P : PacketData ι) (q : ℝ) (J0 : ℕ) :
    HasSum (fun k : D4 → ℤ => modeAmplitude P k q)
      (physicalAmplitudeRaw P q) := by
  have hp (j : ι) (hj : j ∈ P.rows) (m : ℕ) (hm : m ∈ P.mCarrier)
      (n : ℕ) (hn : n ∈ P.nCarrier j) :
      HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
        spectralTest k P.Y0 q * (P.completed k).weight m *
          signedCoefficient P.negativeCusp
            (modePacket (P.packet j) k P.U P.Z) n / (q : ℂ))
        ((signedCoefficient P.negativeCusp (P.packet j) n / (q : ℂ)) *
          normalizedF P.rho P.sigma
            (point4 (q/P.Y0) ((m : ℝ)/P.V)
              ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
              (((P.packet j).level : ℝ)/P.Z))) := by
    have h := actual_global_separation_hasSum P.rho P.sigma J0
      (q/P.Y0) ((m : ℝ)/P.V)
      ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
      (((P.packet j).level : ℝ)/P.Z)
      (P.m_normalized m hm) (P.n_normalized j hj n hn)
      (P.level_normalized j hj)
    apply (HasSum.mul_left
      (signedCoefficient P.negativeCusp (P.packet j) n / (q : ℂ)) h).congr_fun
    intro k
    rw [P.completed_weight_mem k m hm, signedCoefficient_modePacket]
    dsimp [spectralTest]
    ring
  have hs := hasSum_sum (s := P.rows) (fun j hj =>
    hasSum_sum (s := P.mCarrier) (fun m hm =>
      hasSum_sum (s := P.nCarrier j) (fun n hn => hp j hj m hm n hn)))
  have hvalue : physicalAmplitudeRaw P q =
      ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
        (signedCoefficient P.negativeCusp (P.packet j) n / (q : ℂ)) *
          normalizedF P.rho P.sigma
            (point4 (q/P.Y0) ((m : ℝ)/P.V)
              ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
              (((P.packet j).level : ℝ)/P.Z)) := by
    unfold physicalAmplitudeRaw physicalNumerator
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  rw [hvalue]
  apply hs.congr_fun
  intro k
  unfold modeAmplitude
  rw [actualKAmplitude_eq]
  unfold completedPacketSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- The original coefficient series is absolutely summable; the exact
finite packet mass supplies a common bound for all q and modes. -/
theorem modeAmplitude_norm_le (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    ‖modeAmplitude P k q‖ ≤
      ‖actualCoeff P.rho P.sigma k‖ *
        (coefficientMass P * (16/P.Y0)) := by
  by_cases hq : q ∈ P.region
  · have hqlo : P.Y0/16 ≤ q := hq.1
    have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hqlo
    have hs : ‖spectralTest k P.Y0 q‖ ≤ 1 := by
      simpa only [spectralTest] using
        PacketData.spectralMode_norm_le_one k (q/P.Y0)
    have hratio : 1 ≤ (16/P.Y0)*q := by
      have h : (1 : ℝ) ≤ (16*q)/P.Y0 :=
        (le_div_iff₀ P.Y0_pos).2 (by nlinarith [hqlo])
      convert h using 1 <;> ring
    have hk : ‖actualKAmplitude P k q‖ ≤ 16/P.Y0 := by
      rw [actualKAmplitude_eq, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hqpos]
      exact (div_le_iff₀ hqpos).2 (by nlinarith)
    rw [modeAmplitude, norm_mul, norm_mul]
    have hpack := completedPacketSum_norm_le_coefficientMass P k
    have hmiddle : ‖actualKAmplitude P k q‖ *
        ‖completedPacketSum P k‖ ≤
          (16/P.Y0) * coefficientMass P :=
      mul_le_mul hk hpack (norm_nonneg _) (by positivity)
    calc
      ‖actualCoeff P.rho P.sigma k‖ *
          ‖actualKAmplitude P k q‖ * ‖completedPacketSum P k‖ ≤
        ‖actualCoeff P.rho P.sigma k‖ *
          ((16/P.Y0) * coefficientMass P) := by
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_left hmiddle (norm_nonneg _)
      _ = _ := by ring
  · rw [(modeAmplitude_physical P k).2 q hq, norm_zero]
    positivity

def tailAmplitude (P : PacketData ι) (F : Finset (D4 → ℤ)) (q : ℝ) : ℂ :=
  physicalAmplitudeRaw P q - ∑ k ∈ F, modeAmplitude P k q

def tailCoefficientMass (P : PacketData ι) (F : Finset (D4 → ℤ)) : ℝ :=
  ∑' k : (Fᶜ : Set (D4 → ℤ)),
    ‖actualCoeff P.rho P.sigma (k : D4 → ℤ)‖

theorem tailAmplitude_hasSum (P : PacketData ι)
    (F : Finset (D4 → ℤ)) (q : ℝ) :
    HasSum (fun k : (Fᶜ : Set (D4 → ℤ)) =>
      modeAmplitude P (k : D4 → ℤ) q) (tailAmplitude P F q) := by
  have hs : Summable (fun k : D4 → ℤ => modeAmplitude P k q) :=
    (modeAmplitude_hasSum P q 0).summable
  have hsplit := hs.sum_add_tsum_compl (s := F)
  have htotal := (modeAmplitude_hasSum P q 0).tsum_eq
  have hvalue : tailAmplitude P F q =
      ∑' k : (Fᶜ : Set (D4 → ℤ)), modeAmplitude P (k : D4 → ℤ) q := by
    unfold tailAmplitude
    rw [← htotal, ← hsplit]
    exact add_sub_cancel_left _ _
  rw [hvalue]
  exact (hs.subtype (Fᶜ : Set (D4 → ℤ))).hasSum

theorem tailAmplitude_norm_le (P : PacketData ι)
    (F : Finset (D4 → ℤ)) (q : ℝ) :
    ‖tailAmplitude P F q‖ ≤
      (coefficientMass P * (16/P.Y0)) * tailCoefficientMass P F := by
  let c : (Fᶜ : Set (D4 → ℤ)) → ℝ := fun k =>
    ‖actualCoeff P.rho P.sigma (k : D4 → ℤ)‖
  have hc : Summable c := (P.actual_norm_summable 0).subtype _
  have hb : Summable (fun k : (Fᶜ : Set (D4 → ℤ)) =>
      c k * (coefficientMass P * (16/P.Y0))) := hc.mul_right _
  have hnorm := (tailAmplitude_hasSum P F q).norm_le_of_bounded
    hb.hasSum (fun k => modeAmplitude_norm_le P (k : D4 → ℤ) q)
  calc
    ‖tailAmplitude P F q‖ ≤
        ∑' k : (Fᶜ : Set (D4 → ℤ)),
          c k * (coefficientMass P * (16/P.Y0)) := hnorm
    _ = (coefficientMass P * (16/P.Y0)) * tailCoefficientMass P F := by
      rw [hc.tsum_mul_right]
      dsimp [c, tailCoefficientMass]
      ring

theorem tailAmplitude_physical (P : PacketData ι)
    (F : Finset (D4 → ℤ)) : PhysicalAmplitude P (tailAmplitude P F) := by
  constructor
  · have hs : Continuous (fun q : ℝ => ∑ k ∈ F, modeAmplitude P k q) :=
      continuous_finsetSum _ (fun k _ => (modeAmplitude_physical P k).1)
    exact (physicalAmplitudeRaw_continuous P).sub hs
  · intro q hq
    have hs : (∑ k ∈ F, modeAmplitude P k q) = 0 := by
      apply Finset.sum_eq_zero
      intro k _hk
      exact (modeAmplitude_physical P k).2 q hq
    simp only [tailAmplitude, physicalAmplitudeRaw_zero_off P q hq,
      hs, sub_zero]

theorem tailAmplitude_norm_integral_le (P : PacketData ι)
    (F : Finset (D4 → ℤ)) :
    (∫ q : ℝ, ‖tailAmplitude P F q‖) ≤
      ((volume : Measure ℝ).real P.region *
        (coefficientMass P * (16/P.Y0))) * tailCoefficientMass P F := by
  have hAi := (amplitude_integrable P (tailAmplitude P F)
    (tailAmplitude_physical P F)).norm
  have hset : IntegrableOn (fun q : ℝ => ‖tailAmplitude P F q‖) P.region :=
    hAi.integrableOn
  have hzero : (∫ q in P.region, ‖tailAmplitude P F q‖) =
      ∫ q : ℝ, ‖tailAmplitude P F q‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    rw [(tailAmplitude_physical P F).2 q hq, norm_zero]
  rw [← hzero]
  have hconst : IntegrableOn
      (fun _q : ℝ => (coefficientMass P * (16/P.Y0)) *
        tailCoefficientMass P F) P.region :=
    integrableOn_const isCompact_Icc.measure_lt_top
  have hbound := setIntegral_mono_on hset hconst measurableSet_Icc
    (fun q _hq => tailAmplitude_norm_le P F q)
  apply hbound.trans
  rw [setIntegral_const, smul_eq_mul]
  ring

theorem tailCoefficientMass_tendsto_zero (P : PacketData ι) :
    Tendsto (tailCoefficientMass P)
      (atTop : Filter (Finset (D4 → ℤ))) (𝓝 (0 : ℝ)) := by
  exact tendsto_tsum_compl_atTop_zero (P.actual_norm_summable 0)

/-- Support away from q=0 makes the literal K product integrable even
though the K integral itself is defined on the positive axis only. -/
private theorem amplitudeK_integrable_q (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (t : ℝ) :
    Integrable (fun q : ℝ => a q * (imaginaryOrderK t q : ℂ)) := by
  let c : ℝ := P.Y0/32
  have hcpos : 0 < c := by dsimp [c]; positivity
  have heq : (fun q : ℝ => a q * (imaginaryOrderK t q : ℂ)) =
      fun q : ℝ => a q *
        (extendedKKernel c hcpos t q * (q : ℂ)) := by
    funext q
    by_cases hq : q ∈ P.region
    · have he := extendedKKernel_eq_on_physical_region P t q hq
      change extendedKKernel c hcpos t q =
        (imaginaryOrderK t q : ℂ)/(q : ℂ) at he
      rw [he]
      have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hq.1
      have hqne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
      field_simp [hqne] <;> ring
    · rw [ha.2 q hq]
      simp
  rw [heq]
  have hcont : Continuous (fun q : ℝ => a q *
      (extendedKKernel c hcpos t q * (q : ℂ))) := by
    exact ha.1.mul ((extendedKKernel c hcpos t).continuous.mul
      Complex.continuous_ofReal)
  apply hcont.integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  simp only [ha.2 q hn, zero_mul] at hq
  exact hq rfl

theorem modeAmplitudeK_eq_heightFourierTerm (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    amplitudeK P (modeAmplitude P k) t = heightFourierTerm P t k := by
  calc
    amplitudeK P (modeAmplitude P k) t =
        (actualCoeff P.rho P.sigma k * completedPacketSum P k) *
          amplitudeK P (actualKAmplitude P k) t := by
      have heq : (fun q : ℝ => modeAmplitude P k q *
          (imaginaryOrderK t q : ℂ)) =
          fun q : ℝ =>
            (actualCoeff P.rho P.sigma k * completedPacketSum P k) *
              (actualKAmplitude P k q * (imaginaryOrderK t q : ℂ)) := by
        funext q
        unfold modeAmplitude
        ring
      unfold amplitudeK
      rw [heq, integral_const_mul]
    _ = heightFourierTerm P t k := by
      rw [← kTestTransform_eq_amplitudeK]
      exact (heightFourierTerm_eq_packet_const_mul_K P k t).symm

theorem tailAmplitudeK_eq_heightRemainder (P : PacketData ι)
    (F : Finset (D4 → ℤ)) (t : ℝ) :
    amplitudeK P (tailAmplitude P F) t =
      fullPhysicalHeight P t - ∑ k ∈ F, heightFourierTerm P t k := by
  have hfull : amplitudeK P (physicalAmplitudeRaw P) t =
      fullPhysicalHeight P t := by
    unfold amplitudeK fullPhysicalHeight
    rw [fullPhysicalIntegral_eq_K_amplitude]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => mul_comm _ _)
  have hsum : Integrable (fun q : ℝ =>
      ∑ k ∈ F, modeAmplitude P k q * (imaginaryOrderK t q : ℂ)) :=
    integrable_finsetSum F (fun k _hk =>
      amplitudeK_integrable_q P (modeAmplitude P k)
        (modeAmplitude_physical P k) t)
  change (∫ q : ℝ, (physicalAmplitudeRaw P q -
      ∑ k ∈ F, modeAmplitude P k q) * (imaginaryOrderK t q : ℂ)) = _
  simp only [sub_mul, Finset.sum_mul]
  rw [integral_sub
    (amplitudeK_integrable_q P (physicalAmplitudeRaw P)
      (physicalAmplitudeRaw_isPhysical P) t) hsum,
    integral_finsetSum F (fun k _hk =>
      amplitudeK_integrable_q P (modeAmplitude P k)
        (modeAmplitude_physical P k) t)]
  change amplitudeK P (physicalAmplitudeRaw P) t -
      (∑ k ∈ F, amplitudeK P (modeAmplitude P k) t) = _
  rw [hfull]
  apply congrArg (fun z : ℂ => fullPhysicalHeight P t - z)
  apply Finset.sum_congr rfl
  intro k _hk
  exact modeAmplitudeK_eq_heightFourierTerm P k t

/-- A quantitative whole-line L² tail estimate with the real coefficient
L¹ remainder, finite packet mass and actual positive q-volume all visible. -/
theorem fullHeightFourier_tail_energy_le (P : PacketData ι)
    (F : Finset (D4 → ℤ)) :
    (∫ t : ℝ,
      ‖fullPhysicalHeight P t - ∑ k ∈ F, heightFourierTerm P t k‖ ^ 2) ≤
      ((Real.pi/4) *
        ∫ u : ℝ, Real.exp (-(P.Y0/16)*|u|)) *
        (((volume : Measure ℝ).real P.region *
          (coefficientMass P * (16/P.Y0))) * tailCoefficientMass P F) ^ 2 := by
  have hK := amplitudeK_full_height_energy_le P (tailAmplitude P F)
    (tailAmplitude_physical P F)
  have hQ := tailAmplitude_norm_integral_le P F
  have hQ0 : 0 ≤ ∫ q : ℝ, ‖tailAmplitude P F q‖ :=
    integral_nonneg (fun q => norm_nonneg _)
  have hsq := pow_le_pow_left₀ hQ0 hQ 2
  have hfront : 0 ≤ (Real.pi/4) *
      ∫ u : ℝ, Real.exp (-(P.Y0/16)*|u|) := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg (fun u => (Real.exp_pos _).le)
  calc
    (∫ t : ℝ,
      ‖fullPhysicalHeight P t - ∑ k ∈ F, heightFourierTerm P t k‖ ^ 2) =
        ∫ t : ℝ, ‖amplitudeK P (tailAmplitude P F) t‖ ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun t => by rw [tailAmplitudeK_eq_heightRemainder])
    _ ≤ ((Real.pi/4) *
        ∫ u : ℝ, Real.exp (-(P.Y0/16)*|u|)) *
          (∫ q : ℝ, ‖tailAmplitude P F q‖) ^ 2 := hK
    _ ≤ ((Real.pi/4) *
        ∫ u : ℝ, Real.exp (-(P.Y0/16)*|u|)) *
          (((volume : Measure ℝ).real P.region *
            (coefficientMass P * (16/P.Y0))) * tailCoefficientMass P F) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hfront

/-- The original Fourier modes converge in L² of the entire raw height
line, with no compact-height cutoff or spectral-saving hypothesis. -/
theorem fullHeightFourier_tail_L2_tendsto_zero (P : PacketData ι) :
    Tendsto (fun F : Finset (D4 → ℤ) =>
      ∫ t : ℝ,
        ‖fullPhysicalHeight P t -
          ∑ k ∈ F, heightFourierTerm P t k‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  let B : ℝ := (volume : Measure ℝ).real P.region *
    (coefficientMass P * (16/P.Y0))
  let C : ℝ := (Real.pi/4) *
    ∫ u : ℝ, Real.exp (-(P.Y0/16)*|u|)
  have htail := tailCoefficientMass_tendsto_zero P
  have hscaled : Tendsto (fun F : Finset (D4 → ℤ) =>
      C * (B * tailCoefficientMass P F)^2) atTop (𝓝 (0 : ℝ)) := by
    have hB : Tendsto (fun F : Finset (D4 → ℤ) =>
        B * tailCoefficientMass P F) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul htail
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      tendsto_const_nhds.mul (hB.pow 2)
  apply squeeze_zero
    (fun F => integral_nonneg (fun t => sq_nonneg _))
    (fun F => by
      simpa only [B, C] using fullHeightFourier_tail_energy_le P F)
    hscaled

end
end ImbalancedChen.Part3.ActualFullPacketFourierTailL2SourceOnly
