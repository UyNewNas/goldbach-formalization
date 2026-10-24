import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import ImbalancedChen.Part3ActualKTransformFourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED, 2026-10-24.  This file constructs the *full physical*
packet amplitude.  In particular its finite sums use `P.packet j`, the original
signed coefficient, and the actual `normalizedF`; they do not use a Fourier
mode, a replaced packet, or a spectral-saving hypothesis.

The full Fourier identity below consumes the generic compact-q Fubini theorem
and even-profile Fourier bridge.  Those sources are also staged and uncompiled.
-/

namespace ImbalancedChen.Part3.ActualFullPacketFourierBridgeSourceOnly
noncomputable section
open Classical Set MeasureTheory
open Filter
open scoped BigOperators FourierTransform
open P3ActualLiteralPacketIntegralSourceOnly
open P3Period64NativeReconstructionSourceOnly (point4)
open ImbalancedChen.Part3.ActualNormalizedSmoothF (normalizedF normalizedF_contDiff)
open ImaginaryOrderKBesselSourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open ActualKTransformFourier20261024z

variable {ι : Type*}

/-- All original finite masks, signed coefficients, and normalized samples. -/
def physicalNumerator (P : PacketData ι) (q : ℝ) : ℂ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    signedCoefficient P.negativeCusp (P.packet j) n *
      normalizedF P.rho P.sigma
        (point4 (q/P.Y0) ((m : ℝ)/P.V)
          ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
          (((P.packet j).level : ℝ)/P.Z))

theorem physicalNumerator_continuous (P : PacketData ι) :
    Continuous (physicalNumerator P) := by
  have hf := (normalizedF_contDiff P.rho P.sigma).continuous
  have hp (v w z : ℝ) :
      Continuous (fun q : ℝ => point4 (q/P.Y0) v w z) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hF (v w z : ℝ) : Continuous (fun q : ℝ =>
      normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z)) :=
    hf.comp (hp v w z)
  unfold physicalNumerator
  fun_prop

theorem physicalNumerator_zero_off (P : PacketData ι) (q : ℝ)
    (hq : q ∉ P.region) : physicalNumerator P q = 0 := by
  have hF (v w z : ℝ) :
      normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) = 0 := by
    have hh :=
      P3Period64NativeReconstructionSourceOnly.chi_mul_actual P.rho P.sigma
        (point4 (q/P.Y0) v w z)
    change (P3Period64NativeReconstructionSourceOnly.chi (q/P.Y0) : ℂ) *
      normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) =
        normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) at hh
    rw [P.chi_scaled_zero_off q hq] at hh
    simpa only [Complex.ofReal_zero, zero_mul] using hh.symm
  simp only [physicalNumerator, hF, mul_zero, Finset.sum_const_zero]

/-- The global zero extension agrees with the q-restricted amplitude. -/
def physicalAmplitudeRaw (P : PacketData ι) (q : ℝ) : ℂ :=
  physicalNumerator P q / (q : ℂ)

theorem physicalAmplitudeRaw_zero_off (P : PacketData ι) (q : ℝ)
    (hq : q ∉ P.region) : physicalAmplitudeRaw P q = 0 := by
  simp only [physicalAmplitudeRaw, physicalNumerator_zero_off P q hq, zero_div]

theorem physicalAmplitudeRaw_continuous (P : PacketData ι) :
    Continuous (physicalAmplitudeRaw P) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : q = 0
  · subst q
    have ha : 0 < P.Y0/16 := by positivity
    have hnhds : Iio (P.Y0/16) ∈ 𝓝 (0 : ℝ) :=
      isOpen_Iio.mem_nhds ha
    have he : physicalAmplitudeRaw P =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
      filter_upwards [hnhds] with x hx
      apply physicalAmplitudeRaw_zero_off
      intro hmem
      exact (not_lt_of_ge hmem.1) hx
    exact (continuousAt_congr he).2 continuousAt_const
  · have hden : ContinuousAt (fun x : ℝ => (x : ℂ)) q := by fun_prop
    exact (physicalNumerator_continuous P).continuousAt.div hden
      (Complex.ofReal_ne_zero.mpr hq)

theorem physicalAmplitudeRaw_hasCompactSupport (P : PacketData ι) :
    HasCompactSupport (physicalAmplitudeRaw P) := by
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  exact hq (physicalAmplitudeRaw_zero_off P q hn)

theorem physicalAmplitudeRaw_integrable (P : PacketData ι) :
    Integrable (physicalAmplitudeRaw P) :=
  (physicalAmplitudeRaw_continuous P).integrable_of_hasCompactSupport
    (physicalAmplitudeRaw_hasCompactSupport P)

/-- The genuine dq/q amplitude on the actual positive packet region. -/
def physicalAmplitude (P : PacketData ι) : C(P.region, ℂ) where
  toFun q := physicalAmplitudeRaw P q
  continuous_toFun := (physicalAmplitudeRaw_continuous P).comp continuous_subtype_val

theorem physicalAmplitude_apply (P : PacketData ι) (q : P.region) :
    physicalAmplitude P q = physicalAmplitudeRaw P q := rfl

/-- The only height dependence of the *entire* physical packet is K. -/
theorem kPhysical_eq_K_mul_amplitude_on (P : PacketData ι) (t : ℝ)
    (q : P.region) :
    kPhysical P (commonHeight t) q =
      (imaginaryOrderK t q : ℂ) * physicalAmplitude P q := by
  change kPhysical P (commonHeight t) (q : ℝ) =
    (imaginaryOrderK t (q : ℝ) : ℂ) * physicalAmplitudeRaw P (q : ℝ)
  unfold kPhysical physicalAmplitudeRaw physicalNumerator commonHeight
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem kPhysical_eq_K_mul_amplitudeRaw_on (P : PacketData ι) (t q : ℝ)
    (hq : q ∈ P.region) :
    kPhysical P (commonHeight t) q =
      (imaginaryOrderK t q : ℂ) * physicalAmplitudeRaw P q := by
  simpa only [physicalAmplitude_apply] using
    kPhysical_eq_K_mul_amplitude_on P t ⟨q,hq⟩

theorem fullPhysicalIntegral_eq_K_amplitude (P : PacketData ι) (t : ℝ) :
    (∫ q : ℝ, kPhysical P (commonHeight t) q) =
      ∫ q : ℝ, (imaginaryOrderK t q : ℂ) * physicalAmplitudeRaw P q := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  by_cases hq : q ∈ P.region
  · exact kPhysical_eq_K_mul_amplitudeRaw_on P t q hq
  · rw [kPhysical_zero_off P (commonHeight t) q hq,
      physicalAmplitudeRaw_zero_off P q hq, mul_zero]

/-- The same identity globally, with exact vanishing off the original region. -/
theorem kPhysical_eq_K_mul_amplitude_or_zero (P : PacketData ι) (t q : ℝ) :
    kPhysical P (commonHeight t) q =
      if hq : q ∈ P.region then
        (imaginaryOrderK t q : ℂ) * physicalAmplitude P ⟨q,hq⟩
      else 0 := by
  split_ifs with hq
  · exact kPhysical_eq_K_mul_amplitude_on P t ⟨q,hq⟩
  · exact kPhysical_zero_off P (commonHeight t) q hq

/-- The actual full-axis even Laplace profile, with all finite packet data. -/
def physicalEvenProfile (P : PacketData ι) (u : ℝ) : ℂ :=
  ∫ q : ℝ,
    physicalAmplitudeRaw P q * (Real.exp (-q * Real.cosh u) : ℂ)

theorem physicalEvenProfile_even (P : PacketData ι) (u : ℝ) :
    physicalEvenProfile P (-u) = physicalEvenProfile P u := by
  simp only [physicalEvenProfile, Real.cosh_neg]

/-- A displayed profile over exactly the packet's physical q interval. -/
theorem physicalEvenProfile_eq_region (P : PacketData ι) (u : ℝ) :
    physicalEvenProfile P u =
      ∫ q in P.region,
        (physicalNumerator P q / (q : ℂ)) *
          (Real.exp (-q * Real.cosh u) : ℂ) := by
  unfold physicalEvenProfile
  change (∫ q : ℝ, physicalAmplitudeRaw P q *
      (Real.exp (-q * Real.cosh u) : ℂ)) =
    ∫ q in P.region, physicalAmplitudeRaw P q *
      (Real.exp (-q * Real.cosh u) : ℂ)
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  rw [physicalAmplitudeRaw_zero_off P q hq, zero_mul]

theorem physicalAmplitudeRaw_isPhysical (P : PacketData ι) :
    PhysicalAmplitude P (physicalAmplitudeRaw P) :=
  ⟨physicalAmplitudeRaw_continuous P, physicalAmplitudeRaw_zero_off P⟩

theorem physicalEvenProfile_eq_generic (P : PacketData ι) :
    physicalEvenProfile P = qLaplaceProfile P (physicalAmplitudeRaw P) := rfl

/-- L¹ follows from the actual compact q numerator and the uniform envelope. -/
theorem physicalEvenProfile_integrable (P : PacketData ι) :
    Integrable (physicalEvenProfile P) := by
  rw [physicalEvenProfile_eq_generic]
  exact qLaplaceProfile_integrable P (physicalAmplitudeRaw P)
    (physicalAmplitudeRaw_isPhysical P)

/-- The same envelope proves L² without a spectral-saving input. -/
theorem physicalEvenProfile_norm_sq_integrable (P : PacketData ι) :
    Integrable (fun u : ℝ => ‖physicalEvenProfile P u‖ ^ 2) := by
  simp only [physicalEvenProfile_eq_generic]
  exact qLaplaceProfile_norm_sq_integrable P (physicalAmplitudeRaw P)
    (physicalAmplitudeRaw_isPhysical P)

theorem physicalEvenProfile_cosine_eq_half_fourier (P : PacketData ι) (t : ℝ) :
    (∫ u in Ioi (0 : ℝ), (Real.cos (2*t*u) : ℂ) * physicalEvenProfile P u) =
      (1/2 : ℂ) * 𝓕 (physicalEvenProfile P) (t/Real.pi) := by
  simpa only [physicalEvenProfile_eq_generic] using
    qLaplaceProfile_half_fourier P (physicalAmplitudeRaw P)
      (physicalAmplitudeRaw_isPhysical P) t

/-- The complete original physical packet has the exact full-line Fourier
representation at common height.  All packet masks are carried by the
continuous `physicalAmplitudeRaw`; no mode is substituted here. -/
theorem fullPhysicalIntegral_eq_half_fourier (P : PacketData ι) (t : ℝ) :
    (∫ q : ℝ, kPhysical P (commonHeight t) q) =
      (1/2 : ℂ) * 𝓕 (physicalEvenProfile P) (t/Real.pi) := by
  calc
    (∫ q : ℝ, kPhysical P (commonHeight t) q) =
        ∫ q : ℝ, physicalAmplitudeRaw P q * (imaginaryOrderK t q : ℂ) := by
      rw [fullPhysicalIntegral_eq_K_amplitude]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => mul_comm _ _)
    _ = (1/2 : ℂ) * 𝓕 (physicalEvenProfile P) (t/Real.pi) := by
      simpa only [physicalEvenProfile_eq_generic] using
        amplitudeK_half_fourier P (physicalAmplitudeRaw P)
          (physicalAmplitudeRaw_isPhysical P) t

end
end ImbalancedChen.Part3.ActualFullPacketFourierBridgeSourceOnly
