import ImbalancedChen.Part3KTestTransformFubini
import ImbalancedChen.Part3KFullLineFourierBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED (2026-10-24).  The physical q amplitude has compact
support in `[Y0/16,16Y0]`.  Its even Laplace profile is genuinely in L¹ and
L²; the only Fourier identification used below is the separately proved
generic even-function Fourier bridge.  There is no Plancherel assumption.
-/

namespace ImbalancedChen.Part3.ActualKTransformFourier20261024z
noncomputable section

open Classical Set MeasureTheory
open scoped FourierTransform
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode)
open ImaginaryOrderKBesselSourceOnly
open ActualCommonHeightKGramSourceOnly (kTestTransform)
open ActualKTransformFubiniSourceOnly
open KFullLineFourierBridgeSourceOnly

variable {ι : Type*}

/-- A physical q amplitude has global continuity and is exactly zero off the
closed physical interval.  The latter supplies compact support, rather than
being an assumed integrability statement. -/
def PhysicalAmplitude (P : PacketData ι) (a : ℝ → ℂ) : Prop :=
  Continuous a ∧ ∀ q, q ∉ P.region → a q = 0

private theorem amplitude_compactSupport (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) : HasCompactSupport a := by
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  exact hq (ha.2 q hn)

theorem amplitude_integrable (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) : Integrable a :=
  ha.1.integrable_of_hasCompactSupport (amplitude_compactSupport P a ha)

/-- The generic even q-Laplace profile. -/
def qLaplaceProfile (P : PacketData ι) (a : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ q : ℝ, a q * (Real.exp (-q * Real.cosh u) : ℂ)

private theorem qLaplaceIntegrand_integrable (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (u : ℝ) :
    Integrable (fun q : ℝ => a q * (Real.exp (-q * Real.cosh u) : ℂ)) := by
  have hc : Continuous (fun q : ℝ => a q * (Real.exp (-q * Real.cosh u) : ℂ)) := by
    have haC : Continuous a := ha.1
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  simp only [ha.2 q hn, zero_mul] at hq
  exact hq rfl

private theorem half_abs_le_cosh (u : ℝ) : |u| / 2 ≤ Real.cosh u := by
  rcases le_total 0 u with hu | hu
  · simpa only [abs_of_nonneg hu] using half_le_cosh u
  · simpa only [abs_of_nonpos hu, Real.cosh_neg] using half_le_cosh (-u)

private theorem qLaplaceIntegrand_norm_le (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (q u : ℝ) :
    ‖a q * (Real.exp (-q * Real.cosh u) : ℂ)‖ ≤
      ‖a q‖ * Real.exp (-(P.Y0 / 32) * |u|) := by
  by_cases hq : q ∈ P.region
  · have hqlo : P.Y0 / 16 ≤ q := hq.1
    have hY : 0 < P.Y0 / 16 := by
      have := P.Y0_pos
      positivity
    have h1 : (P.Y0 / 16) * Real.cosh u ≤ q * Real.cosh u :=
      mul_le_mul_of_nonneg_right hqlo (Real.cosh_pos u).le
    have h2 : (P.Y0 / 16) * (|u| / 2) ≤ (P.Y0 / 16) * Real.cosh u :=
      mul_le_mul_of_nonneg_left (half_abs_le_cosh u) hY.le
    have hexp : Real.exp (-q * Real.cosh u) ≤
        Real.exp (-(P.Y0 / 32) * |u|) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using
      (mul_le_mul_of_nonneg_left hexp (norm_nonneg (a q)))
  · simp [ha.2 q hq]

private theorem qLaplaceIntegrand_norm_le_amplitude (P : PacketData ι)
    (a : ℝ → ℂ) (ha : PhysicalAmplitude P a) (q u : ℝ) :
    ‖a q * (Real.exp (-q * Real.cosh u) : ℂ)‖ ≤ ‖a q‖ := by
  have h := qLaplaceIntegrand_norm_le P a ha q u
  have h0 : 0 ≤ (P.Y0 / 32) * |u| := by
    have := P.Y0_pos
    positivity
  have he : Real.exp (-(P.Y0 / 32) * |u|) ≤ 1 := by
    simpa using (Real.exp_le_exp.mpr (show -(P.Y0 / 32) * |u| ≤ 0 by linarith))
  exact h.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left he (norm_nonneg (a q)))

theorem qLaplaceProfile_continuous (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) : Continuous (qLaplaceProfile P a) := by
  unfold qLaplaceProfile
  apply continuous_of_dominated (bound := fun q : ℝ => ‖a q‖)
  · intro u
    have hc : Continuous (fun q : ℝ => a q * (Real.exp (-q * Real.cosh u) : ℂ)) := by
      have haC : Continuous a := ha.1
      fun_prop
    exact hc.aestronglyMeasurable
  · intro u
    exact Filter.Eventually.of_forall
      (fun q => qLaplaceIntegrand_norm_le_amplitude P a ha q u)
  · exact (amplitude_integrable P a ha).norm
  · exact Filter.Eventually.of_forall (fun q => by
      have hc : Continuous (fun u : ℝ => a q * (Real.exp (-q * Real.cosh u) : ℂ)) := by
        fun_prop
      exact hc)

theorem qLaplaceProfile_even (P : PacketData ι) (a : ℝ → ℂ) (u : ℝ) :
    qLaplaceProfile P a (-u) = qLaplaceProfile P a u := by
  simp only [qLaplaceProfile, Real.cosh_neg]

theorem exp_neg_abs_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun u : ℝ => Real.exp (-b * |u|)) := by
  have hset : (Iic (0 : ℝ) ∪ Ioi (0 : ℝ)) = Set.univ := by
    ext u
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt u 0
  rw [← integrableOn_univ, ← hset, integrableOn_union]
  constructor
  · have hbase := integrableOn_exp_mul_Iic hb 0
    have he : (fun u : ℝ => Real.exp (-b * |u|)) =ᵐ[volume.restrict (Iic 0)]
        (fun u : ℝ => Real.exp (b * u)) := by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
      simp [abs_of_nonpos hu]
    exact hbase.congr he.symm
  · have hbase := integrableOn_exp_mul_Ioi (by linarith : -b < 0) 0
    have he : (fun u : ℝ => Real.exp (-b * |u|)) =ᵐ[volume.restrict (Ioi 0)]
        (fun u : ℝ => Real.exp (-b * u)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simp [abs_of_pos hu]
    exact hbase.congr he.symm

/-- Uniform exponential decay with the normalization dictated by the actual
physical lower endpoint q=Y0/16. -/
theorem qLaplaceProfile_norm_le (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (u : ℝ) :
    ‖qLaplaceProfile P a u‖ ≤
      (∫ q : ℝ, ‖a q‖) * Real.exp (-(P.Y0 / 32) * |u|) := by
  have hi := qLaplaceIntegrand_integrable P a ha u
  have hb : Integrable (fun q : ℝ => ‖a q‖ *
      Real.exp (-(P.Y0 / 32) * |u|)) :=
    (amplitude_integrable P a ha).norm.mul_const _
  calc
    ‖qLaplaceProfile P a u‖ ≤
        ∫ q : ℝ, ‖a q * (Real.exp (-q * Real.cosh u) : ℂ)‖ := by
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ q : ℝ, ‖a q‖ * Real.exp (-(P.Y0 / 32) * |u|) := by
      exact integral_mono hi.norm hb (fun q => qLaplaceIntegrand_norm_le P a ha q u)
    _ = (∫ q : ℝ, ‖a q‖) * Real.exp (-(P.Y0 / 32) * |u|) := by
      rw [integral_mul_const]

/-- The profile is in L¹ on the full real line. -/
theorem qLaplaceProfile_integrable (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) : Integrable (qLaplaceProfile P a) := by
  have hY : 0 < P.Y0 / 32 := by
    have := P.Y0_pos
    positivity
  have hmaj : Integrable (fun u : ℝ =>
      (∫ q : ℝ, ‖a q‖) * Real.exp (-(P.Y0 / 32) * |u|)) :=
    (exp_neg_abs_integrable hY).const_mul _
  exact hmaj.mono' (qLaplaceProfile_continuous P a ha).aestronglyMeasurable
    (Filter.Eventually.of_forall (qLaplaceProfile_norm_le P a ha))

/-- A literal norm-square integrability statement, equivalent to the usual
L² assertion and directly consumable by packet energy arguments. -/
theorem qLaplaceProfile_norm_sq_integrable (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    Integrable (fun u : ℝ => ‖qLaplaceProfile P a u‖ ^ 2) := by
  have hY : 0 < P.Y0 / 16 := by
    have := P.Y0_pos
    positivity
  have hmaj : Integrable (fun u : ℝ =>
      (∫ q : ℝ, ‖a q‖) ^ 2 * Real.exp (-(P.Y0 / 16) * |u|)) :=
    (exp_neg_abs_integrable hY).const_mul _
  have hc : Continuous (fun u : ℝ => ‖qLaplaceProfile P a u‖ ^ 2) := by
    exact (qLaplaceProfile_continuous P a ha).norm.pow 2
  apply hmaj.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  have h := qLaplaceProfile_norm_le P a ha u
  have hc : 0 ≤ ∫ q : ℝ, ‖a q‖ := integral_nonneg (fun q => norm_nonneg _)
  have he : 0 ≤ Real.exp (-(P.Y0 / 32) * |u|) := (Real.exp_pos _).le
  have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
  calc
    ‖qLaplaceProfile P a u‖ ^ 2 ≤
        ((∫ q : ℝ, ‖a q‖) * Real.exp (-(P.Y0 / 32) * |u|)) ^ 2 := hp
    _ = (∫ q : ℝ, ‖a q‖) ^ 2 * Real.exp (-(P.Y0 / 16) * |u|) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 1
      ring

/-- Absolute integrability of the genuine q/u K integrand for any continuous
physical q amplitude.  The same compact support majorant works for every t. -/
theorem amplitudeK_double_integrable (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => a p.1 * (kIntegrand t p.1 p.2 : ℂ))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hq : Integrable (fun q : ℝ => ‖a q‖) := (amplitude_integrable P a ha).norm
  have hu : Integrable (fun u : ℝ => Real.exp (-(P.Y0 / 32) * u))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hY : 0 < P.Y0 / 16 := by
      have := P.Y0_pos
      positivity
    simpa only [show -(P.Y0 / 16 / 2) = -(P.Y0 / 32) by ring] using
      (exponential_majorant_integrable (a := P.Y0 / 16) hY)
  have hmaj : Integrable (fun p : ℝ × ℝ => ‖a p.1‖ *
      Real.exp (-(P.Y0 / 32) * p.2))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := hq.mul_prod hu
  have hc : Continuous (fun p : ℝ × ℝ => a p.1 * (kIntegrand t p.1 p.2 : ℂ)) := by
    have hk : Continuous (fun p : ℝ × ℝ => (kIntegrand t p.1 p.2 : ℂ)) := by
      unfold kIntegrand
      fun_prop
    exact (ha.1.comp continuous_fst).mul hk
  apply hmaj.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  by_cases hqp : p.1 ∈ P.region
  · have hqlo : P.Y0 / 16 ≤ p.1 := hqp.1
    have hY : 0 < P.Y0 / 16 := by
      have := P.Y0_pos
      positivity
    have hk := kIntegrand_norm_le hY hqlo t p.2
    change ‖a p.1 * (kIntegrand t p.1 p.2 : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hk)
      (norm_nonneg _)
  · simp [ha.2 p.1 hqp]

/-- Generic Fubini identity from the actual integral representation of
`K_{2it}`.  No K-transform identity is taken as an input field. -/
theorem amplitudeK_cosineLaplace (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (t : ℝ) :
    (∫ q : ℝ, a q * (imaginaryOrderK t q : ℂ)) =
      ∫ u in Ioi (0 : ℝ), (Real.cos (2 * t * u) : ℂ) * qLaplaceProfile P a u := by
  have hf := amplitudeK_double_integrable P a ha t
  have hinner (q : ℝ) :
      (∫ u in Ioi (0 : ℝ), a q * (kIntegrand t q u : ℂ)) =
        a q * (imaginaryOrderK t q : ℂ) := by
    simp only [integral_const_mul, integral_complex_ofReal, imaginaryOrderK]
  calc
    (∫ q : ℝ, a q * (imaginaryOrderK t q : ℂ)) =
        ∫ q : ℝ, ∫ u in Ioi (0 : ℝ), a q * (kIntegrand t q u : ℂ) := by
      simp only [hinner]
    _ = ∫ u in Ioi (0 : ℝ), ∫ q : ℝ, a q * (kIntegrand t q u : ℂ) := by
      exact integral_integral_swap hf
    _ = ∫ u in Ioi (0 : ℝ), (Real.cos (2 * t * u) : ℂ) *
        qLaplaceProfile P a u := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      unfold qLaplaceProfile
      have he : (fun q : ℝ => a q * (kIntegrand t q u : ℂ)) =
          (fun q : ℝ => (Real.cos (2 * t * u) : ℂ) *
            (a q * (Real.exp (-q * Real.cosh u) : ℂ))) := by
        funext q
        simp only [kIntegrand, Complex.ofReal_mul]
        ring
      rw [he, integral_const_mul]

theorem amplitudeK_half_fourier (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (t : ℝ) :
    (∫ q : ℝ, a q * (imaginaryOrderK t q : ℂ)) =
      (1 / 2 : ℂ) * 𝓕 (qLaplaceProfile P a) (t / Real.pi) := by
  rw [amplitudeK_cosineLaplace P a ha t]
  exact cosine_integral_eq_half_fourier (qLaplaceProfile P a)
    (qLaplaceProfile_integrable P a ha) (qLaplaceProfile_even P a) t

/-- The generic compact-q amplitude already has a genuine pointwise Fourier
representation.  Both L¹ and the decay used for L² were proved above. -/
theorem qLaplaceProfile_half_fourier (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) (t : ℝ) :
    (∫ u in Ioi (0 : ℝ), (Real.cos (2 * t * u) : ℂ) *
      qLaplaceProfile P a u) =
      (1 / 2 : ℂ) * 𝓕 (qLaplaceProfile P a) (t / Real.pi) := by
  exact cosine_integral_eq_half_fourier (qLaplaceProfile P a)
    (qLaplaceProfile_integrable P a ha) (qLaplaceProfile_even P a) t

/-! The actual spectral-test quotient is a continuous global amplitude.
The harmless max denominator only proves continuity at q=0; on the support
it agrees literally with 1/q. -/

def actualKAmplitude (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) : ℂ :=
  spectralTest k P.Y0 q / ((max q (P.Y0 / 32) : ℝ) : ℂ)

theorem actualKAmplitude_eq (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    actualKAmplitude P k q = spectralTest k P.Y0 q / (q : ℂ) := by
  by_cases hq : q ∈ P.region
  · have hmax : max q (P.Y0 / 32) = q :=
      max_eq_left (by have hqlo : P.Y0 / 16 ≤ q := hq.1
                      linarith [P.Y0_pos])
    simp only [actualKAmplitude, hmax]
  · have hz : spectralTest k P.Y0 q = 0 := by
      simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
        Complex.ofReal_zero, zero_mul]
    simp [actualKAmplitude, hz]

theorem actualKAmplitude_physical (P : PacketData ι) (k : D4 → ℤ) :
    PhysicalAmplitude P (actualKAmplitude P k) := by
  constructor
  · have hs : Continuous (spectralTest k P.Y0) :=
      (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous
    have hm : Continuous (fun q : ℝ => max q (P.Y0 / 32)) :=
      continuous_id.max continuous_const
    have hz : ∀ q : ℝ, ((max q (P.Y0 / 32) : ℝ) : ℂ) ≠ 0 := by
      intro q
      apply Complex.ofReal_ne_zero.mpr
      have hq : 0 < max q (P.Y0 / 32) :=
        lt_of_lt_of_le (by have := P.Y0_pos; positivity : 0 < P.Y0 / 32)
          (le_max_right q _)
      exact hq.ne'
    exact hs.div (Complex.continuous_ofReal.comp hm) hz
  · intro q hq
    simp only [actualKAmplitude, spectralTest, spectralMode,
      P.chi_scaled_zero_off q hq, Complex.ofReal_zero, zero_mul, zero_div]

/-- The requested literal profile on the physical q interval. -/
def actualKLaplaceProfile (P : PacketData ι) (k : D4 → ℤ) (u : ℝ) : ℂ :=
  ∫ q in P.region, (spectralTest k P.Y0 q / (q : ℂ)) *
    (Real.exp (-q * Real.cosh u) : ℂ)

theorem actualKLaplaceProfile_eq_generic (P : PacketData ι)
    (k : D4 → ℤ) (u : ℝ) :
    actualKLaplaceProfile P k u = qLaplaceProfile P (actualKAmplitude P k) u := by
  have he : (fun q : ℝ => (spectralTest k P.Y0 q / (q : ℂ)) *
      (Real.exp (-q * Real.cosh u) : ℂ)) =
      (fun q : ℝ => actualKAmplitude P k q *
        (Real.exp (-q * Real.cosh u) : ℂ)) := by
    funext q
    rw [actualKAmplitude_eq]
  rw [actualKLaplaceProfile, he, qLaplaceProfile, ← setIntegral_univ]
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (subset_univ P.region) (fun q hq => by
      have hz := (actualKAmplitude_physical P k).2 q (notMem_of_mem_sdiff hq)
      simp [hz])).symm

theorem actualKLaplaceProfile_integrable (P : PacketData ι) (k : D4 → ℤ) :
    Integrable (actualKLaplaceProfile P k) := by
  have he : actualKLaplaceProfile P k = qLaplaceProfile P (actualKAmplitude P k) :=
    funext (actualKLaplaceProfile_eq_generic P k)
  rw [he]
  exact qLaplaceProfile_integrable P _ (actualKAmplitude_physical P k)

theorem actualKLaplaceProfile_norm_sq_integrable (P : PacketData ι) (k : D4 → ℤ) :
    Integrable (fun u : ℝ => ‖actualKLaplaceProfile P k u‖ ^ 2) := by
  simp_rw [actualKLaplaceProfile_eq_generic]
  exact qLaplaceProfile_norm_sq_integrable P _ (actualKAmplitude_physical P k)

theorem actualKLaplaceProfile_even (P : PacketData ι) (k : D4 → ℤ) (u : ℝ) :
    actualKLaplaceProfile P k (-u) = actualKLaplaceProfile P k u := by
  simp only [actualKLaplaceProfile_eq_generic, qLaplaceProfile_even]

/-- Pointwise normalization: K_{2it} corresponds to the frequency t/π
because Mathlib's Fourier character is exp(-2πiξu). -/
theorem kTestTransform_eq_half_fourier (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k t =
      (1 / 2 : ℂ) * 𝓕 (actualKLaplaceProfile P k) (t / Real.pi) := by
  have hF := kTestTransform_cosineLaplace_literal P k t
  have hinner (u : ℝ) :
      (∫ q : ℝ, (spectralTest k P.Y0 q / (q : ℂ)) *
        ((Real.exp (-q * Real.cosh u) * Real.cos (2 * t * u) : ℝ) : ℂ)) =
        (Real.cos (2 * t * u) : ℂ) * actualKLaplaceProfile P k u := by
    have hcast (q : ℝ) :
        ((Real.exp (-q * Real.cosh u) * Real.cos (2 * t * u) : ℝ) : ℂ) =
          (Real.cos (2 * t * u) : ℂ) *
            (Real.exp (-q * Real.cosh u) : ℂ) := by
      push_cast
      ring
    simp_rw [hcast]
    have hq : (∫ q : ℝ, (spectralTest k P.Y0 q / (q : ℂ)) *
          ((Real.cos (2 * t * u) : ℂ) *
            (Real.exp (-q * Real.cosh u) : ℂ))) =
          (Real.cos (2 * t * u) : ℂ) *
            qLaplaceProfile P (actualKAmplitude P k) u := by
      unfold qLaplaceProfile
      have he : (fun q : ℝ => (spectralTest k P.Y0 q / (q : ℂ)) *
          ((Real.cos (2 * t * u) : ℂ) *
            (Real.exp (-q * Real.cosh u) : ℂ))) =
          (fun q : ℝ => (Real.cos (2 * t * u) : ℂ) *
            (actualKAmplitude P k q *
              (Real.exp (-q * Real.cosh u) : ℂ))) := by
        funext q
        rw [actualKAmplitude_eq]
        ring
      rw [he, integral_const_mul]
    rw [hq, ← actualKLaplaceProfile_eq_generic]
  rw [hF]
  simp_rw [hinner]
  exact cosine_integral_eq_half_fourier (actualKLaplaceProfile P k)
    (actualKLaplaceProfile_integrable P k) (actualKLaplaceProfile_even P k) t

end
end ImbalancedChen.Part3.ActualKTransformFourier20261024z
