import ImbalancedChen.Part3ActualKFullHeightEnergy
import ImbalancedChen.Part3ActualKZeroPairEnergy
import ImbalancedChen.Part3ImaginaryOrderKZeroOrderPositivity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED (2026-10-24).  Strict nonvanishing at height zero
and strict full-height energy for a nonzero, real, nonnegative compact physical
amplitude.  This is a restricted injectivity statement; no complex-amplitude
or KL-Plancherel injectivity is asserted.
-/

namespace ImbalancedChen.Part3.ActualKStrictPositiveRealAmplitude20261024z

noncomputable section

open Classical Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKZeroOrderPositivitySourceOnly
open ActualCommonHeightKGramSourceOnly (kTestTransform)
open ActualKTransformFourier20261024z
open ActualKFullHeightEnergy20261024z
open ActualKZeroPairEnergy20261024z

variable {ι : Type*}

/-- A nonnegative real amplitude with the exact physical compact support. -/
def NonnegativeRealPhysicalAmplitude (P : PacketData ι) (w : ℝ → ℝ) : Prop :=
  Continuous w ∧ (∀ q, q ∉ P.region → w q = 0) ∧ ∀ q, 0 ≤ w q

private theorem realAmplitude_physical (P : PacketData ι) (w : ℝ → ℝ)
    (hw : NonnegativeRealPhysicalAmplitude P w) :
    PhysicalAmplitude P (fun q => (w q : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp hw.1, ?_⟩
  intro q hq
  simp [hw.2.1 q hq]

private theorem realAmplitude_compactSupport (P : PacketData ι) (w : ℝ → ℝ)
    (hw : NonnegativeRealPhysicalAmplitude P w) : HasCompactSupport w := by
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  exact hq (hw.2.1 q hn)

/-- A continuous real representative of the physical zero-order K kernel.
Only its values on the physical q interval are used. -/
private def zeroOrderKExtension (P : PacketData ι) (q : ℝ) : ℝ :=
  ((q : ℂ) * extendedKKernel (P.Y0 / 32)
    (by have h := P.Y0_pos; positivity) 0 q).re

private theorem zeroOrderKExtension_continuous (P : PacketData ι) :
    Continuous (zeroOrderKExtension P) := by
  have hc : Continuous (fun q : ℝ =>
      (q : ℂ) * extendedKKernel (P.Y0 / 32)
        (by have h := P.Y0_pos; positivity) 0 q) := by
    fun_prop
  exact Complex.continuous_re.comp hc

private theorem zeroOrderKExtension_eq (P : PacketData ι) (q : ℝ)
    (hq : q ∈ P.region) :
    zeroOrderKExtension P q = imaginaryOrderK 0 q := by
  have hqpos : 0 < q := by
    have hlow : P.Y0 / 16 ≤ q := hq.1
    linarith [P.Y0_pos]
  have hqne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  unfold zeroOrderKExtension
  rw [extendedKKernel_eq_on_physical_region P 0 q hq]
  rw [mul_div_cancel₀ _ hqne]
  rfl

/-- The physical K transform of a nonzero nonnegative real amplitude is
strictly positive at height zero.  Compact support makes the real integrand
continuous and integrable; positivity comes from the genuine K₀ integral. -/
theorem amplitudeK_zero_re_pos (P : PacketData ι) (w : ℝ → ℝ)
    (hw : NonnegativeRealPhysicalAmplitude P w)
    (hwpos : ∃ q, 0 < w q) :
    0 < (amplitudeK P (fun q => (w q : ℂ)) 0).re := by
  obtain ⟨q₀, hq₀⟩ := hwpos
  have hq₀mem : q₀ ∈ P.region := by
    by_contra hn
    have hz := hw.2.1 q₀ hn
    linarith
  let f : ℝ → ℝ := fun q => w q * zeroOrderKExtension P q
  have hfcont : Continuous f := hw.1.mul (zeroOrderKExtension_continuous P)
  have hfcomp : HasCompactSupport f := by
    apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
    intro q hq
    by_contra hn
    exact hq (by simp [f, hw.2.1 q hn])
  have hfnonneg : 0 ≤ f := by
    intro q
    by_cases hq : q ∈ P.region
    · have hqpos : 0 < q := by
        have hlow : P.Y0 / 16 ≤ q := hq.1
        linarith [P.Y0_pos]
      change 0 ≤ w q * zeroOrderKExtension P q
      rw [zeroOrderKExtension_eq P q hq]
      exact mul_nonneg (hw.2.2 q) (imaginaryOrderK_zero_pos hqpos).le
    · simp [f, hw.2.1 q hq]
  have hf₀ : f q₀ ≠ 0 := by
    apply ne_of_gt
    change 0 < w q₀ * zeroOrderKExtension P q₀
    rw [zeroOrderKExtension_eq P q₀ hq₀mem]
    have hqpos : 0 < q₀ := by
      have hlow : P.Y0 / 16 ≤ q₀ := hq₀mem.1
      linarith [P.Y0_pos]
    exact mul_pos hq₀ (imaginaryOrderK_zero_pos hqpos)
  have hpos : 0 < ∫ q : ℝ, f q :=
    hfcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hfcomp hfnonneg hf₀
  have hci : Integrable (fun q : ℝ =>
      (w q : ℂ) * (imaginaryOrderK 0 q : ℂ)) :=
    amplitudeK_q_integrable P (fun q => (w q : ℂ))
      (realAmplitude_physical P w hw) 0
  have heq (q : ℝ) :
      ((w q : ℂ) * (imaginaryOrderK 0 q : ℂ)).re = f q := by
    by_cases hq : q ∈ P.region
    · simp [f, zeroOrderKExtension_eq P q hq, ← Complex.ofReal_mul]
    · simp [f, hw.2.1 q hq]
  calc
    (amplitudeK P (fun q => (w q : ℂ)) 0).re =
        ∫ q : ℝ, ((w q : ℂ) * (imaginaryOrderK 0 q : ℂ)).re := by
      exact (integral_re hci).symm
    _ = ∫ q : ℝ, f q := by
      congr 1
      funext q
      exact heq q
    _ > 0 := hpos

theorem amplitudeK_zero_ne (P : PacketData ι) (w : ℝ → ℝ)
    (hw : NonnegativeRealPhysicalAmplitude P w)
    (hwpos : ∃ q, 0 < w q) :
    amplitudeK P (fun q => (w q : ℂ)) 0 ≠ 0 := by
  intro hz
  have hp := amplitudeK_zero_re_pos P w hw hwpos
  simp [hz] at hp

/-- The same compact real amplitude has a strictly positive q-Laplace
profile at every real u. -/
theorem qLaplaceProfile_re_pos (P : PacketData ι) (w : ℝ → ℝ)
    (hw : NonnegativeRealPhysicalAmplitude P w)
    (hwpos : ∃ q, 0 < w q) (u : ℝ) :
    0 < (qLaplaceProfile P (fun q => (w q : ℂ)) u).re := by
  obtain ⟨q₀, hq₀⟩ := hwpos
  let f : ℝ → ℝ := fun q => w q * Real.exp (-q * Real.cosh u)
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hfcomp : HasCompactSupport f := by
    apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
    intro q hq
    by_contra hn
    exact hq (by simp [f, hw.2.1 q hn])
  have hfnonneg : 0 ≤ f := by
    intro q
    exact mul_nonneg (hw.2.2 q) (Real.exp_pos _).le
  have hf₀ : f q₀ ≠ 0 :=
    ne_of_gt (mul_pos hq₀ (Real.exp_pos _))
  have hpos : 0 < ∫ q : ℝ, f q :=
    hfcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hfcomp hfnonneg hf₀
  have heq : qLaplaceProfile P (fun q => (w q : ℂ)) u =
      (∫ q : ℝ, f q : ℝ) := by
    unfold qLaplaceProfile
    have hp : (fun q : ℝ =>
        (w q : ℂ) * (Real.exp (-q * Real.cosh u) : ℂ)) =
        (fun q : ℝ => (f q : ℂ)) := by
      funext q
      simp [f, Complex.ofReal_mul]
    rw [hp, integral_complex_ofReal]
  simpa only [heq, Complex.ofReal_re] using hpos

/-- Strict full-height energy follows from the genuine Fourier energy
identity and positivity of the continuous q-Laplace profile. -/
theorem amplitudeK_full_height_energy_pos (P : PacketData ι) (w : ℝ → ℝ)
    (hw : NonnegativeRealPhysicalAmplitude P w)
    (hwpos : ∃ q, 0 < w q) :
    0 < ∫ t : ℝ, ‖amplitudeK P (fun q => (w q : ℂ)) t‖ ^ 2 := by
  let a : ℝ → ℂ := fun q => (w q : ℂ)
  have ha : PhysicalAmplitude P a := realAmplitude_physical P w hw
  have hpc : Continuous (fun u : ℝ => ‖qLaplaceProfile P a u‖ ^ 2) :=
    (qLaplaceProfile_continuous P a ha).norm.pow 2
  have hpi : Integrable (fun u : ℝ => ‖qLaplaceProfile P a u‖ ^ 2) :=
    qLaplaceProfile_norm_sq_integrable P a ha
  have hpn : 0 ≤ (fun u : ℝ => ‖qLaplaceProfile P a u‖ ^ 2) := by
    intro u
    positivity
  have hpzero : qLaplaceProfile P a 0 ≠ 0 := by
    intro hz
    have hp := qLaplaceProfile_re_pos P w hw hwpos 0
    simp [a, hz] at hp
  have hp0 : (fun u : ℝ => ‖qLaplaceProfile P a u‖ ^ 2) 0 ≠ 0 := by
    change ‖qLaplaceProfile P a 0‖ ^ 2 ≠ 0
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hpzero)
  have hprof : 0 < ∫ u : ℝ, ‖qLaplaceProfile P a u‖ ^ 2 :=
    integral_pos_of_integrable_nonneg_nonzero hpc hpi hpn hp0
  rw [amplitudeK_full_height_energy P a ha]
  exact mul_pos (by positivity : 0 < Real.pi / 4) hprof

/-- The actual continuum K₀(q+r) quadratic form is strictly positive on
nonzero nonnegative real physical amplitudes. -/
theorem regionKZero_strict_positive_of_nonnegative_real
    (P : PacketData ι) (w : ℝ → ℝ)
    (hw : NonnegativeRealPhysicalAmplitude P w)
    (hwpos : ∃ q, 0 < w q) :
    0 < Complex.re
      (∫ q in P.region, ∫ r in P.region,
        (w q : ℂ) * Complex.conj (w r : ℂ) *
          (imaginaryOrderK 0 (q + r) : ℂ)) := by
  have hE := amplitudeK_full_height_energy_pos P w hw hwpos
  have hPair := amplitudeK_full_height_regionKZero P
    (fun q => (w q : ℂ)) (realAmplitude_physical P w hw)
  have hπ : 0 ≤ Real.pi / 2 := by positivity
  by_contra hn
  have hle : Complex.re
      (∫ q in P.region, ∫ r in P.region,
        (w q : ℂ) * Complex.conj (w r : ℂ) *
          (imaginaryOrderK 0 (q + r) : ℂ)) ≤ 0 := le_of_not_gt hn
  have hmul := mul_nonpos_of_nonneg_of_nonpos hπ hle
  linarith

/-- The pointwise positivity hypothesis can equivalently be supplied as
nonvanishing almost everywhere, using continuity and nonnegativity. -/
theorem amplitudeK_zero_ne_of_not_ae_zero (P : PacketData ι) (w : ℝ → ℝ)
    (hw : NonnegativeRealPhysicalAmplitude P w)
    (hn : ¬ (w =ᵐ[volume] fun _ => (0 : ℝ))) :
    amplitudeK P (fun q => (w q : ℂ)) 0 ≠ 0 := by
  apply amplitudeK_zero_ne P w hw
  by_contra hnot
  have hzero : ∀ q : ℝ, w q = 0 := by
    intro q
    have hle : w q ≤ 0 := le_of_not_gt (not_exists.mp hnot q)
    exact le_antisymm hle (hw.2.2 q)
  exact hn (Filter.Eventually.of_forall hzero)

theorem amplitudeK_full_height_energy_pos_of_not_ae_zero
    (P : PacketData ι) (w : ℝ → ℝ)
    (hw : NonnegativeRealPhysicalAmplitude P w)
    (hn : ¬ (w =ᵐ[volume] fun _ => (0 : ℝ))) :
    0 < ∫ t : ℝ, ‖amplitudeK P (fun q => (w q : ℂ)) t‖ ^ 2 := by
  apply amplitudeK_full_height_energy_pos P w hw
  by_contra hnot
  have hzero : ∀ q : ℝ, w q = 0 := by
    intro q
    have hle : w q ≤ 0 := le_of_not_gt (not_exists.mp hnot q)
    exact le_antisymm hle (hw.2.2 q)
  exact hn (Filter.Eventually.of_forall hzero)

/-- A conditional specialization to the literal spectral-test K transform.
The real/nonnegative hypotheses are explicit: generic physical spectral
tests can carry complex phases, so this does not claim their positivity. -/
theorem kTestTransform_zero_ne_of_nonnegative_real_amplitude
    (P : PacketData ι) (k : D4 → ℤ)
    (hreal : ∀ q, (actualKAmplitude P k q).im = 0)
    (hnonneg : ∀ q, 0 ≤ (actualKAmplitude P k q).re)
    (hpos : ∃ q, 0 < (actualKAmplitude P k q).re) :
    kTestTransform P k 0 ≠ 0 := by
  let w : ℝ → ℝ := fun q => (actualKAmplitude P k q).re
  have ha := actualKAmplitude_physical P k
  have hw : NonnegativeRealPhysicalAmplitude P w := by
    refine ⟨Complex.continuous_re.comp ha.1, ?_, ?_⟩
    · intro q hq
      simp [w, ha.2 q hq]
    · exact hnonneg
  have heq : (fun q : ℝ => (w q : ℂ)) = actualKAmplitude P k := by
    funext q
    apply Complex.ext
    · rfl
    · simp [w, hreal q]
  rw [kTestTransform_eq_amplitudeK P k 0, ← heq]
  exact amplitudeK_zero_ne P w hw hpos

end
end ImbalancedChen.Part3.ActualKStrictPositiveRealAmplitude20261024z
