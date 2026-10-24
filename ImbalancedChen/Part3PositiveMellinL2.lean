import ImbalancedChen.Part3PositiveMultiplicativeLog
import ImbalancedChen.Part3FourierL1L2Plancherel
import ImbalancedChen.Part3NativePeriod64Reconstruction
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED. Ordinary Mellin analysis on the physical positive
q-axis. The logarithmic measure isomorphism is proved in the preceding source
module from the real Jacobian. The only Plancherel input here is the genuine
Mathlib Fourier L1∩L2 theorem adapted in Part3FourierL1L2Plancherel.
No automorphic, K-Bessel, or Kuznetsov Plancherel statement is made.
-/

namespace ImbalancedChen.Part3.PositiveMellinL2SourceOnly

noncomputable section

open Classical Set MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace ComplexInnerProductSpace
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralMode spectralTest spectralTest_contDiff)
open PositiveMultiplicativeLogSourceOnly
open FourierL1L2PlancherelSourceOnly

variable {ι : Type*}

private theorem exp_log_ae_dlog :
    (fun q : ℝ => Real.exp (Real.log q)) =ᵐ[positiveMultiplicativeMeasure]
      (id : ℝ → ℝ) := by
  have hpos : ∀ᵐ q ∂positiveMultiplicativeMeasure, 0 < q := by
    unfold positiveMultiplicativeMeasure
    exact (ae_restrict_mem measurableSet_Ioi).mono_ac
      (withDensity_absolutelyContinuous _ _)
  filter_upwards [hpos] with q hq
  exact Real.exp_log hq

/-- Pullback by `q = exp u` is an isometric linear equivalence from the
physical `L²(dq/q)` space to ordinary `L²(du)`. The underlying measure on ℝ
has zero mass outside q>0, so this is exactly positive-axis L². -/
def logarithmicL2Equiv :
    Lp ℂ 2 positiveMultiplicativeMeasure ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving Real.exp exp_measurePreserving
      invFun := Lp.compMeasurePreserving Real.log log_measurePreserving
      left_inv := by
        intro F
        rw [← Lp.compMeasurePreserving_comp_apply F
          exp_measurePreserving log_measurePreserving]
        apply Subtype.ext
        change F.1.compMeasurePreserving (Real.exp ∘ Real.log)
          (exp_measurePreserving.comp log_measurePreserving) = F.1
        have h := AEEqFun.compMeasurePreserving_congr F.1
          (exp_measurePreserving.comp log_measurePreserving)
          measurable_id exp_log_ae_dlog
        simpa using h
      right_inv := by
        intro G
        rw [← Lp.compMeasurePreserving_comp_apply G
          log_measurePreserving exp_measurePreserving]
        apply Subtype.ext
        change G.1.compMeasurePreserving (Real.log ∘ Real.exp)
          (log_measurePreserving.comp exp_measurePreserving) = G.1
        have hcoord : (Real.log ∘ Real.exp) =ᵐ[(volume : Measure ℝ)]
            (id : ℝ → ℝ) :=
          Filter.Eventually.of_forall (fun u => Real.log_exp u)
        have h := AEEqFun.compMeasurePreserving_congr G.1
          (log_measurePreserving.comp exp_measurePreserving)
          measurable_id hcoord
        simpa using h
      map_add' := (Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ)
        Real.exp exp_measurePreserving).map_add
      map_smul' := (Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ)
        Real.exp exp_measurePreserving).map_smul }
  norm_map' := (Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ)
    Real.exp exp_measurePreserving).norm_map

theorem logarithmicL2Equiv_apply_ae
    (F : Lp ℂ 2 positiveMultiplicativeMeasure) :
    (logarithmicL2Equiv F : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      fun u => F (Real.exp u) := by
  exact Lp.coeFn_compMeasurePreserving F exp_measurePreserving

/-- The integral Mellin transform on the physical `dq/q` measure, in the
non-unitary frequency convention `exp(-i t log q)`. -/
def mellinLine (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ q : ℝ, f q * Complex.exp (-Complex.I * (t : ℂ) * (Real.log q : ℂ))
    ∂positiveMultiplicativeMeasure

def logProfile (f : ℝ → ℂ) (u : ℝ) : ℂ := f (Real.exp u)

/-- Exact normalization against Mathlib's Fourier convention
`exp(-2πi u ξ)`; hence ξ=t/(2π). -/
theorem mellinLine_eq_fourier (f : ℝ → ℂ) (hf : Continuous f) (t : ℝ) :
    mellinLine f t = 𝓕 (logProfile f) (t / (2 * Real.pi)) := by
  have hmeas : Measurable (fun q : ℝ =>
      f q * Complex.exp (-Complex.I * (t : ℂ) * (Real.log q : ℂ))) := by
    fun_prop
  have htransport : mellinLine f t =
      ∫ u : ℝ, f (Real.exp u) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log (Real.exp u) : ℂ)) := by
    unfold mellinLine
    rw [← map_exp_volume]
    exact integral_map (by fun_prop) hmeas.aestronglyMeasurable
  rw [htransport, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  have hfreq :
      -2 * Real.pi * (u * (t / (2 * Real.pi))) = -t * u := by
    field_simp [Real.pi_ne_zero]
    ring
  have harg :
      ((↑(-2 * Real.pi * ⟪u, t / (2 * Real.pi)⟫_ℝ) : ℂ) * Complex.I) =
        -Complex.I * (t : ℂ) * (u : ℂ) := by
    rw [Real.inner_apply, hfreq]
    push_cast
    ring
  simp only [logProfile, Real.log_exp, smul_eq_mul, harg]
  ring

/-- Mellin Plancherel for every continuous q-function whose actual
logarithmic profile is in L1∩L2. The constant is 2π because the frequency
variable is t rather than ξ=t/(2π). -/
theorem mellinLine_energy (f : ℝ → ℂ) (hf : Continuous f)
    (h₁ : Integrable (logProfile f)) (h₂ : MemLp (logProfile f) 2) :
    (∫ t : ℝ, ‖mellinLine f t‖ ^ 2) =
      (2 * Real.pi) *
        ∫ q : ℝ, ‖f q‖ ^ 2 ∂positiveMultiplicativeMeasure := by
  have hscale : 0 < 2 * Real.pi :=
    mul_pos (by norm_num) Real.pi_pos
  have hphysical :
      (∫ q : ℝ, ‖f q‖ ^ 2 ∂positiveMultiplicativeMeasure) =
        ∫ u : ℝ, ‖logProfile f u‖ ^ 2 := by
    rw [← map_exp_volume]
    have hmeas : Measurable (fun q : ℝ => ‖f q‖ ^ 2) := by fun_prop
    simpa only [logProfile] using
      (integral_map (by fun_prop) hmeas.aestronglyMeasurable)
  calc
    (∫ t : ℝ, ‖mellinLine f t‖ ^ 2) =
        ∫ t : ℝ, ‖𝓕 (logProfile f) (t / (2 * Real.pi))‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with t
      rw [mellinLine_eq_fourier f hf t]
    _ = (2 * Real.pi) *
        ∫ ξ : ℝ, ‖𝓕 (logProfile f) ξ‖ ^ 2 := by
      rw [Measure.integral_comp_div]
      simp [abs_of_pos hscale]
    _ = (2 * Real.pi) *
        ∫ u : ℝ, ‖logProfile f u‖ ^ 2 := by
      rw [integral_norm_sq_fourier h₁ h₂]
    _ = (2 * Real.pi) *
        ∫ q : ℝ, ‖f q‖ ^ 2 ∂positiveMultiplicativeMeasure := by
      rw [hphysical]

/-- The actual native spectral test in logarithmic physical coordinate. -/
def actualSpectralLogProfile (P : PacketData ι) (k : D4 → ℤ) (u : ℝ) : ℂ :=
  spectralTest k P.Y0 (Real.exp u)

private theorem actual_spectralTest_zero_off_region (P : PacketData ι)
    (k : D4 → ℤ) {q : ℝ} (hq : q ∉ P.region) :
    spectralTest k P.Y0 q = 0 := by
  simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
    Complex.ofReal_zero, zero_mul]

/-- Actual packet support becomes a compact interval in log q. -/
theorem actualSpectralLogProfile_hasCompactSupport (P : PacketData ι)
    (k : D4 → ℤ) : HasCompactSupport (actualSpectralLogProfile P k) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact
      (Icc (Real.log (P.Y0 / 16)) (Real.log (16 * P.Y0))))
  intro u hu
  by_contra hnot
  have hqnot : Real.exp u ∉ P.region := by
    intro hq
    apply hnot
    change Real.exp u ∈ Icc (P.Y0 / 16) (16 * P.Y0) at hq
    constructor
    · calc
        Real.log (P.Y0 / 16) ≤ Real.log (Real.exp u) :=
          Real.log_le_log (div_pos P.Y0_pos (by norm_num)) hq.1
        _ = u := Real.log_exp u
    · calc
        u = Real.log (Real.exp u) := (Real.log_exp u).symm
        _ ≤ Real.log (16 * P.Y0) :=
          Real.log_le_log (Real.exp_pos u) hq.2
  have hz : actualSpectralLogProfile P k u = 0 :=
    actual_spectralTest_zero_off_region P k hqnot
  exact hu hz

theorem actualSpectralLogProfile_continuous (P : PacketData ι)
    (k : D4 → ℤ) : Continuous (actualSpectralLogProfile P k) :=
  (spectralTest_contDiff k P.Y0).continuous.comp Real.continuous_exp

/-- Both genuine domain hypotheses for Fourier Plancherel are supplied by
the actual compact native test, rather than assumed for this specialization. -/
theorem actualSpectralLogProfile_integrable (P : PacketData ι)
    (k : D4 → ℤ) : Integrable (actualSpectralLogProfile P k) :=
  (actualSpectralLogProfile_continuous P k).integrable_of_hasCompactSupport
    (actualSpectralLogProfile_hasCompactSupport P k)

theorem actualSpectralLogProfile_memLp_two (P : PacketData ι)
    (k : D4 → ℤ) : MemLp (actualSpectralLogProfile P k) 2 :=
  (actualSpectralLogProfile_continuous P k).memLp_of_hasCompactSupport
    (actualSpectralLogProfile_hasCompactSupport P k)

private theorem actualSpectralLogProfile_comp_log_ae (P : PacketData ι)
    (k : D4 → ℤ) :
    (fun q : ℝ => actualSpectralLogProfile P k (Real.log q))
      =ᵐ[positiveMultiplicativeMeasure] spectralTest k P.Y0 := by
  filter_upwards [exp_log_ae_dlog] with q hq
  simp only [actualSpectralLogProfile]
  rw [hq]

/-- The same actual compact test is L1 and L2 in its original physical
coordinate under the literal `dq/q` measure. -/
theorem actualSpectralTest_integrable_dlog (P : PacketData ι)
    (k : D4 → ℤ) :
    Integrable (spectralTest k P.Y0) positiveMultiplicativeMeasure := by
  have h := log_measurePreserving.integrable_comp_of_integrable
    (actualSpectralLogProfile_integrable P k)
  have hcomp : Integrable
      (fun q : ℝ => actualSpectralLogProfile P k (Real.log q))
      positiveMultiplicativeMeasure := by
    simpa only [Function.comp_def] using h
  exact hcomp.congr (actualSpectralLogProfile_comp_log_ae P k)

theorem actualSpectralTest_memLp_two_dlog (P : PacketData ι)
    (k : D4 → ℤ) :
    MemLp (spectralTest k P.Y0) 2 positiveMultiplicativeMeasure := by
  have h := (actualSpectralLogProfile_memLp_two P k).comp_measurePreserving
    log_measurePreserving
  exact (memLp_congr_ae (actualSpectralLogProfile_comp_log_ae P k)).1
    (by simpa only [Function.comp_def] using h)

theorem actualSpectralTest_mellin_eq_fourier (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    mellinLine (spectralTest k P.Y0) t =
      𝓕 (actualSpectralLogProfile P k) (t / (2 * Real.pi)) := by
  exact mellinLine_eq_fourier (spectralTest k P.Y0)
    (spectralTest_contDiff k P.Y0).continuous t

/-- The resulting ordinary Mellin energy identity for the actual spectral
test. It does not identify the Bessel K transform with a Mellin transform. -/
theorem actualSpectralTest_mellin_energy (P : PacketData ι)
    (k : D4 → ℤ) :
    (∫ t : ℝ, ‖mellinLine (spectralTest k P.Y0) t‖ ^ 2) =
      (2 * Real.pi) *
        ∫ q : ℝ, ‖spectralTest k P.Y0 q‖ ^ 2
          ∂positiveMultiplicativeMeasure := by
  exact mellinLine_energy (spectralTest k P.Y0)
    (spectralTest_contDiff k P.Y0).continuous
    (actualSpectralLogProfile_integrable P k)
    (actualSpectralLogProfile_memLp_two P k)

end

end ImbalancedChen.Part3.PositiveMellinL2SourceOnly
