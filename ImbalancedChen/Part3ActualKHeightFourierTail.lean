import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit, 2026-10-24.
This is Fourier truncation of the ACTUAL common-height physical integral.
The compact q support and the explicit K budget make its Fourier remainder
absolutely summable with one bound independent of spectral height.
-/

namespace ImbalancedChen.Part3.ActualKHeightFourierTail20261024z

noncomputable section

open Classical Set MeasureTheory Filter
open scoped BigOperators Topology
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly

variable {ι : Type*}

/-- The actual physical q integral at a single common spectral height. -/
def heightPhysicalIntegral (P : PacketData ι) (t : ℝ) : ℂ :=
  ∫ q : ℝ, kPhysical P (commonHeight t) q

/-- The actual Fourier coefficient times its actual common-height mode integral. -/
def heightFourierTerm (P : PacketData ι) (t : ℝ)
    (k : D4 → ℤ) : ℂ :=
  actualCoeff P.rho P.sigma k *
    ∫ q : ℝ, kModeFunction P (commonHeight t) k q

/-- This fixed, nonnegative budget retains the complete packet mass and the
physical region's real volume. -/
def heightFourierBudget (P : PacketData ι) : ℝ :=
  coefficientMass P * (512 / P.Y0^2) * (volume : Measure ℝ).real P.region

private theorem heightFourierBudget_nonneg (P : PacketData ι) :
    0 ≤ heightFourierBudget P := by
  unfold heightFourierBudget
  exact mul_nonneg
    (mul_nonneg (coefficientMass_nonneg P) (by positivity))
    ENNReal.toReal_nonneg

/-- Exact set-integral realization of each Fourier term. -/
private theorem heightFourierTerm_eq_setIntegral (P : PacketData ι)
    (t : ℝ) (k : D4 → ℤ) :
    heightFourierTerm P t k =
      ∫ q in P.region,
        (withKKernel P (commonHeight t)).modeTerm k q := by
  unfold heightFourierTerm
  calc
    actualCoeff P.rho P.sigma k *
        ∫ q : ℝ, kModeFunction P (commonHeight t) k q =
        actualCoeff P.rho P.sigma k *
          ∫ q : ℝ, (withKKernel P (commonHeight t)).modeFunction k q := by
      rw [withKKernel_modeFunction P (commonHeight t) k]
    _ = ∫ q : ℝ, (withKKernel P (commonHeight t)).modeTerm k q := by
      change actualCoeff P.rho P.sigma k *
          ∫ q : ℝ, (withKKernel P (commonHeight t)).modeFunction k q =
        ∫ q : ℝ, actualCoeff P.rho P.sigma k *
          (withKKernel P (commonHeight t)).modeFunction k q
      exact (integral_const_mul (actualCoeff P.rho P.sigma k) _).symm
    _ = ∫ q in P.region,
          (withKKernel P (commonHeight t)).modeTerm k q := by
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun q hq =>
          (withKKernel P (commonHeight t)).mode_zero_off k q hq)).symm

/-- Per-mode bound, uniform over ALL real heights. -/
theorem heightFourierTerm_norm_le (P : PacketData ι)
    (t : ℝ) (k : D4 → ℤ) :
    ‖heightFourierTerm P t k‖ ≤
      ‖actualCoeff P.rho P.sigma k‖ * heightFourierBudget P := by
  have hvol : 0 ≤ (volume : Measure ℝ).real P.region := ENNReal.toReal_nonneg
  have hset : ‖heightFourierTerm P t k‖ ≤
      (‖actualCoeff P.rho P.sigma k‖ *
        (withKKernel P (commonHeight t)).mass) *
          (volume : Measure ℝ).real P.region := by
    rw [heightFourierTerm_eq_setIntegral]
    exact norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
      (fun q hq =>
        (withKKernel P (commonHeight t)).modeTerm_norm_le k q hq)
  calc
    ‖heightFourierTerm P t k‖ ≤
        (‖actualCoeff P.rho P.sigma k‖ *
          (withKKernel P (commonHeight t)).mass) *
            (volume : Measure ℝ).real P.region := hset
    _ ≤ (‖actualCoeff P.rho P.sigma k‖ *
          (coefficientMass P * (512 / P.Y0^2))) *
            (volume : Measure ℝ).real P.region :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (withKKernel_mass_le P (commonHeight t)) (norm_nonneg _)) hvol
    _ = ‖actualCoeff P.rho P.sigma k‖ * heightFourierBudget P := by
      unfold heightFourierBudget
      ring

private theorem heightFourierTerm_hasSum (P : PacketData ι)
    (t : ℝ) :
    HasSum (heightFourierTerm P t) (heightPhysicalIntegral P t) := by
  exact k_hasSum_coefficient_times_modeIntegral P (commonHeight t) 0

/-- The remainder is the exact infinite sum over the complement of the
finite Fourier carrier; no mode is discarded by definition. -/
theorem heightFourier_remainder_hasSum (P : PacketData ι)
    (t : ℝ) (F : Finset (D4 → ℤ)) :
    HasSum
      (fun k : (Fᶜ : Set (D4 → ℤ)) => heightFourierTerm P t k)
      (heightPhysicalIntegral P t - ∑ k ∈ F, heightFourierTerm P t k) := by
  have hs : Summable (heightFourierTerm P t) :=
    (heightFourierTerm_hasSum P t).summable
  have hsplit := hs.sum_add_tsum_compl (s := F)
  have htotal := (heightFourierTerm_hasSum P t).tsum_eq
  have hvalue : heightPhysicalIntegral P t -
        ∑ k ∈ F, heightFourierTerm P t k =
      ∑' k : (Fᶜ : Set (D4 → ℤ)), heightFourierTerm P t k := by
    rw [← htotal, ← hsplit]
    exact add_sub_cancel_left _ _
  rw [hvalue]
  exact (hs.subtype (Fᶜ : Set (D4 → ℤ))).hasSum

/-- Uniform absolute Fourier-tail estimate for every common height t. -/
theorem heightFourier_remainder_norm_le (P : PacketData ι)
    (t : ℝ) (F : Finset (D4 → ℤ)) :
    ‖heightPhysicalIntegral P t -
        ∑ k ∈ F, heightFourierTerm P t k‖ ≤
      heightFourierBudget P *
        ∑' k : (Fᶜ : Set (D4 → ℤ)),
          ‖actualCoeff P.rho P.sigma (k : D4 → ℤ)‖ := by
  let c : (Fᶜ : Set (D4 → ℤ)) → ℝ := fun k =>
    ‖actualCoeff P.rho P.sigma (k : D4 → ℤ)‖
  have hc : Summable c := (P.actual_norm_summable 0).subtype _
  have hb : Summable (fun k : (Fᶜ : Set (D4 → ℤ)) =>
      c k * heightFourierBudget P) := hc.mul_right _
  have hnorm := (heightFourier_remainder_hasSum P t F).norm_le_of_bounded
    hb.hasSum (fun k => heightFourierTerm_norm_le P t (k : D4 → ℤ))
  calc
    ‖heightPhysicalIntegral P t - ∑ k ∈ F, heightFourierTerm P t k‖ ≤
        ∑' k : (Fᶜ : Set (D4 → ℤ)), c k * heightFourierBudget P := hnorm
    _ = heightFourierBudget P *
        ∑' k : (Fᶜ : Set (D4 → ℤ)),
          ‖actualCoeff P.rho P.sigma (k : D4 → ℤ)‖ := by
      rw [hc.tsum_mul_right]
      dsimp [c]
      ring

/-- For every positive error, one finite Fourier carrier controls the tail
simultaneously for every real spectral height and every larger carrier. -/
theorem heightFourier_uniform_finite_approximation (P : PacketData ι)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (D4 → ℤ),
      ∀ G : Finset (D4 → ℤ), F ⊆ G → ∀ t : ℝ,
        ‖heightPhysicalIntegral P t -
          ∑ k ∈ G, heightFourierTerm P t k‖ < ε := by
  let u : (D4 → ℤ) → ℝ := fun k => ‖actualCoeff P.rho P.sigma k‖
  have hu : Summable u := P.actual_norm_summable 0
  have htail : Tendsto
      (fun F : Finset (D4 → ℤ) =>
        ∑' k : (Fᶜ : Set (D4 → ℤ)), u (k : D4 → ℤ))
      atTop (𝓝 (0 : ℝ)) := tendsto_tsum_compl_atTop_zero u
  have hscaled : Tendsto
      (fun F : Finset (D4 → ℤ) =>
        heightFourierBudget P *
          ∑' k : (Fᶜ : Set (D4 → ℤ)), u (k : D4 → ℤ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul htail : Tendsto
        (fun F : Finset (D4 → ℤ) =>
          heightFourierBudget P *
            ∑' k : (Fᶜ : Set (D4 → ℤ)), u (k : D4 → ℤ))
        atTop (𝓝 (heightFourierBudget P * 0)))
  have hevent : ∀ᶠ F in (atTop : Filter (Finset (D4 → ℤ))),
      heightFourierBudget P *
        ∑' k : (Fᶜ : Set (D4 → ℤ)), u (k : D4 → ℤ) < ε :=
    (tendsto_order.1 hscaled).2 ε hε
  obtain ⟨F, hF⟩ := eventually_atTop.1 hevent
  refine ⟨F, ?_⟩
  intro G hFG t
  exact lt_of_le_of_lt (heightFourier_remainder_norm_le P t G)
    (hF G hFG)

end
end ImbalancedChen.Part3.ActualKHeightFourierTail20261024z
