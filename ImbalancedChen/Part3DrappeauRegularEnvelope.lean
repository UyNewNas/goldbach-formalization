import ImbalancedChen.Part3RegularPositiveMeasureExhaustion

/-!
# The cubic regular envelope and the existing height payment

The input is the lower-level regular transform envelope in Drappeau,
Lemma 4.4, (4.12), with its scale-dependent low constant left explicit.
It is not asserted as a new theorem about the actual Bessel transforms.

At `K = max 1 (2 * Y)`, the cubic tail is dominated by the existing
mixed-tail consumer with auxiliary parameter zero. Its high coefficient
is `E * (1 + Y * sqrt Y) / sqrt K`. The accepted geometric-shell sum
then costs at most `64 * E`; the low cut adds `E`. The already proved
base-height comparison supplies the final factor four, hence `260`.

Only this scalar conversion is new. Finite height decomposition,
positive-measure integration and exhaustion reuse the accepted suppliers.
`Y` ranges over every positive real number. The two primitive cumulative
quadratic bounds remain separate, and global integrability is a conclusion.
-/

namespace ImbalancedChen.Part3.DrappeauRegularEnvelope

noncomputable section
open MeasureTheory Set Filter
open RegularCumulativeShellPayment20261102
open RegularPositiveMeasureExhaustion20261102
open scoped BigOperators ComplexConjugate Topology

/-- The coefficient of the old `|t|⁻⁵ᐟ²` tail, with auxiliary scale zero. -/
def tailConstant (E Y : ℝ) : ℝ :=
  E * (1 + Y * Real.sqrt Y) / Real.sqrt (regularBase Y)

theorem tailConstant_nonneg {E Y : ℝ} (hE : 0 ≤ E) (hY : 0 < Y) :
    0 ≤ tailConstant E Y := by
  unfold tailConstant
  positivity

/-- The low estimate includes height zero and needs no lower scale cutoff. -/
theorem envelope_le_low {E Y t : ℝ} (hE : 0 ≤ E) :
    E * min 1 ((1 + Y * Real.sqrt Y) / (1 + |t| ^ 3)) ≤ E := by
  calc
    _ ≤ E * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hE
    _ = E := mul_one E

/-- The cubic envelope fits the accepted tail with auxiliary parameter zero. -/
theorem envelope_le_tail {E Y t : ℝ} (hE : 0 ≤ E) (hY : 0 < Y)
    (ht : regularBase Y ≤ |t|) :
    E * min 1 ((1 + Y * Real.sqrt Y) / (1 + |t| ^ 3)) ≤
      tailConstant E Y * (1 / (|t| ^ 2 * Real.sqrt |t|)) := by
  have hK : 1 ≤ regularBase Y := le_max_left _ _
  have hKpos : 0 < regularBase Y := zero_lt_one.trans_le hK
  have htpos : 0 < |t| := hKpos.trans_le ht
  have hsK : 0 < Real.sqrt (regularBase Y) := Real.sqrt_pos.mpr hKpos
  have hst : 0 < Real.sqrt |t| := Real.sqrt_pos.mpr htpos
  have hnum : 0 ≤ E * (1 + Y * Real.sqrt Y) := by positivity
  have hden : Real.sqrt (regularBase Y) * (|t| ^ 2 * Real.sqrt |t|) ≤ |t| ^ 3 := by
    calc
      _ ≤ Real.sqrt |t| * (|t| ^ 2 * Real.sqrt |t|) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht) (by positivity)
      _ = |t| ^ 2 * (Real.sqrt |t|) ^ 2 := by ring
      _ = |t| ^ 3 := by rw [Real.sq_sqrt (abs_nonneg t)]; ring
  have hdpos : 0 < Real.sqrt (regularBase Y) * (|t| ^ 2 * Real.sqrt |t|) :=
    mul_pos hsK (mul_pos (sq_pos_of_pos htpos) hst)
  calc
    _ ≤ E * ((1 + Y * Real.sqrt Y) / (1 + |t| ^ 3)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hE
    _ = (E * (1 + Y * Real.sqrt Y)) / (1 + |t| ^ 3) := by ring
    _ ≤ (E * (1 + Y * Real.sqrt Y)) / |t| ^ 3 := by
      apply (div_le_div_iff₀ (by positivity : 0 < 1 + |t| ^ 3) (pow_pos htpos 3)).mpr
      nlinarith only [hnum]
    _ ≤ (E * (1 + Y * Real.sqrt Y)) /
        (Real.sqrt (regularBase Y) * (|t| ^ 2 * Real.sqrt |t|)) := by
      apply (div_le_div_iff₀ (pow_pos htpos 3) hdpos).mpr
      exact mul_le_mul_of_nonneg_left hden hnum
    _ = tailConstant E Y * (1 / (|t| ^ 2 * Real.sqrt |t|)) := by
      unfold tailConstant
      ring

private theorem scale_factor_le {Y : ℝ} (hY : 0 < Y) :
    1 + Y * Real.sqrt Y ≤ 2 * (regularBase Y) ^ 3 := by
  let K := regularBase Y
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hYK : Y ≤ K := by
    have h2Y : 2 * Y ≤ K := le_max_right _ _
    linarith
  have hK2 : K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  have hsY : Real.sqrt Y ≤ K := Real.sqrt_le_iff.mpr ⟨hK0, hYK.trans hK2⟩
  have hproduct : Y * Real.sqrt Y ≤ K * K :=
    mul_le_mul hYK hsY (Real.sqrt_nonneg Y) hK0
  have hK23 : K ^ 2 ≤ K ^ 3 := by
    calc
      _ = K ^ 2 * 1 := (mul_one _).symm
      _ ≤ K ^ 2 * K := mul_le_mul_of_nonneg_left hK (sq_nonneg K)
      _ = K ^ 3 := by ring
  have hK3 : 1 ≤ K ^ 3 := hK.trans (hK2.trans hK23)
  change 1 + Y * Real.sqrt Y ≤ 2 * K ^ 3
  nlinarith only [hproduct, hK23, hK3]

/-- The already summed tail costs at most `64 * E`, uniformly in `Y > 0`. -/
theorem tail_cost_le {E Y : ℝ} (hE : 0 ≤ E) (hY : 0 < Y) :
    tailConstant E Y * (32 / ((regularBase Y) ^ 2 * Real.sqrt (regularBase Y))) ≤
      64 * E := by
  have hK : 0 < regularBase Y := zero_lt_one.trans_le (le_max_left _ _)
  have hden : Real.sqrt (regularBase Y) *
      ((regularBase Y) ^ 2 * Real.sqrt (regularBase Y)) = (regularBase Y) ^ 3 := by
    calc
      _ = (regularBase Y) ^ 2 * (Real.sqrt (regularBase Y)) ^ 2 := by ring
      _ = (regularBase Y) ^ 3 := by rw [Real.sq_sqrt hK.le]; ring
  calc
    _ = 32 * E * (1 + Y * Real.sqrt Y) /
        (Real.sqrt (regularBase Y) * ((regularBase Y) ^ 2 * Real.sqrt (regularBase Y))) := by
      unfold tailConstant
      ring
    _ = 32 * E * (1 + Y * Real.sqrt Y) / (regularBase Y) ^ 3 := by rw [hden]
    _ ≤ 64 * E := by
      apply (div_le_iff₀ (pow_pos hK 3)).mpr
      have hp := mul_le_mul_of_nonneg_left (scale_factor_le hY)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hE)
      nlinarith only [hp]

private theorem paid_pair_le {E Y u v A2 B2 : ℝ}
    (hE : 0 ≤ E) (hY : 0 < Y) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2) :
    (E + tailConstant E Y * (32 / ((regularBase Y) ^ 2 * Real.sqrt (regularBase Y)))) *
      pairBudget (regularBase Y) u v A2 B2 ≤
        260 * E * Real.sqrt (((1 + Y ^ 2 + u) * A2) * ((1 + Y ^ 2 + v) * B2)) := by
  have hcost : E + tailConstant E Y *
      (32 / ((regularBase Y) ^ 2 * Real.sqrt (regularBase Y))) ≤ 65 * E := by
    linarith [tail_cost_le hE hY]
  calc
    _ ≤ (65 * E) * (4 * Real.sqrt
        (((1 + Y ^ 2 + u) * A2) * ((1 + Y ^ 2 + v) * B2))) :=
      mul_le_mul hcost (regularBase_pairBudget_le hu hv hA2 hB2)
        (pairBudget_nonneg _ _ _ _ _) (by positivity)
    _ = _ := by ring

/-- Finite positive spectral cuts. The two cumulative energies are primitive
inputs; no paired spectral-return bound is assumed. -/
theorem finite_cut_absolute_le {ι : Type*} (S : Finset ι) (t : ι → ℝ) (H A B : ι → ℂ)
    {E Y u v A2 B2 : ℝ} (hE : 0 ≤ E) (hY : 0 < Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hCumA : ∀ T : ℝ, 1 ≤ T →
      ∑ i ∈ heightCut S t T, ‖A i‖ ^ 2 ≤ (T ^ 2 + u) * A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T →
      ∑ i ∈ heightCut S t T, ‖B i‖ ^ 2 ≤ (T ^ 2 + v) * B2)
    (htransform : ∀ i ∈ S, ‖H i‖ ≤
      E * min 1 ((1 + Y * Real.sqrt Y) / (1 + |t i| ^ 3))) (J : ℕ) :
    ∑ i ∈ heightCut S t ((4 : ℝ) ^ J * regularBase Y), ‖H i * A i * conj (B i)‖ ≤
      260 * E * Real.sqrt (((1 + Y ^ 2 + u) * A2) * ((1 + Y ^ 2 + v) * B2)) := by
  have hlow : ∀ i ∈ heightCut S t (regularBase Y), ‖H i‖ ≤ E := by
    intro i hi
    exact (htransform i (Finset.mem_filter.mp hi).1).trans (envelope_le_low hE)
  have hdecay : ∀ i ∈ S, regularBase Y ≤ |t i| →
      ‖H i‖ ≤ tailConstant E Y * (1 / (|t i| ^ 2 * Real.sqrt |t i|) + 0 / |t i| ^ 3) := by
    intro i hi ht
    simpa only [zero_div, add_zero] using (htransform i hi).trans (envelope_le_tail hE hY ht)
  have hb := regular_cutoff_absolute_payment S t H A B
    (K := regularBase Y) (C := tailConstant E Y) (Y := 0) (E := E)
    (le_max_left _ _) (tailConstant_nonneg hE hY) (by norm_num) hE hu hv hA2 hB2
    hCumA hCumB hlow hdecay J
  calc
    _ ≤ (E + tailConstant E Y *
        (32 / ((regularBase Y) ^ 2 * Real.sqrt (regularBase Y)))) *
        pairBudget (regularBase Y) u v A2 B2 := by
      simpa only [mul_zero, zero_div, add_zero] using hb
    _ ≤ _ := paid_pair_le hE hY hu hv hA2 hB2

/-- Positive-measure finite cuts, including their actual local L1 membership. -/
theorem continuous_cut_absolute_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (t : α → ℝ) (H A B : α → ℂ) (ht : Measurable t)
    (hF : AEStronglyMeasurable (fun x => H x * A x * conj (B x)) μ)
    {E Y u v A2 B2 : ℝ} (hE : 0 ≤ E) (hY : 0 < Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hMA : ∀ T : ℝ, 1 ≤ T → MemLp A 2 (μ.restrict (spectralCut t T)))
    (hMB : ∀ T : ℝ, 1 ≤ T → MemLp B 2 (μ.restrict (spectralCut t T)))
    (hCumA : ∀ T : ℝ, 1 ≤ T →
      (∫ x in spectralCut t T, ‖A x‖ ^ 2 ∂μ) ≤ (T ^ 2 + u) * A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T →
      (∫ x in spectralCut t T, ‖B x‖ ^ 2 ∂μ) ≤ (T ^ 2 + v) * B2)
    (htransform : ∀ x, ‖H x‖ ≤
      E * min 1 ((1 + Y * Real.sqrt Y) / (1 + |t x| ^ 3))) (J : ℕ) :
    IntegrableOn (fun x => H x * A x * conj (B x))
      (spectralCut t ((4 : ℝ) ^ J * regularBase Y)) μ ∧
      (∫ x in spectralCut t ((4 : ℝ) ^ J * regularBase Y), ‖H x * A x * conj (B x)‖ ∂μ) ≤
        260 * E * Real.sqrt (((1 + Y ^ 2 + u) * A2) * ((1 + Y ^ 2 + v) * B2)) := by
  have hlow : ∀ x ∈ spectralCut t (regularBase Y), ‖H x‖ ≤ E :=
    fun x _ => (htransform x).trans (envelope_le_low hE)
  have hdecay : ∀ x, regularBase Y ≤ |t x| →
      ‖H x‖ ≤ tailConstant E Y * (1 / (|t x| ^ 2 * Real.sqrt |t x|) + 0 / |t x| ^ 3) := by
    intro x hx
    simpa only [zero_div, add_zero] using (htransform x).trans (envelope_le_tail hE hY hx)
  obtain ⟨hi, hb⟩ := continuous_cutoff_payment μ t H A B ht hF
    (K := regularBase Y) (C := tailConstant E Y) (Y := 0) (E := E)
    (le_max_left _ _) (tailConstant_nonneg hE hY) (by norm_num) hE hu hv hA2 hB2
    hMA hMB hCumA hCumB hlow hdecay J
  refine ⟨hi, ?_⟩
  calc
    _ ≤ (E + tailConstant E Y *
        (32 / ((regularBase Y) ^ 2 * Real.sqrt (regularBase Y)))) *
        pairBudget (regularBase Y) u v A2 B2 := by
      simpa only [mul_zero, zero_div, add_zero] using hb
    _ ≤ _ := paid_pair_le hE hY hu hv hA2 hB2

/-- Global absolute integrability is proved from the uniformly bounded L1 cuts. -/
theorem regular_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (t : α → ℝ) (H A B : α → ℂ) (ht : Measurable t)
    (hF : AEStronglyMeasurable (fun x => H x * A x * conj (B x)) μ)
    {E Y u v A2 B2 : ℝ} (hE : 0 ≤ E) (hY : 0 < Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hMA : ∀ T : ℝ, 1 ≤ T → MemLp A 2 (μ.restrict (spectralCut t T)))
    (hMB : ∀ T : ℝ, 1 ≤ T → MemLp B 2 (μ.restrict (spectralCut t T)))
    (hCumA : ∀ T : ℝ, 1 ≤ T →
      (∫ x in spectralCut t T, ‖A x‖ ^ 2 ∂μ) ≤ (T ^ 2 + u) * A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T →
      (∫ x in spectralCut t T, ‖B x‖ ^ 2 ∂μ) ≤ (T ^ 2 + v) * B2)
    (htransform : ∀ x, ‖H x‖ ≤
      E * min 1 ((1 + Y * Real.sqrt Y) / (1 + |t x| ^ 3))) :
    Integrable (fun x => H x * A x * conj (B x)) μ ∧
      (∫ x, ‖H x * A x * conj (B x)‖ ∂μ) ≤
        260 * E * Real.sqrt (((1 + Y ^ 2 + u) * A2) * ((1 + Y ^ 2 + v) * B2)) := by
  apply integrable_exhaustion_of_cut_bound μ t (fun x => H x * A x * conj (B x))
    (K := regularBase Y) (le_max_left _ _) (by positivity) hF
  exact continuous_cut_absolute_le μ t H A B ht hF hE hY hu hv hA2 hB2
    hMA hMB hCumA hCumB htransform

/-- The signed complex cut integrals converge only after global L1 is established. -/
theorem integral_exhaustion {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (t : α → ℝ) (H A B : α → ℂ) (ht : Measurable t)
    (hF : AEStronglyMeasurable (fun x => H x * A x * conj (B x)) μ)
    {E Y u v A2 B2 : ℝ} (hE : 0 ≤ E) (hY : 0 < Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hMA : ∀ T : ℝ, 1 ≤ T → MemLp A 2 (μ.restrict (spectralCut t T)))
    (hMB : ∀ T : ℝ, 1 ≤ T → MemLp B 2 (μ.restrict (spectralCut t T)))
    (hCumA : ∀ T : ℝ, 1 ≤ T →
      (∫ x in spectralCut t T, ‖A x‖ ^ 2 ∂μ) ≤ (T ^ 2 + u) * A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T →
      (∫ x in spectralCut t T, ‖B x‖ ^ 2 ∂μ) ≤ (T ^ 2 + v) * B2)
    (htransform : ∀ x, ‖H x‖ ≤
      E * min 1 ((1 + Y * Real.sqrt Y) / (1 + |t x| ^ 3))) :
    Tendsto (fun J : ℕ => ∫ x in spectralCut t ((4 : ℝ) ^ J * regularBase Y),
      H x * A x * conj (B x) ∂μ) atTop (𝓝 (∫ x, H x * A x * conj (B x) ∂μ)) := by
  exact regular_integral_exhaustion μ t (fun x => H x * A x * conj (B x)) ht
    (regular_integrable μ t H A B ht hF hE hY hu hv hA2 hB2
      hMA hMB hCumA hCumB htransform).1 (le_max_left _ _)

end
end ImbalancedChen.Part3.DrappeauRegularEnvelope
