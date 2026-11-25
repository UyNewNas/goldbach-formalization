import ImbalancedChen.Part3ContinuousTraceCauchy
import ImbalancedChen.Part3RegularPositiveMeasureExhaustion

/-!
# Whole-height exhaustion of the printed continuous pair

This connects the accepted finite-cusp Cauchy inequality to the existing
regular positive-measure height payment. The scalar majorant uses the
square roots of the two literal cusp-summed energies, each normalized by
`1 / pi`. The actual pair keeps the conjugate on the left row.

The premises are separate cumulative energy estimates and low/high
pointwise bounds on the test. Whole-line absolute integrability is a
conclusion, established before taking cutoff limits. The shell sum,
constant 516 and positive-measure exhaustion are reused from the existing
supplier. No actual automorphic input or complete P3.5 estimate is asserted.
-/

namespace ImbalancedChen.Part3.ContinuousTraceExhaustion

noncomputable section

open MeasureTheory Set Filter
open RegularCumulativeShellPayment20261102
open RegularPositiveMeasureExhaustion20261102
open scoped BigOperators ComplexConjugate Topology

variable {ι : Type*} [Fintype ι]

private theorem spectralCut_id_eq_Icc (T : ℝ) :
    spectralCut (fun t : ℝ => t) T = Icc (-T) T := by
  ext t
  change |t| ≤ T ↔ -T ≤ t ∧ t ≤ T
  exact abs_le

/-- The literal continuous pair is globally L1, with the existing regular
height constant. Compact L2 is proved from continuity; global L1 and the
absolute paired-trace estimate are not hypotheses. -/
theorem printed_trace_regular_integrable
    (left right : ι → ℝ → ℂ)
    (hleft : ∀ i, Continuous (left i)) (hright : ∀ i, Continuous (right i))
    (test : ℝ → ℂ) (htest : Continuous test)
    {C Y u v A2 B2 : ℝ} (hC : 0 ≤ C) (hY : 0 < Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hleftEnergy : ∀ T : ℝ, 1 ≤ T →
      (∫ t in Icc (-T) T, ∑ i, ‖left i t‖ ^ 2 / Real.pi) ≤ (T ^ 2 + u) * A2)
    (hrightEnergy : ∀ T : ℝ, 1 ≤ T →
      (∫ t in Icc (-T) T, ∑ i, ‖right i t‖ ^ 2 / Real.pi) ≤ (T ^ 2 + v) * B2)
    (hlow : ∀ t : ℝ, |t| ≤ regularBase Y →
      ‖test t‖ ≤ C * (1 + |Real.log Y|) / (1 + Y))
    (hdecay : ∀ t : ℝ, regularBase Y ≤ |t| →
      ‖test t‖ ≤ C * (1 / (|t| ^ 2 * Real.sqrt |t|) + Y / |t| ^ 3)) :
    Integrable (fun t =>
      test t * (∑ i, star (left i t) * right i t / (Real.pi : ℂ))) ∧
      (∫ t, ‖test t * (∑ i, star (left i t) * right i t / (Real.pi : ℂ))‖) ≤
        516 * C * (1 + |Real.log Y|) / (1 + Y) *
          Real.sqrt (((1 + Y ^ 2 + u) * A2) * ((1 + Y ^ 2 + v) * B2)) := by
  let L : ℝ → ℝ := fun t => ∑ i, ‖left i t‖ ^ 2 / Real.pi
  let R : ℝ → ℝ := fun t => ∑ i, ‖right i t‖ ^ 2 / Real.pi
  let A : ℝ → ℂ := fun t => (Real.sqrt (L t) : ℂ)
  let B : ℝ → ℂ := fun t => (Real.sqrt (R t) : ℂ)
  let P : ℝ → ℂ := fun t => ∑ i, star (left i t) * right i t / (Real.pi : ℂ)
  have hL : Continuous L :=
    continuous_finsetSum _ (fun i _ => ((hleft i).norm.pow 2).div_const _)
  have hR : Continuous R :=
    continuous_finsetSum _ (fun i _ => ((hright i).norm.pow 2).div_const _)
  have hL0 (t : ℝ) : 0 ≤ L t := by dsimp [L]; positivity
  have hR0 (t : ℝ) : 0 ≤ R t := by dsimp [R]; positivity
  have hA : Continuous A := Complex.continuous_ofReal.comp hL.sqrt
  have hB : Continuous B := Complex.continuous_ofReal.comp hR.sqrt
  have hAnorm (t : ℝ) : ‖A t‖ = Real.sqrt (L t) := by
    change ‖(Real.sqrt (L t) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hBnorm (t : ℝ) : ‖B t‖ = Real.sqrt (R t) := by
    change ‖(Real.sqrt (R t) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hAsq (t : ℝ) : ‖A t‖ ^ 2 = L t := by
    rw [hAnorm, Real.sq_sqrt (hL0 t)]
  have hBsq (t : ℝ) : ‖B t‖ ^ 2 = R t := by
    rw [hBnorm, Real.sq_sqrt (hR0 t)]
  have hMA : ∀ T : ℝ, 1 ≤ T →
      MemLp A 2 (volume.restrict (spectralCut (fun t : ℝ => t) T)) := by
    intro T _
    rw [spectralCut_id_eq_Icc]
    apply (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).2
    exact (hA.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hMB : ∀ T : ℝ, 1 ≤ T →
      MemLp B 2 (volume.restrict (spectralCut (fun t : ℝ => t) T)) := by
    intro T _
    rw [spectralCut_id_eq_Icc]
    apply (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).2
    exact (hB.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hCumA : ∀ T : ℝ, 1 ≤ T →
      (∫ t in spectralCut (fun t : ℝ => t) T, ‖A t‖ ^ 2) ≤ (T ^ 2 + u) * A2 := by
    intro T hT
    simpa only [spectralCut_id_eq_Icc, hAsq, L] using hleftEnergy T hT
  have hCumB : ∀ T : ℝ, 1 ≤ T →
      (∫ t in spectralCut (fun t : ℝ => t) T, ‖B t‖ ^ 2) ≤ (T ^ 2 + v) * B2 := by
    intro T hT
    simpa only [spectralCut_id_eq_Icc, hBsq, R] using hrightEnergy T hT
  have hG : Continuous (fun t => test t * A t * conj (B t)) :=
    (htest.mul hA).mul hB.star
  obtain ⟨hGi, hGb⟩ := regular_R1_integrable volume (fun t : ℝ => t) test A B
    measurable_id hG.aestronglyMeasurable hC hY hu hv hA2 hB2
    hMA hMB hCumA hCumB hlow hdecay
  have hP : Continuous P :=
    continuous_finsetSum _ (fun i _ => ((hleft i).star.mul (hright i)).div_const _)
  have hdom (t : ℝ) : ‖test t * P t‖ ≤ ‖test t * A t * conj (B t)‖ := by
    simp only [norm_mul, Complex.norm_conj, hAnorm, hBnorm]
    calc
      _ ≤ ‖test t‖ * (Real.sqrt (L t) * Real.sqrt (R t)) :=
        mul_le_mul_of_nonneg_left
          (ContinuousTraceCauchy.printed_trace_norm_le (fun i => left i t) (fun i => right i t))
          (norm_nonneg _)
      _ = _ := by ring
  have hFi : Integrable (fun t => test t * P t) :=
    hGi.norm.mono' (htest.mul hP).aestronglyMeasurable (Eventually.of_forall hdom)
  refine ⟨hFi, ?_⟩
  exact (integral_mono_ae hFi.norm hGi.norm (Eventually.of_forall hdom)).trans hGb

/-- The full tested complex integral inherits the absolute-integral
bound after global integrability has been established. -/
theorem printed_trace_regular_integral_norm_le
    (left right : ι → ℝ → ℂ)
    (hleft : ∀ i, Continuous (left i)) (hright : ∀ i, Continuous (right i))
    (test : ℝ → ℂ) (htest : Continuous test)
    {C Y u v A2 B2 : ℝ} (hC : 0 ≤ C) (hY : 0 < Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hleftEnergy : ∀ T : ℝ, 1 ≤ T →
      (∫ t in Icc (-T) T, ∑ i, ‖left i t‖ ^ 2 / Real.pi) ≤ (T ^ 2 + u) * A2)
    (hrightEnergy : ∀ T : ℝ, 1 ≤ T →
      (∫ t in Icc (-T) T, ∑ i, ‖right i t‖ ^ 2 / Real.pi) ≤ (T ^ 2 + v) * B2)
    (hlow : ∀ t : ℝ, |t| ≤ regularBase Y →
      ‖test t‖ ≤ C * (1 + |Real.log Y|) / (1 + Y))
    (hdecay : ∀ t : ℝ, regularBase Y ≤ |t| →
      ‖test t‖ ≤ C * (1 / (|t| ^ 2 * Real.sqrt |t|) + Y / |t| ^ 3)) :
    ‖∫ t, test t * (∑ i, star (left i t) * right i t / (Real.pi : ℂ))‖ ≤
      516 * C * (1 + |Real.log Y|) / (1 + Y) *
        Real.sqrt (((1 + Y ^ 2 + u) * A2) * ((1 + Y ^ 2 + v) * B2)) := by
  exact (norm_integral_le_integral_norm _).trans
    (printed_trace_regular_integrable left right hleft hright test htest hC hY hu hv hA2 hB2
      hleftEnergy hrightEnergy hlow hdecay).2

/-- Actual signed cutoff integrals converge to the full printed pair.
The same hypotheses first supply global L1, so this is not a totalized
Bochner-integral limit used in place of an integrability proof. -/
theorem printed_trace_regular_integral_exhaustion
    (left right : ι → ℝ → ℂ)
    (hleft : ∀ i, Continuous (left i)) (hright : ∀ i, Continuous (right i))
    (test : ℝ → ℂ) (htest : Continuous test)
    {C Y u v A2 B2 K : ℝ} (hC : 0 ≤ C) (hY : 0 < Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2) (hK : 1 ≤ K)
    (hleftEnergy : ∀ T : ℝ, 1 ≤ T →
      (∫ t in Icc (-T) T, ∑ i, ‖left i t‖ ^ 2 / Real.pi) ≤ (T ^ 2 + u) * A2)
    (hrightEnergy : ∀ T : ℝ, 1 ≤ T →
      (∫ t in Icc (-T) T, ∑ i, ‖right i t‖ ^ 2 / Real.pi) ≤ (T ^ 2 + v) * B2)
    (hlow : ∀ t : ℝ, |t| ≤ regularBase Y →
      ‖test t‖ ≤ C * (1 + |Real.log Y|) / (1 + Y))
    (hdecay : ∀ t : ℝ, regularBase Y ≤ |t| →
      ‖test t‖ ≤ C * (1 / (|t| ^ 2 * Real.sqrt |t|) + Y / |t| ^ 3)) :
    Tendsto (fun j : ℕ => ∫ t in Icc (-((4 : ℝ) ^ j * K)) ((4 : ℝ) ^ j * K),
      test t * (∑ i, star (left i t) * right i t / (Real.pi : ℂ)))
      atTop (𝓝 (∫ t, test t * (∑ i, star (left i t) * right i t / (Real.pi : ℂ)))) := by
  have hi := (printed_trace_regular_integrable left right hleft hright test htest
    hC hY hu hv hA2 hB2 hleftEnergy hrightEnergy hlow hdecay).1
  simpa only [spectralCut_id_eq_Icc] using
    regular_integral_exhaustion volume (fun t : ℝ => t)
      (fun t => test t * (∑ i, star (left i t) * right i t / (Real.pi : ℂ)))
      measurable_id hi hK

end
end ImbalancedChen.Part3.ContinuousTraceExhaustion
