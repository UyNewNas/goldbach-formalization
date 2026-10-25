import ImbalancedChen.Part3GenericIntervalProjectionLimit

/-!
The constructed CLOSED-interval spectral operators satisfy P_a P_b=P_min.
The proof uses genuine scalar-measure DCT for the ramp product defect and
strong convergence plus the proved uniform contraction bound. Idempotence
and commutation follow, with no projection or product-limit premise.
SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT.
-/

namespace ImbalancedChen.Part3.GenericIntervalProjectionLaws20261025a
noncomputable section
open MeasureTheory Filter
open scoped Topology
open GenericResolventScalarMeasure20261025a ClosedIntervalSpectralRamps20261025a
open GenericIntervalProjectionLimit20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem ramp_product_defect_norm_sq (a b : ℝ) (n : ℕ) (f : H) :
    ‖rampOperator R hSA a n (rampOperator R hSA b n f) -
      rampOperator R hSA (min a b) n f‖ ^ 2 =
      ∫ t : ResolventSpectrum R,
        (ramp a n (t : ℝ) * ramp b n (t : ℝ) - ramp (min a b) n (t : ℝ)) ^ 2
        ∂scalarMeasure R hSA f := by
  have hn := realCFC_norm_sq R hSA f
    (spectralRamp R a n * spectralRamp R b n - spectralRamp R (min a b) n)
  rw [map_sub, map_mul, ContinuousLinearMap.sub_apply] at hn
  exact hn

theorem ramp_product_defect_tendsto_zero (a b : ℝ) (f : H) :
    Tendsto (fun n => rampOperator R hSA a n (rampOperator R hSA b n f) -
      rampOperator R hSA (min a b) n f) atTop (𝓝 0) := by
  have hsquare : Tendsto (fun n =>
      ‖rampOperator R hSA a n (rampOperator R hSA b n f) -
        rampOperator R hSA (min a b) n f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [ramp_product_defect_norm_sq] using
      ramp_product_defect_sq_integral_tendsto_zero (spectrumCoordinate R)
        (scalarMeasure R hSA f) a b
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsquare
  have hnorm : Tendsto (fun n =>
      ‖rampOperator R hSA a n (rampOperator R hSA b n f) -
        rampOperator R hSA (min a b) n f‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Strong limits may be multiplied here because the actual left ramps
are uniformly contractions. This bound was proved from actual μ, not assumed. -/
theorem ramp_product_tendsto (a b : ℝ) (f : H) :
    Tendsto (fun n => rampOperator R hSA a n (rampOperator R hSA b n f)) atTop
      (𝓝 (intervalProjection R hSA a (intervalProjection R hSA b f))) := by
  have hb : Tendsto (fun n => ‖rampOperator R hSA b n f - intervalProjection R hSA b f‖)
      atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_intervalProjection R hSA b f)
  have ha : Tendsto (fun n =>
      ‖rampOperator R hSA a n (intervalProjection R hSA b f) -
        intervalProjection R hSA a (intervalProjection R hSA b f)‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp
      (tendsto_intervalProjection R hSA a (intervalProjection R hSA b f))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
  · intro n
    have heq :
        rampOperator R hSA a n (rampOperator R hSA b n f) -
          intervalProjection R hSA a (intervalProjection R hSA b f) =
        rampOperator R hSA a n (rampOperator R hSA b n f - intervalProjection R hSA b f) +
          (rampOperator R hSA a n (intervalProjection R hSA b f) -
            intervalProjection R hSA a (intervalProjection R hSA b f)) := by
      rw [map_sub]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add
      (rampOperator_norm_le R hSA a n _) le_rfl)
  · simpa only [zero_add] using hb.add ha

theorem intervalProjection_mul_apply (a b : ℝ) (f : H) :
    intervalProjection R hSA a (intervalProjection R hSA b f) =
      intervalProjection R hSA (min a b) f := by
  have hp := (ramp_product_tendsto R hSA a b f).sub
    (tendsto_intervalProjection R hSA (min a b) f)
  have hz : intervalProjection R hSA a (intervalProjection R hSA b f) -
      intervalProjection R hSA (min a b) f = 0 :=
    tendsto_nhds_unique hp (ramp_product_defect_tendsto_zero R hSA a b f)
  exact sub_eq_zero.mp hz

/-- Actual spectral interval multiplication, for all real endpoints. -/
theorem intervalProjection_mul (a b : ℝ) :
    intervalProjection R hSA a * intervalProjection R hSA b =
      intervalProjection R hSA (min a b) := by
  ext f
  exact intervalProjection_mul_apply R hSA a b f

theorem intervalProjection_idempotent (a : ℝ) :
    IsIdempotentElem (intervalProjection R hSA a) := by
  simpa only [min_self] using intervalProjection_mul R hSA a a

theorem intervalProjection_commute (a b : ℝ) :
    Commute (intervalProjection R hSA a) (intervalProjection R hSA b) := by
  change intervalProjection R hSA a * intervalProjection R hSA b =
    intervalProjection R hSA b * intervalProjection R hSA a
  rw [intervalProjection_mul, intervalProjection_mul, min_comm]

/-- Nested closed intervals give the exact range inclusion, not merely
an inequality between scalar masses. -/
theorem intervalProjection_range_mono {a b : ℝ} (hab : a ≤ b) :
    (intervalProjection R hSA a).toLinearMap.range ≤
      (intervalProjection R hSA b).toLinearMap.range := by
  rintro x ⟨f, rfl⟩
  refine ⟨intervalProjection R hSA a f, ?_⟩
  rw [intervalProjection_mul_apply, min_eq_right hab]

/-- The actual scalar measure identifies the constructed operator with
the CLOSED interval. In particular any atom exactly at a is included. -/
theorem intervalProjection_norm_sq_measure (a : ℝ) (f : H) :
    ‖intervalProjection R hSA a f‖ ^ 2 =
      (scalarMeasure R hSA f).real {t : ResolventSpectrum R | (t : ℝ) ≤ a} := by
  have hdct := tendsto_integral_of_dominated_convergence
    (μ := scalarMeasure R hSA f)
    (F := fun n (t : ResolventSpectrum R) => ramp a n (t : ℝ) ^ 2)
    (f := fun t : ResolventSpectrum R => closedCut a (t : ℝ)) (fun _ => (1 : ℝ))
    (fun n => ((spectralRamp R a n).continuous.measurable.pow_const 2).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := ramp_bounds a n (t : ℝ)
      have hm := mul_le_mul hb.2 hb.2 hb.1 zero_le_one
      nlinarith))
    (Eventually.of_forall (fun t => by
      apply tendsto_const_nhds.congr'
      filter_upwards [ramp_eventually_eq_cut a (t : ℝ)] with n hn
      rw [hn]
      by_cases ht : (t : ℝ) ≤ a <;> simp [closedCut, ht]))
  have hn : Tendsto (fun n => ∫ t : ResolventSpectrum R, ramp a n (t : ℝ) ^ 2
      ∂scalarMeasure R hSA f) atTop (𝓝 (‖intervalProjection R hSA a f‖ ^ 2)) := by
    simpa only [rampOperator, realCFC_norm_sq] using
      (tendsto_intervalProjection R hSA a f).norm.pow 2
  have heq := tendsto_nhds_unique hn hdct
  rw [heq]
  have hset : MeasurableSet {t : ResolventSpectrum R | (t : ℝ) ≤ a} :=
    measurableSet_le (spectrumCoordinate R).continuous.measurable measurable_const
  change (∫ t : ResolventSpectrum R,
    ({t : ResolventSpectrum R | (t : ℝ) ≤ a}.indicator (fun _ => (1 : ℝ))) t
      ∂scalarMeasure R hSA f) = _
  rw [integral_indicator hset]
  simp [Measure.real]

/-- Positive contractions have no spectral mass below zero. The cutoff
at zero itself is deliberately not removed: it can contain a real atom. -/
theorem intervalProjection_eq_zero_of_negative
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) {a : ℝ} (ha : a < 0) :
    intervalProjection R hSA a = 0 := by
  have hset : {t : ResolventSpectrum R | (t : ℝ) ≤ a} = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro t ht
    have hs := spectrum_coordinate_mem_unitInterval R hpos hnorm t
    linarith [hs.1]
  ext f
  have hn := intervalProjection_norm_sq_measure R hSA a f
  rw [hset] at hn
  have hz : ‖intervalProjection R hSA a f‖ = 0 := by
    have hm : (scalarMeasure R hSA f).real ∅ = 0 := by simp
    rw [hm] at hn
    nlinarith [norm_nonneg (intervalProjection R hSA a f)]
  exact norm_eq_zero.mp hz

/-- The closed endpoint one retains the entire spectrum, including any
atom at one; hence the constructed interval family is normalized. -/
theorem intervalProjection_one (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) :
    intervalProjection R hSA 1 = 1 := by
  have hramp (n : ℕ) : spectralRamp R 1 n = 1 := by
    ext t
    exact ramp_eq_one_of_le (spectrum_coordinate_mem_unitInterval R hpos hnorm t).2 n
  have hop (n : ℕ) (f : H) : rampOperator R hSA 1 n f = f := by
    rw [rampOperator, hramp, map_one]
    rfl
  ext f
  have hf : Tendsto (fun n => rampOperator R hSA 1 n f) atTop (𝓝 f) := by
    simpa only [hop] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))
  exact tendsto_nhds_unique (tendsto_intervalProjection R hSA 1 f) hf

end
end ImbalancedChen.Part3.GenericIntervalProjectionLaws20261025a
