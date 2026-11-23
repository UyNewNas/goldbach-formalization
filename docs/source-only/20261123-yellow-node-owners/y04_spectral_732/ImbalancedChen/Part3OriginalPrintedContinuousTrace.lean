import ImbalancedChen.Part3GeometricCriticalEisenstein
import ImbalancedChen.Part3OriginalRegularThreeMeasures
import ImbalancedChen.Part3OriginalCumulativeContinuousRemoval
import ImbalancedChen.Part3ImaginaryOrderKFirstMoment

/-! Conversion of the native all-cusp measure to the manuscript's geometric
Fourier coefficient. The same change of normalization applies to both actual
rows and to every level in the uniform cumulative sieve. -/
namespace ImbalancedChen.Part3.OriginalPrintedContinuousTrace20261123

noncomputable section
open Complex Real Set Finset MeasureTheory
open scoped BigOperators
open GeometricCriticalEisenstein20261123 ActualCriticalCuspEvaluation20261110
open ActualCuspDenominatorClasses20261110 ActualContinuousClassFourier20261110
open OriginalContinuousClassRemoval20261110 OriginalContinuousCuspGram20261110
open OriginalCumulativeContinuousRemoval20261110 Real ImaginaryOrderKFirstMoment20261025a
open OriginalRegularThreeMeasures20261113 OriginalRegularPacketTest20261113
open OriginalRegularBaseCumulative20261113
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalSignedTraceInput20261102 OriginalTwoZFourierAssembly20261102
open OriginalPrincipalTraceRow20261102r
open P3NativePeriod64SamplingSourceOnly (D4)

/-- This is the single hyperbolic factor in native continuous row energy. -/
theorem gammaScale_norm_sq (t : ℝ) :
    ‖gammaScale (criticalPoint t)‖^2 = Real.cosh (Real.pi*t) := by
  have hG : ‖Complex.Gamma (criticalPoint t)‖^2 = Real.pi / Real.cosh (Real.pi*t) := by
    simpa only [criticalPoint, mul_comm Complex.I (t : ℂ)] using norm_gamma_half_add_mul_I_sq t
  have hRe : (criticalPoint t).re = 1/2 := by norm_num [criticalPoint,Complex.mul_re]
  rw [gammaScale, norm_div, div_pow, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hRe,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt Real.pi_pos.le, hG]
  field_simp [Real.pi_ne_zero, (Real.cosh_pos _).ne']

private theorem marked_scale {N : ℕ} [NeZero N] (S : Finset ℕ) (w : ℕ → ℂ) (index : ℕ → ℤ)
    (hindex : ∀ j ∈ S, index j ≠ 0) (a : Parameters N) (one : Bool) (t : ℝ) :
    markedRow S w index (fun n => nativeR a one n t) =
      gammaScale (criticalPoint t) * markedRow S w index (fun n => printedR a one n t) := by
  rw [markedRow, markedRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [nativeR_eq_geometric a one _ (hindex j hj) t]
  ring

def printedMass {N : ℕ} [NeZero N] (F : Parameters N → ℂ) : ℝ :=
  ∑ a : Parameters N, ‖F a‖^2 / Real.pi

private theorem mass_scale {N : ℕ} [NeZero N] (F : Parameters N → ℂ) (t : ℝ) :
    printedMass F =
      4 * (nativeMass N (fun a => gammaScale (criticalPoint t) * F a) / Real.cosh (Real.pi*t)) := by
  rw [printedMass, nativeMass, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_mul, mul_pow, gammaScale_norm_sq]
  field_simp [Real.pi_ne_zero, (Real.cosh_pos _).ne'] <;> ring

def printedLine (N : ℕ) [NeZero N] (one neg : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (t : ℝ) : ℝ :=
  printedMass (fun a : Parameters N => markedRow S w (mark neg) (fun n => printedR a one n t))

theorem printed_line_eq (N : ℕ) [NeZero N] (one neg : Bool) {L : ℝ} (hL : 0 < L)
    (S : Finset ℕ) (w : ℕ → ℂ) (hS : Dyadic L S) (t : ℝ) :
    printedLine N one neg S w t = 4 * lineTerm N one neg S w t := by
  unfold printedLine lineTerm lineMass nativeRow
  simp_rw [marked_scale S w (mark neg) (mark_ne hL S hS neg)]
  exact mass_scale _ t

/-- All levels, both observing frames and both signs. The one constant is
chosen before the original frequency block and spectral window. -/
theorem printed_continuous_large_sieve (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (one neg : Bool) {T L : ℝ},
      1 ≤ T → 1/2 ≤ L → ∀ (S : Finset ℕ) (w : ℕ → ℂ), Dyadic L S →
        IntegrableOn (printedLine N one neg S w) (Icc (-T) T) ∧
          (∫ t in Icc (-T) T, printedLine N one neg S w t) ≤
            C * (T^2 + L^(1+e)/(N : ℝ)) * energy S w := by
  obtain ⟨D,hD,H⟩ := manuscript_regular_three e he
  refine ⟨4*D, by positivity, ?_⟩
  intro N inst one neg T L hT hL S w hS
  obtain ⟨_,_,hi,hb,_⟩ := H N one neg hT hL S w hS
  have Hline : printedLine N one neg S w = fun t => 4 * lineTerm N one neg S w t :=
    funext (printed_line_eq N one neg (by linarith : 0 < L) S w hS)
  rw [Hline]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ 4 * (D * (T^2 + L^(1+e)/(N : ℝ)) * energy S w) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

private theorem source_scale (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (ha : D.block.atom.residue ≠ 0)
    (upper negativeM : Bool) (ell : D4 → ℤ) (t : ℝ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    ∀ a : Parameters z.val,
      source D r k z upper negativeM ell (fun n => nativeR a true n t) =
        gammaScale (criticalPoint t) *
          source D r k z upper negativeM ell (fun n => printedR a true n t) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  intro a
  exact marked_scale _ _ _ (fun n hn =>
    Int.natAbs_pos.mp (traceIndex_natAbs_pos D k negativeM z.val hn ha)) a true t

private theorem reduced_scale (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (upper negativeM : Bool) (ell : D4 → ℤ) (t : ℝ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    ∀ a : Parameters z.val,
      reduced D r k z upper negativeM ell (fun n => nativeR a true n t) =
        gammaScale (criticalPoint t) *
          reduced D r k z upper negativeM ell (fun n => printedR a true n t) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  intro a
  apply marked_scale
  intro n hn
  have hpos := (nCarrier_positive_coprime D k z.val hn).2.1
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  rcases principalTraceSign_cases D k negativeM with h | h <;> simp [h, hnz]

/-- The geometric signed product for the unremoved, physical Poisson source.
The inner M weight and outer complex conjugation are both the original ones. -/
theorem original_printed_trace_product (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (ha : D.block.atom.residue ≠ 0)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (t : ℝ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    (∑ a : Parameters z.val, star (M J j ell (fun n => printedR a false n t)) *
      source D r k z upper negativeM ell (fun n => printedR a true n t) / (Real.pi : ℂ)) =
      (4 / (Real.cosh (Real.pi*t) : ℂ)) *
        classProduct z.val (fun i => M J j ell (fun n => channelR i false n t))
          (fun i => source D r k z upper negativeM ell (fun n => channelR i true n t)) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  have hM (a : Parameters z.val) : M J j ell (fun n => nativeR a false n t) =
      gammaScale (criticalPoint t) * M J j ell (fun n => printedR a false n t) := by
    apply marked_scale
    intro p hp
    have hpos : 0 < p := lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ)<2) j)
      (Finset.mem_Ico.mp hp).1
    exact_mod_cast hpos.ne'
  have hstar : star (gammaScale (criticalPoint t)) * gammaScale (criticalPoint t) =
      (Real.cosh (Real.pi*t) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, gammaScale_norm_sq]
  rw [original_projected_product, nativeProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have pull (g m v : ℂ) :
      star (g*m)*(g*v)/(4*(Real.pi : ℂ)) =
        (star g*g) * (star m*v/(4*(Real.pi : ℂ))) := by
    rw [star_mul']
    ring
  rw [hM, source_scale D r k z ha upper negativeM ell t a, pull, hstar]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (Real.cosh (Real.pi*t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  field_simp [hp,hc] <;> ring

/-- The actual continuous ABL cost after conversion to the printed measure,
including all cusps, every t, and the primary phase in the reduced source. -/
theorem original_printed_removal (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (ha : D.block.atom.residue ≠ 0)
    (upper negativeM : Bool) (ell : D4 → ℤ) (t : ℝ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    printedMass (fun a : Parameters z.val =>
      source D r k z upper negativeM ell (fun n => printedR a true n t)) ≤
      ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2 *
      printedMass (fun a : Parameters z.val =>
        reduced D r k z upper negativeM ell (fun n => printedR a true n t)) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  have h := original_native_removal D r k z upper negativeM ell t
  simp_rw [source_scale D r k z ha upper negativeM ell t,
    reduced_scale D r k z upper negativeM ell t] at h
  rw [mass_scale _ t, mass_scale _ t]
  have hc := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right h (Real.cosh_pos (Real.pi*t)).le) (show 0 ≤ (4 : ℝ) by norm_num)
  convert hc using 1 <;> ring

end
end ImbalancedChen.Part3.OriginalPrintedContinuousTrace20261123
