import ImbalancedChen.Part3GenericStoneCFCPrimitive
import ImbalancedChen.Part3GenericSpectralEndpointProfile

/-!
Strong Stone for the ACTUAL complex graph resolvent and finite positive
lambda intervals. The coordinate lambda=1/r-1 reverses endpoints:
A=1/(1+b)<B=1/(1+a). The strong limit is the OPEN interval projector plus
one half of each endpoint atom. The r=0 kernel is kept as zero throughout;
no zero atom is discarded and no Stone/projection/limit premise occurs.
SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT.
-/

namespace ImbalancedChen.Part3.GenericStrongStone20261025a
noncomputable section
open MeasureTheory Filter
open scoped Topology
open GenericResolventScalarMeasure20261025a ClosedIntervalSpectralRamps20261025a
open GenericIntervalProjectionLimit20261025a GenericSpectralLeftLimit20261025a
open GenericSpectralEndpointProfile20261025a GenericStoneCFCPrimitive20261025a
open ScalarStieltjesPoissonInversion20261025a ComplexContractionResolvent20261025a

def inverseEndpoint (x : ℝ) : ℝ := 1 / (1 + x)

theorem inverseEndpoint_pos {x : ℝ} (hx : 0 < x) : 0 < inverseEndpoint x := by
  unfold inverseEndpoint
  positivity

theorem inverseEndpoint_reverse {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    inverseEndpoint b < inverseEndpoint a := by
  unfold inverseEndpoint
  apply one_div_lt_one_div_of_lt
  · linarith
  · linarith

theorem lambda_lower_iff {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    c < r⁻¹ - 1 ↔ r < inverseEndpoint c := by
  have hd : 0 < 1 + c := by linarith
  unfold inverseEndpoint
  constructor
  · intro h
    have hi : 1 + c < 1 / r := by rw [one_div]; linarith
    have hm := (lt_div_iff₀ hr).mp hi
    exact (lt_div_iff₀ hd).mpr (by simpa only [mul_comm] using hm)
  · intro h
    have hm := (lt_div_iff₀ hd).mp h
    have hi : 1 + c < 1 / r := (lt_div_iff₀ hr).mpr (by simpa only [mul_comm] using hm)
    rw [one_div] at hi
    linarith

theorem lambda_upper_iff {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    r⁻¹ - 1 < c ↔ inverseEndpoint c < r := by
  have hd : 0 < 1 + c := by linarith
  unfold inverseEndpoint
  constructor
  · intro h
    have hi : 1 / r < 1 + c := by rw [one_div]; linarith
    have hm := (div_lt_iff₀ hr).mp hi
    exact (div_lt_iff₀ hd).mpr (by simpa only [mul_comm] using hm)
  · intro h
    have hm := (div_lt_iff₀ hd).mp h
    have hi : 1 / r < 1 + c := (div_lt_iff₀ hr).mpr (by simpa only [mul_comm] using hm)
    rw [one_div] at hi
    linarith

theorem lambda_eq_iff {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    r⁻¹ - 1 = c ↔ r = inverseEndpoint c := by
  have hd : 1 + c ≠ 0 := by linarith
  unfold inverseEndpoint
  constructor
  · intro h
    have hi : 1 / r = 1 + c := by rw [one_div]; linarith
    have hm := (div_eq_iff hr.ne').mp hi
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using hm.symm
  · intro h
    rw [h]
    simp only [one_div, inv_inv]
    ring

theorem endpointStep_eq_profile {A B : ℝ} (hAB : A < B) (r : ℝ) :
    endpointStep A B r = endpointProfile A B r := by
  rcases lt_trichotomy r A with hr | rfl | hr
  · have hB := hr.trans hAB
    simp [endpointStep, closedCut, strictCut, endpointProfile, hr, hr.le, hB, hB.le,
      hr.ne, hB.ne, not_lt_of_ge hr.le]
  · simp [endpointStep, closedCut, strictCut, endpointProfile, hAB, hAB.le, hAB.ne, hAB.ne']
    <;> norm_num
  · rcases lt_trichotomy r B with hB | rfl | hB
    · simp [endpointStep, closedCut, strictCut, endpointProfile, hr, hB, hB.le,
        not_le_of_gt hr, not_lt_of_ge hr.le, hr.ne', hB.ne]
      <;> norm_num
    · simp [endpointStep, closedCut, strictCut, endpointProfile, hAB, hAB.le, hAB.ne, hAB.ne',
        not_le_of_gt hAB, not_lt_of_ge hAB.le]
      <;> norm_num
    · have hA := hAB.trans hB
      simp [endpointStep, closedCut, strictCut, endpointProfile, not_le_of_gt hA,
        not_le_of_gt hB, not_lt_of_ge hA.le, not_lt_of_ge hB.le, hA.ne', hB.ne']

/-- The inverse-coordinate interval order and both endpoint atoms are
derived explicitly. No atom-free hypothesis is used. -/
theorem lambda_endpointProfile {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 0 < r) :
    endpointProfile a b (r⁻¹ - 1) = endpointStep (inverseEndpoint b) (inverseEndpoint a) r := by
  have hb : 0 < b := ha.trans hab
  rw [endpointStep_eq_profile (inverseEndpoint_reverse ha hab)]
  simp only [endpointProfile, Set.indicator, Set.mem_Ioo, Set.mem_singleton_iff]
  rw [lambda_lower_iff ha hr, lambda_upper_iff hb hr, lambda_eq_iff ha hr, lambda_eq_iff hb hr]
  simp only [and_comm]
  ring

theorem primitiveWeight_tendsto_step {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 0 ≤ r) :
    Tendsto (fun epsilon => primitiveWeight a b epsilon r) (𝓝[>] 0)
      (𝓝 (endpointStep (inverseEndpoint b) (inverseEndpoint a) r)) := by
  by_cases hz : r = 0
  · subst r
    have hA := inverseEndpoint_pos (ha.trans hab)
    have hB := inverseEndpoint_pos ha
    simpa [primitiveWeight_zero, endpointStep, closedCut, strictCut, hA.le, hB.le, hA, hB] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have heq : (fun epsilon => primitiveWeight a b epsilon r) =ᶠ[𝓝[>] 0]
        (fun epsilon => intervalWeight a b epsilon (r⁻¹ - 1)) := by
      filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
      exact primitiveWeight_eq_intervalWeight a b hepsilon hz
    have hh := (intervalWeight_tendsto hab (r⁻¹ - 1)).congr' heq.symm
    simpa only [lambda_endpointProfile ha hab hrpos] using hh

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def normalizedStoneOperator (a b epsilon : ℝ) : H →L[ℂ] H :=
  (1 / Real.pi : ℝ) • ∫ x in a..b,
    operatorImaginary (complexResolvent R ((x : ℂ) + (epsilon : ℂ) * Complex.I))

def lambdaOpenProjection (a b : ℝ) : H →L[ℂ] H :=
  leftProjection R hSA (inverseEndpoint a) - intervalProjection R hSA (inverseEndpoint b)

def lambdaAtomProjection (a : ℝ) : H →L[ℂ] H := atomProjection R hSA (inverseEndpoint a)

theorem left_mul_closed_of_lt {A B : ℝ} (hAB : A < B) :
    leftProjection R hSA B * intervalProjection R hSA A = intervalProjection R hSA A := by
  ext f
  have hev := (below_tendsto B).eventually (gt_mem_nhds hAB)
  have heq : (fun n => intervalProjection R hSA (below B n) (intervalProjection R hSA A f)) =ᶠ[atTop]
      (fun _ => intervalProjection R hSA A f) := by
    filter_upwards [hev] with n hn
    rw [GenericIntervalProjectionLaws20261025a.intervalProjection_mul_apply, min_eq_right hn.le]
  have hc : Tendsto (fun n => intervalProjection R hSA (below B n) (intervalProjection R hSA A f))
      atTop (𝓝 (intervalProjection R hSA A f)) := tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique (tendsto_leftProjection R hSA B _) hc

theorem closed_mul_left_of_lt {A B : ℝ} (hAB : A < B) :
    intervalProjection R hSA A * leftProjection R hSA B = intervalProjection R hSA A := by
  have hs := congrArg star (left_mul_closed_of_lt R hSA hAB)
  simpa only [star_mul, (intervalProjection_selfAdjoint R hSA A).star_eq,
    (leftProjection_selfAdjoint R hSA B).star_eq] using hs

theorem lambdaOpenProjection_selfAdjoint (a b : ℝ) :
    IsSelfAdjoint (lambdaOpenProjection R hSA a b) :=
  (leftProjection_selfAdjoint R hSA (inverseEndpoint a)).sub
    (intervalProjection_selfAdjoint R hSA (inverseEndpoint b))

theorem lambdaOpenProjection_idempotent {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsIdempotentElem (lambdaOpenProjection R hSA a b) := by
  have hord := inverseEndpoint_reverse ha hab
  have hL : leftProjection R hSA (inverseEndpoint a) * leftProjection R hSA (inverseEndpoint a) =
      leftProjection R hSA (inverseEndpoint a) := leftProjection_idempotent R hSA _
  have hP : intervalProjection R hSA (inverseEndpoint b) * intervalProjection R hSA (inverseEndpoint b) =
      intervalProjection R hSA (inverseEndpoint b) :=
    GenericIntervalProjectionLaws20261025a.intervalProjection_idempotent R hSA _
  change (leftProjection R hSA (inverseEndpoint a) - intervalProjection R hSA (inverseEndpoint b)) *
    (leftProjection R hSA (inverseEndpoint a) - intervalProjection R hSA (inverseEndpoint b)) = _
  rw [sub_mul, mul_sub, mul_sub, hL, hP,
    left_mul_closed_of_lt R hSA hord, closed_mul_left_of_lt R hSA hord]
  abel

theorem lambdaAtomProjection_selfAdjoint (a : ℝ) :
    IsSelfAdjoint (lambdaAtomProjection R hSA a) := atomProjection_selfAdjoint R hSA _

theorem lambdaAtomProjection_idempotent (a : ℝ) :
    IsIdempotentElem (lambdaAtomProjection R hSA a) := atomProjection_idempotent R hSA _

theorem endpointOperator_eq_open_half_atoms (a b : ℝ) :
    endpointOperator R hSA (inverseEndpoint b) (inverseEndpoint a) =
      lambdaOpenProjection R hSA a b + (1 / 2 : ℝ) •
        (lambdaAtomProjection R hSA a + lambdaAtomProjection R hSA b) := by
  unfold endpointOperator lambdaOpenProjection lambdaAtomProjection atomProjection
  module

/-- Strong operator Stone, with genuine half weights at both endpoints.
This theorem concerns the actual complex CFC graph resolvent, not an
operator defined independently by a Cauchy integral. -/
theorem strongStone (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (f : H) :
    Tendsto (fun epsilon => normalizedStoneOperator R a b epsilon f) (𝓝[>] 0)
      (𝓝 ((lambdaOpenProjection R hSA a b + (1 / 2 : ℝ) •
        (lambdaAtomProjection R hSA a + lambdaAtomProjection R hSA b)) f)) := by
  let A := inverseEndpoint b
  let B := inverseEndpoint a
  let Q := endpointOperator R hSA A B
  let mu := scalarMeasure R hSA f
  have hstrict (c : ℝ) : Measurable (fun r : ResolventSpectrum R => strictCut c (r : ℝ)) :=
    measurable_const.indicator
      (measurableSet_lt (spectrumCoordinate R).continuous.measurable measurable_const)
  have hstep : Measurable (fun r : ResolventSpectrum R => endpointStep A B (r : ℝ)) :=
    measurable_const.mul ((((measurable_closedCut (spectrumCoordinate R) B).add (hstrict B)).sub
      (measurable_closedCut (spectrumCoordinate R) A)).sub (hstrict A))
  have hstepBound (r : ResolventSpectrum R) : |endpointStep A B (r : ℝ)| ≤ 1 := by
    obtain ⟨n, hn⟩ := (diagonalMap_eventually_step R hSA A B f r).exists
    rw [← hn]
    exact diagonalMap_bounds R hSA A B f n r
  have hDCT : Tendsto (fun epsilon => ∫ r : ResolventSpectrum R,
      (primitiveWeight a b epsilon (r : ℝ) - endpointStep A B (r : ℝ)) ^ 2 ∂mu)
      (𝓝[>] 0) (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (μ := mu)
      (F := fun epsilon (r : ResolventSpectrum R) =>
        (primitiveWeight a b epsilon (r : ℝ) - endpointStep A B (r : ℝ)) ^ 2)
      (f := fun _ : ResolventSpectrum R => (0 : ℝ)) (fun _ => (4 : ℝ))
      (by
        filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
        exact ((((primitiveWeight_continuous a b hepsilon).comp continuous_subtype_val)
          .measurable.sub hstep).pow_const 2).aestronglyMeasurable)
      (by
        filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
        exact Eventually.of_forall (fun r => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have hk := primitiveWeight_bounds hab.le hepsilon (r : ℝ)
          have hka : |primitiveWeight a b epsilon (r : ℝ)| ≤ 1 := by
            simpa only [abs_of_nonneg hk.1] using hk.2
          have htriangle : |primitiveWeight a b epsilon (r : ℝ) - endpointStep A B (r : ℝ)| ≤
              |primitiveWeight a b epsilon (r : ℝ)| + |endpointStep A B (r : ℝ)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le (primitiveWeight a b epsilon (r : ℝ)) (-endpointStep A B (r : ℝ))
          have htwo : |primitiveWeight a b epsilon (r : ℝ) - endpointStep A B (r : ℝ)| ≤ 2 :=
            htriangle.trans (by linarith [hstepBound r])
          have hmul := mul_le_mul htwo htwo (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
          nlinarith [sq_abs (primitiveWeight a b epsilon (r : ℝ) - endpointStep A B (r : ℝ))]))
      (integrable_const 4)
      (Eventually.of_forall (fun r => by
        have hr := (spectrum_coordinate_mem_unitInterval R hpos hnorm r).1
        have hc : Tendsto (fun _ : ℝ => endpointStep A B (r : ℝ)) (𝓝[>] 0)
            (𝓝 (endpointStep A B (r : ℝ))) := tendsto_const_nhds
        have hl := ((primitiveWeight_tendsto_step ha hab hr).sub hc).pow 2
        simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using hl))
    simpa only [integral_zero] using hh
  have herr : (fun epsilon => ‖normalizedStoneOperator R a b epsilon f - Q f‖ ^ 2) =ᶠ[𝓝[>] 0]
      (fun epsilon => ∫ r : ResolventSpectrum R,
        (primitiveWeight a b epsilon (r : ℝ) - endpointStep A B (r : ℝ)) ^ 2 ∂mu) := by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    rw [normalizedStoneOperator, actual_integrated_imaginary_eq_CFC R hSA a b hepsilon]
    exact (cfc_endpoint_error_norm_sq R hSA A B f (primitiveMap R a b epsilon hepsilon)).trans
      (by simp only [primitiveMap_apply]; rfl)
  have hsquare := hDCT.congr' herr.symm
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsquare
  have hnormlimit : Tendsto (fun epsilon => ‖normalizedStoneOperator R a b epsilon f - Q f‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  have hstrong := tendsto_iff_norm_sub_tendsto_zero.mpr hnormlimit
  simpa only [Q, A, B, endpointOperator_eq_open_half_atoms] using hstrong

end
end ImbalancedChen.Part3.GenericStrongStone20261025a
