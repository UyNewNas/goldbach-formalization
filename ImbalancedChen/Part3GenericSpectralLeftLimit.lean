import ImbalancedChen.Part3GenericIntervalProjectionLaws
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Native strong left limits of the already constructed closed spectral
projections. Increasing projection energies make the actual vector
sequence Cauchy; no left-limit or projection is an input. The endpoint
atom is kept as P_a-P_<a and proved to be a genuine self-adjoint idempotent.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3.GenericSpectralLeftLimit20261025a
noncomputable section
open Filter MeasureTheory
open scoped Topology
open GenericIntervalProjectionLimit20261025a GenericIntervalProjectionLaws20261025a
open GenericResolventScalarMeasure20261025a ClosedIntervalSpectralRamps20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def below (a : ℝ) (n : ℕ) : ℝ := a - 1 / ((n : ℝ) + 1)

theorem below_lt (a : ℝ) (n : ℕ) : below a n < a := by
  unfold below
  have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  linarith

theorem below_mono (a : ℝ) : Monotone (below a) := by
  intro m n hmn
  have hc : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  have hr := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1) hc
  dsimp only [below]
  linarith

theorem below_tendsto (a : ℝ) : Tendsto (below a) atTop (𝓝 a) := by
  simpa only [sub_zero, below] using
    tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem nested_projection_difference {a b : ℝ} (hab : a ≤ b) (f : H) :
    ‖intervalProjection R hSA b f - intervalProjection R hSA a f‖ ^ 2 =
      ‖intervalProjection R hSA b f‖ ^ 2 - ‖intervalProjection R hSA a f‖ ^ 2 := by
  have hi : inner ℂ (intervalProjection R hSA b f) (intervalProjection R hSA a f) =
      inner ℂ (intervalProjection R hSA a f) (intervalProjection R hSA a f) := by
    calc
      _ = inner ℂ f (intervalProjection R hSA b (intervalProjection R hSA a f)) :=
        (intervalProjection_selfAdjoint R hSA b).isSymmetric _ _
      _ = inner ℂ f (intervalProjection R hSA a f) := by
        rw [intervalProjection_mul_apply, min_eq_right hab]
      _ = _ := by
        have hh := (intervalProjection_selfAdjoint R hSA a).isSymmetric f
          (intervalProjection R hSA a f)
        rw [intervalProjection_mul_apply, min_self] at hh
        exact hh.symm
  rw [norm_sub_sq, hi, inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_re]
  ring

def leftEnergy (a : ℝ) (f : H) (n : ℕ) : ℝ := ‖intervalProjection R hSA (below a n) f‖ ^ 2

theorem leftEnergy_mono (a : ℝ) (f : H) : Monotone (leftEnergy R hSA a f) := by
  intro m n hmn
  have hh := nested_projection_difference R hSA (below_mono a hmn) f
  have hn := sq_nonneg (‖intervalProjection R hSA (below a n) f -
    intervalProjection R hSA (below a m) f‖)
  dsimp only [leftEnergy]
  linarith

theorem projection_norm_le (a : ℝ) (f : H) : ‖intervalProjection R hSA a f‖ ≤ ‖f‖ :=
  intervalVector_norm_le R hSA a f

theorem leftEnergy_bddAbove (a : ℝ) (f : H) : BddAbove (Set.range (leftEnergy R hSA a f)) := by
  refine ⟨‖f‖ ^ 2, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hh := projection_norm_le R hSA (below a n) f
  dsimp only [leftEnergy]
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

theorem closed_below_cauchy (a : ℝ) (f : H) :
    CauchySeq (fun n => intervalProjection R hSA (below a n) f) := by
  have hE := (tendsto_atTop_ciSup (leftEnergy_mono R hSA a f)
    (leftEnergy_bddAbove R hSA a f)).cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hE (epsilon ^ 2) (sq_pos_of_pos hepsilon)
  refine ⟨N, ?_⟩
  intro n hn
  have hsmall : |leftEnergy R hSA a f n - leftEnergy R hSA a f N| < epsilon ^ 2 := by
    simpa only [Real.dist_eq] using hN n hn
  have hid := nested_projection_difference R hSA (below_mono a hn) f
  have hlt := (le_abs_self (leftEnergy R hSA a f n - leftEnergy R hSA a f N)).trans_lt hsmall
  rw [dist_eq_norm]
  dsimp only [leftEnergy] at hlt
  nlinarith [norm_nonneg (intervalProjection R hSA (below a n) f -
    intervalProjection R hSA (below a N) f)]

theorem exists_left_limit (a : ℝ) (f : H) :
    ∃ u : H, Tendsto (fun n => intervalProjection R hSA (below a n) f) atTop (𝓝 u) :=
  cauchySeq_tendsto_of_complete (closed_below_cauchy R hSA a f)

def leftVector (a : ℝ) (f : H) : H := (exists_left_limit R hSA a f).choose
theorem tendsto_leftVector (a : ℝ) (f : H) :
    Tendsto (fun n => intervalProjection R hSA (below a n) f) atTop (𝓝 (leftVector R hSA a f)) :=
  (exists_left_limit R hSA a f).choose_spec

theorem leftVector_add (a : ℝ) (f g : H) :
    leftVector R hSA a (f + g) = leftVector R hSA a f + leftVector R hSA a g := by
  apply tendsto_nhds_unique (tendsto_leftVector R hSA a (f + g))
  simpa only [map_add] using (tendsto_leftVector R hSA a f).add (tendsto_leftVector R hSA a g)

theorem leftVector_smul (a : ℝ) (z : ℂ) (f : H) :
    leftVector R hSA a (z • f) = z • leftVector R hSA a f := by
  apply tendsto_nhds_unique (tendsto_leftVector R hSA a (z • f))
  simpa only [map_smul] using (tendsto_leftVector R hSA a f).const_smul z

theorem leftVector_norm_le (a : ℝ) (f : H) : ‖leftVector R hSA a f‖ ≤ ‖f‖ :=
  le_of_tendsto' (tendsto_leftVector R hSA a f).norm
    (fun n => projection_norm_le R hSA (below a n) f)

def leftLinearMap (a : ℝ) : H →ₗ[ℂ] H where
  toFun := leftVector R hSA a
  map_add' := leftVector_add R hSA a
  map_smul' := leftVector_smul R hSA a

def leftProjection (a : ℝ) : H →L[ℂ] H :=
  (leftLinearMap R hSA a).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using leftVector_norm_le R hSA a f)

theorem tendsto_leftProjection (a : ℝ) (f : H) :
    Tendsto (fun n => intervalProjection R hSA (below a n) f) atTop
      (𝓝 (leftProjection R hSA a f)) := tendsto_leftVector R hSA a f

theorem leftProjection_selfAdjoint (a : ℝ) : IsSelfAdjoint (leftProjection R hSA a) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro f g
  have hl : Tendsto (fun n => inner ℂ (intervalProjection R hSA (below a n) f) g) atTop
      (𝓝 (inner ℂ (leftProjection R hSA a f) g)) :=
    (tendsto_leftProjection R hSA a f).inner tendsto_const_nhds
  have hr : Tendsto (fun n => inner ℂ f (intervalProjection R hSA (below a n) g)) atTop
      (𝓝 (inner ℂ f (leftProjection R hSA a g))) :=
    tendsto_const_nhds.inner (tendsto_leftProjection R hSA a g)
  have heq : (fun n => inner ℂ (intervalProjection R hSA (below a n) f) g) =
      (fun n => inner ℂ f (intervalProjection R hSA (below a n) g)) := by
    funext n
    exact (intervalProjection_selfAdjoint R hSA (below a n)).isSymmetric f g
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr

theorem leftProjection_norm_le (a : ℝ) : ‖leftProjection R hSA a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro f
  simpa only [one_mul] using leftVector_norm_le R hSA a f

theorem leftProjection_on_below (a : ℝ) (n : ℕ) (f : H) :
    leftProjection R hSA a (intervalProjection R hSA (below a n) f) =
      intervalProjection R hSA (below a n) f := by
  have heq : (fun m => intervalProjection R hSA (below a m)
      (intervalProjection R hSA (below a n) f)) =ᶠ[atTop]
      (fun _ => intervalProjection R hSA (below a n) f) := by
    apply eventually_atTop.mpr
    refine ⟨n, ?_⟩
    intro m hm
    rw [intervalProjection_mul_apply, min_eq_right (below_mono a hm)]
  have hc : Tendsto (fun m => intervalProjection R hSA (below a m)
      (intervalProjection R hSA (below a n) f)) atTop
      (𝓝 (intervalProjection R hSA (below a n) f)) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique (tendsto_leftProjection R hSA a _) hc

theorem leftProjection_idempotent (a : ℝ) : IsIdempotentElem (leftProjection R hSA a) := by
  change leftProjection R hSA a * leftProjection R hSA a = leftProjection R hSA a
  ext f
  have hl := (leftProjection R hSA a).continuous.tendsto
    (leftProjection R hSA a f) |>.comp (tendsto_leftProjection R hSA a f)
  have hr := tendsto_leftProjection R hSA a f
  have heq : (fun n => leftProjection R hSA a (intervalProjection R hSA (below a n) f)) =
      (fun n => intervalProjection R hSA (below a n) f) := by
    funext n
    exact leftProjection_on_below R hSA a n f
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr

theorem closed_mul_left (a : ℝ) : intervalProjection R hSA a * leftProjection R hSA a =
    leftProjection R hSA a := by
  ext f
  have hl := (intervalProjection R hSA a).continuous.tendsto
    (leftProjection R hSA a f) |>.comp (tendsto_leftProjection R hSA a f)
  have heq : (fun n => intervalProjection R hSA a (intervalProjection R hSA (below a n) f)) =
      (fun n => intervalProjection R hSA (below a n) f) := by
    funext n
    rw [intervalProjection_mul_apply, min_eq_right (below_lt a n).le]
  rw [heq] at hl
  exact tendsto_nhds_unique hl (tendsto_leftProjection R hSA a f)

theorem left_mul_closed (a : ℝ) : leftProjection R hSA a * intervalProjection R hSA a =
    leftProjection R hSA a := by
  have hs := congrArg star (closed_mul_left R hSA a)
  simpa only [star_mul, (intervalProjection_selfAdjoint R hSA a).star_eq,
    (leftProjection_selfAdjoint R hSA a).star_eq] using hs

def atomProjection (a : ℝ) : H →L[ℂ] H := intervalProjection R hSA a - leftProjection R hSA a

theorem atomProjection_selfAdjoint (a : ℝ) : IsSelfAdjoint (atomProjection R hSA a) :=
  (intervalProjection_selfAdjoint R hSA a).sub (leftProjection_selfAdjoint R hSA a)

theorem atomProjection_idempotent (a : ℝ) : IsIdempotentElem (atomProjection R hSA a) := by
  have hP : intervalProjection R hSA a * intervalProjection R hSA a = intervalProjection R hSA a :=
    intervalProjection_idempotent R hSA a
  have hL : leftProjection R hSA a * leftProjection R hSA a = leftProjection R hSA a :=
    leftProjection_idempotent R hSA a
  change (intervalProjection R hSA a - leftProjection R hSA a) *
    (intervalProjection R hSA a - leftProjection R hSA a) = _
  rw [sub_mul, mul_sub, mul_sub, hP, hL, closed_mul_left, left_mul_closed]
  abel

def strictCut (a t : ℝ) : ℝ := if t < a then 1 else 0

theorem below_cut_eventually_strict (a t : ℝ) :
    (fun n => closedCut (below a n) t) =ᶠ[atTop] (fun _ => strictCut a t) := by
  by_cases ht : t < a
  · have hh := (below_tendsto a).eventually (gt_mem_nhds ht)
    filter_upwards [hh] with n hn
    simp only [closedCut, strictCut, if_pos ht, if_pos hn.le]
  · exact Eventually.of_forall (fun n => by
      have hh : ¬ t ≤ below a n := by linarith [below_lt a n]
      simp only [closedCut, strictCut, if_neg ht, if_neg hh])

theorem cut_integral (a : ℝ) (f : H) :
    (∫ t : ResolventSpectrum R, closedCut a (t : ℝ) ∂scalarMeasure R hSA f) =
      (scalarMeasure R hSA f).real {t : ResolventSpectrum R | (t : ℝ) ≤ a} := by
  have hs : MeasurableSet {t : ResolventSpectrum R | (t : ℝ) ≤ a} :=
    measurableSet_le (spectrumCoordinate R).continuous.measurable measurable_const
  change (∫ t : ResolventSpectrum R,
    ({t : ResolventSpectrum R | (t : ℝ) ≤ a}.indicator (fun _ => (1 : ℝ))) t
      ∂scalarMeasure R hSA f) = _
  rw [integral_indicator hs]
  simp [Measure.real]

theorem strictCut_integral (a : ℝ) (f : H) :
    (∫ t : ResolventSpectrum R, strictCut a (t : ℝ) ∂scalarMeasure R hSA f) =
      (scalarMeasure R hSA f).real {t : ResolventSpectrum R | (t : ℝ) < a} := by
  have hs : MeasurableSet {t : ResolventSpectrum R | (t : ℝ) < a} :=
    measurableSet_lt (spectrumCoordinate R).continuous.measurable measurable_const
  change (∫ t : ResolventSpectrum R,
    ({t : ResolventSpectrum R | (t : ℝ) < a}.indicator (fun _ => (1 : ℝ))) t
      ∂scalarMeasure R hSA f) = _
  rw [integral_indicator hs]
  simp [Measure.real]

/-- Genuine μ-DCT identifies the native strong left limit with the OPEN
spectral interval. Thus the difference from P_a retains precisely its atom. -/
theorem leftProjection_norm_sq_measure (a : ℝ) (f : H) :
    ‖leftProjection R hSA a f‖ ^ 2 =
      (scalarMeasure R hSA f).real {t : ResolventSpectrum R | (t : ℝ) < a} := by
  have hdct := tendsto_integral_of_dominated_convergence
    (μ := scalarMeasure R hSA f)
    (F := fun n (t : ResolventSpectrum R) => closedCut (below a n) (t : ℝ))
    (f := fun t : ResolventSpectrum R => strictCut a (t : ℝ)) (fun _ => (1 : ℝ))
    (fun n => (measurable_closedCut (spectrumCoordinate R) (below a n)).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (fun t => by
      have hb := closedCut_bounds (below a n) (t : ℝ)
      simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2))
    (Eventually.of_forall (fun t =>
      tendsto_const_nhds.congr' (below_cut_eventually_strict a (t : ℝ)).symm))
  have hn : Tendsto (fun n => ∫ t : ResolventSpectrum R, closedCut (below a n) (t : ℝ)
      ∂scalarMeasure R hSA f) atTop (𝓝 (‖leftProjection R hSA a f‖ ^ 2)) := by
    convert (tendsto_leftProjection R hSA a f).norm.pow 2 using 1
    funext n
    exact (cut_integral R hSA (below a n) f).trans
      (intervalProjection_norm_sq_measure R hSA (below a n) f).symm
  have heq := tendsto_nhds_unique hn hdct
  rw [heq]
  exact strictCut_integral R hSA a f

theorem atomProjection_norm_sq_measure (a : ℝ) (f : H) :
    ‖atomProjection R hSA a f‖ ^ 2 =
      (scalarMeasure R hSA f).real {t : ResolventSpectrum R | (t : ℝ) = a} := by
  have hi : inner ℂ (intervalProjection R hSA a f) (leftProjection R hSA a f) =
      inner ℂ (leftProjection R hSA a f) (leftProjection R hSA a f) := by
    have hPL := congrArg (fun T : H →L[ℂ] H => T f) (closed_mul_left R hSA a)
    change intervalProjection R hSA a (leftProjection R hSA a f) = leftProjection R hSA a f at hPL
    have hId : leftProjection R hSA a * leftProjection R hSA a = leftProjection R hSA a :=
      leftProjection_idempotent R hSA a
    have hLL := congrArg (fun T : H →L[ℂ] H => T f) hId
    change leftProjection R hSA a (leftProjection R hSA a f) = leftProjection R hSA a f at hLL
    calc
      _ = inner ℂ f (intervalProjection R hSA a (leftProjection R hSA a f)) :=
        (intervalProjection_selfAdjoint R hSA a).isSymmetric _ _
      _ = inner ℂ f (leftProjection R hSA a f) := by rw [hPL]
      _ = _ := by
        have hh := (leftProjection_selfAdjoint R hSA a).isSymmetric f (leftProjection R hSA a f)
        rw [hLL] at hh
        exact hh.symm
  have hnorm : ‖atomProjection R hSA a f‖ ^ 2 =
      ‖intervalProjection R hSA a f‖ ^ 2 - ‖leftProjection R hSA a f‖ ^ 2 := by
    rw [atomProjection, ContinuousLinearMap.sub_apply, norm_sub_sq, hi,
      inner_self_eq_norm_sq_to_K]
    simp only [Complex.ofReal_re]
    ring
  have hle : MeasurableSet {t : ResolventSpectrum R | (t : ℝ) ≤ a} :=
    measurableSet_le (spectrumCoordinate R).continuous.measurable measurable_const
  have hlt : MeasurableSet {t : ResolventSpectrum R | (t : ℝ) < a} :=
    measurableSet_lt (spectrumCoordinate R).continuous.measurable measurable_const
  have hc : Integrable (fun t : ResolventSpectrum R => closedCut a (t : ℝ)) (scalarMeasure R hSA f) :=
    (integrable_const (1 : ℝ)).indicator hle
  have ho : Integrable (fun t : ResolventSpectrum R => strictCut a (t : ℝ)) (scalarMeasure R hSA f) :=
    (integrable_const (1 : ℝ)).indicator hlt
  rw [hnorm, intervalProjection_norm_sq_measure, leftProjection_norm_sq_measure,
    ← cut_integral R hSA a f, ← strictCut_integral R hSA a f, ← integral_sub hc ho]
  have hpoint (t : ResolventSpectrum R) : closedCut a (t : ℝ) - strictCut a (t : ℝ) =
      ({t : ResolventSpectrum R | (t : ℝ) = a}.indicator (fun _ => (1 : ℝ))) t := by
    rcases lt_trichotomy (t : ℝ) a with ht | ht | ht
    · simp [closedCut, strictCut, ht, ht.le, ht.ne]
    · simp [closedCut, strictCut, ht]
    · simp [closedCut, strictCut, not_le_of_gt ht, not_lt_of_ge ht.le, ht.ne']
  simp_rw [hpoint]
  rw [integral_indicator (measurableSet_eq (spectrumCoordinate R).continuous.measurable measurable_const)]
  simp [Measure.real]

end
end ImbalancedChen.Part3.GenericSpectralLeftLimit20261025a
