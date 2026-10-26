import ImbalancedChen.Part3CuspPhysicalWeakTailModes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual compact-height exhaustion in the TWO physical graph norms.
One measurable height cutoff acts on both coordinates, and its error
converges to zero in Haar×dy/y² for the value and Haar×dy for the derivative.
The generic L² assertion is proved by dominated convergence of squared
errors. No compact-support approximation or graph density is assumed.
This is a norm approximation primitive; it does not by itself assert that
the cutoffs satisfy a smooth weak-testing definition.
-/
namespace ImbalancedChen.Part3.CuspPhysicalHeightExhaustion20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a

attribute [local instance] Measure.Subtype.measureSpace

section GeneralL2
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def indicatorVector (s : Set α) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp u).indicator hs).toLp (s.indicator u)

theorem indicatorVector_ae (s : Set α) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    (indicatorVector s hs u : α → ℂ) =ᵐ[μ] s.indicator u :=
  ((Lp.memLp u).indicator hs).coeFn_toLp

private theorem norm_sq_integral (u : Lp ℂ 2 μ) :
    ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  have h := L2.inner_def (𝕜 := ℂ) u u
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  rw [integral_ofReal] at h
  exact Complex.ofReal_injective h

theorem indicatorVector_error_sq (s : Set α) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    ‖indicatorVector s hs u - u‖^2 = ∫ x, ‖s.indicator u x - u x‖^2 ∂μ := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (indicatorVector s hs u) u,
    indicatorVector_ae s hs u] with x hsub hind
  simp only [hsub, Pi.sub_apply, hind]

/-- Native L² cutoff convergence from eventual membership. The bound is
exactly ‖u‖², since an indicator error is either zero or minus u. -/
theorem indicatorVector_tendsto (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n))
    (hmem : ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, x ∈ s n) (u : Lp ℂ 2 μ) :
    Tendsto (fun n => indicatorVector (s n) (hs n) u) atTop (𝓝 u) := by
  have hsq : Integrable (fun x => ‖u x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hconv : Tendsto (fun n => ∫ x, ‖(s n).indicator u x - u x‖^2 ∂μ)
      atTop (𝓝 0) := by
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ‖(s n).indicator u x - u x‖^2)
        atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hmem] with x hx
      apply (tendsto_congr' (hx.mono fun n hn => by simp [hn])).mpr
      exact tendsto_const_nhds
    have h := tendsto_integral_of_dominated_convergence (fun x => ‖u x‖^2)
      (fun n => (((Lp.aestronglyMeasurable u).indicator (hs n)).sub
        (Lp.aestronglyMeasurable u)).norm.pow_const 2) hsq
      (fun n => Eventually.of_forall fun x => by
        by_cases hx : x ∈ s n <;>
          simp [hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
      (f := fun _ => (0 : ℝ)) hlim
    simpa only [integral_zero] using h
  have hnormsq : Tendsto (fun n => ‖indicatorVector (s n) (hs n) u - u‖^2)
      atTop (𝓝 0) := by
    simpa only [indicatorVector_error_sq] using hconv
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hnormsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

end GeneralL2

def heightBand (a : ℝ) (n : ℕ) : Set PositiveHeight :=
  {y | a ≤ (y : ℝ) ∧ (y : ℝ) ≤ a + (n : ℝ) + 1}

def cylinderHeightBand (a : ℝ) (n : ℕ) : Set CuspCylinder :=
  univ ×ˢ heightBand a n

theorem heightBand_measurable (a : ℝ) (n : ℕ) : MeasurableSet (heightBand a n) :=
  ((isClosed_le continuous_const continuous_subtype_val).inter
    (isClosed_le continuous_subtype_val continuous_const)).measurableSet

theorem cylinderHeightBand_measurable (a : ℝ) (n : ℕ) :
    MeasurableSet (cylinderHeightBand a n) :=
  MeasurableSet.univ.prod (heightBand_measurable a n)

theorem heightBand_isCompact {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IsCompact (heightBand a n) := by
  have hb : 0 < a + (n : ℝ) + 1 := by positivity
  exact positiveHeight_Icc_isCompact (⟨a, ha⟩ : PositiveHeight)
    (⟨a + (n : ℝ) + 1, hb⟩ : PositiveHeight)

theorem cylinderHeightBand_isCompact {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IsCompact (cylinderHeightBand a n) :=
  isCompact_univ.prod (heightBand_isCompact ha n)

theorem eventually_mem_heightBand (a : ℝ) (y : PositiveHeight) (hy : a ≤ (y : ℝ)) :
    ∀ᶠ n : ℕ in atTop, y ∈ heightBand a n := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((y : ℝ) - a)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact ⟨hy, by linarith⟩

theorem functionMeasure_eventually_mem_band (a : ℝ) :
    ∀ᵐ z ∂functionMeasure a, ∀ᶠ n : ℕ in atTop, z ∈ cylinderHeightBand a n := by
  filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
  exact (eventually_mem_heightBand a z.2 (le_of_lt hz.2)).mono fun n hn => ⟨mem_univ _, hn⟩

theorem derivativeMeasure_eventually_mem_band (a : ℝ) :
    ∀ᵐ z ∂derivativeMeasure a, ∀ᶠ n : ℕ in atTop, z ∈ cylinderHeightBand a n := by
  filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
  exact (eventually_mem_heightBand a z.2 (le_of_lt hz.2)).mono fun n hn => ⟨mem_univ _, hn⟩

def physicalHeightCutoff (a : ℝ) (n : ℕ)
    (p : FunctionL2 a × DerivativeL2 a) : FunctionL2 a × DerivativeL2 a :=
  (indicatorVector (cylinderHeightBand a n) (cylinderHeightBand_measurable a n) p.1,
   indicatorVector (cylinderHeightBand a n) (cylinderHeightBand_measurable a n) p.2)

/-- One actual compact-height exhaustion works in both physical norms.
No norm-comparison between raw and weighted measures is used here. -/
theorem physicalHeightCutoff_tendsto (a : ℝ) (p : FunctionL2 a × DerivativeL2 a) :
    Tendsto (fun n => physicalHeightCutoff a n p) atTop (𝓝 p) :=
  (indicatorVector_tendsto (cylinderHeightBand a) (cylinderHeightBand_measurable a)
    (functionMeasure_eventually_mem_band a) p.1).prodMk_nhds
  (indicatorVector_tendsto (cylinderHeightBand a) (cylinderHeightBand_measurable a)
    (derivativeMeasure_eventually_mem_band a) p.2)

end
end ImbalancedChen.Part3.CuspPhysicalHeightExhaustion20261026b
