import ImbalancedChen.Part3Gamma0TruncatedChartCutoff
import ImbalancedChen.Part3PositiveRectangleNativeHyperbolicL2
import ImbalancedChen.Part3Gamma0PositiveRectangleRellichCharts

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Fixed-truncation compactness on the ACTUAL Gamma0 quotient. The local
native L2 tuple consists of the actual inverse-class charts multiplied
by the explicitly constructed cutoff. A proved reconstruction distance
bound transfers its finite energy-ball compactness to the actual quotient
core. The primitive bound is exactly the localized mass plus both actual
physical derivative energies, not compactness or a reconstruction premise.

The uniform derivation of this local bound from the quotient form norm is
separate. The all-cusps tail and global compact embedding remain OPEN.
-/

namespace ImbalancedChen.Part3.Gamma0FixedCoreRellich20261026b
noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped UpperHalfPlane BigOperators ENNReal
open Gamma0FiniteChartReconstruction20261026b
open Gamma0QuotientChartReconstruction20261026b
open Gamma0ChartCoordinateErrorBudget20261026b
open Gamma0TruncatedChartCutoff20261026b
open Gamma0QuotientCellPushforward20261025a
open PositiveRectangleAffineNormalization20261026b
open PositiveRectanglePhysicalRellich20261026b
open PositiveRectangleNativeHyperbolicL220261026b
open Gamma0PositiveRectangleRellichCharts20261026b
open Gamma0LocalFourierTailCharts20261026a
open Gamma0CompactTensorPoincareC2Core20261025a
open ActualGamma0MaassDescent20261025a MaassWeakOperatorCore20261024zz

structure SmoothQuotient (N : ℕ) [NeZero N] where
  function : Gamma0OrbitSpace N → ℂ
  measurable : Measurable function
  memLp : MemLp function 2 (carrierPushforward N)
  smooth : ContDiffOn ℝ 2 (extendUpper (function ∘ orbitProjection N)) positiveChart

def smoothPullback (N : ℕ) [NeZero N] (F : SmoothQuotient N) : SmoothFunction :=
  ⟨F.function ∘ orbitProjection N, F.smooth⟩

def actualSeed (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (F : SmoothQuotient N) (i : ChartIndex N) :
    RectangleSeed (cutoffRectangle Y hY) (cutoffMargin Y) :=
  classSeed N (cutoffRectangle Y hY) (cutoffMargin_pos hY).le
    (upperCutoff Y hY) (upperCutoff_C2 Y hY) (upperCutoff_support_region Y hY)
    (smoothPullback N F) (chartClass N i)

def nativeTuple (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) (F : SmoothQuotient N) :
    ChartIndex N → Lp ℂ 2 (volume : Measure UpperHalfPlane) :=
  fun i => nativeL2 (cutoffMargin_pos hY).le (actualSeed N Y hY F i)

def localEnergyFamily (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) (A : ℝ) :
    Set (SmoothQuotient N) :=
  {F | ∀ i : ChartIndex N, actualSeed N Y hY F i ∈
    h1Ball (cutoffRectangle Y hY) (cutoffMargin Y) A}

def coreL2 (N : ℕ) [NeZero N] (Y : ℝ) (F : SmoothQuotient N) :
    Lp ℂ 2 (carrierPushforward N) :=
  (F.memLp.indicator (quotientCore_measurable N Y)).toLp
    ((quotientCore N Y).indicator F.function)

theorem nativeTuple_totallyBounded (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (A : ℝ) (hA : 0 ≤ A) :
    TotallyBounded (nativeTuple N Y hY '' localEnergyFamily N Y hY A) := by
  have hc : IsCompact {v : ChartIndex N → Lp ℂ 2 (volume : Measure UpperHalfPlane) |
      ∀ i, v i ∈ closure (nativeL2 (cutoffMargin_pos hY).le ''
        h1Ball (cutoffRectangle Y hY) (cutoffMargin Y) A)} :=
    isCompact_pi_infinite (fun _ =>
      (native_h1Ball_totallyBounded (cutoffRectangle Y hY) (cutoffMargin_pos hY) A hA).
        closure.isCompact isClosed_closure.isComplete)
  apply hc.totallyBounded.subset
  rintro v ⟨F, hF, rfl⟩ i
  exact subset_closure ⟨actualSeed N Y hY F i, hF i, rfl⟩

theorem actualSeed_nativeFunction (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (F : SmoothQuotient N) (i : ChartIndex N) (z : UpperHalfPlane) :
    nativeFunction (actualSeed N Y hY F i) z =
      localizedClassChart N (F.function ∘ orbitProjection N) (upperCutoff Y hY)
        (chartClass N i) z :=
  extendUpper_pair _ z

theorem actualSeed_on_cell (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (F : SmoothQuotient N) (i : ChartIndex N) {z : UpperHalfPlane}
    (hz : z ∈ truncatedModularCell Y) :
    nativeFunction (actualSeed N Y hY F i) z =
      F.function (orbitProjection N (chartMatrix N i • z)) := by
  rw [actualSeed_nativeFunction, localized_chart_eq_pullback_on_cell N Y hY _ i hz]
  rfl

theorem lp_ofReal_norm_square {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : Lp ℂ 2 μ) : ENNReal.ofReal (‖u‖^2) = ∫⁻ x, ENNReal.ofReal (‖u x‖^2) ∂μ := by
  have hint : Integrable (fun x => ‖u x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm u.memLp.aestronglyMeasurable).mp u.memLp
  have hsquare : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
      ← integral_re (L2.integrable_inner u u)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_re])
  rw [hsquare]
  exact ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun x => sq_nonneg _))

theorem core_distance_square_lintegral (N : ℕ) [NeZero N] (Y : ℝ)
    (F G : SmoothQuotient N) :
    ENNReal.ofReal (‖coreL2 N Y F - coreL2 N Y G‖^2) =
      ∫⁻ q in quotientCore N Y, ENNReal.ofReal (‖F.function q-G.function q‖^2)
        ∂carrierPushforward N := by
  rw [lp_ofReal_norm_square]
  rw [← lintegral_indicator (quotientCore_measurable N Y)]
  apply lintegral_congr_ae
  filter_upwards [(F.memLp.indicator (quotientCore_measurable N Y)).coeFn_toLp,
    (G.memLp.indicator (quotientCore_measurable N Y)).coeFn_toLp,
    Lp.coeFn_sub (coreL2 N Y F) (coreL2 N Y G)] with q hF hG hsub
  rw [hsub, hF, hG]
  by_cases hq : q ∈ quotientCore N Y <;> simp [hq]

theorem nativeTuple_distance_square_lintegral (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (F G : SmoothQuotient N) (i : ChartIndex N) :
    ENNReal.ofReal (‖nativeTuple N Y hY F i-nativeTuple N Y hY G i‖^2) =
      ∫⁻ z : UpperHalfPlane, ENNReal.ofReal
        (‖nativeFunction (actualSeed N Y hY F i) z-
          nativeFunction (actualSeed N Y hY G i) z‖^2) := by
  rw [lp_ofReal_norm_square]
  apply lintegral_congr_ae
  filter_upwards [(nativeFunction_memLp (cutoffMargin_pos hY).le
      (actualSeed N Y hY F i)).coeFn_toLp,
    (nativeFunction_memLp (cutoffMargin_pos hY).le
      (actualSeed N Y hY G i)).coeFn_toLp,
    Lp.coeFn_sub (nativeTuple N Y hY F i) (nativeTuple N Y hY G i)] with z hF hG hsub
  rw [hsub, hF, hG]

/-- Finite actual chart reconstruction has a proved norm bound on the
genuine quotient. The right side is the native tuple norm, already proved
equal to the physical weighted chart norm. -/
theorem core_distance_square_le_sum (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (F G : SmoothQuotient N) :
    ‖coreL2 N Y F-coreL2 N Y G‖^2 ≤
      ∑ i : ChartIndex N, ‖nativeTuple N Y hY F i-nativeTuple N Y hY G i‖^2 := by
  have hzero : quotientReconstruct N Y (fun _ _ => (0 : ℂ)) = 0 := by
    simpa using quotientReconstruct_actual_pullbacks N Y
      (fun _ => (0 : ℂ))
  have h := quotient_core_error_le_actual_chart_errors N Y
    (F.function-G.function) (F.measurable.sub G.measurable)
    (fun _ _ => (0 : ℂ)) (fun _ => measurable_const)
  simp only [hzero, Pi.zero_apply, sub_zero, Pi.sub_apply] at h
  have hlocal : (∑ i : ChartIndex N, ∫⁻ z in truncatedModularCell Y,
      ENNReal.ofReal
        (‖F.function (orbitProjection N (chartMatrix N i • z))-
          G.function (orbitProjection N (chartMatrix N i • z))‖^2)) ≤
      ∑ i : ChartIndex N,
        ENNReal.ofReal (‖nativeTuple N Y hY F i-nativeTuple N Y hY G i‖^2) := by
    apply Finset.sum_le_sum
    intro i _
    rw [nativeTuple_distance_square_lintegral]
    calc
      _ = ∫⁻ z in truncatedModularCell Y, ENNReal.ofReal
          (‖nativeFunction (actualSeed N Y hY F i) z-
            nativeFunction (actualSeed N Y hY G i) z‖^2) := by
        apply setLIntegral_congr_fun (truncatedModularCell_measurable Y)
        intro z hz
        rw [actualSeed_on_cell N Y hY F i hz, actualSeed_on_cell N Y hY G i hz]
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have hnn : 0 ≤ ∑ i : ChartIndex N,
      ‖nativeTuple N Y hY F i-nativeTuple N Y hY G i‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hfinal := h.trans hlocal
  rw [← core_distance_square_lintegral] at hfinal
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at hfinal
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hfinal

theorem core_distance_le_tuple_distance (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (F G : SmoothQuotient N) :
    dist (coreL2 N Y F) (coreL2 N Y G) ≤
      ((Fintype.card (ChartIndex N) : ℝ)+1) *
        dist (nativeTuple N Y hY F) (nativeTuple N Y hY G) := by
  let d := dist (nativeTuple N Y hY F) (nativeTuple N Y hY G)
  let n : ℝ := Fintype.card (ChartIndex N)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hd : 0 ≤ d := dist_nonneg
  have hsum : (∑ i : ChartIndex N,
      ‖nativeTuple N Y hY F i-nativeTuple N Y hY G i‖^2) ≤ n*d^2 := by
    calc
      _ ≤ ∑ _i : ChartIndex N, d^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (by
          simpa only [dist_eq_norm] using dist_le_pi_dist
            (nativeTuple N Y hY F) (nativeTuple N Y hY G) i) 2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, n]
  have hs := (core_distance_square_le_sum N Y hY F G).trans hsum
  have hnc : n ≤ (n+1)^2 := by nlinarith
  have hs' := hs.trans (mul_le_mul_of_nonneg_right hnc (sq_nonneg d))
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg (by linarith : 0 ≤ n+1) hd)).mp
  simpa only [dist_eq_norm, mul_pow] using hs'

/-- Actual fixed-truncation quotient L2 total boundedness from an explicit
bound on the actual localized mass and both physical derivatives. -/
theorem fixed_core_energy_family_totallyBounded (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (A : ℝ) (hA : 0 ≤ A) :
    TotallyBounded (coreL2 N Y '' localEnergyFamily N Y hY A) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  let c : ℝ := (Fintype.card (ChartIndex N) : ℝ)+1
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨T, hTsub, hTfin, hTcover⟩ := Metric.finite_approx_of_totallyBounded
    (nativeTuple_totallyBounded N Y hY A hA) (ε/c) (div_pos hε hc)
  letI : Fintype T := hTfin.fintype
  let pick : T → SmoothQuotient N := fun v => Classical.choose (hTsub v.2)
  have hpick (v : T) : pick v ∈ localEnergyFamily N Y hY A ∧
      nativeTuple N Y hY (pick v) = v := Classical.choose_spec (hTsub v.2)
  refine ⟨range (fun v : T => coreL2 N Y (pick v)), finite_range _, ?_⟩
  rintro u ⟨F, hF, rfl⟩
  obtain ⟨v, hv, hdist⟩ := mem_iUnion₂.mp (hTcover ⟨F, hF, rfl⟩)
  refine mem_iUnion₂.mpr ⟨coreL2 N Y (pick ⟨v,hv⟩), ⟨⟨v,hv⟩, rfl⟩, ?_⟩
  rw [mem_ball]
  apply (core_distance_le_tuple_distance N Y hY F (pick ⟨v,hv⟩)).trans_lt
  rw [(hpick ⟨v,hv⟩).2]
  calc
    c * dist (nativeTuple N Y hY F) v < c * (ε/c) :=
      mul_lt_mul_of_pos_left hdist hc
    _ = ε := by field_simp [hc.ne']

end
end ImbalancedChen.Part3.Gamma0FixedCoreRellich20261026b
