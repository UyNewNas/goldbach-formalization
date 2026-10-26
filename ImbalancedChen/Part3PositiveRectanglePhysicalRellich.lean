import ImbalancedChen.Part3PositiveRectangleAffineNormalization

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
The previously proved unit-rectangle Rellich theorem is transported to
every physical positive-height rectangle with its actual affine constants.
The weighted physical L2 vector is multiplication by 1/y on the support;
its compact extension below the rectangle supplies a genuine L2 object. -/

namespace ImbalancedChen.Part3.PositiveRectanglePhysicalRellich20261026b
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
open CompactRectanglePhysicalRellich20261026a
open PositiveRectangleAffineNormalization20261026b

def difference {R : Rectangle} {δ : ℝ} (s t : RectangleSeed R δ) : RectangleSeed R δ :=
  ⟨s.function - t.function, s.smooth.sub t.smooth, by
    intro p hp
    by_contra hn
    have hs : s.function p = 0 := by by_contra hz; exact hn (s.support_subset hz)
    have ht : t.function p = 0 := by by_contra hz; exact hn (t.support_subset hz)
    exact hp (by simp only [Pi.sub_apply, hs, ht, sub_self])⟩

theorem physical_difference {R : Rectangle} {δ : ℝ} (s t : RectangleSeed R δ) :
    physical (difference s t) = physical s - physical t := by
  apply Lp.ext
  filter_upwards [(s.smooth.continuous.memLp_of_hasCompactSupport
    (compact_of_support R s.support_subset)).coeFn_toLp,
    (t.smooth.continuous.memLp_of_hasCompactSupport
      (compact_of_support R t.support_subset)).coeFn_toLp,
    ((difference s t).smooth.continuous.memLp_of_hasCompactSupport
      (compact_of_support R (difference s t).support_subset)).coeFn_toLp,
    Lp.coeFn_sub (physical s) (physical t)] with p hs ht hd hsub
  rw [hd, hsub, hs, ht]
  rfl

theorem normalized_difference {R : Rectangle} {δ : ℝ} (s t : RectangleSeed R δ) :
    physicalSeed (normalized (difference s t)) =
      physicalSeed (normalized s) - physicalSeed (normalized t) := by
  apply Lp.ext
  filter_upwards [((normalized s).smooth.continuous.memLp_of_hasCompactSupport
    (seed_compactSupport (normalized s))).coeFn_toLp,
    ((normalized t).smooth.continuous.memLp_of_hasCompactSupport
      (seed_compactSupport (normalized t))).coeFn_toLp,
    ((normalized (difference s t)).smooth.continuous.memLp_of_hasCompactSupport
      (seed_compactSupport (normalized (difference s t)))).coeFn_toLp,
    Lp.coeFn_sub (physicalSeed (normalized s)) (physicalSeed (normalized t))]
      with p hs ht hd hsub
  rw [hd, hsub, hs, ht]
  rfl

theorem affine_distance {R : Rectangle} {δ : ℝ} (s t : RectangleSeed R δ) :
    dist (physical s) (physical t) = Real.sqrt (R.width * R.height) *
      dist (physicalSeed (normalized s)) (physicalSeed (normalized t)) := by
  have hj : 0 < R.width * R.height := mul_pos R.width_pos R.height_pos
  have he := normalized_square (difference s t)
  rw [physical_difference, normalized_difference] at he
  have hsq : ‖physical s - physical t‖^2 =
      (R.width * R.height) * ‖physicalSeed (normalized s) - physicalSeed (normalized t)‖^2 := by
    rw [he]
    field_simp [R.width_pos.ne', R.height_pos.ne']
  simp only [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hj.le]
  exact hsq

def energy {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) : ℝ :=
  directionalEnergy s 0 + directionalEnergy s 1

theorem directionalEnergy_nonneg {R : Rectangle} {δ : ℝ}
    (s : RectangleSeed R δ) (j : Fin 2) : 0 ≤ directionalEnergy s j :=
  integral_nonneg (fun p => sq_nonneg _)

def affineH1Constant (R : Rectangle) : ℝ :=
  (R.width * R.height)⁻¹ + R.width / R.height + R.height / R.width

theorem affineH1Constant_pos (R : Rectangle) : 0 < affineH1Constant R := by
  unfold affineH1Constant
  have hw := R.width_pos
  have hh := R.height_pos
  positivity

def h1Ball (R : Rectangle) (δ A : ℝ) : Set (RectangleSeed R δ) :=
  {s | ‖physical s‖^2 + energy s ≤ A}

theorem normalized_h1_bound {R : Rectangle} {δ A : ℝ} (s : RectangleSeed R δ)
    (hs : s ∈ h1Ball R δ A) :
    normalized s ∈ physicalH1Ball δ (affineH1Constant R * A) := by
  change ‖physicalSeed (normalized s)‖^2 + physicalEnergy (normalized s) ≤ _
  rw [normalized_square, normalized_energy]
  have hn := sq_nonneg ‖physical s‖
  have hx := directionalEnergy_nonneg s 0
  have hy := directionalEnergy_nonneg s 1
  have ha : 0 ≤ (R.width * R.height)⁻¹ := inv_nonneg.mpr (mul_pos R.width_pos R.height_pos).le
  have hb : 0 ≤ R.width / R.height := div_nonneg R.width_pos.le R.height_pos.le
  have hc : 0 ≤ R.height / R.width := div_nonneg R.height_pos.le R.width_pos.le
  have h1 := mul_nonneg (add_nonneg hb hc) hn
  have h2 := mul_nonneg (add_nonneg ha hc) hx
  have h3 := mul_nonneg (add_nonneg ha hb) hy
  have h4 := mul_le_mul_of_nonneg_left hs (affineH1Constant_pos R).le
  dsimp [h1Ball, energy, affineH1Constant] at hs h4 ⊢
  nlinarith

theorem normalized_family_totallyBounded (R : Rectangle) {δ : ℝ} (hδ : 0 < δ)
    (A : ℝ) (hA : 0 ≤ A) :
    TotallyBounded ((fun s : RectangleSeed R δ => physicalSeed (normalized s)) ''
      h1Ball R δ A) := by
  apply (physicalH1Ball_totallyBounded hδ (affineH1Constant R * A)
    (mul_nonneg (affineH1Constant_pos R).le hA)).subset
  rintro u ⟨s, hs, rfl⟩
  exact ⟨normalized s, normalized_h1_bound s hs, rfl⟩

/-- Genuine arbitrary-rectangle physical Rellich, obtained by transporting
the proved finite-box theorem through the exact affine distance identity. -/
theorem physical_h1Ball_totallyBounded (R : Rectangle) {δ : ℝ} (hδ : 0 < δ)
    (A : ℝ) (hA : 0 ≤ A) : TotallyBounded (physical '' h1Ball R δ A) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  let c := Real.sqrt (R.width * R.height)
  have hc : 0 < c := Real.sqrt_pos.mpr (mul_pos R.width_pos R.height_pos)
  obtain ⟨T, hTsub, hTfin, hTcover⟩ := Metric.finite_approx_of_totallyBounded
    (normalized_family_totallyBounded R hδ A hA) (ε/c) (div_pos hε hc)
  letI : Fintype T := hTfin.fintype
  let pick : T → RectangleSeed R δ := fun v => Classical.choose (hTsub v.2)
  have hpick (v : T) : pick v ∈ h1Ball R δ A ∧ physicalSeed (normalized (pick v)) = v :=
    Classical.choose_spec (hTsub v.2)
  refine ⟨range (fun v : T => physical (pick v)), finite_range _, ?_⟩
  rintro u ⟨s, hs, rfl⟩
  obtain ⟨v, hv, hdist⟩ := Set.mem_iUnion₂.mp (hTcover ⟨s, hs, rfl⟩)
  refine Set.mem_iUnion₂.mpr ⟨physical (pick ⟨v,hv⟩), ⟨⟨v,hv⟩, rfl⟩, ?_⟩
  rw [mem_ball, affine_distance, (hpick ⟨v,hv⟩).2]
  change c * dist (physicalSeed (normalized s)) v < ε
  calc
    c * dist (physicalSeed (normalized s)) v < c * (ε/c) :=
      mul_lt_mul_of_pos_left hdist hc
    _ = ε := by field_simp [hc.ne']

def weight (R : Rectangle) (p : Plane) : ℝ := (max R.bottom p.2)⁻¹

theorem weight_continuous (R : Rectangle) : Continuous (weight R) :=
  (continuous_const.max continuous_snd).inv₀ (fun p =>
    ne_of_gt (R.bottom_pos.trans_le (le_max_left _ _)))

theorem weight_nonneg (R : Rectangle) (p : Plane) : 0 ≤ weight R p := by
  exact inv_nonneg.mpr (R.bottom_pos.le.trans (le_max_left _ _))

theorem weight_le (R : Rectangle) (p : Plane) : weight R p ≤ R.bottom⁻¹ := by
  exact one_div_le_one_div_of_le R.bottom_pos (le_max_left _ _)

def weightedFunction {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) (p : Plane) : ℂ :=
  (weight R p : ℂ) * s.function p

theorem weightedFunction_continuous {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) :
    Continuous (weightedFunction s) :=
  (Complex.continuous_ofReal.comp (weight_continuous R)).mul s.smooth.continuous

theorem weightedFunction_compact {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) :
    HasCompactSupport (weightedFunction s) := (compact_of_support R s.support_subset).mul_left

def weightedPhysical {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) : PhysicalL2 :=
  ((weightedFunction_continuous s).memLp_of_hasCompactSupport
    (weightedFunction_compact s)).toLp (weightedFunction s)

theorem weightedPhysical_square {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) :
    ‖weightedPhysical s‖^2 = ∫ p : Plane, (weight R p)^2 * ‖s.function p‖^2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (weightedPhysical s) (weightedPhysical s))]
  apply integral_congr_ae
  filter_upwards [((weightedFunction_continuous s).memLp_of_hasCompactSupport
    (weightedFunction_compact s)).coeFn_toLp] with p hp
  simp only [hp, inner_self_eq_norm_sq_to_K, Complex.ofReal_re, weightedFunction,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The vector is literally the dy dx / y² norm on the supported physical
function; the harmless extension of 1/y below the rectangle disappears. -/
theorem weightedPhysical_hyperbolic_square {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s : RectangleSeed R δ) :
    ‖weightedPhysical s‖^2 = ∫ p : Plane, (p.2⁻¹)^2 * ‖s.function p‖^2 := by
  rw [weightedPhysical_square]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    by_cases hp : s.function p = 0
    · simp [hp]
    · have hy := region_height hδ (s.support_subset hp)
      simp only [weight, max_eq_right hy.1])

theorem weighted_norm_le {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) :
    ‖weightedPhysical s‖ ≤ R.bottom⁻¹ * ‖physical s‖ := by
  have hi : Integrable (fun p : Plane => (weight R p)^2 * ‖s.function p‖^2) := by
    have h := ((weightedFunction_continuous s).norm.pow 2).integrable_of_hasCompactSupport
      ((weightedFunction_compact s).norm.comp_left (g := fun t : ℝ => t^2) (by simp))
    simpa only [weightedFunction, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs] using h
  have hj : Integrable (fun p : Plane => (R.bottom⁻¹)^2 * ‖s.function p‖^2) :=
    ((s.smooth.continuous.norm.pow 2).integrable_of_hasCompactSupport
      ((compact_of_support R s.support_subset).norm.comp_left
        (g := fun t : ℝ => t^2) (by simp))).const_mul _
  have hle := integral_mono hi hj (fun p =>
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (weight_nonneg R p) (weight_le R p) 2) (sq_nonneg _))
  rw [← weightedPhysical_square, integral_const_mul, ← physical_square] at hle
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr R.bottom_pos.le)
    (norm_nonneg _))).mp
  simpa only [mul_pow] using hle

/-- Both physical weighted-mass comparison constants are explicit. -/
theorem weighted_square_bounds {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s : RectangleSeed R δ) :
    ((R.bottom + R.height)⁻¹)^2 * ‖physical s‖^2 ≤ ‖weightedPhysical s‖^2 ∧
      ‖weightedPhysical s‖^2 ≤ (R.bottom⁻¹)^2 * ‖physical s‖^2 := by
  have hi : Integrable (fun p : Plane => (weight R p)^2 * ‖s.function p‖^2) := by
    have h := ((weightedFunction_continuous s).norm.pow 2).integrable_of_hasCompactSupport
      ((weightedFunction_compact s).norm.comp_left (g := fun t : ℝ => t^2) (by simp))
    simpa only [weightedFunction, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs] using h
  have hj : Integrable (fun p : Plane => ((R.bottom + R.height)⁻¹)^2 * ‖s.function p‖^2) :=
    ((s.smooth.continuous.norm.pow 2).integrable_of_hasCompactSupport
      ((compact_of_support R s.support_subset).norm.comp_left
        (g := fun t : ℝ => t^2) (by simp))).const_mul _
  constructor
  · have hle := integral_mono hj hi (fun p => by
      by_cases hp : s.function p = 0
      · simp [hp]
      · have hy := region_height hδ (s.support_subset hp)
        have hb := (hyperbolic_density_bounds R hy).1
        simpa only [weight, max_eq_right hy.1] using
          mul_le_mul_of_nonneg_right hb (sq_nonneg ‖s.function p‖))
    rwa [integral_const_mul, ← physical_square, ← weightedPhysical_square] at hle
  · have hle := pow_le_pow_left₀ (norm_nonneg (weightedPhysical s)) (weighted_norm_le s) 2
    simpa only [mul_pow] using hle

theorem weighted_difference {R : Rectangle} {δ : ℝ} (s t : RectangleSeed R δ) :
    weightedPhysical (difference s t) = weightedPhysical s - weightedPhysical t := by
  apply Lp.ext
  filter_upwards [((weightedFunction_continuous s).memLp_of_hasCompactSupport
    (weightedFunction_compact s)).coeFn_toLp,
    ((weightedFunction_continuous t).memLp_of_hasCompactSupport
      (weightedFunction_compact t)).coeFn_toLp,
    ((weightedFunction_continuous (difference s t)).memLp_of_hasCompactSupport
      (weightedFunction_compact (difference s t))).coeFn_toLp,
    Lp.coeFn_sub (weightedPhysical s) (weightedPhysical t)] with p hs ht hd hsub
  rw [hd, hsub, hs, ht]
  simp only [weightedFunction, difference, Pi.sub_apply, mul_sub]

theorem weighted_distance_le {R : Rectangle} {δ : ℝ} (s t : RectangleSeed R δ) :
    dist (weightedPhysical s) (weightedPhysical t) ≤
      R.bottom⁻¹ * dist (physical s) (physical t) := by
  simpa only [dist_eq_norm, physical_difference, weighted_difference] using
    weighted_norm_le (difference s t)

/-- Actual weighted physical L2 total boundedness. The lower height
constant is retained in the finite covering radius. -/
theorem weighted_h1Ball_totallyBounded (R : Rectangle) {δ : ℝ} (hδ : 0 < δ)
    (A : ℝ) (hA : 0 ≤ A) : TotallyBounded (weightedPhysical '' h1Ball R δ A) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨T, hTsub, hTfin, hTcover⟩ := Metric.finite_approx_of_totallyBounded
    (physical_h1Ball_totallyBounded R hδ A hA) (R.bottom * ε)
    (mul_pos R.bottom_pos hε)
  letI : Fintype T := hTfin.fintype
  let pick : T → RectangleSeed R δ := fun v => Classical.choose (hTsub v.2)
  have hpick (v : T) : pick v ∈ h1Ball R δ A ∧ physical (pick v) = v :=
    Classical.choose_spec (hTsub v.2)
  refine ⟨range (fun v : T => weightedPhysical (pick v)), finite_range _, ?_⟩
  rintro u ⟨s, hs, rfl⟩
  obtain ⟨v, hv, hdist⟩ := Set.mem_iUnion₂.mp (hTcover ⟨s, hs, rfl⟩)
  refine Set.mem_iUnion₂.mpr ⟨weightedPhysical (pick ⟨v,hv⟩), ⟨⟨v,hv⟩, rfl⟩, ?_⟩
  rw [mem_ball]
  apply (weighted_distance_le s (pick ⟨v,hv⟩)).trans_lt
  rw [(hpick ⟨v,hv⟩).2]
  calc
    R.bottom⁻¹ * dist (physical s) v < R.bottom⁻¹ * (R.bottom * ε) :=
      mul_lt_mul_of_pos_left hdist (inv_pos.mpr R.bottom_pos)
    _ = ε := by field_simp [R.bottom_pos.ne']

theorem weighted_h1Ball_compact_closure (R : Rectangle) {δ : ℝ} (hδ : 0 < δ)
    (A : ℝ) (hA : 0 ≤ A) :
    IsCompact (closure (weightedPhysical '' h1Ball R δ A)) :=
  (weighted_h1Ball_totallyBounded R hδ A hA).closure.isCompact isClosed_closure.isComplete

end
end ImbalancedChen.Part3.PositiveRectanglePhysicalRellich20261026b
