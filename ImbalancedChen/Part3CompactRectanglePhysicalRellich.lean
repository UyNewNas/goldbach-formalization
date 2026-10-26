import ImbalancedChen.Part3ProductCircleFiniteBoxRellich
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Physical compact smooth seeds with ONE common positive margin inside the
unit rectangle. Canonical representative lifting constructs actual torus
L2 vectors; no smooth periodic extension or Rellich theorem is assumed.
The SAME margin is proved to support the actual partial derivatives, so
the physical FTC/IBP endpoint terms vanish. Actual derivative Fourier laws
then place the physical energy ball in the proved product-circle H1 ball.
An exact distance identity transports total boundedness back to physical
L2(R^2). Weak H1 completion and quotient partition reconstruction are not
asserted here. -/

namespace ImbalancedChen.Part3.CompactRectanglePhysicalRellich20261026a
noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped BigOperators ENNReal
open ProductCircleFiniteBoxRellich20261026a
open LocalRectangleFourierTail20261026a
open P3CuspHorizontalDerivativeParsevalSourceOnly

def rectangle : Set (ℝ × ℝ) := Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1
def marginRectangle (δ : ℝ) : Set (ℝ × ℝ) := Icc δ (1-δ) ×ˢ Icc δ (1-δ)

def representative (z : Torus) : Fin 2 → ℝ :=
  ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))) z).1

def lift (F : ℝ × ℝ → ℂ) (z : Torus) : ℂ :=
  F (representative z 0, representative z 1)

theorem representative_coe (x : Fin 2 → ℝ)
    (hx : ∀ j, x j ∈ Ioc (0 : ℝ) 1) :
    representative (fun j => (x j : UnitAddCircle)) = x := by
  funext j
  exact congrArg Subtype.val (AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hx j))

theorem lift_memLp (F : ℝ × ℝ → ℂ) (hF : Continuous F) :
    MemLp (lift F) 2 (volume : Measure Torus) := by
  have hm : Measurable (lift F) := by
    apply hF.measurable.comp
    have hr : Measurable representative := measurable_subtype_coe.comp
      (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))).measurable
    exact ((measurable_pi_apply 0).comp hr).prodMk ((measurable_pi_apply 1).comp hr)
  obtain ⟨b, hb⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).bddAbove_image hF.norm.continuousOn
  apply MemLp.of_bound hm.aestronglyMeasurable (max b 0)
  apply Filter.Eventually.of_forall
  intro z
  have hr (j : Fin 2) : representative z j ∈ Icc (0 : ℝ) 1 := by
    exact ⟨((UnitAddTorus.measurableEquivPiIoc (fun _ => (0 : ℝ))) z).2 j |>.1.le,
      by simpa only [zero_add] using
        (((UnitAddTorus.measurableEquivPiIoc (fun _ => (0 : ℝ))) z).2 j).2⟩
  exact (hb ⟨_, ⟨hr 0, hr 1⟩, rfl⟩).trans (le_max_left _ _)

def liftL2 (F : ℝ × ℝ → ℂ) (hF : Continuous F) : TorusL2 :=
  (lift_memLp F hF).toLp (lift F)

theorem cube_integral (G : ℝ × ℝ → ℂ) :
    (∫ x : Fin 2 → ℝ in {x | ∀ j, x j ∈ Ioc (0 : ℝ) 1}, G (x 0,x 1)) =
      ∫ p in rectangle, G p := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hp := (measurePreserving_finTwoArrow μ).integral_comp' G
  have hl : (volume : Measure (Fin 2 → ℝ)).restrict
      {x | ∀ j, x j ∈ Ioc (0 : ℝ) 1} = Measure.pi (fun _ : Fin 2 => μ) := by
    have hc : {x : Fin 2 → ℝ | ∀ j, x j ∈ Ioc (0 : ℝ) 1} =
        Set.univ.pi (fun _ => Ioc (0 : ℝ) 1) := by ext x; simp
    rw [hc]
    exact Measure.restrict_pi_pi _
  have hr : μ.prod μ = (volume : Measure (ℝ × ℝ)).restrict rectangle := by
    simpa only [μ, rectangle, Measure.volume_eq_prod] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (Ioc (0 : ℝ) 1) (Ioc (0 : ℝ) 1))
  rw [hl, ← hr]
  exact hp

theorem lift_integral (F : ℝ × ℝ → ℂ) :
    (∫ z : Torus, lift F z) = ∫ p in rectangle, F p := by
  rw [UnitAddTorus.integral_preimage (lift F) (fun _ => (0 : ℝ))]
  have heq : (∫ x : Fin 2 → ℝ in {x | ∀ j, x j ∈ Ioc (0 : ℝ) 1},
      lift F (fun j => (x j : UnitAddCircle))) =
      ∫ x : Fin 2 → ℝ in {x | ∀ j, x j ∈ Ioc (0 : ℝ) 1}, F (x 0,x 1) := by
    apply setIntegral_congr_fun (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc))
    intro x hx
    simp only [lift, representative_coe x hx]
  simpa only [zero_add] using heq.trans (cube_integral F)

theorem liftL2_square (F : ℝ × ℝ → ℂ) (hF : Continuous F) :
    ‖liftL2 F hF‖^2 = ∫ p in rectangle, ‖F p‖^2 := by
  rw [norm_square_integral]
  calc
    _ = ∫ z : Torus, ‖lift F z‖^2 :=
      integral_congr_ae ((lift_memLp F hF).coeFn_toLp.mono (fun z hz => by rw [hz]))
    _ = _ := lift_integral (fun p => ‖F p‖^2)

def phase (n : ℤ) (x : ℝ) : ℂ := AddCircle.fourier (-n) (x : UnitAddCircle)

theorem coefficient_rectangle (F : ℝ × ℝ → ℂ) (hF : Continuous F) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (liftL2 F hF) k =
      ∫ p in rectangle, phase (k 0) p.1 * phase (k 1) p.2 * F p := by
  have hcoe : UnitAddTorus.mFourierCoeff (liftL2 F hF) k =
      UnitAddTorus.mFourierCoeff (lift F) k := by
    apply integral_congr_ae
    filter_upwards [(lift_memLp F hF).coeFn_toLp] with z hz
    rw [hz]
  rw [hcoe, UnitAddTorus.mFourierCoeff_eq_integral (lift F) k (fun _ => (0 : ℝ))]
  have heq : (∫ x : Fin 2 → ℝ in {x | ∀ j, x j ∈ Ioc (0 : ℝ) 1},
      UnitAddTorus.mFourier (-k) (fun j => (x j : UnitAddCircle)) •
        lift F (fun j => (x j : UnitAddCircle))) =
      ∫ x : Fin 2 → ℝ in {x | ∀ j, x j ∈ Ioc (0 : ℝ) 1},
        phase (k 0) (x 0) * phase (k 1) (x 1) * F (x 0,x 1) := by
    apply setIntegral_congr_fun (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc))
    intro x hx
    simp only [lift, representative_coe x hx, UnitAddTorus.mFourier,
      ContinuousMap.coe_mk, Fin.prod_univ_two, Pi.neg_apply, phase, smul_eq_mul]
  simpa only [zero_add] using heq.trans (cube_integral _)

theorem coefficient_x_first (F : ℝ × ℝ → ℂ) (hF : Continuous F) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (liftL2 F hF) k =
      ∫ y in (0 : ℝ)..1, phase (k 1) y *
        AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun x => F (x,y)) (k 0) := by
  rw [coefficient_rectangle]
  have hc : Continuous (fun p : ℝ × ℝ => phase (k 0) p.1 * phase (k 1) p.2 * F p) := by
    unfold phase
    fun_prop
  have hi := hc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
  have hir := hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [rectangle, ← Measure.prod_restrict] at hir ⊢
  rw [integral_prod_symm _ hir]
  simp_rw [AddCircle.fourierCoeffOn_eq_integral, sub_zero, inv_one, one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp [phase]; ring))

theorem coefficient_y_first (F : ℝ × ℝ → ℂ) (hF : Continuous F) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (liftL2 F hF) k =
      ∫ x in (0 : ℝ)..1, phase (k 0) x *
        AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun y => F (x,y)) (k 1) := by
  rw [coefficient_rectangle]
  have hc : Continuous (fun p : ℝ × ℝ => phase (k 0) p.1 * phase (k 1) p.2 * F p) := by
    unfold phase
    fun_prop
  have hi := (hc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [rectangle, ← Measure.prod_restrict] at hi ⊢
  rw [integral_prod _ hi]
  simp_rw [AddCircle.fourierCoeffOn_eq_integral, sub_zero, inv_one, one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_const_mul]
    rfl)

def direction (j : Fin 2) : ℝ × ℝ := if j = 0 then (1,0) else (0,1)
def partial (F : ℝ × ℝ → ℂ) (j : Fin 2) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ F p (direction j)

theorem partial_continuous (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 2 F) (j : Fin 2) :
    Continuous (partial F j) := (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem partial_support (F : ℝ × ℝ → ℂ) {δ : ℝ}
    (hs : Function.support F ⊆ marginRectangle δ) (j : Fin 2) :
    Function.support (partial F j) ⊆ marginRectangle δ := by
  have ht : tsupport F ⊆ marginRectangle δ :=
    closure_minimal hs (isClosed_Icc.prod isClosed_Icc)
  exact (subset_closure.trans (tsupport_fderiv_apply_subset ℝ (direction j))).trans ht

structure Seed (δ : ℝ) where
  function : ℝ × ℝ → ℂ
  smooth : ContDiff ℝ 2 function
  support_subset : Function.support function ⊆ marginRectangle δ

theorem seed_compactSupport {δ : ℝ} (s : Seed δ) : HasCompactSupport s.function :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_tsupport
    (closure_minimal s.support_subset (isClosed_Icc.prod isClosed_Icc))

theorem seed_partial_memLp {δ : ℝ} (s : Seed δ) (j : Fin 2) :
    MemLp (partial s.function j) 2 (volume : Measure (ℝ × ℝ)) := by
  have hc : HasCompactSupport (partial s.function j) :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_tsupport
      (closure_minimal (partial_support _ s.support_subset j) (isClosed_Icc.prod isClosed_Icc))
  exact (partial_continuous _ s.smooth j).memLp_of_hasCompactSupport hc

theorem seed_partial_energy_integrable {δ : ℝ} (s : Seed δ) (j : Fin 2) :
    Integrable (fun p : ℝ × ℝ => ‖partial s.function j p‖^2) :=
  (memLp_two_iff_integrable_sq_norm (seed_partial_memLp s j).aestronglyMeasurable).mp
    (seed_partial_memLp s j)

theorem margin_endpoints_zero (F : ℝ × ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hs : Function.support F ⊆ marginRectangle δ) :
    (∀ y, F (0,y) = 0 ∧ F (1,y) = 0) ∧
      (∀ x, F (x,0) = 0 ∧ F (x,1) = 0) := by
  constructor <;> intro t <;> constructor <;> by_contra hn
  all_goals have hb := hs hn
  all_goals dsimp [marginRectangle] at hb
  all_goals linarith [hb.1.1, hb.1.2, hb.2.1, hb.2.2]

/-- The common zero margin also applies to the ACTUAL derivatives.
No boundary term is suppressed by assuming smooth periodization. -/
theorem seed_partials_endpoints_zero {δ : ℝ} (hδ : 0 < δ) (s : Seed δ) (j : Fin 2) :
    (∀ y, partial s.function j (0,y) = 0 ∧ partial s.function j (1,y) = 0) ∧
      (∀ x, partial s.function j (x,0) = 0 ∧ partial s.function j (x,1) = 0) :=
  margin_endpoints_zero _ hδ (partial_support _ s.support_subset j)

/-- Actual two physical partials, not supplied Fourier multipliers. -/
theorem seed_derivative_pair {δ : ℝ} (hδ : 0 < δ) (s : Seed δ) :
    DerivativePair (liftL2 s.function s.smooth.continuous)
      (fun j => liftL2 (partial s.function j) (partial_continuous _ s.smooth j)) := by
  intro j k
  have hend := margin_endpoints_zero s.function hδ s.support_subset
  have hd (j : Fin 2) := partial_continuous s.function s.smooth j
  fin_cases j
  · rw [coefficient_x_first _ (hd 0), coefficient_x_first _ s.smooth.continuous]
    have hm (y : ℝ) : AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun x => partial s.function 0 (x,y)) (k 0) =
        (2 * (Real.pi : ℂ) * Complex.I * (k 0 : ℂ)) *
          AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
            (fun x => s.function (x,y)) (k 0) := by
      apply derivative_fourier_coefficient
      · intro x _
        have hline := (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
        simpa only [partial, direction, if_pos rfl] using
          ((s.smooth.differentiable (by norm_num) (x,y)).hasFDerivAt.comp_hasDerivAt x hline)
      · exact (hend.1 y).2.trans (hend.1 y).1.symm
      · exact ((hd 0).comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    simp_rw [hm]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  · rw [coefficient_y_first _ (hd 1), coefficient_y_first _ s.smooth.continuous]
    have hm (x : ℝ) : AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun y => partial s.function 1 (x,y)) (k 1) =
        (2 * (Real.pi : ℂ) * Complex.I * (k 1 : ℂ)) *
          AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
            (fun y => s.function (x,y)) (k 1) := by
      apply derivative_fourier_coefficient
      · intro y _
        have hline := (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
        simpa only [partial, direction, Fin.one_ne_zero, if_false] using
          ((s.smooth.differentiable (by norm_num) (x,y)).hasFDerivAt.comp_hasDerivAt y hline)
      · exact (hend.2 x).2.trans (hend.2 x).1.symm
      · exact ((hd 1).comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
    simp_rw [hm]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring

def physicalEnergy {δ : ℝ} (s : Seed δ) : ℝ :=
  ∑ j : Fin 2, ∫ p : ℝ × ℝ, ‖partial s.function j p‖^2

def torusSeed {δ : ℝ} (s : Seed δ) : TorusL2 := liftL2 s.function s.smooth.continuous

theorem margin_subset_rectangle {δ : ℝ} (hδ : 0 < δ) : marginRectangle δ ⊆ rectangle := by
  intro p hp
  exact ⟨⟨lt_of_lt_of_le hδ hp.1.1, by linarith [hp.1.2]⟩,
    ⟨lt_of_lt_of_le hδ hp.2.1, by linarith [hp.2.2]⟩⟩

theorem norm_lift_physical (F : ℝ × ℝ → ℂ) (hF : Continuous F) {δ : ℝ}
    (hδ : 0 < δ) (hs : Function.support F ⊆ marginRectangle δ) :
    ‖liftL2 F hF‖^2 = ∫ p : ℝ × ℝ, ‖F p‖^2 := by
  rw [liftL2_square]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hz : F p = 0 := by
    by_contra hn
    exact hp (margin_subset_rectangle hδ (hs hn))
  simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem torusSeed_energy {δ : ℝ} (hδ : 0 < δ) (s : Seed δ) :
    (∑ j : Fin 2, ‖liftL2 (partial s.function j) (partial_continuous _ s.smooth j)‖^2) =
      physicalEnergy s := by
  apply Finset.sum_congr rfl
  intro j _
  exact norm_lift_physical _ (partial_continuous _ s.smooth j) hδ
    (partial_support _ s.support_subset j)

theorem physical_seed_torus_error {δ : ℝ} (hδ : 0 < δ) (s : Seed δ)
    (K : ℕ) (hK : 0 < K) :
    ‖torusSeed s - projection K (torusSeed s)‖^2 ≤ tailConstant K * physicalEnergy s := by
  simpa only [torusSeed_energy hδ s] using
    projection_error_le K hK (torusSeed s) _ (seed_derivative_pair hδ s)

def physicalSeed {δ : ℝ} (s : Seed δ) : Lp ℂ 2 (volume : Measure (ℝ × ℝ)) :=
  (s.smooth.continuous.memLp_of_hasCompactSupport (seed_compactSupport s)).toLp s.function

def seedBall (δ B E : ℝ) : Set (Seed δ) :=
  {s | ‖physicalSeed s‖ ≤ B ∧ physicalEnergy s ≤ E}

/-- One genuine two-dimensional finite box is selected BEFORE every
member of the physical common-rectangle energy family. -/
theorem exists_uniform_physical_box_cutoff {δ : ℝ} (hδ : 0 < δ)
    (B E ε : ℝ) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ s ∈ seedBall δ B E,
      ‖torusSeed s - projection K (torusSeed s)‖^2 < ε := by
  have ht : Tendsto (fun K => tailConstant K * E) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using LocalRectangleFourierTail20261026a.tailConstant_tendsto_zero.mul_const E
  have he : ∀ᶠ K : ℕ in atTop, tailConstant K * E < ε := ht.eventually (gt_mem_nhds hε)
  obtain ⟨K, hK, hsmall⟩ := ((eventually_gt_atTop 0).and he).exists
  refine ⟨K, hK, ?_⟩
  intro s hs
  exact ((physical_seed_torus_error hδ s K hK).trans
    (mul_le_mul_of_nonneg_left hs.2 (by unfold tailConstant; positivity))).trans_lt hsmall

theorem physicalSeed_square {δ : ℝ} (s : Seed δ) :
    ‖physicalSeed s‖^2 = ∫ p : ℝ × ℝ, ‖s.function p‖^2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (physicalSeed s) (physicalSeed s))]
  apply integral_congr_ae
  filter_upwards [(s.smooth.continuous.memLp_of_hasCompactSupport
    (seed_compactSupport s)).coeFn_toLp] with p hp
  simp only [hp, inner_self_eq_norm_sq_to_K, Complex.ofReal_re]

theorem torusSeed_norm {δ : ℝ} (hδ : 0 < δ) (s : Seed δ) :
    ‖torusSeed s‖ = ‖physicalSeed s‖ := by
  have hs := norm_lift_physical s.function s.smooth.continuous hδ s.support_subset
  rw [← physicalSeed_square] at hs
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem seedBall_torus_totallyBounded {δ : ℝ} (hδ : 0 < δ) (B E : ℝ) (hE : 0 ≤ E) :
    TotallyBounded (torusSeed '' seedBall δ B E) := by
  apply (energyBall_totallyBounded B E hE).subset
  rintro u ⟨s, hs, rfl⟩
  refine ⟨by simpa only [torusSeed_norm hδ s] using hs.1,
    (fun j => liftL2 (partial s.function j) (partial_continuous _ s.smooth j)),
    seed_derivative_pair hδ s, ?_⟩
  simpa only [torusSeed_energy hδ s] using hs.2

theorem seed_distance {δ : ℝ} (hδ : 0 < δ) (s t : Seed δ) :
    dist (physicalSeed s) (physicalSeed t) = dist (torusSeed s) (torusSeed t) := by
  let r : Seed δ := ⟨s.function - t.function, s.smooth.sub t.smooth, by
    intro p hp
    by_contra hn
    have hs : s.function p = 0 := by by_contra hz; exact hn (s.support_subset hz)
    have ht : t.function p = 0 := by by_contra hz; exact hn (t.support_subset hz)
    exact hp (by simp only [Pi.sub_apply, hs, ht, sub_self])⟩
  have hphysical : physicalSeed r = physicalSeed s - physicalSeed t := by
    apply Lp.ext
    filter_upwards [(s.smooth.continuous.memLp_of_hasCompactSupport (seed_compactSupport s)).coeFn_toLp,
      (t.smooth.continuous.memLp_of_hasCompactSupport (seed_compactSupport t)).coeFn_toLp,
      (r.smooth.continuous.memLp_of_hasCompactSupport (seed_compactSupport r)).coeFn_toLp,
      Lp.coeFn_sub (physicalSeed s) (physicalSeed t)] with p hs ht hr hsub
    rw [hr, hsub, hs, ht]
    rfl
  have htorus : torusSeed r = torusSeed s - torusSeed t := by
    apply Lp.ext
    filter_upwards [(lift_memLp s.function s.smooth.continuous).coeFn_toLp,
      (lift_memLp t.function t.smooth.continuous).coeFn_toLp,
      (lift_memLp r.function r.smooth.continuous).coeFn_toLp,
      Lp.coeFn_sub (torusSeed s) (torusSeed t)] with p hs ht hr hsub
    rw [hr, hsub, hs, ht]
    rfl
  simpa only [dist_eq_norm, hphysical, htorus] using (torusSeed_norm hδ r).symm

/-- Actual physical compact-rectangle H1 energy balls are L2 totally
bounded. This is not an abstract compact embedding supplied as a premise. -/
theorem smooth_common_rectangle_energyBall_totallyBounded {δ : ℝ} (hδ : 0 < δ)
    (B E : ℝ) (hE : 0 ≤ E) : TotallyBounded (physicalSeed '' seedBall δ B E) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨t, htSub, htFin, htCover⟩ := Metric.finite_approx_of_totallyBounded
    (seedBall_torus_totallyBounded hδ B E hE) ε hε
  letI : Fintype t := htFin.fintype
  let pick : t → Seed δ := fun v => Classical.choose (htSub v.2)
  have hpick (v : t) : pick v ∈ seedBall δ B E ∧ torusSeed (pick v) = v :=
    Classical.choose_spec (htSub v.2)
  let centers : Set (Lp ℂ 2 (volume : Measure (ℝ × ℝ))) :=
    range (fun v : t => physicalSeed (pick v))
  refine ⟨centers, finite_range _, ?_⟩
  rintro u ⟨s, hs, rfl⟩
  obtain ⟨v, hv, hdist⟩ := Set.mem_iUnion₂.mp (htCover ⟨s, hs, rfl⟩)
  refine Set.mem_iUnion₂.mpr ⟨physicalSeed (pick ⟨v,hv⟩), ⟨⟨v,hv⟩, rfl⟩, ?_⟩
  rw [mem_ball, seed_distance hδ, (hpick ⟨v,hv⟩).2]
  exact hdist

/-- Consequently the physical L2 closure is genuinely compact. No
identification with a maximal weak derivative domain is asserted. -/
theorem smooth_common_rectangle_energyBall_compact_closure {δ : ℝ} (hδ : 0 < δ)
    (B E : ℝ) (hE : 0 ≤ E) :
    IsCompact (closure (physicalSeed '' seedBall δ B E)) :=
  (smooth_common_rectangle_energyBall_totallyBounded hδ B E hE).closure.isCompact
    isClosed_closure.isComplete

def physicalH1Ball (δ R : ℝ) : Set (Seed δ) :=
  {s | ‖physicalSeed s‖^2 + physicalEnergy s ≤ R}

theorem physicalEnergy_nonneg {δ : ℝ} (s : Seed δ) : 0 ≤ physicalEnergy s :=
  Finset.sum_nonneg (fun j _ => integral_nonneg (fun p => sq_nonneg _))

/-- A single genuine H1 energy bound controls BOTH the L2 mass and both
physical derivatives. This is the compact-rectangle Rellich endpoint. -/
theorem physicalH1Ball_totallyBounded {δ : ℝ} (hδ : 0 < δ) (R : ℝ) (hR : 0 ≤ R) :
    TotallyBounded (physicalSeed '' physicalH1Ball δ R) := by
  apply (smooth_common_rectangle_energyBall_totallyBounded hδ (Real.sqrt R) R hR).subset
  rintro u ⟨s, hs, rfl⟩
  refine ⟨s, ⟨?_, ?_⟩, rfl⟩
  · have he := physicalEnergy_nonneg s
    have hn := norm_nonneg (physicalSeed s)
    have hr := Real.sqrt_nonneg R
    have hsqrt := Real.sq_sqrt hR
    dsimp [physicalH1Ball] at hs
    nlinarith
  · dsimp [physicalH1Ball] at hs
    linarith [sq_nonneg (‖physicalSeed s‖)]

theorem physicalH1Ball_compact_closure {δ : ℝ} (hδ : 0 < δ) (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (closure (physicalSeed '' physicalH1Ball δ R)) :=
  (physicalH1Ball_totallyBounded hδ R hR).closure.isCompact isClosed_closure.isComplete

end
end ImbalancedChen.Part3.CompactRectanglePhysicalRellich20261026a
