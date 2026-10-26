import ImbalancedChen.Part3CuspHorizontalDerivativeParseval
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
Actual periodic C2 functions on the open upper plane have C2 literal
horizontal Fourier coefficients. Compact rectangles pay for both height
derivatives. Two genuine periodic integrations by parts turn the actual
Maass PDE into the coefficient ODE, including its sign and 2*pi*n factor.
No coefficient regularity or coefficient ODE is an input.
-/

namespace ImbalancedChen.Part3.ActualMaassFourierODE20261026a
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open P3CuspHorizontalDerivativeParsevalSourceOnly

def upperDomain : Set (ℝ × ℝ) := {p | 0 < p.2}
theorem upperDomain_isOpen : IsOpen upperDomain := isOpen_lt continuous_const continuous_snd

def partialX (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ u p (1, 0)
def partialY (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ u p (0, 1)

theorem partialX_contDiffOn {u : ℝ × ℝ → ℂ} {n k : ℕ∞ω}
    (hu : ContDiffOn ℝ n u upperDomain) (hk : k + 1 ≤ n) :
    ContDiffOn ℝ k (partialX u) upperDomain :=
  (hu.fderiv_of_isOpen upperDomain_isOpen hk).clm_apply contDiffOn_const

theorem partialY_contDiffOn {u : ℝ × ℝ → ℂ} {n k : ℕ∞ω}
    (hu : ContDiffOn ℝ n u upperDomain) (hk : k + 1 ≤ n) :
    ContDiffOn ℝ k (partialY u) upperDomain :=
  (hu.fderiv_of_isOpen upperDomain_isOpen hk).clm_apply contDiffOn_const

theorem horizontal_hasDerivAt {u : ℝ × ℝ → ℂ}
    (hu : DifferentiableOn ℝ u upperDomain) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => u (t, y)) (partialX u (x, y)) x := by
  exact ((hu (x, y) hy).differentiableAt (upperDomain_isOpen.mem_nhds hy)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

theorem vertical_hasDerivAt {u : ℝ × ℝ → ℂ}
    (hu : DifferentiableOn ℝ u upperDomain) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => u (x, t)) (partialY u (x, y)) y := by
  exact ((hu (x, y) hy).differentiableAt (upperDomain_isOpen.mem_nhds hy)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

abbrev PeriodCell := Icc (0 : ℝ) 1
attribute [local instance] Measure.Subtype.measureSpace

local instance periodCell_finite : IsFiniteMeasure (volume : Measure PeriodCell) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_lt_top

/-- Integrate on the actual compact period cell; its endpoints have zero mass. -/
def periodIntegral (F : ℝ × ℝ → ℂ) (y : ℝ) : ℂ := ∫ x : PeriodCell, F (x, y)

theorem periodIntegral_eq_interval (F : ℝ × ℝ → ℂ) (y : ℝ) :
    periodIntegral F y = ∫ x in (0 : ℝ)..1, F (x, y) := by
  rw [periodIntegral, integral_subtype_comap measurableSet_Icc,
    intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem continuous_slice {F : ℝ × ℝ → ℂ} (hF : ContinuousOn F upperDomain)
    {y : ℝ} (hy : 0 < y) : Continuous (fun x : ℝ => F (x, y)) := by
  exact hF.comp_continuous (by fun_prop) (fun x => hy)

theorem continuous_cell_slice {F : ℝ × ℝ → ℂ} (hF : ContinuousOn F upperDomain)
    {y : ℝ} (hy : 0 < y) : Continuous (fun x : PeriodCell => F (x, y)) :=
  (continuous_slice hF hy).comp continuous_subtype_val

/-- Compactness supplies the derivative domination; no integral derivative
or uniform derivative bound is assumed. -/
theorem periodIntegral_hasDerivAt {F G : ℝ × ℝ → ℂ}
    (hF : ContinuousOn F upperDomain) (hG : ContinuousOn G upperDomain)
    (hd : ∀ x : ℝ, ∀ y : ℝ, 0 < y → HasDerivAt (fun t => F (x, t)) (G (x, y)) y)
    {y : ℝ} (hy : 0 < y) : HasDerivAt (periodIntegral F) (periodIntegral G y) y := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (y / 2) (2 * y)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKU : K ⊆ upperDomain := by
    intro p hp
    exact lt_of_lt_of_le (by linarith : 0 < y / 2) hp.2.1
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hG.norm.mono hKU)
  have hnb : Ioo (y / 2) (2 * y) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ t in 𝓝 y,
      AEStronglyMeasurable (fun x : PeriodCell => F (x, t)) volume := by
    filter_upwards [hnb] with t ht
    exact (continuous_cell_slice hF (by linarith [ht.1])).aestronglyMeasurable
  have hfi : Integrable (fun x : PeriodCell => F (x, y)) volume :=
    (continuous_cell_slice hF hy).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgmeas := (continuous_cell_slice hG hy).aestronglyMeasurable
  have hbnd : ∀ᵐ x : PeriodCell, ∀ t ∈ Ioo (y / 2) (2 * y), ‖G (x, t)‖ ≤ B := by
    exact Filter.Eventually.of_forall (fun x t ht => hB ⟨(x, t), ⟨x.property, ht.1.le, ht.2.le⟩, rfl⟩)
  have hdiff : ∀ᵐ x : PeriodCell, ∀ t ∈ Ioo (y / 2) (2 * y),
      HasDerivAt (fun v => F (x, v)) (G (x, t)) t := by
    exact Filter.Eventually.of_forall (fun x t ht => hd x t (by linarith [ht.1]))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hnb hmeas hfi hgmeas
    hbnd (integrable_const B) hdiff).2

/-- Continuity follows from a genuine continuous compact-cell family. -/
theorem periodIntegral_continuousOn {F : ℝ × ℝ → ℂ}
    (hF : ContinuousOn F upperDomain) : ContinuousOn (periodIntegral F) (Ioi (0 : ℝ)) := by
  apply continuousOn_integral_of_compact_support (k := (univ : Set PeriodCell)) isCompact_univ
  · exact hF.comp (by fun_prop)
      (fun p hp => hp.1)
  · intro p x hp hx
    exact False.elim (hx (mem_univ x))

def phase (n : ℤ) (x : ℝ) : ℂ := AddCircle.fourier (-n) (x : UnitAddCircle)
def phased (n : ℤ) (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := phase n p.1 * u p
def coefficient (u : ℝ × ℝ → ℂ) (n : ℤ) : ℝ → ℂ := periodIntegral (phased n u)

theorem phase_continuous (n : ℤ) : Continuous (phase n) :=
  (AddCircle.fourier (-n)).continuous.comp AddCircle.continuous_mk'

theorem phased_continuousOn {u : ℝ × ℝ → ℂ} (hu : ContinuousOn u upperDomain) (n : ℤ) :
    ContinuousOn (phased n u) upperDomain :=
  ((phase_continuous n).comp continuous_fst).continuousOn.mul hu

theorem coefficient_eq_fourierCoeffOn (u : ℝ × ℝ → ℂ) (n : ℤ) (y : ℝ) :
    coefficient u n y = AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun x => u (x, y)) n := by
  rw [AddCircle.fourierCoeffOn_eq_integral, coefficient, periodIntegral_eq_interval]
  simp only [sub_zero, div_one, one_smul, smul_eq_mul, phased, phase]

theorem coefficient_continuousOn {u : ℝ × ℝ → ℂ} (hu : ContinuousOn u upperDomain)
    (n : ℤ) : ContinuousOn (coefficient u n) (Ioi (0 : ℝ)) :=
  periodIntegral_continuousOn (phased_continuousOn hu n)

theorem coefficient_hasDerivAt {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 1 u upperDomain) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (coefficient u n) (coefficient (partialY u) n y) y := by
  apply periodIntegral_hasDerivAt (phased_continuousOn hu.continuousOn n)
    (phased_continuousOn (partialY_contDiffOn hu (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)).continuousOn n)
  intro x t ht
  exact (vertical_hasDerivAt (hu.differentiableOn (by norm_num)) x ht).const_mul (phase n x)

theorem coefficient_deriv {u : ℝ × ℝ → ℂ} (hu : ContDiffOn ℝ 1 u upperDomain)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    deriv (coefficient u n) y = coefficient (partialY u) n y :=
  (coefficient_hasDerivAt hu n hy).deriv

theorem coefficient_deriv_hasDerivAt {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (coefficient u n)) (coefficient (partialY (partialY u)) n y) y := by
  have heq : deriv (coefficient u n) =ᶠ[𝓝 y] coefficient (partialY u) n := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact coefficient_deriv (hu.of_le (by norm_num)) n ht
  exact (coefficient_hasDerivAt (partialY_contDiffOn hu (by norm_num)) n hy).congr_of_eventuallyEq heq

theorem coefficient_contDiffOn_two {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain) (n : ℤ) :
    ContDiffOn ℝ 2 (coefficient u n) (Ioi (0 : ℝ)) := by
  have hdy : ContDiffOn ℝ 1 (partialY u) upperDomain := partialY_contDiffOn hu (by norm_num)
  have hdy2 : ContinuousOn (partialY (partialY u)) upperDomain :=
    (partialY_contDiffOn hdy (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)).continuousOn
  have hdc : ContDiffOn ℝ 1 (coefficient (partialY u) n) (Ioi (0 : ℝ)) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (coefficient_hasDerivAt hdy n hy).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    apply (contDiffOn_zero.mpr (coefficient_continuousOn hdy2 n)).congr
    intro y hy
    exact coefficient_deriv hdy n hy
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun y hy => (coefficient_hasDerivAt (hu.of_le (by norm_num)) n hy).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply hdc.congr
  intro y hy
  exact coefficient_deriv (hu.of_le (by norm_num)) n hy

/-- The derivative inherits genuine period one by differentiating the
translated identity, so the second IBP has its own proved boundary cancellation. -/
theorem partialX_periodic {u : ℝ × ℝ → ℂ}
    (hu : DifferentiableOn ℝ u upperDomain)
    (hp : ∀ x y : ℝ, 0 < y → u (x + 1, y) = u (x, y))
    (x : ℝ) {y : ℝ} (hy : 0 < y) : partialX u (x + 1, y) = partialX u (x, y) := by
  have hshift := (horizontal_hasDerivAt hu (x + 1) hy).comp x ((hasDerivAt_id x).add_const 1)
  have heq : (fun t : ℝ => u (t + 1, y)) = fun t => u (t, y) := funext (fun t => hp t y hy)
  have hd : HasDerivAt (fun t => u (t, y)) (partialX u (x + 1, y)) x := by
    simpa only [Function.comp_def, mul_one, heq] using hshift
  exact hd.unique (horizontal_hasDerivAt hu x hy)

theorem coefficient_partialX {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 1 u upperDomain)
    (hp : ∀ x y : ℝ, 0 < y → u (x + 1, y) = u (x, y))
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (partialX u) n y = (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * coefficient u n y := by
  simp only [coefficient_eq_fourierCoeffOn]
  apply derivative_fourier_coefficient
  · intro x hx
    exact horizontal_hasDerivAt (hu.differentiableOn (by norm_num)) x hy
  · simpa using hp 0 y hy
  · exact (continuous_slice (partialX_contDiffOn hu
      (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)).continuousOn hy).intervalIntegrable 0 1

theorem coefficient_partialX_twice {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain)
    (hp : ∀ x y : ℝ, 0 < y → u (x + 1, y) = u (x, y))
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (partialX (partialX u)) n y =
      -((2 * Real.pi * (n : ℝ) : ℝ) : ℂ)^2 * coefficient u n y := by
  rw [coefficient_partialX (partialX_contDiffOn hu (by norm_num))
    (fun x y hy => partialX_periodic (hu.differentiableOn (by norm_num)) hp x hy) n hy,
    coefficient_partialX (hu.of_le (by norm_num)) hp n hy]
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * (n : ℂ))^2 * coefficient u n y * Complex.I_sq

/-- The native Maass PDE implies the literal Fourier coefficient ODE.
The parameter lambda can be complex; no eigenvalue classification is hidden. -/
theorem actual_coefficient_maass_ode {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u upperDomain)
    (hp : ∀ x y : ℝ, 0 < y → u (x + 1, y) = u (x, y))
    (lambda : ℂ)
    (hPDE : ∀ p ∈ upperDomain,
      -(p.2 : ℂ)^2 * (partialX (partialX u) p + partialY (partialY u) p) = lambda * u p)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ)^2 * (deriv (deriv (coefficient u n)) y -
      ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ)^2 * coefficient u n y) = lambda * coefficient u n y := by
  have hxx : ContinuousOn (partialX (partialX u)) upperDomain :=
    (partialX_contDiffOn (partialX_contDiffOn hu (by norm_num) : ContDiffOn ℝ 1 _ _)
      (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)).continuousOn
  have hyy : ContinuousOn (partialY (partialY u)) upperDomain :=
    (partialY_contDiffOn (partialY_contDiffOn hu (by norm_num) : ContDiffOn ℝ 1 _ _)
      (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)).continuousOn
  have hixx := (continuous_cell_slice (phased_continuousOn hxx n) hy).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hiyy := (continuous_cell_slice (phased_continuousOn hyy n) hy).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hi : -(y : ℂ)^2 *
      (coefficient (partialX (partialX u)) n y + coefficient (partialY (partialY u)) n y) =
      lambda * coefficient u n y := by
    unfold coefficient periodIntegral
    rw [← integral_add hixx hiyy, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      have h := hPDE (x, y) hy
      dsimp [phased]
      linear_combination phase n x * h)
  rw [coefficient_partialX_twice hu hp n hy] at hi
  rw [(coefficient_deriv_hasDerivAt hu n hy).deriv]
  convert hi using 1 <;> ring

end
end ImbalancedChen.Part3.ActualMaassFourierODE20261026a
