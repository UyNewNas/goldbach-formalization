import ImbalancedChen.Part3Gamma0ParabolicEisensteinHalfPairs
import ImbalancedChen.Part3PowerSeedPeriodization
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Fourier interchange for the ACTUAL parabolic Eisenstein series at real
s>1. The norm-integral series on the horizontal period [0,1] is proved
summable from the existing quantitative lattice majorant on a bounded
vertical strip. The original actual half-primitive-pair sum can therefore
be integrated term by term; no Fourier interchange or hAbsSum is a field.
The primitive level rows are also grouped by their literal first integer
coordinate c, retaining the genuine N|c restriction and IsCoprime(c,d).
This does not yet evaluate the grouped c coefficients or their zeta sums.
-/

namespace ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a

noncomputable section

open Set MeasureTheory EisensteinSeries
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEisensteinHalfPairs20261025a
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini

/-- The actual height-y horizontal point of H. -/
def horizontalPoint (y : ℝ) (hy : 0 < y) (x : ℝ) : UpperHalfPlane :=
  ⟨⟨x, y⟩, hy⟩

/-- The literal period-one Fourier term for one primitive level row. -/
def primitiveFourierTerm (N : ℕ) (s y : ℝ) (hy : 0 < y)
    (n : ℤ) (v : LevelPrimitiveRow N) (x : ℝ) : ℂ :=
  fourierPhase n x * (seed s (horizontalPoint y hy x) v.1 : ℂ)

/-- The actual full Eisenstein coefficient, with the original normalization. -/
def actualEisensteinFourier (N : ℕ) (s y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    fourierPhase n x * (actualParabolicEisenstein N s (horizontalPoint y hy x) : ℂ)

/-- A completely explicit summable horizontal majorant, derived from the
actual seed bound on the strip |Re|<=1 and Im>=y. -/
def rowMajorant (N : ℕ) (s y : ℝ) (hy : 0 < y)
    (v : LevelPrimitiveRow N) : ℝ :=
  (y ^ s * EisensteinSeries.r ⟨⟨1, y⟩, hy⟩ ^ (-(2 * s))) *
    ‖v.1‖ ^ (-(2 * s))

theorem primitiveFourierTerm_measurable (N : ℕ) (s y : ℝ) (hy : 0 < y)
    (n : ℤ) (v : LevelPrimitiveRow N) :
    Measurable (primitiveFourierTerm N s y hy n v) := by
  unfold primitiveFourierTerm fourierPhase seed horizontalPoint
  fun_prop

theorem primitiveFourierTerm_norm_le (N : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (n : ℤ) (v : LevelPrimitiveRow N)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖primitiveFourierTerm N s y hy n v x‖ ≤ rowMajorant N s y hy v := by
  have hstrip : horizontalPoint y hy x ∈ UpperHalfPlane.verticalStrip 1 y := by
    change |x| ≤ 1 ∧ y ≤ y
    exact ⟨by rw [abs_of_pos hx.1]; exact hx.2, le_rfl⟩
  have hbound := seed_bound_on_boundedStrip s hs 1 y y hy v.1
    (horizontalPoint y hy x) hstrip (le_refl y)
  have hnonneg : 0 ≤ seed s (horizontalPoint y hy x) v.1 := by
    unfold seed
    positivity
  simpa only [primitiveFourierTerm, norm_mul, fourierPhase_norm,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg, one_mul,
    rowMajorant] using hbound

theorem rowMajorant_summable (N : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) : Summable (rowMajorant N s y hy) := by
  have h := (EisensteinSeries.summable_one_div_norm_rpow
    (by linarith : 2 < 2 * s)).mul_left
      (y ^ s * EisensteinSeries.r ⟨⟨1, y⟩, hy⟩ ^ (-(2 * s)))
  exact h.subtype _

theorem primitiveFourierTerm_integrable (N : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (n : ℤ) (v : LevelPrimitiveRow N) :
    IntegrableOn (primitiveFourierTerm N s y hy n v) (Ioc (0 : ℝ) 1) := by
  apply IntegrableOn.of_bound (by simp)
    (primitiveFourierTerm_measurable N s y hy n v).aestronglyMeasurable.restrict
    (rowMajorant N s y hy v)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact primitiveFourierTerm_norm_le N s hs y hy n v hx

/-- The genuine primitive-row norm-integral series is summable. The bound
is proved on every x in the actual Fourier interval before interchange. -/
theorem primitiveFourierTerm_integral_norm_summable
    (N : ℕ) (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    Summable (fun v : LevelPrimitiveRow N =>
      ∫ x in Ioc (0 : ℝ) 1, ‖primitiveFourierTerm N s y hy n v x‖) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)
  letI : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  have hmass : μ.real univ = 1 := by simp [μ, measureReal_def]
  apply (rowMajorant_summable N s hs y hy).of_nonneg_of_le
    (fun v => integral_nonneg (fun x => norm_nonneg _))
  intro v
  have hbound : ∀ᵐ x ∂μ,
      ‖primitiveFourierTerm N s y hy n v x‖ ≤ rowMajorant N s y hy v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact primitiveFourierTerm_norm_le N s hs y hy n v hx
  have h := integral_mono_ae
    (primitiveFourierTerm_integrable N s hs y hy n v).norm
    (integrable_const (rowMajorant N s y hy v)) hbound
  simpa only [integral_const, hmass, one_smul] using h

/-- Actual Eisenstein Fourier interchange over ALL primitive level rows.
No single-seed transform is being substituted for the original series. -/
theorem actualEisensteinFourier_eq_primitive_integrals
    (N : ℕ) (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    actualEisensteinFourier N s y hy n =
      (1 / 2 : ℂ) * ∑' v : LevelPrimitiveRow N,
        ∫ x in Ioc (0 : ℝ) 1, primitiveFourierTerm N s y hy n v x := by
  have hpoint (x : ℝ) :
      fourierPhase n x *
          (actualParabolicEisenstein N s (horizontalPoint y hy x) : ℂ) =
        (1 / 2 : ℂ) * ∑' v : LevelPrimitiveRow N,
          primitiveFourierTerm N s y hy n v x := by
    rw [actualParabolicEisenstein_eq_half_pair_sum N s hs]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_tsum]
    change fourierPhase n x * ((1 / 2 : ℂ) *
        ∑' v : LevelPrimitiveRow N, (seed s (horizontalPoint y hy x) v.1 : ℂ)) =
      (1 / 2 : ℂ) * ∑' v : LevelPrimitiveRow N,
        fourierPhase n x * (seed s (horizontalPoint y hy x) v.1 : ℂ)
    rw [tsum_mul_left]
    ring
  rw [actualEisensteinFourier, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    _ = ∫ x in Ioc (0 : ℝ) 1,
        (1 / 2 : ℂ) * ∑' v : LevelPrimitiveRow N,
          primitiveFourierTerm N s y hy n v x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (1 / 2 : ℂ) *
        ∫ x in Ioc (0 : ℝ) 1, ∑' v : LevelPrimitiveRow N,
          primitiveFourierTerm N s y hy n v x := by rw [integral_const_mul]
    _ = _ := by
      rw [← integral_tsum_of_summable_integral_norm
        (primitiveFourierTerm_integrable N s hs y hy n)
        (primitiveFourierTerm_integral_norm_summable N s hs y hy n)]

/-- The second integer coordinate at fixed literal first coordinate c.
The level condition N|c remains INSIDE the genuine primitive-row index. -/
abbrev PrimitiveD (N : ℕ) (c : ℤ) :=
  {d : ℤ // IsCoprime c d ∧ (N : ℤ) ∣ c}

def rowByFirstEquiv (N : ℕ) : LevelPrimitiveRow N ≃ Σ c : ℤ, PrimitiveD N c where
  toFun v := ⟨v.1 0, v.1 1, v.property⟩
  invFun p := ⟨![p.1, p.2.1], by simpa using p.2.property⟩
  left_inv v := by
    apply Subtype.ext
    funext j
    fin_cases j <;> rfl
  right_inv p := by
    rcases p with ⟨c, d, hd⟩
    rfl

/-- Actual primitive Fourier coefficients grouped by their true integer
c, including c=0 and retaining the original level-divisibility condition. -/
theorem actualEisensteinFourier_eq_integer_c_sum
    (N : ℕ) (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    actualEisensteinFourier N s y hy n =
      (1 / 2 : ℂ) * ∑' c : ℤ, ∑' d : PrimitiveD N c,
        ∫ x in Ioc (0 : ℝ) 1,
          fourierPhase n x * (seed s (horizontalPoint y hy x) ![c, d.1] : ℂ) := by
  have hnorm : Summable (fun v : LevelPrimitiveRow N =>
      ‖∫ x in Ioc (0 : ℝ) 1, primitiveFourierTerm N s y hy n v x‖) :=
    (primitiveFourierTerm_integral_norm_summable N s hs y hy n).of_nonneg_of_le
      (fun v => norm_nonneg _) (fun v => norm_integral_le_integral_norm _)
  have hsum : Summable (fun v : LevelPrimitiveRow N =>
      ∫ x in Ioc (0 : ℝ) 1, primitiveFourierTerm N s y hy n v x) := hnorm.of_norm
  rw [actualEisensteinFourier_eq_primitive_integrals N s hs y hy n]
  congr 1
  let e := (rowByFirstEquiv N).symm
  have hsigma := e.summable_iff.mpr hsum
  calc
    _ = ∑' p : Σ c : ℤ, PrimitiveD N c,
        ∫ x in Ioc (0 : ℝ) 1,
          fourierPhase n x * (seed s (horizontalPoint y hy x) ![p.1, p.2.1] : ℂ) :=
      (e.tsum_eq _).symm
    _ = _ := hsigma.tsum_sigma

end
end ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a