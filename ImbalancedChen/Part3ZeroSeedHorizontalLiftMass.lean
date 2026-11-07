import ImbalancedChen.Part3GammaZeroSeedCompactLiftContinuity
import ImbalancedChen.Part3CanonicalTensorHyperbolicLaplacianForm
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual canonical upper-half-plane dxdy/y^2 squared mass of a separated
horizontal lift factors into its two literal one-dimensional masses.
The fixed smooth integer unit partition has horizontal squared mass <=2,
so the ORIGINAL compactHeightLift of every original HeightSeed has raw
canonical squared mass <=2 times the physical dy/y^2 profile squared mass.
All transport is through the actual H inclusion, its actual volume
density, and the canonical complex-to-real-pair measure equivalence.
This supplies the missing tensor-mass bridge to normalized small-height
tests; no quotient mass or profile-scaling conclusion is assumed here.
-/
namespace ImbalancedChen.Part3.ZeroSeedHorizontalLiftMass20261026b

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open CanonicalTensorHyperbolicLaplacianForm20261024z
open GammaZeroSeedCompactLiftContinuity20261026b
open SmoothIntegerUnitPartition20261026b SmoothZeroHeightSeedProfiles20261026b
open ActualInfinityCuspAnnihilator20261026b

def horizontalSquareMass (g : ℝ → ℂ) : ℝ≥0∞ := ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2)

def physicalHeightSquareMass (h : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (‖h y‖^2/y^2)

/-- Actual canonical hyperbolic volume, with the physical density paid
before Tonelli. No finiteness of either mass is required. -/
theorem canonical_separated_squareMass (g h : ℝ → ℂ) (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ z : UpperHalfPlane, ENNReal.ofReal (‖g z.re*h z.im‖^2)) =
      horizontalSquareMass g * physicalHeightSquareMass h := by
  let A : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖g x‖^2)
  let B : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (‖h y‖^2/y^2)
  let G : ℝ × ℝ → ℝ≥0∞ := fun p => A p.1 * B p.2
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hpoint (z : UpperHalfPlane) :
      (upperDensityNN z : ℝ≥0∞)*ENNReal.ofReal (‖g z.re*h z.im‖^2) =
        G (Complex.measurableEquivRealProd (z : ℂ)) := by
    have hd : (upperDensityNN z : ℝ≥0∞) = ENNReal.ofReal ((z.im⁻¹)^2) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      simp [upperDensityNN, one_div]
    have hr : (z.im⁻¹)^2 * ‖g z.re*h z.im‖^2 =
        ‖g z.re‖^2 * (‖h z.im‖^2/z.im^2) := by
      simp only [norm_mul, mul_pow, div_eq_mul_inv, inv_pow]
      ring
    calc
      _ = ENNReal.ofReal ((z.im⁻¹)^2 * ‖g z.re*h z.im‖^2) := by
        rw [hd, ENNReal.ofReal_mul (sq_nonneg _)]
      _ = ENNReal.ofReal (‖g z.re‖^2 * (‖h z.im‖^2/z.im^2)) := congrArg ENNReal.ofReal hr
      _ = _ := by rw [ENNReal.ofReal_mul (sq_nonneg _)]; rfl
  have hvol : (volume : Measure UpperHalfPlane) =
      ((volume : Measure ℂ).comap UpperHalfPlane.coe).withDensity
        (fun z => (upperDensityNN z : ℝ≥0∞)) := UpperHalfPlane.volume_def
  rw [hvol, lintegral_withDensity_eq_lintegral_mul _ upperDensityNN_measurable.coe_nnreal_ennreal
    (by fun_prop : Measurable (fun z : UpperHalfPlane => ENNReal.ofReal (‖g z.re*h z.im‖^2)))]
  calc
    _ = ∫⁻ z : UpperHalfPlane, G (Complex.measurableEquivRealProd (z : ℂ))
        ∂((volume : Measure ℂ).comap UpperHalfPlane.coe) := lintegral_congr hpoint
    _ = ∫⁻ z : ℂ, G (Complex.measurableEquivRealProd z)
        ∂(((volume : Measure ℂ).comap UpperHalfPlane.coe).map UpperHalfPlane.coe) :=
      (UpperHalfPlane.measurableEmbedding_coe.lintegral_map _).symm
    _ = ∫⁻ z in Set.range (UpperHalfPlane.coe : UpperHalfPlane → ℂ),
        G (Complex.measurableEquivRealProd z) := by
      rw [UpperHalfPlane.measurableEmbedding_coe.map_comap]
    _ = ∫⁻ p in upperChart, G p := by
      rw [range_upperHalfPlane_coe_eq_chart_preimage]
      exact Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
        Complex.measurableEquivRealProd.measurableEmbedding G upperChart
    _ = horizontalSquareMass g * physicalHeightSquareMass h := by
      have hU : upperChart = (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
        ext p
        simp [upperChart]
      rw [hU, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
      exact lintegral_prod_mul hA.aemeasurable hB.aemeasurable

theorem unitPartition_horizontalSquareMass_le_two :
    horizontalSquareMass complexHorizontalPartition ≤ 2 := by
  have hpoint : ∀ x : ℝ, ENNReal.ofReal (‖complexHorizontalPartition x‖^2) ≤
      (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hx]
      have hn : ‖complexHorizontalPartition x‖^2 ≤ 1 := by
        nlinarith [complexHorizontalPartition_norm_le_one x, norm_nonneg (complexHorizontalPartition x)]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hn
    · have hz : complexHorizontalPartition x = 0 := by
        by_cases hlo : x ≤ -1
        · simp only [complexHorizontalPartition, horizontalUnitPartition_zero_left x hlo,
            Complex.ofReal_zero]
        · have hhi : 1 ≤ x := le_of_not_ge (fun h => hx ⟨(lt_of_not_ge hlo).le, h⟩)
          simp only [complexHorizontalPartition, horizontalUnitPartition_zero_right x hhi,
            Complex.ofReal_zero]
      simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero,
        indicator_of_notMem hx, le_refl]
  calc
    _ ≤ ∫⁻ x : ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) x := lintegral_mono hpoint
    _ = 2 := by
      rw [lintegral_indicator measurableSet_Icc, lintegral_const]
      simp [Real.volume_Icc]

theorem compactHeightLift_squareMass_eq (s : HeightSeed) :
    (∫⁻ z : UpperHalfPlane, ENNReal.ofReal (‖compactHeightLift s z‖^2)) =
      horizontalSquareMass complexHorizontalPartition * physicalHeightSquareMass s.toFun :=
  canonical_separated_squareMass complexHorizontalPartition s.toFun
    complexHorizontalPartition_cinfty.continuous.measurable s.continuous.measurable

theorem compactHeightLift_squareMass_le (s : HeightSeed) :
    (∫⁻ z : UpperHalfPlane, ENNReal.ofReal (‖compactHeightLift s z‖^2)) ≤
      2 * physicalHeightSquareMass s.toFun := by
  rw [compactHeightLift_squareMass_eq]
  exact mul_le_mul_right' unitPartition_horizontalSquareMass_le_two _

end
end ImbalancedChen.Part3.ZeroSeedHorizontalLiftMass20261026b
