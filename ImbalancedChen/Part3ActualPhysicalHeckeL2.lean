import ImbalancedChen.Part3ActualHeckeSecondL2
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The ORIGINAL physical quotient Hecke trace genuinely maps measurable L2
functions to L2. Finite Cauchy-Schwarz pays its norm mass, and the actual
finite correspondence carrier plus proved second-projection measure pay
the global integral. Neither trace L2 nor a Hecke boundedness premise is
assumed. The explicit squared-mass multiplier is (p+1)^2/p.
-/

namespace ImbalancedChen.Part3.ActualPhysicalHeckeL220261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeRealBranch20261026b
open ActualPrimeHeckeQuotientDescent20261026b ActualPoincareSpectralCoefficient20261026a
open ActualHeckeCorrespondenceCarrier20261026b ActualHeckeCanonicalCarrierMeasure20261026b
open ActualHeckeSecondProjection20261026b ActualHeckeSecondCoverMeasure20261026b
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a

theorem nativeHecke_measurable (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ) (hf : Measurable f) :
    Measurable (nativeHecke p hp f) := by
  letI : NeZero p := ⟨hp.ne'⟩
  apply measurable_const.mul
  exact Finset.univ.measurable_sum (fun j hj =>
    hf.comp (continuous_const_smul (branchSL p hp j)).measurable)

theorem quotientHecke_measurable (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) (hU : Measurable U) :
    Measurable (quotientHecke N p hp hpN U) := by
  apply measurable_from_quotient.mpr
  exact nativeHecke_measurable p hp.pos (testLift N U) (hU.comp (orbitProjection_measurable N))

theorem nativeHecke_norm_square_le (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ) (z : ℍ) :
    ‖nativeHecke p hp f z‖^2 ≤
      letI : NeZero p := ⟨hp.ne'⟩
      ((p+1 : ℝ)/(p : ℝ)) * ∑ j : Branch p, ‖f (branchSL p hp j • z)‖^2 := by
  letI : NeZero p := ⟨hp.ne'⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpR
  have hsum : ‖∑ j : Branch p, f (branchSL p hp j • z)‖^2 ≤
      (p+1 : ℝ)*∑ j : Branch p, ‖f (branchSL p hp j • z)‖^2 := by
    have ht := norm_sum_le (Finset.univ : Finset (Branch p)) (fun j => f (branchSL p hp j • z))
    have hsquare : ‖∑ j : Branch p, f (branchSL p hp j • z)‖^2 ≤
        (∑ j : Branch p, ‖f (branchSL p hp j • z)‖)^2 := by
      simpa only [pow_two] using mul_le_mul ht ht (norm_nonneg _)
        (Finset.sum_nonneg (fun j hj => norm_nonneg _))
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Branch p))
      (fun _ => (1 : ℝ)) (fun j => ‖f (branchSL p hp j • z)‖)
    exact hsquare.trans (by simpa [branch_card] using hCS)
  have hcoeff : ‖(Real.sqrt (p : ℝ) : ℂ)⁻¹‖^2 = (p : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
      ← inv_pow, Real.sq_sqrt hpR.le]
  change ‖(Real.sqrt (p : ℝ) : ℂ)⁻¹*(∑ j : Branch p, f (branchSL p hp j • z))‖^2 ≤ _
  rw [norm_mul, mul_pow, hcoeff]
  calc
    _ ≤ (p : ℝ)⁻¹*((p+1 : ℝ)*∑ j : Branch p, ‖f (branchSL p hp j • z)‖^2) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpR.le)
    _ = _ := by ring

theorem quotientHecke_sq_mass_le (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) (hU : Measurable U) :
    (∫⁻ q, ENNReal.ofReal (‖quotientHecke N p hp hpN U q‖^2) ∂carrierPushforward N) ≤
      ENNReal.ofReal ((p+1 : ℝ)/(p : ℝ)) *
        ((p+1 : ℝ≥0∞) * ∫⁻ q, ENNReal.ofReal (‖U q‖^2) ∂carrierPushforward N) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let E : Gamma0OrbitSpace N → ℝ≥0∞ := fun q => ENNReal.ofReal (‖U q‖^2)
  have hE : Measurable E := (hU.norm.pow_const 2).ennreal_ofReal
  let F : ℍ → ℝ≥0∞ := fun z => E (secondProjection N p hp hpN (orbitProjection (N*p) z))
  have hF : Measurable F := (hE.comp (secondProjection_measurable N p hp hpN)).comp (orbitProjection_measurable (N*p))
  have hcor := correspondenceCarrier_lintegral N p hp hpN F hF
  simp only [F, secondProjection_cover_branch] at hcor
  have hquot : (∫⁻ z in correspondenceCarrier N p hp hpN, F z) =
      ∫⁻ q, E (secondProjection N p hp hpN q) ∂carrierPushforward (N*p) := by
    rw [← correspondenceCarrier_pushforward_eq N p hp hpN,
      lintegral_cellPushforward (N*p) (correspondenceCarrier N p hp hpN) _
        (hE.comp (secondProjection_measurable N p hp hpN))]
  have hsecond := lintegral_map hE (secondProjection_measurable N p hp hpN)
    (μ := carrierPushforward (N*p))
  rw [secondProjection_map_measure N p hN hp hpN, lintegral_smul_measure] at hsecond
  have hpoint (z : ℍ) : ENNReal.ofReal (‖nativeHecke p hp.pos (testLift N U) z‖^2) ≤
      ENNReal.ofReal ((p+1 : ℝ)/(p : ℝ)) * ∑ j : Branch p,
        E (orbitProjection N (branchSL p hp.pos j • z)) := by
    have h := ENNReal.ofReal_le_ofReal (nativeHecke_norm_square_le p hp.pos (testLift N U) z)
    rw [ENNReal.ofReal_mul (div_nonneg (by positivity) hpR.le),
      ENNReal.ofReal_sum_of_nonneg (fun j hj => sq_nonneg _)] at h
    exact h
  rw [lintegral_reducedCarrier N _ ((quotientHecke_measurable N p hp hpN U hU).norm.pow_const 2).ennreal_ofReal]
  change (∫⁻ z in reducedCarrier N, ENNReal.ofReal (‖nativeHecke p hp.pos (testLift N U) z‖^2)) ≤ _
  calc
    _ ≤ ∫⁻ z in reducedCarrier N, ENNReal.ofReal ((p+1 : ℝ)/(p : ℝ)) *
        ∑ j : Branch p, E (orbitProjection N (branchSL p hp.pos j • z)) := lintegral_mono hpoint
    _ = ENNReal.ofReal ((p+1 : ℝ)/(p : ℝ)) * ∫⁻ z in correspondenceCarrier N p hp hpN, F z := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact congrArg (fun a : ℝ≥0∞ => ENNReal.ofReal ((p+1 : ℝ)/(p : ℝ))*a) hcor.symm
    _ = _ := by rw [hquot, ← hsecond]

/-- Genuine L2 mapping of the original physical trace, with no trace
norm or bounded-Hecke premise. Measurability concerns only original U. -/
theorem quotientHecke_memLp (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) (hU : Measurable U) (hU2 : MemLp U 2 (carrierPushforward N)) :
    MemLp (quotientHecke N p hp hpN U) 2 (carrierPushforward N) := by
  have hsq := (memLp_two_iff_integrable_sq_norm hU2.aestronglyMeasurable).mp hU2
  have hmass : (∫⁻ q, ENNReal.ofReal (‖U q‖^2) ∂carrierPushforward N) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg (‖U q‖)))).mp hsq.hasFiniteIntegral
  have hfin : (∫⁻ q, ENNReal.ofReal (‖quotientHecke N p hp hpN U q‖^2) ∂carrierPushforward N) < ∞ :=
    (quotientHecke_sq_mass_le N p hN hp hpN U hU).trans_lt
      (ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top (by simp) hmass))
  have hT := quotientHecke_measurable N p hp hpN U hU
  apply (memLp_two_iff_integrable_sq_norm hT.aestronglyMeasurable).mpr
  exact ⟨(hT.norm.pow_const 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg _))).mpr hfin⟩

end
end ImbalancedChen.Part3.ActualPhysicalHeckeL220261026b
