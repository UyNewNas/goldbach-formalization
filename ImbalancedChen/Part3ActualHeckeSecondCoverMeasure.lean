import ImbalancedChen.Part3ActualFrickeQuotientMeasure
import ImbalancedChen.Part3ActualHeckeSecondProjection

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual second Hecke correspondence projection has canonical quotient
pushforward degree p+1. Literal matrix algebra proves W_(Np)=W_N*B_inf,
then the actual projection is Fricke_N composed with forgetPrimeLevel
composed with Fricke_(Np). Both Fricke quotient measure laws and the
relative-cover degree were independently proved; no adjoint symmetry or
second projection measure is supplied as an assumption.
-/

namespace ImbalancedChen.Part3.ActualHeckeSecondCoverMeasure20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open FrickeNormalizer ActualFrickeQuotientMeasure20261026b
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeRealBranch20261026b
open ActualHeckeSecondProjection20261026b ActualHeckeForgetCoverMeasure20261026b
open Gamma0QuotientCellPushforward20261025a

/-- Actual level-product Fricke factorization, retaining every original
square-root scaling factor of both Fricke matrices and the Hecke branch. -/
theorem fricke_product_level_factor (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    frickeSL (N*p) (Nat.mul_pos hN hp) = frickeSL N hN * branchSL p hp none := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hNs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNr).ne'
  have hps : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpr).ne'
  have hroot : Real.sqrt ((N*p : ℕ) : ℝ) = Real.sqrt (N : ℝ)*Real.sqrt (p : ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul hNr.le]
  have hpdiv : (Real.sqrt (p : ℝ))⁻¹*(p : ℝ) = Real.sqrt (p : ℝ) := by
    simpa only [div_eq_mul_inv, mul_comm] using (Real.div_sqrt (x := (p : ℝ)))
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeSL, frickeMatrix, branchSL, branchRealMatrix, branchMatrix,
      coe_mul, Matrix.mul_fin_two, hroot, hpdiv, smul_eq_mul] <;>
    field_simp [hNs,hps] <;> ring

theorem fricke_double_level_action (N p : ℕ) (hN : 0 < N) (hp : 0 < p) (z : ℍ) :
    frickeSL N hN • (frickeSL (N*p) (Nat.mul_pos hN hp) • z) = branchSL p hp none • z := by
  rw [fricke_product_level_factor, mul_smul, frickeSL_action_involutive N hN]

/-- Exact identity of the two actual quotient correspondence maps. -/
theorem secondProjection_fricke_factor (N p : ℕ) (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    secondProjection N p hp hpN = quotientFricke N hN ∘ forgetPrimeLevel N p ∘
      quotientFricke (N*p) (Nat.mul_pos hN hp.pos) := by
  funext q
  refine Quotient.inductionOn q (fun z => ?_)
  simp only [Function.comp_apply, quotientFricke_projection, forgetPrimeLevel_projection,
    secondProjection_projection, fricke_double_level_action N p hN hp.pos]

/-- FULL actual second-projection measure, with the same canonical
quotient measures and the same degree p+1 as the first projection. -/
theorem secondProjection_map_measure (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    (carrierPushforward (N*p)).map (secondProjection N p hp hpN) =
      (p+1 : ℝ≥0∞) • carrierPushforward N := by
  calc
    _ = (((carrierPushforward (N*p)).map (quotientFricke (N*p) (Nat.mul_pos hN hp.pos))).map
        (forgetPrimeLevel N p)).map (quotientFricke N hN) := by
      rw [Measure.map_map (forgetPrimeLevel_measurable N p)
          (quotientFricke_measurable (N*p) (Nat.mul_pos hN hp.pos)),
        Measure.map_map (quotientFricke_measurable N hN)
          ((forgetPrimeLevel_measurable N p).comp (quotientFricke_measurable (N*p) (Nat.mul_pos hN hp.pos))),
        secondProjection_fricke_factor N p hN hp hpN]
    _ = ((p+1 : ℝ≥0∞) • carrierPushforward N).map (quotientFricke N hN) := by
      rw [quotientFricke_map_measure, forgetPrimeLevel_map_measure N p hp hpN]
    _ = _ := by rw [Measure.map_smul, quotientFricke_map_measure]

end
end ImbalancedChen.Part3.ActualHeckeSecondCoverMeasure20261026b
