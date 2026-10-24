import ImbalancedChen.Part3RealEisensteinSeedConvergence
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

This file constructs the genuine real-`s` primitive-pair Eisenstein sum for the
full modular group, with the classical factor `1/2` because `(c,d)` and
`(-c,-d)` give the same summand. Its automorphy is derived from the literal
Möbius action, the imaginary-part denominator formula, and Mathlib's
`gammaSetEquiv` bijection of primitive integer pairs. The real-`s > 1`
summability input comes from `Part3RealEisensteinSeedConvergence`.

No Laplace eigenvalue, differentiation under the sum, spectral continuation,
or Kuznetsov formula is asserted here.
-/

namespace ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy

noncomputable section

open Complex UpperHalfPlane EisensteinSeries Matrix
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.RealEisensteinSeedConvergence

private theorem quotient_seed_cancel (y A R s : ℝ)
    (hy : 0 ≤ y) (hA : 0 ≤ A) (hR : 0 < R) :
    (y / R ^ 2) ^ s * (A / R) ^ (-(2 * s)) =
      y ^ s * A ^ (-(2 * s)) := by
  rw [Real.div_rpow hy (sq_nonneg R) s,
    Real.div_rpow hA hR.le (-(2 * s))]
  have hpow : (R ^ 2) ^ s = R ^ (2 * s) := by
    simpa only [Real.rpow_natCast] using (Real.rpow_mul hR.le 2 s).symm
  rw [hpow, Real.rpow_neg hR.le (2 * s)]
  have hRp : R ^ (2 * s) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
  field_simp [hRp] <;> ring

/-- The complex linear denominator transforms by the exact Möbius factor.
This is the weight `-1` case of Mathlib's literal lattice-term identity;
there is no assumption of Eisenstein automorphy. -/
private theorem linear_apply (v : Fin 2 → ℤ) (γ : SL(2, ℤ)) (z : ℍ) :
    (v 0 : ℂ) * (γ • z : ℂ) + (v 1 : ℂ) =
      (UpperHalfPlane.denom γ z)⁻¹ *
        ((v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 * (z : ℂ) +
          (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1) := by
  simpa [EisensteinSeries.eisSummand] using
    (EisensteinSeries.eisSummand_SL2_apply (-1) v γ z)

/-- Transformation of the actual real-parameter seed under every modular
matrix. The numerator contributes `|cz+d|^(-2s)` and the denominator of the
linear form contributes its reciprocal, leaving the relabelled pair. -/
theorem seed_SL2_apply (s : ℝ) (v : Fin 2 → ℤ)
    (γ : SL(2, ℤ)) (z : ℍ) :
    seed s (γ • z) v =
      seed s z (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  let D : ℂ := UpperHalfPlane.denom γ z
  let T : Fin 2 → ℤ := v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
  have hD : 0 < ‖D‖ := norm_pos_iff.mpr (UpperHalfPlane.denom_ne_zero γ z)
  have him : (γ • z).im = z.im / ‖D‖ ^ 2 := by
    rw [UpperHalfPlane.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  have hlin : (v 0 : ℂ) * (γ • z : ℂ) + (v 1 : ℂ) =
      D⁻¹ * ((T 0 : ℂ) * (z : ℂ) + (T 1 : ℂ)) := by
    exact linear_apply v γ z
  have hnorm : ‖(v 0 : ℂ) * (γ • z : ℂ) + (v 1 : ℂ)‖ =
      ‖(T 0 : ℂ) * (z : ℂ) + (T 1 : ℂ)‖ / ‖D‖ := by
    rw [hlin, norm_mul, norm_inv, div_eq_mul_inv]
    ring
  change (γ • z).im ^ s *
      ‖(v 0 : ℂ) * (γ • z : ℂ) + (v 1 : ℂ)‖ ^ (-(2 * s)) =
    z.im ^ s * ‖(T 0 : ℂ) * (z : ℂ) + (T 1 : ℂ)‖ ^ (-(2 * s))
  rw [him, hnorm]
  exact quotient_seed_cancel z.im
    ‖(T 0 : ℂ) * (z : ℂ) + (T 1 : ℂ)‖ ‖D‖ s
    z.im_pos.le (norm_nonneg _) hD

/-- Mathlib's actual primitive-pair action, specialized to the full modular
group. The congruence label is unique modulo one. -/
def primitivePairEquiv (γ : SL(2, ℤ)) :
    EisensteinSeries.gammaSet 1 1 0 ≃ EisensteinSeries.gammaSet 1 1 0 := by
  simpa only [Matrix.zero_vecMul] using
    (EisensteinSeries.gammaSetEquiv (N := 1) (r := 1)
      (0 : Fin 2 → ZMod 1) γ)

/-- The classical primitive-pair real Eisenstein series, normalized by `1/2`
to count the two signs of a primitive pair once. -/
def primitiveEisenstein (s : ℝ) (z : ℍ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑' v : EisensteinSeries.gammaSet 1 1 0, seed s z v.1

/-- The two oriented representatives of a primitive pair have the same seed. -/
theorem seed_neg (s : ℝ) (z : ℍ) (v : Fin 2 → ℤ) :
    seed s z (-v) = seed s z v := by
  have hlin : ((-v) 0 : ℂ) * (z : ℂ) + ((-v) 1 : ℂ) =
      -((v 0 : ℂ) * (z : ℂ) + (v 1 : ℂ)) := by
    simp [Pi.neg_apply] <;> ring
  simp only [seed, hlin, norm_neg]

/-- Full modular automorphy of the actual absolutely convergent primitive
real-`s` series. The reindexing is valid for `s > 1` by seed summability. -/
theorem primitiveEisenstein_SL2_invariant (s : ℝ) (hs : 1 < s)
    (γ : SL(2, ℤ)) (z : ℍ) :
    primitiveEisenstein s (γ • z) = primitiveEisenstein s z := by
  have habs : Summable (fun v : EisensteinSeries.gammaSet 1 1 0 => seed s z v.1) :=
    primitiveSeed_summable s hs z
  have hsum :
      (∑' v : EisensteinSeries.gammaSet 1 1 0, seed s (γ • z) v.1) =
      (∑' v : EisensteinSeries.gammaSet 1 1 0, seed s z v.1) := by
    calc
      _ = ∑' v : EisensteinSeries.gammaSet 1 1 0,
            seed s z (v.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
              congr 1
              funext v
              exact seed_SL2_apply s v.1 γ z
      _ = ∑' v : EisensteinSeries.gammaSet 1 1 0, seed s z v.1 := by
            simpa [primitivePairEquiv, EisensteinSeries.gammaSetEquiv] using
              (primitivePairEquiv γ).tsum_eq
                (fun v : EisensteinSeries.gammaSet 1 1 0 => seed s z v.1)
  simpa only [primitiveEisenstein] using congrArg ((1 / 2 : ℝ) * ·) hsum

end

end ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy
