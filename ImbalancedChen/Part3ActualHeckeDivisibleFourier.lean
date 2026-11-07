import ImbalancedChen.Part3ActualHeckeTranslationProjector
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual upper dilation branch is evaluated at every divisible Fourier
index p*m. Combined with the proved lower translation projector this gives
the exact p^-1/2 two-branch prime-Hecke expression, including both physical
heights. Periodicity is an input about the original function only. The raw
identity needs no prime or level condition; Gamma automorphy is separate.
-/

namespace ImbalancedChen.Part3.ActualHeckeDivisibleFourier20261026b
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ActualMaassFourierODE20261026a ActualHeckeTranslationProjector20261026b

/-- Integer Fourier phase and actual unit periodicity pay for the entire
p-period integral. No divisibility-supported Fourier ansatz is assumed. -/
theorem literalCoefficient_nat_dilation (p : ℕ) (hp : 0 < p)
    (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1) (m : ℤ) :
    literalCoefficient (fun x => f ((p : ℝ)*x)) ((p : ℤ)*m) = literalCoefficient f m := by
  let H : ℝ → ℂ := fun t => phase m t * f t
  have hH : Continuous H := (phase_continuous m).mul hf
  have hphase : Function.Periodic (phase m) 1 := by
    intro x
    simpa only [Int.cast_neg, Int.cast_one, sub_neg_eq_add] using phase_sub_int m (-1) x
  have hHp : Function.Periodic H 1 := by
    intro x
    dsimp [H]
    rw [hphase x, hper x]
  have hlong : (∫ t in (0 : ℝ)..(p : ℝ), H t) =
      (p : ℝ) • ∫ t in (0 : ℝ)..1, H t := by
    simpa [zsmul_eq_mul, Complex.real_smul] using hHp.intervalIntegral_add_zsmul_eq (p : ℤ) 0
        (fun a b => hH.intervalIntegrable a b)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold literalCoefficient
  simp_rw [← phase_nat_mul p m]
  change (∫ x in (0 : ℝ)..1, H ((p : ℝ)*x)) = ∫ t in (0 : ℝ)..1, H t
  rw [intervalIntegral.integral_comp_mul_left H hpR, mul_zero, mul_one, hlong,
    smul_smul, inv_mul_cancel₀ hpR, one_smul]

def heckeUp (p : ℕ) (u : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  u ((p : ℝ)*z.1, (p : ℝ)*z.2)

def primeHeckeExpression (p : ℕ) (u : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  (Real.sqrt (p : ℝ) : ℂ)⁻¹ * (heckeUp p u z + heckeDown p u z)

theorem heckeDown_slice_continuous (p : ℕ) (hp : 0 < p) {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u upperDomain) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => heckeDown p u (x,y)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold heckeDown translationSum
  exact continuous_finset_sum _ (fun b hb =>
    (continuous_slice hu (div_pos hy hpR)).comp (by fun_prop))

theorem coefficient_heckeUp_divisible (p : ℕ) (hp : 0 < p) {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u upperDomain)
    (hper : ∀ x y : ℝ, 0 < y → u (x+1,y) = u (x,y))
    (m : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (heckeUp p u) ((p : ℤ)*m) y = coefficient u m ((p : ℝ)*y) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  simpa only [literalCoefficient, coefficient, periodIntegral_eq_interval,
    phased, heckeUp] using literalCoefficient_nat_dilation p hp
      (fun x => u (x,(p : ℝ)*y)) (continuous_slice hu (mul_pos hpR hy))
      (fun x => hper x _ (mul_pos hpR hy)) m

/-- Literal two-branch Hecke coefficient at index p*m. The level condition
p not dividing N is only needed by the separate Gamma automorphy theorem. -/
theorem coefficient_primeHeckeExpression_divisible (p : ℕ) (hp : 0 < p)
    {u : ℝ × ℝ → ℂ} (hu : ContinuousOn u upperDomain)
    (hper : ∀ x y : ℝ, 0 < y → u (x+1,y) = u (x,y))
    (m : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (primeHeckeExpression p u) ((p : ℤ)*m) y =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
        (coefficient u m ((p : ℝ)*y) +
          (p : ℂ) * coefficient u ((p : ℤ)*((p : ℤ)*m)) (y/(p : ℝ))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hup : Continuous (fun x => heckeUp p u (x,y)) :=
    (continuous_slice hu (mul_pos hpR hy)).comp (by fun_prop)
  have hdown := heckeDown_slice_continuous p hp hu hy
  have hlinear : coefficient (primeHeckeExpression p u) ((p : ℤ)*m) y =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
        (coefficient (heckeUp p u) ((p : ℤ)*m) y +
          coefficient (heckeDown p u) ((p : ℤ)*m) y) := by
    simp only [coefficient, periodIntegral_eq_interval, phased, primeHeckeExpression]
    calc
      _ = ∫ x in (0 : ℝ)..1, (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
          (phase ((p : ℤ)*m) x * heckeUp p u (x,y) +
            phase ((p : ℤ)*m) x * heckeDown p u (x,y)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          (((phase_continuous _).mul hup).intervalIntegrable 0 1)
          (((phase_continuous _).mul hdown).intervalIntegrable 0 1)]
  rw [hlinear, coefficient_heckeUp_divisible p hp hu hper m hy,
    coefficient_heckeDown p hp hu _ hy, Complex.real_smul]

end
end ImbalancedChen.Part3.ActualHeckeDivisibleFourier20261026b
