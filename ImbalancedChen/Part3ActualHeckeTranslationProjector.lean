import ImbalancedChen.Part3ActualMaassFourierODE

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The literal lower-triangular Hecke translation sum has Fourier coefficient
p times the original coefficient at index p*n and physical height y/p.
The p factor is proved by affine substitution and an actual partition of
[0,1]. No coefficient identity, periodicity, or spectral expansion is input
to the one-dimensional identity. No Gamma automorphy is asserted here.
-/

namespace ImbalancedChen.Part3.ActualHeckeTranslationProjector20261026b
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ActualMaassFourierODE20261026a

def literalCoefficient (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, phase n x * f x

def translationSum (p : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ b ∈ Finset.range p, f ((x+(b : ℝ))/(p : ℝ))

theorem phase_nat_mul (p : ℕ) (n : ℤ) (x : ℝ) :
    phase n ((p : ℝ)*x) = phase ((p : ℤ)*n) x := by
  simp only [phase, AddCircle.fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem phase_sub_int (n b : ℤ) (x : ℝ) : phase n (x-(b : ℝ)) = phase n x := by
  have hb : ((b : ℝ) : UnitAddCircle) = 0 :=
    AddCircle.coe_eq_zero_iff.mpr ⟨b, by simp [zsmul_eq_mul]⟩
  simp only [phase, AddCircle.coe_sub, hb, sub_zero]

/-- One actual affine subinterval of the translation-sum integral. -/
theorem translationTerm_integral (p : ℕ) (hp : 0 < p) (f : ℝ → ℂ)
    (n : ℤ) (b : ℕ) :
    (∫ x in (0 : ℝ)..1, phase n x * f ((x+(b : ℝ))/(p : ℝ))) =
      (p : ℝ) • ∫ t in (b : ℝ)/(p : ℝ)..((b : ℝ)+1)/(p : ℝ),
        phase ((p : ℤ)*n) t * f t := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  let H : ℝ → ℂ := fun t => phase ((p : ℤ)*n) t * f t
  have heq (x : ℝ) : phase n x * f ((x+(b : ℝ))/(p : ℝ)) =
      H (x/(p : ℝ)+(b : ℝ)/(p : ℝ)) := by
    have harg : (p : ℝ)*((x+(b : ℝ))/(p : ℝ))-(b : ℝ) = x := by
      field_simp [hpR]
      ring
    have hphase : phase n x = phase ((p : ℤ)*n) ((x+(b : ℝ))/(p : ℝ)) := by
      calc
        phase n x = phase n ((p : ℝ)*((x+(b : ℝ))/(p : ℝ))-(b : ℝ)) :=
          congrArg (phase n) harg.symm
        _ = phase n ((p : ℝ)*((x+(b : ℝ))/(p : ℝ))) := by
          simpa only [Int.cast_natCast] using phase_sub_int n (b : ℤ)
            ((p : ℝ)*((x+(b : ℝ))/(p : ℝ)))
        _ = _ := phase_nat_mul p n _
    simp only [H, hphase, ← add_div]
  simp_rw [heq]
  simpa only [zero_div, zero_add, ← add_div, add_comm 1 (b : ℝ)] using
    (intervalIntegral.integral_comp_div_add H hpR ((b : ℝ)/(p : ℝ)) (a := 0) (b := 1))

/-- Finite translation sum = the exact p-fold coefficient transfer.
Continuity pays for every partition integral; the Jacobian was proved above. -/
theorem literalCoefficient_translationSum (p : ℕ) (hp : 0 < p)
    (f : ℝ → ℂ) (hf : Continuous f) (n : ℤ) :
    literalCoefficient (translationSum p f) n =
      (p : ℝ) • literalCoefficient f ((p : ℤ)*n) := by
  have hi (b : ℕ) : IntervalIntegrable
      (fun x => phase n x * f ((x+(b : ℝ))/(p : ℝ))) volume 0 1 :=
    ((phase_continuous n).mul (hf.comp (by fun_prop))).intervalIntegrable _ _
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun b : ℕ => (b : ℝ)/(p : ℝ)) (n := p)
    (f := fun t => phase ((p : ℤ)*n) t * f t)
    (fun b hb => ((phase_continuous _).mul hf).intervalIntegrable _ _)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [Nat.cast_zero, zero_div, div_self hpR] at hpart
  unfold literalCoefficient translationSum
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun b hb => hi b)]
  simp_rw [translationTerm_integral p hp f n]
  rw [← Finset.smul_sum]
  congr 1
  convert hpart using 1 <;> simp only [Nat.cast_add, Nat.cast_one]

def heckeDown (p : ℕ) (u : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  translationSum p (fun x => u (x,z.2/(p : ℝ))) z.1

/-- Applied to the literal native Maass coefficient. The original physical
height is y/p, and the original Fourier index is p*n. -/
theorem coefficient_heckeDown (p : ℕ) (hp : 0 < p) {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u upperDomain) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (heckeDown p u) n y =
      (p : ℝ) • coefficient u ((p : ℤ)*n) (y/(p : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  simpa only [literalCoefficient, coefficient, periodIntegral_eq_interval,
    phased, heckeDown] using literalCoefficient_translationSum p hp
      (fun x => u (x,y/(p : ℝ))) (continuous_slice hu (div_pos hy hpR)) n

end
end ImbalancedChen.Part3.ActualHeckeTranslationProjector20261026b
