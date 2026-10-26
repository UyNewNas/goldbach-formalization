import ImbalancedChen.Part3ActualHeckeDivisibleFourier

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The upper Hecke dilation branch has no Fourier coefficient at an index not
divisible by p. This is proved from its actual fractional period 1/p and
the faithful unit-circle character, not assumed from a Fourier expansion.
This completes the branches needed for the literal all-index normalized
prime-Hecke coefficient identity. No Gamma automorphy input.
-/

namespace ImbalancedChen.Part3.ActualHeckeNondivisibleFourier20261026b
noncomputable section
open Set MeasureTheory
open ActualMaassFourierODE20261026a ActualHeckeTranslationProjector20261026b
open ActualHeckeDivisibleFourier20261026b

theorem phase_add (n : ℤ) (x a : ℝ) : phase n (x+a) = phase n x * phase n a := by
  simp only [phase, AddCircle.coe_add, AddCircle.fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul]

/-- Faithfulness of the actual circle character detects integer
divisibility. The integer index may be positive, negative, or zero. -/
theorem phase_reciprocal_ne_one (p : ℕ) (hp : 0 < p) (n : ℤ)
    (hn : ¬ (p : ℤ) ∣ n) : phase n (1/(p : ℝ)) ≠ 1 := by
  intro hphase
  have hc : AddCircle.toCircle ((-n) • ((1/(p : ℝ) : ℝ) : UnitAddCircle)) =
      (1 : Circle) := Subtype.ext hphase
  have hz : (-n) • ((1/(p : ℝ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0))
      (by simpa only [AddCircle.toCircle_zero] using hc)
  rw [← AddCircle.coe_zsmul] at hz
  have hq : (((-(n : ℝ)/(p : ℝ) : ℝ)) : UnitAddCircle) = 0 := by
    simpa [zsmul_eq_mul, div_eq_mul_inv] using hz
  obtain ⟨k, hk⟩ := AddCircle.coe_eq_zero_iff.mp hq
  simp only [zsmul_eq_mul, mul_one] at hk
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hreal : (n : ℝ) = (p : ℝ) * (-(k : ℝ)) := by
    have h := (eq_div_iff hpR).mp hk
    nlinarith
  apply hn
  refine ⟨-k, ?_⟩
  exact_mod_cast hreal

/-- A genuine fractional period forces the absent Fourier coefficient
to vanish. No coefficient support rule is supplied as an assumption. -/
theorem literalCoefficient_nat_dilation_eq_zero (p : ℕ) (hp : 0 < p)
    (f : ℝ → ℂ) (hper : Function.Periodic f 1) (n : ℤ)
    (hn : ¬ (p : ℤ) ∣ n) :
    literalCoefficient (fun x => f ((p : ℝ)*x)) n = 0 := by
  let g : ℝ → ℂ := fun x => f ((p : ℝ)*x)
  let H : ℝ → ℂ := fun x => phase n x * g x
  let c : ℂ := phase n (1/(p : ℝ))
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hg : Function.Periodic g 1 := by
    intro x
    have h := hper.nat_mul p ((p : ℝ)*x)
    convert h using 1 <;> dsimp [g] <;> congr 1 <;> ring
  have hgf (x : ℝ) : g (x+1/(p : ℝ)) = g x := by
    have harg : (p : ℝ)*(x+1/(p : ℝ)) = (p : ℝ)*x+1 := by
      field_simp [hpR] <;> ring
    exact (congrArg f harg).trans (hper _)
  have hHp : Function.Periodic H 1 := by
    intro x
    change phase n (x+1) * g (x+1) = phase n x * g x
    rw [hg x]
    have hph : phase n (x+1) = phase n x := by
      simpa only [Int.cast_neg, Int.cast_one, sub_neg_eq_add] using phase_sub_int n (-1) x
    rw [hph]
  have hpoint (x : ℝ) : H (x+1/(p : ℝ)) = c * H x := by
    change phase n (x+1/(p : ℝ)) * g (x+1/(p : ℝ)) =
      phase n (1/(p : ℝ)) * (phase n x * g x)
    rw [phase_add, hgf]
    ring
  have hshift : (∫ x in (0 : ℝ)..1, H (x+1/(p : ℝ))) = ∫ x in (0 : ℝ)..1, H x := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm 1 (1/(p : ℝ))] using
      hHp.intervalIntegral_add_eq (1/(p : ℝ)) 0
  have hfix : c * (∫ x in (0 : ℝ)..1, H x) = ∫ x in (0 : ℝ)..1, H x := by
    rw [← intervalIntegral.integral_const_mul]
    have heq : (fun x => c * H x) = fun x => H (x+1/(p : ℝ)) :=
      funext (fun x => (hpoint x).symm)
    rw [heq]
    exact hshift
  have hzero : (c-1) * (∫ x in (0 : ℝ)..1, H x) = 0 := by
    linear_combination hfix
  have hc : c-1 ≠ 0 := sub_ne_zero.mpr (phase_reciprocal_ne_one p hp n hn)
  exact (mul_eq_zero.mp hzero).resolve_left hc

theorem coefficient_heckeUp_nondivisible (p : ℕ) (hp : 0 < p)
    {u : ℝ × ℝ → ℂ}
    (hper : ∀ x y : ℝ, 0 < y → u (x+1,y) = u (x,y))
    (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) {y : ℝ} (hy : 0 < y) :
    coefficient (heckeUp p u) n y = 0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  simpa only [literalCoefficient, coefficient, periodIntegral_eq_interval, phased, heckeUp] using
    literalCoefficient_nat_dilation_eq_zero p hp (fun x => u (x,(p : ℝ)*y))
      (fun x => hper x _ (mul_pos hpR hy)) n hn

end
end ImbalancedChen.Part3.ActualHeckeNondivisibleFourier20261026b
