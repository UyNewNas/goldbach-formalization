import ImbalancedChen.Part3ActualCoprimePhysicalHecke

-- SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-27.
-- The actual normalized local square relation is proved from literal branches.
-- No Hecke algebra relation, Fourier expansion or eigenfunction is assumed.

namespace ImbalancedChen.Part3.ActualPrimeSquarePhysicalHecke20261027
noncomputable section
open scoped BigOperators
open ActualMaassFourierODE20261026a ActualHeckeTranslationProjector20261026b
open ActualHeckeDivisibleFourier20261026b ActualCoprimePhysicalHecke20261026b
open PeriodicHeckeFiniteReindex20261026b

abbrev Plane := ℝ × ℝ

-- The p middle branches of the genuine determinant p squared formula.
def middleSquare (p : ℕ) (u : Plane → ℂ) (z : Plane) : ℂ :=
  ∑ b ∈ Finset.range p, u (z.1 + (b : ℝ)/(p : ℝ), z.2)

def rawPrimeSquare (p : ℕ) (u : Plane → ℂ) (z : Plane) : ℂ :=
  heckeUp (p*p) u z + middleSquare p u z + heckeDown (p*p) u z

-- The determinant p squared normalization is exactly p inverse.
def primeSquareExpression (p : ℕ) (u : Plane → ℂ) (z : Plane) : ℂ :=
  (p : ℂ)⁻¹ * rawPrimeSquare p u z

private theorem up_add (p : ℕ) (u v : Plane → ℂ) :
    heckeUp p (u+v) = heckeUp p u + heckeUp p v := rfl

private theorem down_add (p : ℕ) (u v : Plane → ℂ) :
    heckeDown p (u+v) = heckeDown p u + heckeDown p v := by
  funext z
  simp [heckeDown, translationSum, Finset.sum_add_distrib]

theorem heckeUp_heckeUp (p : ℕ) (u : Plane → ℂ) (z : Plane) :
    heckeUp p (heckeUp p u) z = heckeUp (p*p) u z := by
  unfold heckeUp
  apply congrArg u
  apply Prod.ext <;> push_cast <;> ring

theorem heckeUp_heckeDown (p : ℕ) (hp : 0 < p) (u : Plane → ℂ) (z : Plane) :
    heckeUp p (heckeDown p u) z = middleSquare p u z := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  change (∑ b ∈ Finset.range p,
    u (((p : ℝ)*z.1+(b : ℝ))/(p : ℝ), ((p : ℝ)*z.2)/(p : ℝ))) = _
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg u
  apply Prod.ext <;> dsimp <;> field_simp [hpR] <;> ring

-- The other mixed term is exactly p times the original value.
-- This is where ORIGINAL period one is used, at unchanged positive height.
theorem heckeDown_heckeUp (p : ℕ) (hp : 0 < p) (u : Plane → ℂ)
    (hper : ∀ x y : ℝ, 0 < y → u (x+1,y) = u (x,y))
    (z : Plane) (hz : 0 < z.2) :
    heckeDown p (heckeUp p u) z = (p : ℂ) * u z := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hf : Function.Periodic (fun x : ℝ => u (x,z.2)) 1 :=
    fun x => hper x z.2 hz
  have harg (b : ℕ) :
      ((p : ℝ)*((z.1+(b : ℝ))/(p : ℝ)), (p : ℝ)*(z.2/(p : ℝ))) =
        (z.1+(b : ℝ),z.2) := by
    apply Prod.ext <;> dsimp <;> field_simp [hpR] <;> ring
  change (∑ b ∈ Finset.range p,
    u ((p : ℝ)*((z.1+(b : ℝ))/(p : ℝ)), (p : ℝ)*(z.2/(p : ℝ)))) = _
  simp_rw [harg]
  have hshift (b : ℕ) : u (z.1+(b : ℝ),z.2) = u z := by
    simpa only [mul_one] using (hf.nat_mul b) z.1
  simp_rw [hshift]
  simp

-- Mixed-radix digits enumerate all p squared lower branches exactly once.
theorem heckeDown_heckeDown (p : ℕ) (hp : 0 < p) (u : Plane → ℂ) (z : Plane) :
    heckeDown p (heckeDown p u) z = heckeDown (p*p) u z := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  change (∑ a ∈ Finset.range p, ∑ b ∈ Finset.range p,
    u (((z.1+(a : ℝ))/(p : ℝ)+(b : ℝ))/(p : ℝ), (z.2/(p : ℝ))/(p : ℝ))) =
      ∑ r ∈ Finset.range (p*p), u ((z.1+(r : ℝ))/((p*p : ℕ) : ℝ),z.2/((p*p : ℕ) : ℝ))
  have harg (a b : ℕ) :
      (((z.1+(a : ℝ))/(p : ℝ)+(b : ℝ))/(p : ℝ), (z.2/(p : ℝ))/(p : ℝ)) =
        ((z.1+((a+p*b : ℕ) : ℝ))/((p*p : ℕ) : ℝ),z.2/((p*p : ℕ) : ℝ)) := by
    apply Prod.ext <;> push_cast <;> field_simp [hpR] <;> ring
  simp_rw [harg]
  exact finite_radix_sum p p
    (fun r => u ((z.1+(r : ℝ))/((p*p : ℕ) : ℝ),z.2/((p*p : ℕ) : ℝ)))

-- The full raw relation, with every geometric branch proved above.
theorem rawHecke_square (p : ℕ) (hp : 0 < p) (u : Plane → ℂ)
    (hper : ∀ x y : ℝ, 0 < y → u (x+1,y) = u (x,y))
    (z : Plane) (hz : 0 < z.2) :
    rawHecke p (rawHecke p u) z = rawPrimeSquare p u z + (p : ℂ)*u z := by
  change heckeUp p (heckeUp p u+heckeDown p u) z +
    heckeDown p (heckeUp p u+heckeDown p u) z = _
  rw [up_add, down_add]
  change (heckeUp p (heckeUp p u) z + heckeUp p (heckeDown p u) z) +
    (heckeDown p (heckeUp p u) z + heckeDown p (heckeDown p u) z) = _
  rw [heckeUp_heckeUp, heckeUp_heckeDown p hp,
    heckeDown_heckeUp p hp u hper z hz, heckeDown_heckeDown p hp]
  unfold rawPrimeSquare
  abel

theorem inverse_sqrt_square (p : ℕ) :
    (Real.sqrt (p : ℝ) : ℂ)⁻¹ * (Real.sqrt (p : ℝ) : ℂ)⁻¹ = (p : ℂ)⁻¹ := by
  have hs : (Real.sqrt (p : ℝ) : ℂ)^2 = (p : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg p)
  rw [← mul_inv, ← pow_two, hs]

-- Actual local normalized Hecke relation, with the identity coefficient one.
-- It needs only positive p and original unit periodicity; no prime axiom is used.
theorem primeHeckeExpression_square (p : ℕ) (hp : 0 < p) (u : Plane → ℂ)
    (hper : ∀ x y : ℝ, 0 < y → u (x+1,y) = u (x,y))
    (z : Plane) (hz : 0 < z.2) :
    primeHeckeExpression p (primeHeckeExpression p u) z =
      primeSquareExpression p u z + u z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
    rawHecke p ((Real.sqrt (p : ℝ) : ℂ)⁻¹ • rawHecke p u) z = _
  rw [rawHecke_smul]
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt (p : ℝ) : ℂ)⁻¹ * rawHecke p (rawHecke p u) z) = _
  rw [← mul_assoc, inverse_sqrt_square, rawHecke_square p hp u hper z hz]
  unfold primeSquareExpression
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hpC, one_mul]

end
end ImbalancedChen.Part3.ActualPrimeSquarePhysicalHecke20261027
