import ImbalancedChen.Part3PeriodicHeckeFiniteReindex
import ImbalancedChen.Part3ActualHeckeDivisibleFourier

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The ORIGINAL literal positive-height Hecke formula commutes at coprime
positive p,q for every original period-one function. Up/up branches agree
by real multiplication; down/down branches use genuine mixed-radix finite
reindexing; mixed branches use actual coprime residue permutations and
original integer periodicity. All real heights and the exact inverse
sqrt(p), inverse sqrt(q) normalizations remain explicit. No continuity,
PDE, spectral type, quotient eigenfunction or commutation premise occurs.
-/

namespace ImbalancedChen.Part3.ActualCoprimePhysicalHecke20261026b
noncomputable section
open Set
open scoped BigOperators
open ActualMaassFourierODE20261026a ActualHeckeTranslationProjector20261026b
open ActualHeckeDivisibleFourier20261026b PeriodicHeckeFiniteReindex20261026b

abbrev Plane := ℝ × ℝ

def rawHecke (p : ℕ) (u : Plane → ℂ) : Plane → ℂ := heckeUp p u+heckeDown p u

private theorem heckeUp_add (p : ℕ) (u v : Plane → ℂ) :
    heckeUp p (u+v)=heckeUp p u+heckeUp p v := rfl

private theorem heckeDown_add (p : ℕ) (u v : Plane → ℂ) :
    heckeDown p (u+v)=heckeDown p u+heckeDown p v := by
  funext z
  simp [heckeDown,translationSum,Finset.sum_add_distrib]

theorem rawHecke_smul (p : ℕ) (c : ℂ) (u : Plane → ℂ) :
    rawHecke p (c • u)=c • rawHecke p u := by
  funext z
  simp [rawHecke,heckeUp,heckeDown,translationSum,Finset.mul_sum,mul_add,smul_eq_mul]

private theorem heckeUp_up (p q : ℕ) (u : Plane → ℂ) (z : Plane) :
    heckeUp p (heckeUp q u) z=heckeUp q (heckeUp p u) z := by
  unfold heckeUp
  apply congrArg u
  apply Prod.ext <;> ring

/-- Exact lower/lower expansion: genuine physical y/(p*q), and a+p*b
runs every residue ONCE by the actual finite radix equivalence. -/
private theorem heckeDown_down_flat (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (u : Plane → ℂ) (z : Plane) :
    heckeDown p (heckeDown q u) z =
      ∑ r ∈ Finset.range (p*q),u ((z.1+(r : ℝ))/((p*q : ℕ) : ℝ),z.2/((p*q : ℕ) : ℝ)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  change (∑ a ∈ Finset.range p,∑ b ∈ Finset.range q,
    u (((z.1+(a : ℝ))/(p : ℝ)+(b : ℝ))/(q : ℝ),(z.2/(p : ℝ))/(q : ℝ))) = _
  have harg (a b : ℕ) : (((z.1+(a : ℝ))/(p : ℝ)+(b : ℝ))/(q : ℝ),(z.2/(p : ℝ))/(q : ℝ)) =
      ((z.1+((a+p*b : ℕ) : ℝ))/((p*q : ℕ) : ℝ),z.2/((p*q : ℕ) : ℝ)) := by
    apply Prod.ext <;> push_cast <;> field_simp [hpR,hqR] <;> ring
  simp_rw [harg]
  exact finite_radix_sum p q (fun r => u ((z.1+(r : ℝ))/((p*q : ℕ) : ℝ),z.2/((p*q : ℕ) : ℝ)))

private theorem heckeDown_down (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (u : Plane → ℂ) (z : Plane) :
    heckeDown p (heckeDown q u) z=heckeDown q (heckeDown p u) z := by
  rw [heckeDown_down_flat p q hp hq,heckeDown_down_flat q p hq hp,Nat.mul_comm q p]

/-- The mixed term is reindexed by multiplication by p modulo q. The
integer difference acts at the SAME genuine physical height p*y/q. -/
private theorem heckeUp_down (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (u : Plane → ℂ) (hper : ∀ x y : ℝ,0<y → u (x+1,y)=u (x,y))
    (z : Plane) (hz : 0 < z.2) :
    heckeUp p (heckeDown q u) z=heckeDown q (heckeUp p u) z := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  let f : ℝ → ℂ := fun x => u (x,(p : ℝ)*z.2/(q : ℝ))
  have hf : Function.Periodic f 1 := fun x => hper x _ (div_pos (mul_pos hpR hz) hqR)
  change (∑ b ∈ Finset.range q,u (((p : ℝ)*z.1+(b : ℝ))/(q : ℝ),((p : ℝ)*z.2)/(q : ℝ))) =
    ∑ b ∈ Finset.range q,u ((p : ℝ)*((z.1+(b : ℝ))/(q : ℝ)),(p : ℝ)*(z.2/(q : ℝ)))
  calc
    _ = ∑ b ∈ Finset.range q,f (((p : ℝ)*z.1+((p*b : ℕ) : ℝ))/(q : ℝ)) :=
      (periodic_coprime_residue_sum p q hq hpq f hf ((p : ℝ)*z.1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      unfold f
      congr 1
      apply Prod.ext <;> push_cast <;> field_simp [hpR.ne',hqR.ne'] <;> ring

/-- Original unnormalized positive-height coprime Hecke identity. Every
finite branch has been derived separately, with original periodicity only. -/
theorem rawHecke_coprime_commute (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (u : Plane → ℂ) (hper : ∀ x y : ℝ,0<y → u (x+1,y)=u (x,y))
    (z : Plane) (hz : 0 < z.2) :
    rawHecke p (rawHecke q u) z=rawHecke q (rawHecke p u) z := by
  change heckeUp p (heckeUp q u+heckeDown q u) z+heckeDown p (heckeUp q u+heckeDown q u) z =
    heckeUp q (heckeUp p u+heckeDown p u) z+heckeDown q (heckeUp p u+heckeDown p u) z
  rw [heckeUp_add,heckeDown_add,heckeUp_add,heckeDown_add]
  change (heckeUp p (heckeUp q u) z+heckeUp p (heckeDown q u) z)+
    (heckeDown p (heckeUp q u) z+heckeDown p (heckeDown q u) z) =
    (heckeUp q (heckeUp p u) z+heckeUp q (heckeDown p u) z)+
      (heckeDown q (heckeUp p u) z+heckeDown q (heckeDown p u) z)
  rw [heckeUp_up p q u z,heckeDown_down p q hp hq u z,
    heckeUp_down p q hp hq hpq u hper z hz,
    ← heckeUp_down q p hq hp hpq.symm u hper z hz]
  abel

/-- Exact product of the physical inverse square-root normalizations. -/
theorem physical_normalization_product (p q : ℕ) :
    (Real.sqrt (p : ℝ) : ℂ)⁻¹*(Real.sqrt (q : ℝ) : ℂ)⁻¹ =
      (Real.sqrt ((p*q : ℕ) : ℝ) : ℂ)⁻¹ := by
  rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg p),Complex.ofReal_mul,mul_inv]

/-- ORIGINAL literal normalized p^-1/2 formula, genuinely commuting for
all coprime positive p,q on all original unit-periodic positive charts. -/
theorem primeHeckeExpression_coprime_commute (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (u : Plane → ℂ)
    (hper : ∀ x y : ℝ,0<y → u (x+1,y)=u (x,y)) (z : Plane) (hz : 0 < z.2) :
    primeHeckeExpression p (primeHeckeExpression q u) z =
      primeHeckeExpression q (primeHeckeExpression p u) z := by
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
    rawHecke p ((Real.sqrt (q : ℝ) : ℂ)⁻¹ • rawHecke q u) z =
    (Real.sqrt (q : ℝ) : ℂ)⁻¹ *rawHecke q ((Real.sqrt (p : ℝ) : ℂ)⁻¹ • rawHecke p u) z
  rw [rawHecke_smul,rawHecke_smul]
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹*((Real.sqrt (q : ℝ) : ℂ)⁻¹*rawHecke p (rawHecke q u) z) =
    (Real.sqrt (q : ℝ) : ℂ)⁻¹*((Real.sqrt (p : ℝ) : ℂ)⁻¹*rawHecke q (rawHecke p u) z)
  rw [rawHecke_coprime_commute p q hp hq hpq u hper z hz]
  ring

/-- Equality on the genuine upper chart suffices in the literal finite
Hecke formula: all p-scaled and divided physical heights remain positive. -/
theorem primeHeckeExpression_congr_upper (p : ℕ) (hp : 0 < p) {u v : Plane → ℂ}
    (heq : ∀ z ∈ upperDomain,u z=v z) (z : Plane) (hz : 0 < z.2) :
    primeHeckeExpression p u z=primeHeckeExpression p v z := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  have hup := heq ((p : ℝ)*z.1,(p : ℝ)*z.2) (mul_pos hpR hz)
  have hdown : (∑ b ∈ Finset.range p,u ((z.1+(b : ℝ))/(p : ℝ),z.2/(p : ℝ))) =
      ∑ b ∈ Finset.range p,v ((z.1+(b : ℝ))/(p : ℝ),z.2/(p : ℝ)) := by
    exact Finset.sum_congr rfl (fun b hb => heq _ (div_pos hz hpR))
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹*(u ((p : ℝ)*z.1,(p : ℝ)*z.2)+
    ∑ b ∈ Finset.range p,u ((z.1+(b : ℝ))/(p : ℝ),z.2/(p : ℝ))) = _
  rw [hup,hdown]
  rfl

end
end ImbalancedChen.Part3.ActualCoprimePhysicalHecke20261026b

