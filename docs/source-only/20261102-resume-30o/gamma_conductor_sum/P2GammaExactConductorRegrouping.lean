import ImbalancedChen.P2GammaConvolutionLargeConductor

/-!
SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.

The conductor and quotient are independent integer indices. No coprimality
between them is imposed. The two coefficient rows are selected before either
index, and both induced unit projectors remain in the exact identity.
-/

namespace ImbalancedChen.P2GammaExactConductorRegrouping
noncomputable section
open scoped Classical BigOperators
open AnalyticNumberTheory.LargeSieve
open P2GammaInducedCharacterDictionary P2GammaConvolutionLargeConductor

/-- The unique primitive induction datum at a fixed positive level. -/
def InductionDatum (q : ℕ) :=
  Σ r : {r : ℕ // r ∈ nonprincipalConductors q}, PrimitiveCharacter r.1

def induce {q : ℕ} (p : InductionDatum q) : DirichletCharacter ℂ q :=
  DirichletCharacter.changeLevel
    ((Nat.mem_divisors.mp (Finset.mem_filter.mp p.1.2).1).1) p.2.1

theorem induce_conductor {q : ℕ} (hq : 0<q) (p : InductionDatum q) :
    (induce p).conductor=p.1.1 := by
  let : NeZero q := ⟨hq.ne'⟩
  simp only [induce,DirichletCharacter.conductor_changeLevel,primitive_conductor]

theorem induce_injective {q : ℕ} (hq : 0<q) :
    Function.Injective (induce (q:=q)) := by
  let : NeZero q := ⟨hq.ne'⟩
  intro p p' h
  have hbase : p.1=p'.1 := Subtype.ext (by
    rw [← induce_conductor hq p,← induce_conductor hq p']
    exact congrArg (fun chi => chi.conductor) h)
  rcases p with ⟨⟨r,hmem⟩,psi⟩
  rcases p' with ⟨⟨r',hmem'⟩,psi'⟩
  cases hbase
  have hp : psi=psi' := by
    apply Subtype.ext
    apply DirichletCharacter.changeLevel_injective
      ((Nat.mem_divisors.mp (Finset.mem_filter.mp hmem).1).1)
    exact h
  cases hp
  rfl

theorem induce_nonprincipal {q : ℕ} (hq : 0<q) (p : InductionDatum q) :
    induce p ∈ nonprincipalCharacters q := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [mem_nonprincipalCharacters_iff_conductor_ne_one,induce_conductor hq]
  have hr := (Finset.mem_filter.mp p.1.2).2
  omega

def encode {q : ℕ} (hq : 0<q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ∈ nonprincipalCharacters q) :
    InductionDatum q := by
  let : NeZero q := ⟨hq.ne'⟩
  refine ⟨⟨chi.conductor,?_⟩,conductorPrimitiveCharacter chi⟩
  have hc0 : 0<chi.conductor :=
    Nat.pos_of_dvd_of_pos chi.conductor_dvd_level hq
  have hc1 := mem_nonprincipalCharacters_iff_conductor_ne_one.mp hchi
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨chi.conductor_dvd_level,hq.ne'⟩,by omega⟩

@[simp] theorem induce_encode {q : ℕ} (hq : 0<q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ∈ nonprincipalCharacters q) :
    induce (encode hq chi hchi)=chi :=
  changeLevel_conductorPrimitiveCharacter chi

/-- Existence and uniqueness include the conductor, not just the character
at a conductor supplied as an extra premise. -/
theorem existsUnique_primitive_induction {q : ℕ} (hq : 0<q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ∈ nonprincipalCharacters q) :
    ∃! p : InductionDatum q, induce p=chi := by
  refine ⟨encode hq chi hchi,induce_encode hq chi hchi,?_⟩
  intro p hp
  exact induce_injective hq (hp.trans (induce_encode hq chi hchi).symm)

/-- Arbitrary level-dependent summands, rather than a function which was
already assumed to depend only on the conductor. -/
theorem sum_nonprincipal_induced {q : ℕ} (hq : 0<q)
    (F : DirichletCharacter ℂ q → ℝ) :
    (∑ chi ∈ nonprincipalCharacters q,F chi) =
      ∑ r ∈ (nonprincipalConductors q).attach, ∑ psi : PrimitiveCharacter r.1,
        F (DirichletCharacter.changeLevel
          ((Nat.mem_divisors.mp (Finset.mem_filter.mp
            r.2).1).1)
          psi.1) := by
  classical
  let T := (nonprincipalConductors q).attach.sigma
    (fun r => (Finset.univ : Finset (PrimitiveCharacter r.1)))
  have hT : (∑ p ∈ T,F (induce ⟨p.1,p.2⟩)) =
      ∑ r ∈ (nonprincipalConductors q).attach, ∑ psi : PrimitiveCharacter r.1,
        F (DirichletCharacter.changeLevel
          ((Nat.mem_divisors.mp (Finset.mem_filter.mp
            r.2).1).1)
          psi.1) := by
    dsimp [T]
    rw [Finset.sum_sigma]
    rfl
  rw [← hT]
  refine Finset.sum_bij'
    (fun chi hchi => (encode hq chi hchi : InductionDatum q))
    (fun p _ => induce p) ?_ ?_ ?_ ?_ ?_
  · intro chi hchi
    simp only [T,Finset.mem_sigma,Finset.mem_attach,Finset.mem_univ,and_self]
  · intro p hp
    exact induce_nonprincipal hq p
  · intro chi hchi
    exact induce_encode hq chi hchi
  · intro p hp
    apply induce_injective hq
    exact induce_encode hq (induce p) (induce_nonprincipal hq p)
  · intro chi hchi
    rw [induce_encode]

/-- General finite divisor/quotient change of variables, with no arithmetic
filter on the pair (r,k). Every q=r*k occurs exactly once for fixed r. -/
theorem sum_conductor_quotient (Q : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ nonprincipalConductors q,F r (q/r)) =
      ∑ k ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 2 (Q/k),F r k := by
  rw [← Finset.sum_sigma',← Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun p _ => (⟨p.1/p.2,p.2⟩ : Σ _ : ℕ,ℕ))
    (fun p _ => (⟨p.2*p.1,p.2⟩ : Σ _ : ℕ,ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q,r⟩ hp
    obtain ⟨hq,hr⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hrdiv,hr2⟩ := Finset.mem_filter.mp hr
    have hq0 := (Finset.mem_Icc.mp hq).1
    have hqQ := (Finset.mem_Icc.mp hq).2
    have hrq := (Nat.mem_divisors.mp hrdiv).1
    have hr0 : 0<r := by omega
    have hprod : r*(q/r)=q := Nat.mul_div_cancel' hrq
    have hk0 : 0<q/r := Nat.div_pos (Nat.le_of_dvd hq0 hrq) hr0
    rw [Finset.mem_sigma,Finset.mem_Icc,Finset.mem_Icc]
    refine ⟨⟨hk0,(Nat.div_le_self q r).trans hqQ⟩,hr2,?_⟩
    apply (Nat.le_div_iff_mul_le hk0).mpr
    simpa [hprod] using hqQ
  · rintro ⟨k,r⟩ hp
    obtain ⟨hk,hr⟩ := Finset.mem_sigma.mp hp
    have hk0 := (Finset.mem_Icc.mp hk).1
    obtain ⟨hr2,hrQ⟩ := Finset.mem_Icc.mp hr
    have hr0 : 0<r := by omega
    have hprod : r*k≤Q := (Nat.le_div_iff_mul_le hk0).mp hrQ
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hr0 hk0,hprod⟩,?_⟩
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right r k,(Nat.mul_pos hr0 hk0).ne'⟩,hr2⟩
  · rintro ⟨q,r⟩ hp
    have hr := (Finset.mem_sigma.mp hp).2
    have hd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hr).1).1
    dsimp
    rw [Nat.mul_div_cancel' hd]
  · rintro ⟨k,r⟩ hp
    have hr2 := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hp).2).1
    have hr0 : 0<r := by omega
    dsimp
    rw [Nat.mul_div_cancel_left k hr0]
  · rintro ⟨q,r⟩ hp
    rfl

def levelAmplitude (a : ℤ → ℂ) (M : ℤ) (L q : ℕ)
    (chi : DirichletCharacter ℂ q) : ℝ :=
  ‖∑ n ∈ Finset.Icc (M+1) (M+L),a n*chi (n : ZMod q)‖

/-- Only positive source integers are needed for the actual Gamma rows.
The finite large sieve itself remains available on arbitrary integer rows. -/
theorem levelAmplitude_induced (a : ℤ → ℂ) (M : ℤ) (hM : 0≤M)
    (L r k : ℕ) (psi : PrimitiveCharacter r) :
    levelAmplitude a M L (r*k)
      (DirichletCharacter.changeLevel (dvd_mul_right r k) psi.1) =
      rowAmplitude (unitMask k a) M L r psi := by
  unfold levelAmplitude rowAmplitude
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0≤n := by have := (Finset.mem_Icc.mp hn).1; omega
  have hncast : (n.toNat : ℤ)=n := Int.toNat_of_nonneg hn0
  have h := changeLevel_apply_quotient r k n.toNat psi.1
  have habs : n.natAbs=n.toNat := by rw [← hncast]; simp
  have hcastq : (n : ZMod (r*k))=(n.toNat : ZMod (r*k)) := by rw [← hncast]; simp
  have hcastr : (n : ZMod r)=(n.toNat : ZMod r) := by rw [← hncast]; simp
  rw [unitMask,habs,hcastq,hcastr]
  rw [h]
  by_cases hc : n.toNat.Coprime k <;> simp only [hc,if_true,if_false,mul_zero,zero_mul]

def allNonprincipalMajorant (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,(1/(q.totient : ℝ))*
    ∑ chi ∈ nonprincipalCharacters q,
      levelAmplitude a Ma La q chi*levelAmplitude b Mb Lb q chi

/-- Orthogonality's exact nonprincipal rectangle, with arbitrary moving
primitive residue. The rows do not depend on the modulus or residue. -/
def rectangleCharacterDiscrepancy (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb q : ℕ) (z : ZMod q) : ℂ :=
  (q.totient : ℂ)⁻¹*∑ chi ∈ nonprincipalCharacters q,
    chi z*(∑ m ∈ Finset.Icc (Ma+1) (Ma+La),a m*chi (m : ZMod q))*
      (∑ n ∈ Finset.Icc (Mb+1) (Mb+Lb),b n*chi (n : ZMod q))

/-- Taking the residue maximum incurs no residue-count factor: the same
right side holds for EVERY residue, including every moving inverse target. -/
theorem rectangleCharacterDiscrepancy_norm_le (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb q : ℕ) (z : ZMod q) :
    ‖rectangleCharacterDiscrepancy a b Ma Mb La Lb q z‖ ≤
      (1/(q.totient : ℝ))*∑ chi ∈ nonprincipalCharacters q,
        levelAmplitude a Ma La q chi*levelAmplitude b Mb Lb q chi := by
  unfold rectangleCharacterDiscrepancy
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  simp only [one_div]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ chi ∈ nonprincipalCharacters q,
        ‖chi z*(∑ m ∈ Finset.Icc (Ma+1) (Ma+La),a m*chi (m : ZMod q))*
          (∑ n ∈ Finset.Icc (Mb+1) (Mb+Lb),b n*chi (n : ZMod q))‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro chi hchi
      rw [norm_mul,norm_mul]
      have h := chi.norm_le_one z
      dsimp [levelAmplitude]
      nlinarith [norm_nonneg (∑ m ∈ Finset.Icc (Ma+1) (Ma+La),
        a m*chi (m : ZMod q)),norm_nonneg (∑ n ∈ Finset.Icc (Mb+1) (Mb+Lb),
        b n*chi (n : ZMod q))]

theorem sum_rectangleCharacterDiscrepancy_norm_le (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb Q : ℕ) (z : (q : ℕ) → ZMod q) :
    (∑ q ∈ Finset.Icc 1 Q,‖rectangleCharacterDiscrepancy a b Ma Mb La Lb q (z q)‖)≤
      allNonprincipalMajorant a b Ma Mb La Lb Q := by
  exact Finset.sum_le_sum fun q hq => rectangleCharacterDiscrepancy_norm_le
    a b Ma Mb La Lb q (z q)

def inducedTotal (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb Q : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 Q,inducedShell a b Ma Mb La Lb k (Finset.Icc 2 (Q/k))

/-- Exact original-modulus regrouping. There is no replacement of phi(r*k)
by a product until AFTER this identity. -/
theorem allNonprincipalMajorant_eq_inducedTotal
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (hMa : 0≤Ma) (hMb : 0≤Mb)
    (La Lb Q : ℕ) :
    allNonprincipalMajorant a b Ma Mb La Lb Q =
      inducedTotal a b Ma Mb La Lb Q := by
  unfold allNonprincipalMajorant inducedTotal inducedShell
  let F : ℕ → ℕ → ℝ := fun r k => (1/((r*k).totient : ℝ))*
    ∑ psi : PrimitiveCharacter r,
      rowAmplitude (unitMask k a) Ma La r psi*
        rowAmplitude (unitMask k b) Mb Lb r psi
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ nonprincipalConductors q,F r (q/r) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq0 := (Finset.mem_Icc.mp hq).1
      rw [sum_nonprincipal_induced hq0,Finset.mul_sum]
      rw [← Finset.sum_attach (nonprincipalConductors q) (fun r => F r (q/r))]
      apply Finset.sum_congr rfl
      intro r hr
      have hd := (Nat.mem_divisors.mp (Finset.mem_filter.mp r.2).1).1
      have hprod : r.1*(q/r.1)=q := Nat.mul_div_cancel' hd
      cases r with
      | mk r hr =>
       dsimp at hprod ⊢
       generalize hk : q/r=k at hprod ⊢
       subst q
       dsimp [F]
       congr 2
       apply Finset.sum_congr rfl
       intro psi hpsi
       rw [levelAmplitude_induced a Ma hMa,levelAmplitude_induced b Mb hMb]
    _ = _ := sum_conductor_quotient Q F

end
end ImbalancedChen.P2GammaExactConductorRegrouping
