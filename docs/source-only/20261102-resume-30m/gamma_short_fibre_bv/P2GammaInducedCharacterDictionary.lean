import ImbalancedChen.P2OriginalGammaUpperPrimeBVAttachment
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import MathlibNt.AnalyticNumberTheory.LargeSieve.ConductorChangeLevelLedger

/-!
SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.

The induced-character dictionary for the actual original Gamma source.
The quotient k in q=r*k need not be coprime to r. Both source factors keep
their k-coprimality masks. The principal character is removed against the
exact q-coprime mean, before any norm is taken. No BV estimate is a premise.

This file does not supply the still-missing whole-Gamma convolution estimate.
-/

namespace ImbalancedChen.P2GammaInducedCharacterDictionary
noncomputable section
open scoped Classical BigOperators
open AnalyticNumberTheory.LargeSieve
open P2OriginalGammaUpperLowRankConsumer P2OriginalU5ExactNormalizedSource
open P2OriginalU5WholeGroupCapacity P2TwentyOneUnsiftedArithmeticSource
open Wu2008DoubleSieve

/-- Induction to r*k has precisely the extra k-unit gate. In particular,
there is no hypothesis r.Coprime k. -/
theorem changeLevel_apply_quotient (r k n : ℕ)
    (psi : DirichletCharacter ℂ r) :
    (DirichletCharacter.changeLevel (dvd_mul_right r k) psi) (n : ZMod (r*k)) =
      if n.Coprime k then psi (n : ZMod r) else 0 := by
  by_cases hn : n.Coprime (r*k)
  · have hnk := (Nat.coprime_mul_iff_right.mp hn).2
    rw [if_pos hnk]
    simpa only [Int.cast_natCast] using
      DirichletCharacter.changeLevel_eq_cast_of_dvd' psi
        (dvd_mul_right r k) (Nat.isCoprime_iff_coprime.mpr hn)
  · have hz :
        (DirichletCharacter.changeLevel (dvd_mul_right r k) psi)
          (n : ZMod (r*k)) = 0 :=
      MulChar.map_nonunit _ (fun h => hn ((ZMod.isUnit_iff_coprime n (r*k)).mp h))
    rw [hz]
    by_cases hnk : n.Coprime k
    · rw [if_pos hnk]
      have hnr : ¬ n.Coprime r := fun hnr =>
        hn (Nat.coprime_mul_iff_right.mpr ⟨hnr,hnk⟩)
      exact (MulChar.map_nonunit psi
        (fun h => hnr ((ZMod.isUnit_iff_coprime n r).mp h))).symm
    · rw [if_neg hnk]

/-- The literal induced transform of a product has TWO auxiliary gates. -/
theorem changeLevel_product (r k m n : ℕ)
    (psi : DirichletCharacter ℂ r) :
    (DirichletCharacter.changeLevel (dvd_mul_right r k) psi)
        ((m*n : ℕ) : ZMod (r*k)) =
      (if m.Coprime k then psi (m : ZMod r) else 0) *
        (if n.Coprime k then psi (n : ZMod r) else 0) := by
  rw [Nat.cast_mul,map_mul,changeLevel_apply_quotient,changeLevel_apply_quotient]

/-- Exact rectangular character factorization, including all nonunits.
The two coefficient sequences are fixed before the character is selected. -/
theorem induced_rectangle_factorization (r k : ℕ)
    (psi : DirichletCharacter ℂ r) (S T : Finset ℕ) (a b : ℕ → ℂ) :
    (∑ m ∈ S, ∑ n ∈ T, a m*b n*
      (DirichletCharacter.changeLevel (dvd_mul_right r k) psi)
        ((m*n : ℕ) : ZMod (r*k))) =
      (∑ m ∈ S, (if m.Coprime k then a m else 0)*psi (m : ZMod r)) *
        (∑ n ∈ T, (if n.Coprime k then b n else 0)*psi (n : ZMod r)) := by
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [changeLevel_product]
  by_cases hmk : m.Coprime k <;> by_cases hnk : n.Coprime k <;>
    simp only [hmk,hnk,if_true,if_false,mul_zero,zero_mul] <;> ring

/-- Exact gcd factor in the induced-level totient. -/
theorem totient_product_gcd (r k : ℕ) (hr : 0<r) :
    ((r*k).totient : ℝ) =
      (r.totient : ℝ)*(k.totient : ℝ)*(r.gcd k : ℝ)/((r.gcd k).totient : ℝ) := by
  have hg : 0<(r.gcd k).totient :=
    Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left k hr)
  have hgR : (0 : ℝ)<(r.gcd k).totient := by exact_mod_cast hg
  apply (eq_div_iff hgR.ne').mpr
  have h := Nat.totient_gcd_mul_totient_mul r k
  exact_mod_cast (by simpa only [mul_comm] using h)

/-- The denominator inequality needs no squarefree or coprime-factor premise. -/
theorem inv_totient_product_le (r k : ℕ) (hr : 0<r) (hk : 0<k) :
    (1 : ℝ)/((r*k).totient : ℝ) ≤
      1/((r.totient : ℝ)*(k.totient : ℝ)) := by
  have hp : (0 : ℝ)<(r.totient : ℝ)*(k.totient : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.totient_pos.mpr hr) (Nat.totient_pos.mpr hk)
  have hh : (r.totient : ℝ)*(k.totient : ℝ)≤((r*k).totient : ℝ) := by
    exact_mod_cast Nat.totient_super_multiplicative r k
  exact one_div_le_one_div_of_le hp hh

/-- One physical Gamma kernel is exactly the nonprincipal character sum.
The principal term is the SAME q-coprime mean, not the total source mass. -/
theorem gammaKernel_eq_nonprincipal {N q : ℕ} (hq : 0<q)
    (hN : N.Coprime q) (m : ℕ) :
    ((gammaKernel N q m : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ chi ∈ nonprincipalCharacters q,
        chi ((N : ZMod q)⁻¹)*chi (m : ZMod q) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hNu : IsUnit (N : ZMod q) := (ZMod.isUnit_iff_coprime N q).mpr hN
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hNu (m : ZMod q)
  rw [sum_allCharacters_eq_principal_add_nonprincipal] at horth
  have honeN : (1 : DirichletCharacter ℂ q) ((N : ZMod q)⁻¹)=1 := by
    change (if IsUnit ((N : ZMod q)⁻¹) then (1 : ℂ) else 0)=1
    have hNuInv : IsUnit ((N : ZMod q)⁻¹) := by
      simpa only [Int.cast_natCast] using
        (ZMod.isUnit_inv (n := (N : ℤ)) (by simpa only [Int.cast_natCast] using hNu))
    simp only [hNuInv,if_true]
  have honem : (1 : DirichletCharacter ℂ q) (m : ZMod q)=
      if m.Coprime q then 1 else 0 := by
    change (if IsUnit (m : ZMod q) then (1 : ℂ) else 0)=_
    simp only [ZMod.isUnit_iff_coprime]
  rw [honeN,one_mul,honem] at horth
  have hphi : (q.totient : ℂ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hres : (N : ZMod q)=(m : ZMod q) ↔ Nat.ModEq q m N := by
    rw [eq_comm,ZMod.natCast_eq_natCast_iff]
  rw [hres] at horth
  have hsum : (∑ chi ∈ nonprincipalCharacters q,
      chi ((N : ZMod q)⁻¹)*chi (m : ZMod q)) =
      (if Nat.ModEq q m N then (q.totient : ℂ) else 0)-
        (if m.Coprime q then (1 : ℂ) else 0) := by
    exact eq_sub_of_add_eq' horth
  rw [hsum]
  by_cases hAP : Nat.ModEq q m N <;> by_cases hcop : m.Coprime q <;>
    simp [gammaKernel,hAP,hcop,div_eq_mul_inv,hphi,mul_sub]

/-- Apply the induced dictionary to the literal original label. The old
marked pair, whole Gamma word and quotient are all kept as separate gates. -/
theorem original_Gamma_label_induced (r k : ℕ)
    (psi : DirichletCharacter ℂ r) (t : ℕ × ℕ) (x : Label) :
    (DirichletCharacter.changeLevel (dvd_mul_right r k) psi)
        ((product (t.1*t.2) x : ℕ) : ZMod (r*k)) =
      (if (t.1*t.2).Coprime k then psi ((t.1*t.2 : ℕ) : ZMod r) else 0) *
      (if x.1.prod.Coprime k then psi (x.1.prod : ZMod r) else 0) *
      (if x.2.Coprime k then psi (x.2 : ZMod r) else 0) := by
  unfold product
  simp only [Nat.cast_mul,map_mul,changeLevel_apply_quotient]

/-- The quotient label 1 gives exactly one in the induced character factor;
it is not deleted from a nonempty original product family. -/
theorem original_unit_quotient_induced (r k : ℕ)
    (psi : DirichletCharacter ℂ r) (t : ℕ × ℕ) (w : List ℕ) :
    (DirichletCharacter.changeLevel (dvd_mul_right r k) psi)
        ((product (t.1*t.2) (w,1) : ℕ) : ZMod (r*k)) =
      (if (t.1*t.2).Coprime k then psi ((t.1*t.2 : ℕ) : ZMod r) else 0) *
      (if w.prod.Coprime k then psi (w.prod : ZMod r) else 0) := by
  simpa using original_Gamma_label_induced r k psi t (w,1)

/-- The exact original source reaches the nonprincipal-character kernel
without changing a mother-list occurrence, representation or mean. -/
theorem original_Gamma_nonprincipal_dictionary {N q : ℕ} (hq : 0<q)
    (hN : N.Coprime q) (t : ℕ × ℕ) :
    gammaDiscrepancy N t q =
      sourceTest N t (fun m => ((q.totient : ℂ)⁻¹ *
        ∑ chi ∈ nonprincipalCharacters q,
          chi ((N : ZMod q)⁻¹)*chi (m : ZMod q)).re) := by
  unfold gammaDiscrepancy
  apply congrArg (sourceTest N t)
  funext m
  have h := congrArg Complex.re (gammaKernel_eq_nonprincipal hq hN m)
  simpa only [Complex.ofReal_re] using h

end
end ImbalancedChen.P2GammaInducedCharacterDictionary
