import ImbalancedChen.Part3IntegerFirstColumnNormalForm
import Mathlib.Data.Nat.Prime.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Generic INTEGER determinant-p normal form for a genuine 2x2 matrix.
The positive natural k is exactly gcd(M00,M10), not an arbitrary supplied
branch tag. Its divisibility into det(M)=p forces k=1 or k=p. The integral
SL2 completion, oriented beta and actual inverse reduction come from the
primitive-column construction in the adjacent module, which REUSES the
pinned Mathlib Bezout completion. No Hecke C-preservation, cusp width,
affine-coordinate formula, or preselected matrix factorization is assumed.
-/

namespace ImbalancedChen.Part3.IntegerDetPrimeNormalForm20261026b

noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
open IntegerFirstColumnNormalForm20261026b

theorem firstColumnGcd_dvd_prime (p : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = (p : ℤ)) : firstColumnGcd M ∣ p := by
  have hz := firstColumnGcd_dvd_det M
  rw [hdet] at hz
  exact Int.natCast_dvd_natCast.mp hz

theorem firstColumnGcd_prime_cases (p : ℕ) (hp : p.Prime)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = (p : ℤ)) :
    firstColumnGcd M = 1 ∨ firstColumnGcd M = p :=
  (Nat.dvd_prime hp).mp (firstColumnGcd_dvd_prime p M hdet)

/-- The lower diagonal entry is the ACTUAL exact determinant quotient;
the product identity holds in integers without a division convention gap. -/
theorem firstColumn_diagonal_product (p : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = (p : ℤ)) :
    (firstColumnGcd M : ℤ) * ((p : ℤ) / (firstColumnGcd M : ℤ)) = (p : ℤ) := by
  apply Int.mul_ediv_cancel'
  simpa only [hdet] using firstColumnGcd_dvd_det M

/-- Strong consumer interface: canonical gcd, primitive-column entries,
oriented beta, actual h^-1*M and exact M recovery are all retained. -/
theorem exists_prime_normal_form_with_gcd (p : ℕ) (hp : p.Prime)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = (p : ℤ)) :
    ∃ h : SL(2, ℤ), ∃ k : ℕ, ∃ beta : ℤ,
      k = firstColumnGcd M ∧ 0 < k ∧ k ∣ p ∧ (k = 1 ∨ k = p) ∧
      h 0 0 = M 0 0 / (k : ℤ) ∧ h 1 0 = M 1 0 / (k : ℤ) ∧
      beta = h 1 1 * M 0 1 - h 0 1 * M 1 1 ∧
      (h⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * M = !![(k : ℤ), beta; 0, (p : ℤ) / (k : ℤ)] ∧
      M = (h : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), beta; 0, (p : ℤ) / (k : ℤ)] := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hne : M.det ≠ 0 := by rw [hdet]; exact hpz
  obtain ⟨h, beta, h00, h10, hbeta, hinverse, hfactor⟩ := exists_gcd_upper_triangular M hne
  refine ⟨h, firstColumnGcd M, beta, rfl, firstColumnGcd_pos M hne,
    firstColumnGcd_dvd_prime p M hdet, firstColumnGcd_prime_cases p hp M hdet,
    h00, h10, hbeta, ?_, ?_⟩
  · simpa only [hdet] using hinverse
  · simpa only [hdet] using hfactor

/-- Literal requested natural-diagonal formulation. The natural quotient
p/k casts to exactly the integer quotient used by the strong interface. -/
theorem exists_prime_normal_form (p : ℕ) (hp : p.Prime)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = (p : ℤ)) :
    ∃ h : SL(2, ℤ), ∃ k : ℕ, ∃ beta : ℤ,
      0 < k ∧ k ∈ ({1, p} : Finset ℕ) ∧ k = Int.gcd (M 0 0) (M 1 0) ∧
      beta = h 1 1 * M 0 1 - h 0 1 * M 1 1 ∧
      M = (h : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), beta; 0, ((p / k : ℕ) : ℤ)] := by
  obtain ⟨h, k, beta, hk, hkpos, _hdiv, hcases, _h00, _h10, hbeta, _hinverse, hfactor⟩ :=
    exists_prime_normal_form_with_gcd p hp M hdet
  refine ⟨h, k, beta, hkpos, ?_, ?_, hbeta, ?_⟩
  · simpa only [Finset.mem_insert, Finset.mem_singleton] using hcases
  · simpa only [firstColumnGcd] using hk
  · simpa only [Int.natCast_ediv] using hfactor

end
end ImbalancedChen.Part3.IntegerDetPrimeNormalForm20261026b
