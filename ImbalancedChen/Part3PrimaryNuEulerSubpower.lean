import ImbalancedChen.Part3FixedRhoPrimarySignedFiniteDecomposition
import ImbalancedChen.Part3SignedDivisorDeletion
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
SOURCEONLY / UNCOMPILED / OPEN30. One weighted-primary-nu arithmetic step.
The first import is the exact planned 7a9c64b9 parent, not an installation
claim. Other project imports are existing sources. No ancestor is copied.

The original theta is 7/32. After the original 1/nu count, its weight is
nu^(7/32-1), NOT 1/nu. A finite Euler product bounds the entire primary sum;
each Euler factor is <=4, so the product is <=tau(|rho|)^2. The existing
fixed-order divisor subpower theorem supplies a constant BEFORE rho, the
finite source, and every actual atom. The final actual theorem uses the
original c0>0 to derive nonzero signed rho and the original polynomial
upper bound on |rho|. It never assumes rho>0 or a desired nu-sum estimate.

The factor |rho|^(7/32) from (|rho|nu)^(7/32)/nu remains explicit. Nothing
here supplies the B_nu count, a spectral estimate, or Eq24/25 themselves.
-/

namespace ImbalancedChen.Part3.PrimaryNuEulerSubpowerSourceOnly
noncomputable section
open Classical Finset
open ActualCompletedSquarePushforwardSourceOnly
open FixedRhoPrimarySignedFiniteSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualM2FinitePoissonAdapterSourceOnly
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Multiplicativity on naturals, including the harmless value at zero.
The Euler theorem sums only positive factoredNumbers. -/
def primaryNuWeightHom : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (7 / 32 - 1 : ℝ)
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul] using
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

def primaryEuler (rho : ℤ) : ℝ :=
  ∏ p ∈ rho.natAbs.primeFactors, (1 - (p : ℝ) ^ (7 / 32 - 1 : ℝ))⁻¹

theorem prime_weight_lt_one {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ (7 / 32 - 1 : ℝ) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by norm_num)

/-- Only a FINITE prime support is used. The full natural-number series
with exponent -25/32 is not claimed summable. -/
theorem primaryEuler_hasSum (rho : ℤ) :
    HasSum (fun n : Nat.factoredNumbers rho.natAbs.primeFactors =>
      (n.val : ℝ) ^ (7 / 32 - 1 : ℝ)) (primaryEuler rho) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖primaryNuWeightHom p‖ < 1 := by
    intro p hprime
    change ‖(p : ℝ) ^ (7 / 32 - 1 : ℝ)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact prime_weight_lt_one hprime
  have hs := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := primaryNuWeightHom) hp rho.natAbs.primeFactors).2
  have hf : rho.natAbs.primeFactors.filter Nat.Prime = rho.natAbs.primeFactors :=
    filter_eq_self.mpr (fun p hprime => Nat.prime_of_mem_primeFactors hprime)
  change HasSum (fun n : Nat.factoredNumbers rho.natAbs.primeFactors =>
    (n.val : ℝ) ^ (7 / 32 - 1 : ℝ))
      (∏ p ∈ rho.natAbs.primeFactors with p.Prime,
        (1 - (p : ℝ) ^ (7 / 32 - 1 : ℝ))⁻¹) at hs
  simpa only [hf, primaryEuler] using hs

/-- Any finite part of rho-primary positive integers has this same Euler
majorant, independent of cutoff and cardinality. Nonzero rho is essential
to identify its prime divisors with its finite primeFactors. -/
theorem finite_supported_sum_le_euler {rho : ℤ} (hrho : rho ≠ 0)
    (S : Finset ℕ)
    (hS : ∀ nu ∈ S, ∀ p : ℕ, p.Prime → p ∣ nu → p ∣ rho.natAbs) :
    (∑ nu ∈ S, (nu : ℝ) ^ (7 / 32 - 1 : ℝ)) ≤ primaryEuler rho := by
  have hrhoN := Int.natAbs_ne_zero.mpr hrho
  let emb : {nu // nu ∈ S} → Nat.factoredNumbers rho.natAbs.primeFactors :=
    fun nu => ⟨nu.val, Nat.mem_factoredNumbers'.mpr (fun p hp hpn =>
      (Nat.mem_primeFactors_of_ne_zero hrhoN).mpr ⟨hp, hS nu.val nu.property p hp hpn⟩)⟩
  have hinj : Function.Injective emb := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun n : Nat.factoredNumbers rho.natAbs.primeFactors => n.val) hab
  have hs := sum_le_hasSum (S.attach.image emb)
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n.val) (7 / 32 - 1 : ℝ))
    (primaryEuler_hasSum rho)
  rw [sum_image hinj.injOn] at hs
  change (∑ nu ∈ S.attach, (nu.val : ℝ) ^ (7 / 32 - 1 : ℝ)) ≤ primaryEuler rho at hs
  rw [Finset.sum_attach S (fun nu : ℕ => (nu : ℝ) ^ (7 / 32 - 1 : ℝ))] at hs
  exact hs

/-- A rational, non-numerical bound: -25/32<=-1/2 and sqrt(p)>=4/3. -/
theorem prime_weight_le_three_quarters {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ (7 / 32 - 1 : ℝ) ≤ 3 / 4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt p := by
    by_contra h
    have hlt : Real.sqrt p < (4 / 3 : ℝ) := lt_of_not_ge h
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg (p : ℝ)) hlt.le
    rw [← pow_two, Real.sq_sqrt hp0] at hsq
    nlinarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 / 3) hs
  calc
    _ ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = (Real.sqrt p)⁻¹ := by rw [Real.rpow_neg hp0, ← Real.sqrt_eq_rpow]
    _ ≤ _ := by simpa only [one_div, inv_div] using hi

theorem primaryEuler_le_divisor_square {rho : ℤ} (hrho : rho ≠ 0) :
    primaryEuler rho ≤ (rho.natAbs.divisors.card : ℝ)^2 := by
  have hn := Int.natAbs_ne_zero.mpr hrho
  have hfactor {p : ℕ} (hp : p.Prime) :
      (1 - (p : ℝ) ^ (7 / 32 - 1 : ℝ))⁻¹ ≤ (4 : ℝ) := by
    have hw := prime_weight_le_three_quarters hp
    have hden : (1 / 4 : ℝ) ≤ 1 - (p : ℝ) ^ (7 / 32 - 1 : ℝ) := by linarith
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hden
    have hfour : (1 / (1 / 4) : ℝ) = 4 := by norm_num
    rw [hfour] at hi
    simpa only [one_div] using hi
  calc
    primaryEuler rho ≤ ∏ p ∈ rho.natAbs.primeFactors,
        (((rho.natAbs.factorization p + 1 : ℕ) : ℝ)^2) := by
      apply prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        exact sub_nonneg.mpr (prime_weight_lt_one (Nat.prime_of_mem_primeFactors hp)).le
      · intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hf := hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
        have hfR : (2 : ℝ) ≤ ((rho.natAbs.factorization p + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 2 ≤ rho.natAbs.factorization p + 1 by omega)
        exact (hfactor hprime).trans (by nlinarith)
    _ = _ := by simp only [Nat.card_divisors hn, Nat.cast_prod, prod_pow]

/-- The constant precedes rho AND the finite support. This is the genuine
nu^(theta-1) subpower estimate, not a harmonic or a support-size bound. -/
theorem finite_supported_sum_subpower {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (rho : ℤ), rho ≠ 0 → ∀ S : Finset ℕ,
      (∀ nu ∈ S, ∀ p : ℕ, p.Prime → p ∣ nu → p ∣ rho.natAbs) →
      (∑ nu ∈ S, (nu : ℝ) ^ (7 / 32 - 1 : ℝ)) ≤ C * (rho.natAbs : ℝ)^eps := by
  obtain ⟨K, hK, htau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show 0 < eps / 2 by positivity)
  refine ⟨K^2, by positivity, ?_⟩
  intro rho hrho S hS
  have ht : (rho.natAbs.divisors.card : ℝ) ≤ K * (rho.natAbs : ℝ)^(eps/2) := by
    simpa only [fouvryTau_two] using htau rho.natAbs (Int.natAbs_pos.mpr hrho)
  calc
    _ ≤ primaryEuler rho := finite_supported_sum_le_euler hrho S hS
    _ ≤ (rho.natAbs.divisors.card : ℝ)^2 := primaryEuler_le_divisor_square hrho
    _ ≤ (K * (rho.natAbs : ℝ)^(eps/2))^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) ht 2
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
        show (eps / 2) * ((2 : ℕ) : ℝ) = eps by ring]

/-- Exact original ABL cost after the count's 1/nu. In particular the
|rho|^theta factor is not cancelled by the primary-nu arithmetic budget. -/
theorem primaryKeys_ABL_cost_eq (rho : ℤ) (U : Finset Source) :
    (∑ nu ∈ primaryKeys rho U,
      ((rho.natAbs : ℝ) * (nu : ℝ))^(7 / 32 : ℝ) / (nu : ℝ)) =
      (rho.natAbs : ℝ)^(7 / 32 : ℝ) *
        ∑ nu ∈ primaryKeys rho U, (nu : ℝ)^(7 / 32 - 1 : ℝ) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro nu hnu
  have hn : (0 : ℝ) < nu := by exact_mod_cast primaryKeys_pos hnu
  rw [Real.mul_rpow (Nat.cast_nonneg _) hn.le,
    Real.rpow_sub hn, Real.rpow_one, mul_div_assoc]

/-- Nonzero comes from the ORIGINAL c0>0 gate of RestrictedMediumObligation,
not from an invented positivity condition on the signed branch residue. -/
theorem actual_signedResidue_ne_zero {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (hc0 : 0 < c0) (he : MediumAdmissible B sigma kappa c0 e) (negative : Bool) :
    signedResidue negative e.residue ≠ 0 := by
  apply Int.natAbs_ne_zero.mp
  rw [signedResidue_natAbs]
  exact Int.natAbs_ne_zero.mpr (mediumAdmissible_residue_ne_zero hc0 he)

/-- Actual uniform scale budget. C depends only on fixed kappa and eps;
it precedes B, all admissible atoms, both signed branches and EVERY finite
source (hence also actualNonzeroSource and every existing count chart). -/
theorem actual_primaryKeys_sum_subpower (kappa : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (e : MediumAtom),
      0 < c0 → MediumAdmissible B sigma kappa c0 e →
      ∀ (negative : Bool) (U : Finset Source),
      (∑ nu ∈ primaryKeys (signedResidue negative e.residue) U,
        (nu : ℝ)^(7 / 32 - 1 : ℝ)) ≤ C * e.scale^eps := by
  let K : ℝ := max 1 (1 + kappa)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := by linarith
  let eta : ℝ := eps / K
  have heta : 0 < eta := div_pos heps hKpos
  have hKeta : K * eta = eps := by dsimp [eta]; field_simp [hKpos.ne']
  obtain ⟨C, hC, hbound⟩ := finite_supported_sum_subpower heta
  refine ⟨C, hC, ?_⟩
  intro B sigma c0 e hc0 he negative U
  have hrho := actual_signedResidue_ne_zero hc0 he negative
  have hs := hbound (signedResidue negative e.residue) hrho
    (primaryKeys (signedResidue negative e.residue) U)
    (fun nu hnu p hp hpn => primaryKeys_prime_support hnu hp hpn)
  rw [signedResidue_natAbs] at hs
  have hx : 1 ≤ e.scale := by
    change 1 ≤ e.U * e.V
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ e.U * e.V := mul_le_mul he.1 he.2.1 zero_le_one (zero_le_one.trans he.1)
  obtain ⟨_, _, _, _, _, _, _, hres, _⟩ := he
  have haK : (e.residue.natAbs : ℝ) ≤ e.scale^K :=
    hres.trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1+kappa)))
  calc
    _ ≤ C * (e.residue.natAbs : ℝ)^eta := hs
    _ ≤ C * (e.scale^K)^eta := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) haK heta.le) hC.le
    _ = _ := by rw [← Real.rpow_mul (zero_le_one.trans hx), hKeta]

/-- Direct actual payment of the original (|rho|nu)^theta / nu cost.
The polynomial |rho|^theta is displayed outside the selectable small power. -/
theorem actual_primaryKeys_ABL_cost_subpower (kappa : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (e : MediumAtom),
      0 < c0 → MediumAdmissible B sigma kappa c0 e →
      ∀ (negative : Bool) (U : Finset Source),
      (∑ nu ∈ primaryKeys (signedResidue negative e.residue) U,
        (((signedResidue negative e.residue).natAbs : ℝ) * (nu : ℝ))^(7 / 32 : ℝ) /
          (nu : ℝ)) ≤ (e.residue.natAbs : ℝ)^(7 / 32 : ℝ) * (C * e.scale^eps) := by
  obtain ⟨C, hC, hbound⟩ := actual_primaryKeys_sum_subpower kappa heps
  refine ⟨C, hC, ?_⟩
  intro B sigma c0 e hc0 he negative U
  rw [primaryKeys_ABL_cost_eq, signedResidue_natAbs]
  exact mul_le_mul_of_nonneg_left (hbound B sigma c0 e hc0 he negative U)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end
end ImbalancedChen.Part3.PrimaryNuEulerSubpowerSourceOnly
