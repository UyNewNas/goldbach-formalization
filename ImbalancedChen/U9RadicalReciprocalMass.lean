import ImbalancedChen.U9OrdinaryRowExplicitFiniteUpper
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pinned Mathlib's finite-prime Euler HasSum theorem is reused at exponent1.
No false global summability of the harmonic series is assumed. For a fixed
positive e, every finite set of multiples of e supported on its prime
factors has reciprocal mass at most1/phi(e). This is the true prime-power
fibre estimate required when grouping an original harmonic sum by radical.
-/

namespace ImbalancedChen.U9SemiprimeSwitch
noncomputable section
open Classical
open scoped BigOperators

def reciprocalHom : ℕ →* ℝ where
  toFun n := 1 / (n : ℝ)
  map_one' := by simp
  map_mul' m n := by simp only [Nat.cast_mul, one_div, mul_inv_rev, mul_comm]

private theorem reciprocalHom_prime_norm {p : ℕ} (hp : Nat.Prime p) :
    ‖reciprocalHom p‖ < 1 := by
  change ‖1 / (p : ℝ)‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_lt_one (by exact_mod_cast hp.pos)).mpr
  exact_mod_cast hp.one_lt

/-- The finite-prime geometric supplier also bounds any finite smooth
mass uniformly in its actual modulus D, including all prime powers of D. -/
theorem finite_factored_reciprocal_mass (D : ℕ) (hD : 0 < D)
    (K : Finset (Nat.factoredNumbers D.primeFactors)) :
    (∑ k ∈ K, 1 / (k.val : ℝ)) ≤ (D : ℝ) / (Nat.totient D : ℝ) := by
  have hEuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalHom) (fun {_} hp => reciprocalHom_prime_norm hp) D.primeFactors
  have hK := hEuler.2.summable.sum_le_tsum K
    (fun k _ => by change 0 ≤ 1 / (k.val : ℝ); positivity)
  rw [hEuler.2.tsum_eq] at hK
  have hfilter : D.primeFactors.filter Nat.Prime = D.primeFactors :=
    Finset.filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primeFactors hp)
  simp only [hfilter] at hK
  have hphi : (Nat.totient D : ℝ) = (D : ℝ) *
      ∏ p ∈ D.primeFactors, (1 - 1 / (p : ℝ)) := by
    have h := congrArg (algebraMap ℚ ℝ) (Nat.totient_eq_mul_prod_factors D)
    simpa only [map_natCast, map_mul, map_prod, map_sub, map_one, map_inv₀, one_div] using h
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hphi0 : (Nat.totient D : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hD).ne'
  have hprod0 : (∏ p ∈ D.primeFactors, (1 - 1 / (p : ℝ))) ≠ 0 := by
    intro hz
    apply hphi0
    rw [hphi, hz, mul_zero]
  calc
    _ ≤ ∏ p ∈ D.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := hK
    _ = (D : ℝ) / (Nat.totient D : ℝ) := by
      rw [hphi]
      simp only [Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv_rev]
      field_simp [hD0, hprod0] <;> ring

/-- A finite prime-power fibre is paid by its exact Euler local mass. -/
theorem finite_primeSupport_reciprocal_mass (e : ℕ) (he : 0 < e)
    (F : Finset ℕ) (hFpos : ∀ n ∈ F, 0 < n)
    (hFdiv : ∀ n ∈ F, e ∣ n)
    (hFprime : ∀ n ∈ F, n.primeFactors ⊆ e.primeFactors) :
    (∑ n ∈ F, 1 / (n : ℝ)) ≤ 1 / (Nat.totient e : ℝ) := by
  have hquot (n : ℕ) (hn : n ∈ F) : n / e ∈ Nat.factoredNumbers e.primeFactors := by
    have hn0 := (hFpos n hn).ne'
    have hd := hFdiv n hn
    apply Nat.mem_factoredNumbers_of_primeFactors_subset
    · exact (Nat.div_pos (Nat.le_of_dvd (hFpos n hn) hd) he).ne'
    · exact (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hd) hn0).trans (hFprime n hn)
  let encode (n : ℕ) (hn : n ∈ F) : Nat.factoredNumbers e.primeFactors :=
    ⟨n / e, hquot n hn⟩
  let T : Finset (Nat.factoredNumbers e.primeFactors) :=
    F.attach.image fun n => encode n.val n.property
  have hreindex : (∑ n ∈ F, 1 / (n : ℝ)) =
      (1 / (e : ℝ)) * ∑ k ∈ T, 1 / (k.val : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij encode ?_ ?_ ?_ ?_
    · intro n hn
      exact Finset.mem_image.mpr ⟨⟨n, hn⟩, Finset.mem_attach _ _, rfl⟩
    · intro n hn m hm hnm
      have hdiv : n / e = m / e := congrArg Subtype.val hnm
      calc
        n = e * (n / e) := (Nat.mul_div_cancel' (hFdiv n hn)).symm
        _ = e * (m / e) := congrArg (fun k => e * k) hdiv
        _ = m := Nat.mul_div_cancel' (hFdiv m hm)
    · intro k hk
      obtain ⟨n, _, hnk⟩ := Finset.mem_image.mp hk
      exact ⟨n.val, n.property, hnk⟩
    · intro n hn
      have hmul : (n : ℝ) = (e : ℝ) * ((n / e : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' (hFdiv n hn)).symm
      change 1 / (n : ℝ) = (1 / (e : ℝ)) * (1 / ((n / e : ℕ) : ℝ))
      rw [hmul]
      simp only [one_div, mul_inv_rev]
      ring
  have hEuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalHom) (fun {_} hp => reciprocalHom_prime_norm hp) e.primeFactors
  have hT := hEuler.2.summable.sum_le_tsum T
    (fun k _ => by change 0 ≤ 1 / (k.val : ℝ); positivity)
  rw [hEuler.2.tsum_eq] at hT
  have hfilter : e.primeFactors.filter Nat.Prime = e.primeFactors :=
    Finset.filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primeFactors hp)
  simp only [hfilter] at hT
  have hphi : (Nat.totient e : ℝ) = (e : ℝ) *
      ∏ p ∈ e.primeFactors, (1 - 1 / (p : ℝ)) := by
    have h := congrArg (algebraMap ℚ ℝ) (Nat.totient_eq_mul_prod_factors e)
    simpa only [map_natCast, map_mul, map_prod, map_sub, map_one, map_inv₀, one_div] using h
  calc
    _ = (1 / (e : ℝ)) * ∑ k ∈ T, 1 / (k.val : ℝ) := hreindex
    _ ≤ (1 / (e : ℝ)) *
        ∏ p ∈ e.primeFactors, (1 - 1 / (p : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 1 / ((e : ℝ) * ∏ p ∈ e.primeFactors, (1 - 1 / (p : ℝ))) := by
      simp only [Finset.prod_inv_distrib, one_div, mul_inv_rev]
      ring
    _ = _ := by rw [← hphi]

end
end ImbalancedChen.U9SemiprimeSwitch
