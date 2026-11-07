import ImbalancedChen.P2EnhancedNegativeChildSignedModulus

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
The actual signed physical coefficient is NOT bounded by one. Its true
three-window occurrence multiplicity is controlled using separation of
the selected prime p>=a from all prime factors of the actual residual k<a.
The argument keeps p dividing old d and does not require squarefree d. -/

namespace ImbalancedChen.P2EnhancedNegativeChildMultiplicity

noncomputable section
open scoped Classical BigOperators
open Wu2008DoubleSieve P2EnhancedTwentyOneSameQWeighted
open P2EnhancedNegativeChildRosser P2EnhancedNegativeChildSignedModulus

def oldTag (m : Mark) : ℕ × Fin 3 := (m.1.1, m.1.2.1)

theorem separated_prime_residual_unique {d p r k s : ℕ} {a : ℝ}
    (hd : 0 < d) (hp : p.Prime) (hr : r.Prime) (hpa : a ≤ (p : ℝ))
    (hs : SmallPrimeSupportedAt a s) (hprod : d * p * k = d * r * s) :
    p = r ∧ k = s := by
  have hpk : p * k = r * s := Nat.eq_of_mul_eq_mul_left hd (by simpa only [mul_assoc] using hprod)
  have hnot : ¬ p ∣ s := by
    intro hps
    have hmem : p ∈ s.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hps, hs.1⟩
    exact (not_lt_of_ge hpa) (hs.2 p hmem)
  have hdiv : p ∣ r * s := by rw [← hpk]; exact dvd_mul_right p k
  have hpr : p ∣ r := (hp.dvd_mul.mp hdiv).resolve_right hnot
  have hpeq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos hpk⟩

/-- One actual old d and one original window occurrence j determine at
most one active p,k at each full modulus q. Distinct j remain distinct. -/
theorem oldTag_injective_on_fibre {N : ℕ} {Q : ℝ} {D : Finset ℕ}
    (hd : ∀ d ∈ D, 0 < d) (q : ℕ) :
    Set.InjOn oldTag (modulusFibre N Q D q : Set Mark) := by
  intro m hm n hn htag
  have hmdata := mark_original_data (Finset.mem_filter.mp hm).1
  have hndata := mark_original_data (Finset.mem_filter.mp hn).1
  have hprod := (Finset.mem_filter.mp hm).2.trans (Finset.mem_filter.mp hn).2.symm
  rcases m with ⟨⟨d, j, p⟩, k⟩
  rcases n with ⟨⟨e, i, r⟩, s⟩
  have hde : d = e := congrArg Prod.fst htag
  have hji : j = i := congrArg Prod.snd htag
  subst e
  subst i
  have hp := mem_primeWindow.mp hmdata.2.1
  have hr := mem_primeWindow.mp hndata.2.1
  have hs := (actualSmallRosserMinus_active hndata.2.2).2.2
  obtain ⟨hpr, hks⟩ := separated_prime_residual_unique (hd d hmdata.1)
    hp.1 hr.1 hp.2.2.1 hs hprod
  subst r
  subst s
  rfl

/-- Complete positive marked multiplicity, with the original sigma(d),
is at most THREE copies of the original total sigma mass. -/
theorem markedMultiplicityMass_le_three_mass (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d) (q : ℕ) :
    markedMultiplicityMass N Q D sigma q ≤ 3 * ∑ d ∈ D, sigma d := by
  let I := (modulusFibre N Q D q).image oldTag
  have hI : I ⊆ D.product (Finset.univ : Finset (Fin 3)) := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_product.mpr
      ⟨(mark_original_data (Finset.mem_filter.mp hm).1).1, Finset.mem_univ _⟩
  calc
    markedMultiplicityMass N Q D sigma q = ∑ t ∈ I, sigma t.1 := by
      unfold markedMultiplicityMass I
      rw [Finset.sum_image (oldTag_injective_on_fibre hd q)]
      rfl
    _ ≤ ∑ t ∈ D.product (Finset.univ : Finset (Fin 3)), sigma t.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun t ht _ => hsigma t.1 (Finset.mem_product.mp ht).1)
    _ = 3 * ∑ d ∈ D, sigma d := by
      rw [Finset.sum_product, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hmem
      simp <;> ring

/-- Actual signed rho inherits this proved multiplicity budget. There is
no independent hrho bound and no change to the underlying coefficient. -/
theorem physicalCoefficient_abs_le_three_mass (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d) (q : ℕ) :
    |physicalCoefficient N Q D sigma q| ≤ 3 * ∑ d ∈ D, sigma d :=
  (physicalCoefficient_abs_le_marked_mass N Q D sigma hsigma q).trans
    (markedMultiplicityMass_le_three_mass N Q D sigma hd hsigma q)

end
end ImbalancedChen.P2EnhancedNegativeChildMultiplicity
