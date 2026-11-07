import ImbalancedChen.U9NormalizerDominatesHarmonic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The exact D-smooth/D-coprime factor split and pinned finite-prime Euler
HasSum imply H_L≤(D/phi(D))*H_D(L), uniformly in EVERY positive D.
This is the finite Euler-decomposition proof of the same density factor
as prime deletion; it uses neither fixed-D asymptotics nor global harmonic
summability. The actual ordinary row normalizer and finite prime upper
bound acquire an explicit Euler-factor/logarithm main term.
-/

namespace ImbalancedChen.U9SemiprimeSwitch
noncomputable section
open Classical
open scoped BigOperators

def smoothPart (D n : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p => p ∈ D.primeFactors).prod

def roughPart (D n : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p => p ∉ D.primeFactors).prod

private theorem smooth_rough_product {D n : ℕ} (hn : n ≠ 0) :
    n = smoothPart D n * roughPart D n := by
  have hsplit (l : List ℕ) : l.prod =
      (l.filter fun p => p ∈ D.primeFactors).prod *
      (l.filter fun p => p ∉ D.primeFactors).prod := by
    induction l with
    | nil => simp
    | cons a l ih =>
        by_cases ha : a ∈ D.primeFactors <;>
          simp [ha, ih, mul_assoc, mul_comm, mul_left_comm]
  rw [smoothPart, roughPart, ← hsplit, Nat.prod_primeFactorsList hn]

def smoothLabel (D n : ℕ) : Nat.factoredNumbers D.primeFactors :=
  ⟨smoothPart D n, Nat.prod_mem_factoredNumbers D.primeFactors n⟩

private theorem roughPart_coprime (D n : ℕ) (hD : D ≠ 0) :
    Nat.Coprime (roughPart D n) D := by
  have hlist : ∀ l : List ℕ, (∀ p ∈ l, Nat.Coprime p D) → Nat.Coprime l.prod D := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
        intro h
        exact Nat.coprime_mul_iff_left.mpr
          ⟨h a (List.mem_cons_self _ _), ih (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩
  apply hlist
  intro p hp
  obtain ⟨hpList, hpD⟩ := List.mem_filter.mp hp
  have hpNot : p ∉ D.primeFactors := by simpa only [decide_eq_true_eq] using hpD
  have hprime := Nat.prime_of_mem_primeFactorsList hpList
  apply hprime.coprime_iff_not_dvd.mpr
  intro hd
  have hmem := Nat.mem_primeFactors.mpr ⟨hprime, hd, hD⟩
  exact hpNot hmem

/-- Every harmonic index splits into an actual D-smooth factor and a
positive D-coprime factor at most L. The finite image retains collisions
correctly through the exact product identity. -/
theorem harmonic_le_euler_mul_coprimeHarmonic (D L : ℕ) (hD : 0 < D) :
    (harmonic L : ℝ) ≤ ((D : ℝ) / (Nat.totient D : ℝ)) * coprimeHarmonic D L := by
  let encode (n : ℕ) : Nat.factoredNumbers D.primeFactors × ℕ :=
    (smoothLabel D n, roughPart D n)
  let F := (Finset.Icc 1 L).image encode
  let K := F.image Prod.fst
  let R := (Finset.Icc 1 L).filter fun r => Nat.Coprime r D
  have hprod (n : ℕ) (hn : n ∈ Finset.Icc 1 L) :
      n = (encode n).1.val * (encode n).2 := smooth_rough_product
        (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  have hinj : Set.InjOn encode (Finset.Icc 1 L : Set ℕ) := by
    intro n hn m hm heq
    exact (hprod n hn).trans ((congrArg (fun x => x.1.val * x.2) heq).trans (hprod m hm).symm)
  have hreindex : (harmonic L : ℝ) =
      ∑ x ∈ F, (1 / (x.1.val : ℝ)) * (1 / (x.2 : ℝ)) := by
    rw [F, Finset.sum_image hinj]
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    apply Finset.sum_congr rfl
    intro n hn
    have hR : (n : ℝ) = ((encode n).1.val : ℝ) * ((encode n).2 : ℝ) := by
      exact_mod_cast hprod n hn
    rw [hR]
    simp only [one_div, mul_inv_rev]
    ring
  have hsubset : F ⊆ K ×ˢ R := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hsplit := hprod n hn
    have hsmpos : 0 < (encode n).1.val :=
      Nat.pos_of_ne_zero (smoothLabel D n).property.1
    have hrpos : 0 < (encode n).2 := by
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      rw [hsplit] at hnpos
      exact (Nat.mul_pos_iff.mp hnpos).2
    have hrle : (encode n).2 ≤ n := by
      calc
        (encode n).2 ≤ (encode n).1.val * (encode n).2 := Nat.le_mul_of_pos_left _ hsmpos
        _ = n := hsplit.symm
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨encode n, Finset.mem_image.mpr ⟨n, hn, rfl⟩, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hrpos, hrle.trans (Finset.mem_Icc.mp hn).2⟩, roughPart_coprime D n hD.ne'⟩
  have hHnonneg : 0 ≤ coprimeHarmonic D L :=
    Finset.sum_nonneg fun _ _ => by positivity
  calc
    _ = ∑ x ∈ F, (1 / (x.1.val : ℝ)) * (1 / (x.2 : ℝ)) := hreindex
    _ ≤ ∑ x ∈ K ×ˢ R, (1 / (x.1.val : ℝ)) * (1 / (x.2 : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
    _ = (∑ k ∈ K, 1 / (k.val : ℝ)) * coprimeHarmonic D L := by
      simp only [Finset.sum_product, Finset.sum_mul_sum, coprimeHarmonic, R]
    _ ≤ _ := mul_le_mul_of_nonneg_right (finite_factored_reciprocal_mass D hD K) hHnonneg

theorem euler_mul_harmonic_le_coprimeHarmonic (D L : ℕ) (hD : 0 < D) :
    ((Nat.totient D : ℝ) / (D : ℝ)) * (harmonic L : ℝ) ≤ coprimeHarmonic D L := by
  have h := harmonic_le_euler_mul_coprimeHarmonic D L hD
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hphi0 : (Nat.totient D : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hD).ne'
  calc
    _ ≤ ((Nat.totient D : ℝ) / (D : ℝ)) *
        (((D : ℝ) / (Nat.totient D : ℝ)) * coprimeHarmonic D L) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp [hD0, hphi0] <;> ring

/-- The required dimension-one normalizer lower bound is uniform in D. -/
theorem ordinaryG_lower_harmonic_log (D L z : ℕ) (hD : 0 < D) (hLz : L < z) :
    ((Nat.totient D : ℝ) / (D : ℝ)) * (harmonic L : ℝ) ≤ ordinaryG D z L ∧
      ((Nat.totient D : ℝ) / (D : ℝ)) * Real.log (L + 1 : ℕ) ≤ ordinaryG D z L := by
  have hmain := (euler_mul_harmonic_le_coprimeHarmonic D L hD).trans
    (coprimeHarmonic_le_ordinaryG D L z hLz)
  exact ⟨hmain, (mul_le_mul_of_nonneg_left (log_add_one_le_harmonic L) (by positivity)).trans hmain⟩

/-- The original row finite upper now has an explicit Euler/logarithm
main term. Its coupled analytic aggregation remains a separate obligation. -/
theorem actualPrimeRowAP_le_explicit_euler_log
    (N d z L : ℕ) (hL : 1 ≤ L) (hLz : L < z) (X : ℝ) (p q : ℕ)
    (hf : factorAllowed N p q) (hX : 0 ≤ X) (hd : 0 < d) (hNd : Nat.Coprime N d) :
    ((actualPrimeRowAP N X p q d).card : ℝ) ≤
      (((d * N : ℕ) : ℝ) / (Nat.totient (d * N) : ℝ)) *
        endpointMass N X p q d 1 / Real.log (L + 1 : ℕ) +
        2 * (N.divisors.card : ℝ) * (L : ℝ) ^ 2 + (z : ℝ) := by
  have hNpos : 0 < N := (mem_chenAdditivePrimeCarrier.mp hf.1).2.1.pos.trans
    (mem_chenAdditivePrimeCarrier.mp hf.1).1
  have hD := mul_pos hd hNpos
  have hphi : (0 : ℝ) < Nat.totient (d * N) := by exact_mod_cast Nat.totient_pos.mpr hD
  have hDR : (0 : ℝ) < ((d * N : ℕ) : ℝ) := by exact_mod_cast hD
  have hlog : 0 < Real.log (L + 1 : ℕ) := Real.log_pos (by exact_mod_cast (show 1 < L + 1 by omega))
  have hmass : 0 ≤ endpointMass N X p q d 1 := by
    rw [← rowAPDiv_card_real_eq_endpointMass hf hX hd zero_lt_one]
    positivity
  have hG := (ordinaryG_lower_harmonic_log (d * N) L z hD hLz).2
  have hdiv := div_le_div_of_nonneg_left hmass (mul_pos (div_pos hphi hDR) hlog) hG
  have heq : endpointMass N X p q d 1 /
      (((Nat.totient (d * N) : ℝ) / ((d * N : ℕ) : ℝ)) * Real.log (L + 1 : ℕ)) =
      (((d * N : ℕ) : ℝ) / (Nat.totient (d * N) : ℝ)) *
        endpointMass N X p q d 1 / Real.log (L + 1 : ℕ) := by
    field_simp [hphi.ne', hDR.ne', hlog.ne'] <;> ring
  rw [heq] at hdiv
  have hrow := actualPrimeRowAP_le_explicit_finite N d z L hL X p q hf hX hd hNd
  linarith

end
end ImbalancedChen.U9SemiprimeSwitch
