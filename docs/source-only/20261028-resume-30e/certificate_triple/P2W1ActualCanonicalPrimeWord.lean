import ImbalancedChen.P2W1UnsiftedPrimeProductSource

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual independent W1 labels have a canonical complete prime word:
the immutable old word, three distinguished strictly ordered slots, then
the primeFactorsList of the EXACT integer tail. Repeated tail factors
are retained with multiplicity; n=1 gives the empty tail, not a deletion.
The rank bound counts every slot and is uniform before N is selected.
This does not assert the still missing positive-K geometric/PP licence.
-/
namespace ImbalancedChen.P2W1ActualCanonicalPrimeWord
noncomputable section
open scoped Classical BigOperators
open P2W1UnsiftedPrimeProductSource
open P2EnhancedW1OrderedPositiveTripleWord
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalActionMassBound (W1Anchor)

def primeWord (old : List ℕ) (a : Label) : List ℕ :=
  old ++ [first a.1,middle a.1,last a.1] ++ a.2.primeFactorsList

theorem primeWord_product {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {a : Label} (ha : Geometry N Q old i j a) :
    (primeWord old a).prod = product old a := by
  simp only [primeWord,List.prod_append,List.prod_cons,List.prod_nil,
    mul_one,Nat.prod_primeFactorsList ha.2.2.2.2.2.1.ne',product,tripleProduct]
  ring

theorem primeWord_primes {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {a : Label} (hold : ∀ p ∈ old, Nat.Prime p)
    (ha : Geometry N Q old i j a) : ∀ p ∈ primeWord old a, Nat.Prime p := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact hold p hp
    · simp only [List.mem_cons,List.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact ha.1.1
      · exact ha.2.1.1
      · exact ha.2.2.1.1
  · exact Nat.prime_of_mem_primeFactorsList hp

/-- Each canonical tail factor is an actual divisor of n and therefore
inherits the original q2 roughness, including repeated prime slots. -/
theorem tail_factor_lower {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {a : Label} (ha : Geometry N Q old i j a) {p : ℕ}
    (hp : p ∈ a.2.primeFactorsList) : middle a.1 ≤ p :=
  ha.2.2.2.2.2.2.1 p (Nat.prime_of_mem_primeFactorsList hp)
    (Nat.dvd_of_mem_primeFactorsList hp)

theorem primeWord_fixed_power {N : ℕ} {Q eta : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {a : Label}
    (ha : Geometry N Q old i j a)
    (hold : ∀ p ∈ old, (N : ℝ)^eta ≤ (p : ℝ))
    (hcut : (N : ℝ)^eta ≤ cutoff Q old.prod (W1Anchor j)) :
    ∀ p ∈ primeWord old a, (N : ℝ)^eta ≤ (p : ℝ) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact hold p hp
    · simp only [List.mem_cons,List.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hcut.trans ha.1.2.1
      · exact hcut.trans ha.2.1.2.1
      · exact hcut.trans ha.2.2.1.2.1
  · have hrough : (middle a.1 : ℝ) ≤ p := by exact_mod_cast tail_factor_lower ha hp
    exact hcut.trans (ha.2.1.2.1.trans hrough)

private theorem list_power_le_product (w : List ℕ) (z : ℝ) (hz : 0 ≤ z)
    (hw : ∀ p ∈ w, z ≤ (p : ℝ)) : z^w.length ≤ (w.prod : ℝ) := by
  revert hw
  induction w with
  | nil => intro _; simp only [List.length_nil,pow_zero,List.prod_nil,Nat.cast_one,le_refl]
  | cons p w ih =>
      intro hw
      have hp := hw p (List.mem_cons_self _ _)
      have hrest : ∀ q ∈ w, z ≤ (q : ℝ) :=
        fun q hq => hw q (List.mem_cons_of_mem _ hq)
      rw [List.length_cons,pow_succ,List.prod_cons,Nat.cast_mul]
      calc
        z^w.length*z ≤ (w.prod : ℝ)*(p : ℝ) :=
          mul_le_mul (ih hrest) hp hz (Nat.cast_nonneg _)
        _ = (p : ℝ)*(w.prod : ℝ) := mul_comm _ _

/-- A fixed positive power floor bounds the FULL canonical rank, with
prime powers counted repeatedly. No squarefree truncation is used. -/
theorem primeWord_rank_le_inv_power {N : ℕ} {Q eta : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {a : Label}
    (hN : 1 < N) (heta : 0 < eta) (ha : Geometry N Q old i j a)
    (hold : ∀ p ∈ old, (N : ℝ)^eta ≤ (p : ℝ))
    (hcut : (N : ℝ)^eta ≤ cutoff Q old.prod (W1Anchor j)) :
    ((primeWord old a).length : ℝ) ≤ 1/eta := by
  have hpow := list_power_le_product (primeWord old a) ((N : ℝ)^eta)
    (Real.rpow_nonneg (Nat.cast_nonneg N) eta) (primeWord_fixed_power ha hold hcut)
  have hprod : ((primeWord old a).prod : ℝ) ≤ (N : ℝ) := by
    rw [primeWord_product ha]
    exact_mod_cast ha.2.2.2.2.2.2.2.le
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hpowEq : (N : ℝ)^(eta*((primeWord old a).length : ℝ)) =
      ((N : ℝ)^eta)^(primeWord old a).length := by
    rw [Real.rpow_mul (Nat.cast_nonneg N),Real.rpow_natCast]
  have hpowLe : (N : ℝ)^(eta*((primeWord old a).length : ℝ)) ≤ (N : ℝ)^1 := by
    rw [hpowEq,Real.rpow_one]
    exact hpow.trans hprod
  have he := (Real.rpow_le_rpow_left_iff hNreal).mp hpowLe
  apply (le_div_iff₀ heta).mpr
  nlinarith only [he]

/-- R is selected from eta alone, before N or an action/source label.
The predicate is on the actual complete canonical W1 word. -/
theorem exists_uniform_rank_cap (eta : ℝ) (heta : 0 < eta) :
    ∃ R : ℕ, ∀ {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10} {a : Label},
      1 < N → Geometry N Q old i j a →
      (∀ p ∈ old, (N : ℝ)^eta ≤ (p : ℝ)) →
      (N : ℝ)^eta ≤ cutoff Q old.prod (W1Anchor j) →
      (primeWord old a).length ≤ R := by
  obtain ⟨R,hR⟩ := exists_nat_gt (1/eta)
  refine ⟨R,?_⟩
  intro N Q old i j a hN ha hold hcut
  have hle := (primeWord_rank_le_inv_power hN heta ha hold hcut).trans hR.le
  exact_mod_cast hle

/-- The boundary n=1 remains an ordinary canonical source word. -/
theorem primeWord_unit_tail (old : List ℕ) (t : TripleLabel) :
    primeWord old (t,1) = old ++ [first t,middle t,last t] := by
  simp [primeWord]

end
end ImbalancedChen.P2W1ActualCanonicalPrimeWord
