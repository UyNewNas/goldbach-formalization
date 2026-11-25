import ImbalancedChen.P5ZU1011OriginalFifteenTopFourUniqueness
import Mathlib.Data.List.Sort

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Cross-policy actual native factorization interface for the static FULL16
compiler. The earlier concrete15 injection is not assumed to cover a new
mark carrier. Its public prefix objects are reused; this extension uses
Mathlib's sorted-permutation equality and sorted prime-factor lists, rather
than repeating its private top-prefix induction. Structural support inputs
are explicit: actual original ordered prime source, strict residual prime
support, and each row's own cutoff<=its own smallest prefix prime. No
uniqueness, unit amplitude, density, distribution or count bound is an input.
-/

namespace ImbalancedChen.P5Z.U1011StaticNativeTopFourExtension

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenTopFourUniqueness P5U1011JointOverlap

private theorem actual_prefix_prime_order {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) :
    (prefix t).Pairwise (· ≥ ·) ∧ (∀ p ∈ prefix t, Nat.Prime p) ∧
      (∀ p ∈ prefix t, t.1.1 ≤ p) := by
  obtain ⟨h1,h2,h3,h4,h12,h23,h34⟩ := joint_carrier_order ht
  refine ⟨?_,?_,?_⟩
  · simp [prefix,List.pairwise_cons] <;> omega
  · intro p hp
    simp only [prefix,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (mem_chenAdditivePrimeCarrier.mp h4).2.1
    · exact (mem_chenAdditivePrimeCarrier.mp h3).2.1
    · exact (mem_chenAdditivePrimeCarrier.mp h2).2.1
    · exact (mem_chenAdditivePrimeCarrier.mp h1).2.1
  · intro p hp
    simp only [prefix,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> omega

private theorem residual_below_prefix {N d : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) {Z : ℝ} (hd : SmallPrimeSupportedAt Z d)
    (hZ : Z ≤ (t.1.1 : ℝ)) : ∀ r ∈ d.primeFactorsList, ∀ p ∈ prefix t, r < p := by
  intro r hr p hp
  have hpf : r ∈ d.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_of_mem_primeFactorsList hr,Nat.dvd_of_mem_primeFactorsList hr,hd.1⟩
  have hlast := (actual_prefix_prime_order ht).2.2 p hp
  have hlastR : (t.1.1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlast
  have h : (r : ℝ) < (p : ℝ) := ((hd.2 r hpf).trans_le hZ).trans_le hlastR
  exact_mod_cast h

private theorem sorted_native_factor_list {N d : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) {Z : ℝ} (hd : SmallPrimeSupportedAt Z d)
    (hZ : Z ≤ (t.1.1 : ℝ)) :
    (prefix t ++ d.primeFactorsList.reverse).Pairwise (· ≥ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨(actual_prefix_prime_order ht).1,(Nat.primeFactorsList_sorted d).reverse.pairwise,?_⟩
  intro p hp r hr
  exact (residual_below_prefix ht hd hZ r (List.mem_reverse.mp hr) p hp).le

/-- Changing from an ordinary selected-mask row to a true W row may
change Z and rho, but cannot change the top-four factorization of q. -/
theorem actual_native_tuple_divisor_unique {N d e : ℕ} {E : ℕ × ℕ → Prop} {t s : Four}
    (ht : t ∈ jointSelector N E) (hs : s ∈ jointSelector N E)
    {Zt Zs : ℝ} (hd : SmallPrimeSupportedAt Zt d) (he : SmallPrimeSupportedAt Zs e)
    (hZt : Zt ≤ (t.1.1 : ℝ)) (hZs : Zs ≤ (s.1.1 : ℝ))
    (hmod : fullPrefix t * d = fullPrefix s * e) : t = s ∧ d = e := by
  have hprimeT : ∀ p ∈ prefix t ++ d.primeFactorsList.reverse, Nat.Prime p := by
    intro p hp
    exact (List.mem_append.mp hp).elim ((actual_prefix_prime_order ht).2.1 p)
      (fun h => Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp h))
  have hprimeS : ∀ p ∈ prefix s ++ e.primeFactorsList.reverse, Nat.Prime p := by
    intro p hp
    exact (List.mem_append.mp hp).elim ((actual_prefix_prime_order hs).2.1 p)
      (fun h => Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp h))
  have hprod : (prefix t ++ d.primeFactorsList.reverse).prod =
      (prefix s ++ e.primeFactorsList.reverse).prod := by
    rw [List.prod_append,List.prod_append,List.prod_reverse,List.prod_reverse,
      prefix_prod,prefix_prod,Nat.prod_primeFactorsList hd.1,Nat.prod_primeFactorsList he.1]
    exact hmod
  have hperm := (Nat.primeFactorsList_unique hprod hprimeT).trans
    (Nat.primeFactorsList_unique (rfl : (prefix s ++ e.primeFactorsList.reverse).prod =
      (prefix s ++ e.primeFactorsList.reverse).prod) hprimeS).symm
  have hlist := hperm.eq_of_pairwise' (sorted_native_factor_list ht hd hZt)
    (sorted_native_factor_list hs he hZs)
  have hpref : prefix t = prefix s := by
    have htake := congrArg (List.take 4) hlist
    simpa [prefix] using htake
  have htuple : t = s := prefix_injective hpref
  have hb : 0 < fullPrefix t := by
    rw [fullPrefix_eq_multiplier]
    exact joint_multiplier_pos ht
  have hmod' := hmod
  rw [← htuple] at hmod'
  exact ⟨htuple,Nat.eq_of_mul_eq_mul_left hb hmod'⟩

end
end ImbalancedChen.P5Z.U1011StaticNativeTopFourExtension
