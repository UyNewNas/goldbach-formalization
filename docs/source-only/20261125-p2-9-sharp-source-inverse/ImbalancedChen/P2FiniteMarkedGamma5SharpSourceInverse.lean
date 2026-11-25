import ImbalancedChen.P2FiniteMarkedGamma5LogExtension
import ImbalancedChen.P2MarkedPrimeDivisorFloorCore
import Mathlib.Data.List.OfFn

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

Pointwise inverse for the original sharp Gamma5 pair/rough-cofactor
source. The original raw gates, fresh-prime target coprimality and prime
tail coordinates recover the original badLabels and roughNumbers.
The inclusive bad wall and ordinary product cap, strict pair order and
upper endpoints, and nondecreasing tail order are kept literally.

The tail may be empty and may contain repeated primes. Its canonical
factorization is recovered with the existing primeFactorsList_unique
theorem; no new factorization theory is supplied. The old prefix enters
through the unchanged positive integer d. This does not yet reindex
a marked-history sum or compare the whole smooth profile with its sharp
ordinary mass.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5SharpSourceInverse
noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2SeedOmegaLiteralFibre (a0 a2)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedSwitchedUnsiftedSource (pairLabels badPair)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels pair_prod_pos)
open P2EnhancedBadGamma5ConstantCutoff (original_cutoff)
open Part5OriginalH430ClassicalFixedClampGeometry (prime_divisor_floor)
open P2FiniteMarkedGamma5LogExtension
open scoped Classical BigOperators

/-- Literal sharp Gamma5 geometry recovers its original ordered prime
pair and inclusive rough cofactor, with the same canonical ordered tail.
No target coprimality or distinctness condition is added to the tail. -/
theorem raw_source_inverse {N d r : ℕ} {Q : ℝ}
    {qs : Fin 2 → ℕ} {rs : Fin r → ℕ}
    (hd : 0 < d)
    (hq : ∀ i, (qs i).Prime ∧ (qs i).Coprime N)
    (hr : ∀ i, (rs i).Prime)
    (hraw : ∀ g ∈ program r, raw N Q d qs rs g) :
    let l : List ℕ := [qs 0, qs 1]
    let m : ℕ := (List.ofFn rs).prod
    l ∈ badLabels N Q d ∧
      m ∈ roughNumbers ((N : ℝ) / (d * l.prod : ℕ)) (cutoff Q d (227 / 50)) ∧
      m.primeFactorsList = List.ofFn rs := by
  let l : List ℕ := [qs 0, qs 1]
  let L : List ℕ := List.ofFn rs
  change l ∈ badLabels N Q d ∧
    L.prod ∈ roughNumbers ((N : ℝ) / (d * l.prod : ℕ)) (cutoff Q d (227 / 50)) ∧
    L.prod.primeFactorsList = L
  have hwindow (i : Fin 2) :
      qs i ∈ primeWindow N (cutoff Q d (227 / 50)) (cutoff Q d (29 / 10)) := by
    refine mem_primeWindow.mpr ⟨(hq i).1, (hq i).2, ?_, ?_⟩
    · rw [original_cutoff Q d]
      exact hraw (.lower i) (mem_program.mpr trivial)
    · simpa only [cutoff, show (1 / (29 / 10) : ℝ) = a2 by norm_num [a2]] using
        hraw (.upper i) (mem_program.mpr trivial)
  have hpair : l ∈ pairLabels N Q d := by
    unfold pairLabels
    apply (secondFunctionalMother_tuple_mem _ _ _).mpr
    refine ⟨by simp [l], ?_, ?_⟩
    · have horder : qs 0 < qs 1 :=
        hraw .pairOrder (mem_program.mpr trivial)
      simpa [l] using horder
    · intro q hqmem
      have hcases : q = qs 0 ∨ q = qs 1 := by
        simpa only [l, List.mem_cons, List.not_mem_nil, or_false] using hqmem
      rcases hcases with rfl | rfl
      · exact hwindow 0
      · exact hwindow 1
  have hbad : badPair Q d l := by
    simpa [badPair, l, raw] using
      hraw .badSquare (mem_program.mpr trivial)
  have hL : ∀ q ∈ L, q.Prime ∧ cutoff Q d (227 / 50) ≤ (q : ℝ) := by
    intro q hqmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hqmem
    refine ⟨hr i, ?_⟩
    rw [original_cutoff Q d]
    exact hraw (.rough i) (mem_program.mpr trivial)
  have hpositive : 0 < L.prod := List.prod_pos (fun q hqmem => (hL q hqmem).1.pos)
  have hden : 0 < d * l.prod := Nat.mul_pos hd (pair_prod_pos hpair)
  have hproduct : fullProduct d qs rs = d * l.prod * L.prod := by
    simp only [fullProduct, l, L, List.prod_cons, List.prod_nil, mul_one, List.prod_ofFn]
    ring
  have hcap : d * l.prod * L.prod ≤ N := by
    rw [← hproduct]
    exact hraw .product (mem_program.mpr trivial)
  have hrough :
      L.prod ∈ roughNumbers ((N : ℝ) / (d * l.prod : ℕ)) (cutoff Q d (227 / 50)) := by
    refine mem_roughNumbers.mpr ⟨hpositive, ?_, ?_⟩
    · apply (le_div_iff₀ (Nat.cast_pos.mpr hden)).mpr
      exact_mod_cast (by simpa only [Nat.mul_comm] using hcap :
        L.prod * (d * l.prod) ≤ N)
    · intro q hqprime hqdiv
      exact prime_divisor_floor hL q hqprime hqdiv
  have hsorted : L.Pairwise (· ≤ ·) := by
    change (List.ofFn rs).Pairwise (· ≤ ·)
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hraw (.tailOrder i j) (mem_program.mpr hij)
  have hcanonical : L = L.prod.primeFactorsList :=
    (Nat.primeFactorsList_unique rfl (fun q hqmem => (hL q hqmem).1)).eq_of_pairwise'
      hsorted (Nat.primeFactorsList_sorted _).pairwise
  exact ⟨mem_filter.mpr ⟨hpair, hbad⟩, hrough, hcanonical.symm⟩

end
end ImbalancedChen.P2FiniteMarkedGamma5SharpSourceInverse
