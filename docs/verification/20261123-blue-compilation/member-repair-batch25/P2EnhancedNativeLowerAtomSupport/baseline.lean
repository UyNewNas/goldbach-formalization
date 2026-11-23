import ImbalancedChen.P2EnhancedPrimeAtomSortedMerge
import ImbalancedChen.Part3ActualCompactAllRankSupport
import ImbalancedChen.ActualSmallRosser

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual LOWER native Rosser coefficient has even one-based set-prefix
tests. These produce the lower/odd zero-based indexed cubes, while its
physical cutoff w^2<=L supplies the separate strict head restriction.
This head restriction cannot be read from the lower parity tests alone.
The existing decreasing-filter identity and numerical admissibility
supplier are reused; no final square support is assumed.

A nonzero literal lower coefficient on the original target N*B therefore
gives its actual residual prime vector at L=Q/B. Its actual sieve-product
support supplies squarefreeness and coprimality with B. The new sorted
merge then retains full and selected gates on the real B*d prime vector.
No independent beta replacement, ordinary density, AP, K or enhanced gain
licence is asserted.
-/

namespace ImbalancedChen.P2EnhancedNativeLowerAtomSupport

noncomputable section

open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open MathlibNt.SieveTheory.LiLiuPrereqWFAdmissibility
open Part3.ActualCompactAllRankSupport
open P2EnhancedSelectedSortedDwellMerge P2EnhancedPrimeAtomSortedMerge
open scoped Classical

/-- Even set-prefix cardinality gives the actual lower/odd indexed cubes. -/
theorem lower_set_indexed_cubes {L : ℝ} (input : List ℕ)
    (hsort : input.Pairwise (· > ·)) (hadm : LowerAdmissibleSet L input.toFinset) :
    CubicPrefixBound false (fun p : ℕ => (p : ℝ)) L input := by
  intro i hi hpar
  change i % 2 = 1 at hpar
  have hfilter := decreasing_filter_eq_take input hsort i hi
  have hnd : (input.take (i + 1)).Nodup := hsort.nodup.sublist (List.take_sublist _ _)
  have hcard : (input.toFinset.filter (fun p => input[i] ≤ p)).card = i + 1 := by
    rw [hfilter, List.toFinset_card_of_nodup hnd, List.length_take,
      Nat.min_eq_left (by omega)]
  have heven : Even (input.toFinset.filter (fun p => input[i] ≤ p)).card := by
    rw [hcard, Nat.even_iff]
    omega
  have htest := hadm input[i] (List.mem_toFinset.mpr (List.getElem_mem hi)) heven
  have hprod : (input.take (i + 1)).toFinset.prod id = (input.take (i + 1)).prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnd
  rw [hfilter, hprod, List.take_succ_eq_append_getElem hi] at htest
  simpa only [List.prod_append, List.prod_singleton, Nat.cast_mul,
    actualNatList_cast_prod, pow_succ, mul_assoc, mul_comm, mul_left_comm] using htest

/-- Lower parity plus the ACTUAL physical head cutoff proves all four
numerical admissibility fields. Empty and unit atoms remain included. -/
theorem lower_set_numerical_admissible {w L : ℝ} (input : List ℕ)
    (hprime : ∀ p ∈ input, p.Prime) (hsort : input.Pairwise (· > ·))
    (hadm : LowerAdmissibleSet L input.toFinset)
    (hcut : ∀ p ∈ input, (p : ℝ) < w) (hlevel : w ^ 2 ≤ L) :
    Admissible false (fun p : ℕ => (p : ℝ)) L input := by
  refine ⟨?_, ?_, ?_, lower_set_indexed_cubes input hsort hadm⟩
  · intro p hp
    exact_mod_cast (hprime p hp).one_lt.le
  · intro i j hi hj hij
    by_cases heq : i = j
    · subst j
      exact le_rfl
    · have hlt := (List.pairwise_iff_getElem.mp hsort) i j hi hj (by omega)
      exact_mod_cast hlt.le
  · intro hlen
    have hp : (0 : ℝ) < input[0] := Nat.cast_pos.mpr (hprime _ (List.getElem_mem hlen)).pos
    have hw := hcut input[0] (List.getElem_mem hlen)
    have hsum : (0 : ℝ) < w + (input[0] : ℝ) := by linarith
    have hdiff := mul_pos (sub_pos.mpr hw) hsum
    apply (Real.lt_sqrt (Nat.cast_nonneg input[0])).mpr
    nlinarith only [hdiff, hlevel]

theorem lower_set_dwell_support {w L : ℝ} (input : List ℕ)
    (hprime : ∀ p ∈ input, p.Prime) (hsort : input.Pairwise (· > ·))
    (hadm : LowerAdmissibleSet L input.toFinset)
    (hcut : ∀ p ∈ input, (p : ℝ) < w) (hlevel : w ^ 2 ≤ L) :
    actualDwellSupport L input :=
  actualDwellSupport_of_admissible
    (lower_set_numerical_admissible input hprime hsort hadm hcut hlevel)

/-- Literal nonzero native lower coefficient produces its residual full
well vector. No support or admissibility conclusion is supplied by a caller. -/
theorem actual_minus_residual_well {N cap d : ℕ} {w L : ℝ}
    (hd : actualSmallRosserMinus N cap w L d ≠ 0) (hlevel : w ^ 2 ≤ L) :
    actualDwellSupport L d.primeFactorsList.reverse := by
  have ha := lowerWeight_active hd
  have hs := actualSmallRosserSupport_squarefree N cap w ha.1
  have hprime : ∀ p ∈ d.primeFactorsList.reverse, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)
  have hge : d.primeFactorsList.reverse.Pairwise (· ≥ ·) :=
    (Nat.primeFactorsList_sorted d).reverse.pairwise
  have hnd : d.primeFactorsList.reverse.Nodup := hs.nodup_primeFactorsList.reverse
  have hgt : d.primeFactorsList.reverse.Pairwise (· > ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hle := (List.pairwise_iff_getElem.mp hge) i j hi hj hij
    have hne := (List.pairwise_iff_getElem.mp hnd) i j hi hj hij
    omega
  have hsmall := (actualSmallRosserMinus_active hd).2.2
  apply lower_set_dwell_support d.primeFactorsList.reverse hprime hgt
  · simpa only [List.toFinset_reverse, Nat.toFinset_factors] using ha.2.2
  · intro p hp
    apply hsmall.2 p
    simpa only [Nat.toFinset_factors] using
      (List.mem_toFinset.mpr (List.mem_reverse.mp hp))
  · exact hlevel

/-- A real native lower residual atom is merged with its original prefix.
Its literal target N*B supplies the needed B-coprimality internally. -/
theorem native_minus_full_and_selected {N cap B d : ℕ} {Q w : ℝ}
    (old : List ℕ) (S : ℕ → Prop) (hB : old.prod = B) (hBsf : Squarefree B)
    (holdPrime : ∀ p ∈ old, p.Prime) (holdSort : old.Pairwise (· ≥ ·))
    (holdWell : actualDwellSupport Q old) (hgates : RemainingSquares Q old S)
    (hselected : ∀ p, S p → p ∈ old)
    (hd : actualSmallRosserMinus (N * B) cap w (Q / (B : ℝ)) d ≠ 0)
    (hlevel : w ^ 2 ≤ Q / (B : ℝ)) :
    actualDwellSupport Q ((B * d).primeFactorsList.reverse) ∧
      selected ((B * d).primeFactorsList.reverse) S = selected old S ∧
      actualDwellSupport (Q / ((selected old S).prod : ℝ))
        (remaining ((B * d).primeFactorsList.reverse) S) := by
  have hactive := actualSmallRosserMinus_active hd
  have hdsf := actualSmallRosserSupport_squarefree (N * B) cap w hactive.1
  have hdtarget := actualSmallRosserSupport_coprime_target (N * B) cap w hactive.1
  have hcop : B.Coprime d := (hdtarget.of_dvd_right (dvd_mul_left B N)).symm
  have hprod : d.primeFactorsList.reverse.prod = d := by
    rw [List.prod_reverse, Nat.prod_primeFactorsList hdsf.ne_zero]
  have hprime : ∀ p ∈ d.primeFactorsList.reverse, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)
  have h := prime_atom_full_and_selected old d.primeFactorsList.reverse S hB hprod hBsf hdsf hcop
    holdPrime hprime holdSort holdWell hgates hselected (actual_minus_residual_well hd hlevel)
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩

end
end ImbalancedChen.P2EnhancedNativeLowerAtomSupport
