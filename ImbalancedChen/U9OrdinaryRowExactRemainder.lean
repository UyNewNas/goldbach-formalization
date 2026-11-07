import ImbalancedChen.U9OrdinaryRowSieveModel

/-!
# The matching U9 row sieve has explicit CRT/endpoint remainders

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The raw source mass is the actual preprime AP-row cardinal. Its divisor
mass is the actual same-row AP/divisibility cardinal. Their exact values
are sums over full lcm(lcm(d,e),N) admissible residues with the original
factor-dependent endpoint ceilings. There is no AP saving assumption.
-/

namespace ImbalancedChen.U9SemiprimeSwitch

noncomputable section
open Classical
open scoped BigOperators

def endpointMass (N : ℕ) (X : ℝ) (p q d e : ℕ) : ℝ :=
  ∑ a ∈ rowResidues N p q d e,
    (endpointCount (rowLower N X p q) (rowUpper N p q) (rowModulus N d e) a : ℝ)

theorem rowAPDiv_card_real_eq_endpointMass {N p q d e : ℕ} {X : ℝ}
    (hf : factorAllowed N p q) (hX : 0 ≤ X) (hd : 0 < d) (he : 0 < e) :
    ((rowAPDiv N X p q d e).card : ℝ) = endpointMass N X p q d e := by
  have h := congrArg (fun x : ℤ => (x : ℝ))
    (rowAPDiv_card_eq_exact_residue_endpoints hf hX hd he)
  simpa only [Int.cast_natCast, Int.cast_sum, endpointMass] using h

theorem row_divisor_filter (N p q d e : ℕ) (X : ℝ) :
    (rowAPDiv N X p q d 1).filter (fun r => e ∣ r) = rowAPDiv N X p q d e := by
  ext r
  simp only [rowAPDiv, Finset.mem_filter, one_dvd, and_true, and_assoc]

theorem ordinaryRow_multSum (N d z : ℕ) (X : ℝ) (p q e : ℕ) :
    (ordinaryRowSieve N d z X p q).multSum e =
      ((rowAPDiv N X p q d e).card : ℝ) := by
  change (∑ r ∈ rowAPDiv N X p q d 1, if e ∣ r then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter, row_divisor_filter]
  simp

theorem ordinaryRow_remainder_raw (N d z : ℕ) (X : ℝ) (p q e : ℕ) :
    (ordinaryRowSieve N d z X p q).rem e =
      ((rowAPDiv N X p q d e).card : ℝ) -
        ((rowAPDiv N X p q d 1).card : ℝ) / (e : ℝ) := by
  rw [BoundingSieve.rem, ordinaryRow_multSum]
  change _ - (1 / (e : ℝ)) * _ = _
  ring

/-- The complete finite remainder is now explicit at the original row
endpoints, for every positive divisor e and every positive original d. -/
theorem ordinaryRow_remainder_endpoints {N p q d e z : ℕ} {X : ℝ}
    (hf : factorAllowed N p q) (hX : 0 ≤ X) (hd : 0 < d) (he : 0 < e) :
    (ordinaryRowSieve N d z X p q).rem e =
      endpointMass N X p q d e - endpointMass N X p q d 1 / (e : ℝ) := by
  rw [ordinaryRow_remainder_raw,
    rowAPDiv_card_real_eq_endpointMass hf hX hd he,
    rowAPDiv_card_real_eq_endpointMass hf hX hd zero_lt_one]

def siftedPreprimeRow (N d z : ℕ) (X : ℝ) (p q : ℕ) : Finset ℕ :=
  (rowAPDiv N X p q d 1).filter fun r => Nat.Coprime r (sieveProduct (d * N) z)

theorem ordinaryRow_siftedSum (N d z : ℕ) (X : ℝ) (p q : ℕ) :
    (ordinaryRowSieve N d z X p q).siftedSum =
      ((siftedPreprimeRow N d z X p q).card : ℝ) := by
  change (∑ r ∈ rowAPDiv N X p q d 1,
    if Nat.Coprime (sieveProduct (d * N) z) r then (1 : ℝ) else 0) = _
  simp_rw [Nat.coprime_comm]
  rw [← Finset.sum_filter]
  simp only [siftedPreprimeRow, Finset.sum_const, nsmul_eq_mul, mul_one]

end
end ImbalancedChen.U9SemiprimeSwitch
