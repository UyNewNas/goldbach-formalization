import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.CoprimeRecentering

/-!
# P4B: exact primitive-modulus endpoint removal

SOURCE-ONLY / YELLOW / UNCOMPILED.

The actual displayed modulus carrier contains only positive squarefree
integers. Modulus one contributes zero to both real signed functionals and
to each outer primitive atom, independently of roughness or weight signs.
The final active carrier keeps the identical attached rho and only its
nonzero terms at moduli greater than one; all sum identities are exact.
-/

namespace ImbalancedChen.P4BPrimitiveModulusEndpoints

noncomputable section
open scoped BigOperators

/-- Positivity is a proved consequence of actual support squarefreeness. -/
theorem actualSmallRoughModuli_pos
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ actualSmallRoughModuli retainOdd N cap w z) : 0 < d := by
  exact Nat.pos_of_ne_zero (actualSmallRoughModuli_squarefree retainOdd N cap w z hd).ne_zero

theorem attachedUpperModuli_pos
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N : ℕ) {d : ℕ} (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    0 < d := by
  exact actualSmallRoughModuli_pos (retain N) N (cap N) _ _ hd

/-- There is no modulus-zero atom in the actual attached carrier. -/
theorem zero_not_mem_attachedUpperModuli
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ) :
    0 ∉ attachedUpperModuli nu r epsilon retain cap N := by
  intro hzero
  have hpos := attachedUpperModuli_pos nu r epsilon retain cap N hzero
  omega

/-- Removing modulus one leaves only genuine positive moduli greater
than one, even when the displayed coefficient happens to be zero. -/
theorem attachedUpperModuli_erase_one_gt_one
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N : ℕ) {d : ℕ}
    (hd : d ∈ (attachedUpperModuli nu r epsilon retain cap N).erase 1) : 1 < d := by
  obtain ⟨hdne, hdmem⟩ := Finset.mem_erase.mp hd
  have hpos := attachedUpperModuli_pos nu r epsilon retain cap N hdmem
  omega

/-- Every integer lies in the unique residue class modulo one. -/
theorem realHalfProductCongruenceMass_one (b : ℝ) (N : ℕ) (T : ℝ) :
    realHalfProductCongruenceMass b N T 1 =
      ((realHalfProductSource b N T).card : ℝ) := by
  classical
  have hfilter : (realHalfProductSource b N T).filter
      (fun m => Nat.ModEq 1 m N) = realHalfProductSource b N T := by
    apply Finset.filter_eq_self.mpr
    intro m _hm
    change m % 1 = N % 1
    simp only [Nat.mod_one]
  rw [realHalfProductCongruenceMass, hfilter]

/-- Coprimality to one never removes a source member. -/
theorem realHalfProductCoprimeMass_one (b : ℝ) (N : ℕ) (T : ℝ) :
    realHalfProductCoprimeMass b N T 1 =
      ((realHalfProductSource b N T).card : ℝ) := by
  classical
  have hfilter : (realHalfProductSource b N T).filter
      (fun m => Nat.Coprime m 1) = realHalfProductSource b N T := by
    apply Finset.filter_eq_self.mpr
    intro m _hm
    change Nat.gcd m 1 = 1
    simp
  rw [realHalfProductCoprimeMass, hfilter]

theorem real_distribution_kernel_one (b : ℝ) (N : ℕ) (T : ℝ) :
    realHalfProductCongruenceMass b N T 1 -
      realHalfProductCoprimeMass b N T 1 / (Nat.totient 1 : ℝ) = 0 := by
  rw [realHalfProductCongruenceMass_one, realHalfProductCoprimeMass_one]
  simp

theorem real_coprime_kernel_one (b : ℝ) (N : ℕ) (T : ℝ) :
    (realHalfProductCoprimeMass b N T 1 -
      ((realHalfProductSource b N T).card : ℝ)) / (Nat.totient 1 : ℝ) = 0 := by
  rw [realHalfProductCoprimeMass_one]
  simp only [sub_self, zero_div]

/-- Explicit same-rho summands vanish at modulus one for any rho. -/
theorem real_distribution_summand_one
    (b : ℝ) (N : ℕ) (T : ℝ) (rho : ℕ → ℝ) :
    rho 1 * (realHalfProductCongruenceMass b N T 1 -
      realHalfProductCoprimeMass b N T 1 / (Nat.totient 1 : ℝ)) = 0 := by
  rw [real_distribution_kernel_one, mul_zero]

theorem real_coprime_summand_one
    (b : ℝ) (N : ℕ) (T : ℝ) (rho : ℕ → ℝ) :
    rho 1 * ((realHalfProductCoprimeMass b N T 1 -
      ((realHalfProductSource b N T).card : ℝ)) / (Nat.totient 1 : ℝ)) = 0 := by
  rw [real_coprime_kernel_one, mul_zero]

/-- Finite erasure is exact whenever the erased atom is zero. -/
theorem signed_sum_eq_erase_one
    (Q : Finset ℕ) (F : ℕ → ℝ) (hF : F 1 = 0) :
    (∑ d ∈ Q, F d) = ∑ d ∈ Q.erase 1, F d := by
  exact (Finset.sum_erase Q hF).symm

/-- The complete real distribution functional equals its erased version;
the physical coefficient is unchanged. -/
theorem realPhysicalDistributionError_eq_erase_one
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    realPhysicalDistributionError b N T Q rho =
      realPhysicalDistributionError b N T (Q.erase 1) rho := by
  unfold realPhysicalDistributionError
  exact signed_sum_eq_erase_one Q _ (real_distribution_summand_one b N T rho)

/-- The complete real coprime correction has the same exact erasure. -/
theorem realPhysicalCoprimeCorrection_eq_erase_one
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    realPhysicalCoprimeCorrection b N T Q rho =
      realPhysicalCoprimeCorrection b N T (Q.erase 1) rho := by
  unfold realPhysicalCoprimeCorrection
  exact signed_sum_eq_erase_one Q _ (real_coprime_summand_one b N T rho)

/-- Every outer signed atom has zero modulus-one primitive discrepancy. -/
theorem outer_primitive_summand_one
    (S : Finset ℕ) (weight rho : ℕ → ℝ) (a : ℕ) :
    rho 1 * finitePrimitiveDiscrepancy S weight a 1 = 0 := by
  rw [finitePrimitiveDiscrepancy_modulus_one, mul_zero]

/-- This equality applies separately to each atom weight of a signed
outer decomposition, with the same physical coefficient. -/
theorem outer_primitive_signed_sum_eq_erase_one
    (S Q : Finset ℕ) (weight rho : ℕ → ℝ) (a : ℕ) :
    (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight a d) =
      ∑ d ∈ Q.erase 1, rho d * finitePrimitiveDiscrepancy S weight a d := by
  exact signed_sum_eq_erase_one Q _ (outer_primitive_summand_one S weight rho a)

/-- Signed outer mass also has no modulus-one coprime correction. -/
theorem outer_coprime_kernel_one (S : Finset ℕ) (weight : ℕ → ℝ) :
    (finiteCoprimeMass S weight 1 - finiteSourceMass S weight) /
      (Nat.totient 1 : ℝ) = 0 := by
  classical
  have hfilter : S.filter (fun m => Nat.Coprime m 1) = S := by
    apply Finset.filter_eq_self.mpr
    intro m _hm
    change Nat.gcd m 1 = 1
    simp
  simp only [finiteCoprimeMass, finiteSourceMass, hfilter, sub_self, zero_div]

theorem outer_coprime_signed_sum_eq_erase_one
    (S Q : Finset ℕ) (weight rho : ℕ → ℝ) :
    (∑ d ∈ Q, rho d *
      ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
        (Nat.totient d : ℝ))) =
      ∑ d ∈ Q.erase 1, rho d *
        ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
          (Nat.totient d : ℝ)) := by
  apply signed_sum_eq_erase_one Q
  rw [outer_coprime_kernel_one, mul_zero]

/-- Exact active positive-modulus carrier for a signed P3 consumer.
This removes zero coefficient atoms after the harmless endpoint erasure. -/
def attachedPrimitiveModuli
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N : ℕ) : Finset ℕ := by
  classical
  exact (attachedUpperModuli nu r epsilon retain cap N).filter
    (fun d => 1 < d ∧ attachedUpperCoefficient nu r epsilon retain cap N d ≠ 0)

@[simp] theorem mem_attachedPrimitiveModuli
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N d : ℕ) :
    d ∈ attachedPrimitiveModuli nu r epsilon retain cap N ↔
      d ∈ attachedUpperModuli nu r epsilon retain cap N ∧
        1 < d ∧ attachedUpperCoefficient nu r epsilon retain cap N d ≠ 0 := by
  classical
  simp only [attachedPrimitiveModuli, Finset.mem_filter]

/-- A consumer obtains a genuine squarefree primitive modulus greater
than one and a nonzero value of the literal attached coefficient. -/
theorem attachedPrimitiveModuli_properties
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N : ℕ) {d : ℕ}
    (hd : d ∈ attachedPrimitiveModuli nu r epsilon retain cap N) :
    1 < d ∧ Squarefree d ∧ Nat.Coprime N d ∧
      attachedUpperCoefficient nu r epsilon retain cap N d ≠ 0 := by
  obtain ⟨hdmem, hdgt, hactive⟩ := (mem_attachedPrimitiveModuli nu r epsilon retain cap N d).mp hd
  refine ⟨hdgt, ?_, ?_, hactive⟩
  · exact actualSmallRoughModuli_squarefree (retain N) N (cap N) _ _ hdmem
  · exact (actualSmallRoughModuli_coprime_target (retain N) N (cap N) _ _ hdmem).symm

/-- Universal exact restriction of a same-rho signed kernel sum. The
only kernel condition is its actual zero value at the modulus-one endpoint. -/
theorem attached_signed_sum_eq_primitiveModuli
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N : ℕ) (F : ℕ → ℝ) (hF : F 1 = 0) :
    (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d * F d) =
      ∑ d ∈ attachedPrimitiveModuli nu r epsilon retain cap N,
        attachedUpperCoefficient nu r epsilon retain cap N d * F d := by
  classical
  symm
  apply Finset.sum_subset
    (show attachedPrimitiveModuli nu r epsilon retain cap N ⊆
      attachedUpperModuli nu r epsilon retain cap N from
      fun d hd => ((mem_attachedPrimitiveModuli nu r epsilon retain cap N d).mp hd).1)
  intro d hd hnotactive
  by_cases hrho : attachedUpperCoefficient nu r epsilon retain cap N d = 0
  · simp only [hrho, zero_mul]
  · by_cases hd1 : d = 1
    · simp only [hd1, hF, mul_zero]
    · have hpos := attachedUpperModuli_pos nu r epsilon retain cap N hd
      have hdgt : 1 < d := by omega
      exact False.elim (hnotactive
        ((mem_attachedPrimitiveModuli nu r epsilon retain cap N d).mpr ⟨hd, hdgt, hrho⟩))

/-- The real distribution functional is exactly its active-modulus sum. -/
theorem attached_realPhysicalDistributionError_eq_primitiveModuli
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (b : ℝ) (N : ℕ) (T : ℝ) :
    realPhysicalDistributionError b N T
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) =
      realPhysicalDistributionError b N T
        (attachedPrimitiveModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) := by
  unfold realPhysicalDistributionError
  exact attached_signed_sum_eq_primitiveModuli nu r epsilon retain cap N _
    (real_distribution_kernel_one b N T)

theorem attached_realPhysicalCoprimeCorrection_eq_primitiveModuli
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (b : ℝ) (N : ℕ) (T : ℝ) :
    realPhysicalCoprimeCorrection b N T
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) =
      realPhysicalCoprimeCorrection b N T
        (attachedPrimitiveModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) := by
  unfold realPhysicalCoprimeCorrection
  exact attached_signed_sum_eq_primitiveModuli nu r epsilon retain cap N _
    (real_coprime_kernel_one b N T)

/-- Per-atom interface for signed P3 estimates: the entire physical sum
has exactly the active >1 carrier, with no absolute-modulus expansion. -/
theorem attached_outer_primitive_signed_sum_eq_primitiveModuli
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N : ℕ) (S : Finset ℕ) (weight : ℕ → ℝ) (a : ℕ) :
    (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d *
        finitePrimitiveDiscrepancy S weight a d) =
      ∑ d ∈ attachedPrimitiveModuli nu r epsilon retain cap N,
        attachedUpperCoefficient nu r epsilon retain cap N d *
          finitePrimitiveDiscrepancy S weight a d := by
  exact attached_signed_sum_eq_primitiveModuli nu r epsilon retain cap N _
    (finitePrimitiveDiscrepancy_modulus_one S weight a)

theorem attached_outer_coprime_signed_sum_eq_primitiveModuli
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N : ℕ) (S : Finset ℕ) (weight : ℕ → ℝ) :
    (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d *
        ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
          (Nat.totient d : ℝ))) =
      ∑ d ∈ attachedPrimitiveModuli nu r epsilon retain cap N,
        attachedUpperCoefficient nu r epsilon retain cap N d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ)) := by
  exact attached_signed_sum_eq_primitiveModuli nu r epsilon retain cap N _
    (outer_coprime_kernel_one S weight)

end
end ImbalancedChen.P4BPrimitiveModulusEndpoints
