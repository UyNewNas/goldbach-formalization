import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.ActualUpperCountingInputs
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.ModEq

/-!
# Integer-shift outer carriers for the identical physical upper coefficient

SOURCE ONLY / YELLOW / UNCOMPILED.
The test argument is the natural absolute value of (N : Int) - (m : Int).
Its divisor mask equals the original moving residue mask for every m,
including m > N. On the original real source it agrees with N - m in Nat.
Thus a positive outer source may have nonzero weight beyond N, and its full
mass, coprime correction and signed primitive error remain on that carrier.
No analytic admissibility of an arbitrary smoothing weight is asserted.
-/

namespace ImbalancedChen
namespace P4B

noncomputable section

open scoped BigOperators

/-- The exact divisor/residue equivalence is proved from the integer
divisibility APIs; no comparison of m and N is assumed, also at d = 0. -/
theorem integerShiftNatAbs_dvd_iff_modEq (N m d : ℕ) :
    d ∣ ((N : ℤ) - (m : ℤ)).natAbs ↔ Nat.ModEq d m N := by
  rw [← Int.natCast_dvd, ← Nat.modEq_iff_dvd]

/-- On the actual source the integer shift is precisely the existing
natural shift, retaining the endpoint m = N and its zero test argument. -/
theorem integerShiftNatAbs_eq_natSub_of_le {N m : ℕ} (hmN : m ≤ N) :
    ((N : ℤ) - (m : ℤ)).natAbs = N - m := by
  rw [← Int.natCast_sub hmN, Int.natAbs_natCast]

/-- Weighted Fubini on any finite natural carrier, with no support bound.
The modulus coefficient rho is unchanged by the integer shift. -/
theorem sum_weight_mul_physicalDivisorSum_integerShift_eq_rho_mul_finiteCongruenceMass
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ) :
    (∑ m ∈ S, weight m *
      physicalDivisorSum Q rho (((N : ℤ) - (m : ℤ)).natAbs)) =
      ∑ d ∈ Q, rho d * finiteCongruenceMass S weight N d := by
  classical
  unfold physicalDivisorSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  unfold finiteCongruenceMass
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _hm
  have hiff := integerShiftNatAbs_dvd_iff_modEq N m d
  by_cases hmod : Nat.ModEq d m N
  · simp only [if_pos (hiff.mpr hmod), if_pos hmod, mul_comm]
  · have hdvd : ¬d ∣ ((N : ℤ) - (m : ℤ)).natAbs := fun h => hmod (hiff.mp h)
    simp only [if_neg hdvd, if_neg hmod, mul_zero]

/-- Exact signed decomposition on the entire outer carrier. No terms
with m > N are discarded, and no absolute discrepancy sum is introduced. -/
theorem sum_weight_mul_physicalDivisorSum_integerShift_eq_same_rho_main_add_errors
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ) :
    (∑ m ∈ S, weight m *
      physicalDivisorSum Q rho (((N : ℤ) - (m : ℤ)).natAbs)) =
      finiteSourceMass S weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ))) +
        ∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d := by
  rw [sum_weight_mul_physicalDivisorSum_integerShift_eq_rho_mul_finiteCongruenceMass
    N S Q weight rho]
  unfold physicalDensitySum finitePrimitiveDiscrepancy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  ring

/-- Compare the original natural-shift sum to the positive outer
integer-shift sum. Nonnegativity is needed at all absolute integer shifts,
including negative differences beyond N; the source itself stays literal. -/
theorem sum_physicalDivisorSum_realSource_le_integer_outer
    (b : ℝ) (N : ℕ) (T : ℝ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hsource : realHalfProductSource b N T ⊆ S)
    (houter : ∀ m ∈ S,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m)
    (hnonneg : ∀ n : ℕ, 0 ≤ physicalDivisorSum Q rho n) :
    (∑ m ∈ realHalfProductSource b N T, physicalDivisorSum Q rho (N - m)) ≤
      ∑ m ∈ S, weight m *
        physicalDivisorSum Q rho (((N : ℤ) - (m : ℤ)).natAbs) := by
  classical
  calc
    (∑ m ∈ realHalfProductSource b N T, physicalDivisorSum Q rho (N - m)) =
        ∑ m ∈ realHalfProductSource b N T,
          (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) *
            physicalDivisorSum Q rho (((N : ℤ) - (m : ℤ)).natAbs) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [integerShiftNatAbs_eq_natSub_of_le (mem_realHalfProductSource.mp hm).1]
      simp only [if_pos hm, one_mul]
    _ = ∑ m ∈ S,
        (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) *
          physicalDivisorSum Q rho (((N : ℤ) - (m : ℤ)).natAbs) := by
      apply Finset.sum_subset hsource
      intro m _hmS hmSource
      simp only [if_neg hmSource, zero_mul]
    _ ≤ _ := Finset.sum_le_sum fun m hm =>
      mul_le_mul_of_nonneg_right (houter m hm)
        (hnonneg (((N : ℤ) - (m : ℤ)).natAbs))

/-- Complete finite upper bound on an arbitrary positive outer carrier.
There is no upper bound on m or on the nonzero support of weight. Every
arithmetic quantity uses exactly Q and rho from the all-natural majorant. -/
theorem RealB_cast_le_same_rho_integer_outer_main_add_errors
    {b T : ℝ} (N z : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hsource : realHalfProductSource b N T ⊆ S)
    (houter : ∀ m ∈ S,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      finiteSourceMass S weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ))) +
        (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d) +
        (z : ℝ) + (T + 1) := by
  classical
  have hnonneg : ∀ n : ℕ, 0 ≤ physicalDivisorSum Q rho n := by
    intro n
    have h := hmajor n
    split_ifs at h with hcop
    · exact zero_le_one.trans h
    · exact h
  have hsum := sum_physicalDivisorSum_realSource_le_integer_outer
    b N T S Q weight rho hsource houter hnonneg
  have h := (RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff
    N z Q rho hb hT hmajor).trans
      (add_le_add (add_le_add hsum (le_refl (z : ℝ))) (le_refl (T + 1)))
  rw [sum_weight_mul_physicalDivisorSum_integerShift_eq_same_rho_main_add_errors
    N S Q weight rho] at h
  exact h

/-- An all-integer majorant supplies the same finite theorem directly.
Its natural restriction changes neither the carrier Q nor rho. -/
theorem RealB_cast_le_same_rho_integer_outer_main_add_errors_of_integer_majorant
    {b T : ℝ} (N z : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hsource : realHalfProductSource b N T ⊆ S)
    (houter : ∀ m ∈ S,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m)
    (hmajor : ∀ n : ℤ,
      (if Nat.Coprime n.natAbs (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n.natAbs) :
    (RealB b N : ℝ) ≤
      finiteSourceMass S weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ))) +
        (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d) +
        (z : ℝ) + (T + 1) := by
  apply RealB_cast_le_same_rho_integer_outer_main_add_errors
    N z S Q weight rho hb hT hsource houter
  intro n
  simpa only [Int.natAbs_natCast] using hmajor (n : ℤ)

/-- Literal small/rough attachment specialization, obtained from its proved
all-integer majorant. Positive outer weight above N is allowed. -/
theorem RealB_cast_le_actualSmallRoughRho_integer_outer_main_add_errors
    {b T : ℝ} (N cap : ℕ) (retainOdd : List ℕ → Bool) (w z L : ℝ)
    (S : Finset ℕ) (weight : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ))
    (hsource : realHalfProductSource b N T ⊆ S)
    (houter : ∀ m ∈ S,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m) :
    (RealB b N : ℝ) ≤
      finiteSourceMass S weight *
          physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
            (actualSmallRoughRho retainOdd N cap w z L) +
        (∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
          actualSmallRoughRho retainOdd N cap w z L d *
            ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
              (Nat.totient d : ℝ))) +
        (∑ d ∈ actualSmallRoughModuli retainOdd N cap w z,
          actualSmallRoughRho retainOdd N cap w z L d *
            finitePrimitiveDiscrepancy S weight N d) +
        (Nat.ceil z : ℝ) + (T + 1) := by
  apply RealB_cast_le_same_rho_integer_outer_main_add_errors_of_integer_majorant
    N (Nat.ceil z) S (actualSmallRoughModuli retainOdd N cap w z) weight
    (actualSmallRoughRho retainOdd N cap w z L) hb hT hsource houter
  intro n
  have h := actualSmallRoughRho_majorant retainOdd N cap w z L hL hwL hwz hzcap n
  rw [actualSmallRoughIndicator_eq_sieveProduct_natAbs] at h
  exact h

/-- The actual counting-parameter attachment also enters with the same
coefficient and no geometry restriction beyond positive outer domination. -/
theorem RealB_cast_le_attachedUpper_integer_outer_main_add_errors
    {b T nu r epsilon : ℝ} (N : ℕ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (S : Finset ℕ) (weight : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T) (hnu : 0 < nu) (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon ≤ 1) (hepsilonR : epsilon ^ 2 ≤ r)
    (hN : 2 ≤ N) (hcap : (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hsource : realHalfProductSource b N T ⊆ S)
    (houter : ∀ m ∈ S,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m) :
    (RealB b N : ℝ) ≤
      finiteSourceMass S weight *
          physicalDensitySum (attachedUpperModuli nu r epsilon retain cap N)
            (attachedUpperCoefficient nu r epsilon retain cap N) +
        (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
          attachedUpperCoefficient nu r epsilon retain cap N d *
            ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
              (Nat.totient d : ℝ))) +
        (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
          attachedUpperCoefficient nu r epsilon retain cap N d *
            finitePrimitiveDiscrepancy S weight N d) +
        (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) + (T + 1) := by
  exact RealB_cast_le_same_rho_integer_outer_main_add_errors
    N (Nat.ceil ((N : ℝ) ^ (nu * r))) S
    (attachedUpperModuli nu r epsilon retain cap N) weight
    (attachedUpperCoefficient nu r epsilon retain cap N) hb hT hsource houter
    (attachedUpperCoefficient_majorant hnu hepsilon hepsilonOne hepsilonR
      retain cap hN hcap)

end

end P4B
end ImbalancedChen
