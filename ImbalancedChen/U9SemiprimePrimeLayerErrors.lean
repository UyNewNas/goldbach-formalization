import ImbalancedChen.U9SemiprimeFibreMultiplicity

/-!
# Actual zero-one prime layers and grouped U9 progression errors

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original integer fibre coefficient is exactly the sum of its two
zero-one superlevel sets. These are concrete subsets of the original prime
carrier, independent of the modulus. They retain the original first/last
factor multiplicity, old centre mask, strict near-cap gate and moving cut.
There is no replacement by an independent semiprime beta coefficient.

The progression discrepancy of each layer uses its exact coprime prime
mass divided by the FULL phi(d). The finite original signed error is then
exactly the sum of these discrepancies with the SAME rho, followed by a
proved grouped triangle inequality. No progression norm bound is supplied
as a premise; obtaining the analytical saving remains OPEN.
-/

namespace ImbalancedChen.U9SemiprimeSwitch

noncomputable section

open scoped BigOperators
open Classical

/-- Modulus-independent prime superlevel sets of the actual label count. -/
def primeLayer (k N : ℕ) (X : ℝ) (m : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter fun r => k ≤ (fibre N X m r).card

theorem weight_eq_two_indicators (N : ℕ) (X : ℝ) (m r : ℕ) :
    weight N X m r =
      (if 1 ≤ (fibre N X m r).card then 1 else 0) +
      (if 2 ≤ (fibre N X m r).card then 1 else 0) := by
  have hb := fibre_card_le_two N X m r
  have hc : (fibre N X m r).card = 0 ∨ (fibre N X m r).card = 1 ∨
      (fibre N X m r).card = 2 := by omega
  change ((fibre N X m r).card : ℝ) = _
  rcases hc with hc | hc | hc <;> simp [hc]

/-- Exact weighted prime sum, not a majorant by twice an unweighted image. -/
theorem weighted_prime_sum_eq_layers (N : ℕ) (X : ℝ) (m : ℕ) (G : ℕ → ℝ) :
    (∑ r ∈ chenAdditivePrimeCarrier N, weight N X m r * G r) =
      (∑ r ∈ primeLayer 1 N X m, G r) +
      ∑ r ∈ primeLayer 2 N X m, G r := by
  simp only [primeLayer, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [weight_eq_two_indicators]
  split_ifs <;> ring

def layerAPCount (k N : ℕ) (X : ℝ) (m d : ℕ) : ℝ :=
  (((primeLayer k N X m).filter
    (fun r => Nat.ModEq d r (residue N m d))).card : ℝ)

def layerCoprimeCount (k N : ℕ) (X : ℝ) (m d : ℕ) : ℝ :=
  (((primeLayer k N X m).filter (fun r => Nat.Coprime r d)).card : ℝ)

/-- The exact layer discrepancy uses primitive prime mass and the complete
modulus d. Semiprime rows not coprime to d make no primitive contribution. -/
def layerError (k N : ℕ) (X : ℝ) (m d : ℕ) : ℝ :=
  if Nat.Coprime m d then
    layerAPCount k N X m d - layerCoprimeCount k N X m d / (Nat.totient d : ℝ)
  else 0

theorem APCount_eq_layer_rows (N : ℕ) (X : ℝ) (d : ℕ) :
    APCount N X d = ∑ m ∈ Finset.range N, if Nat.Coprime m d then
      layerAPCount 1 N X m d + layerAPCount 2 N X m d else 0 := by
  unfold APCount
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : Nat.Coprime m d
  · simp only [hm, if_true]
    have h := weighted_prime_sum_eq_layers N X m
      (fun r => if Nat.ModEq d r (residue N m d) then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  · simp only [hm, if_false]

theorem coprimeMass_eq_layer_rows (N : ℕ) (X : ℝ) (d : ℕ) :
    coprimeMass N X d = ∑ m ∈ Finset.range N, if Nat.Coprime m d then
      layerCoprimeCount 1 N X m d + layerCoprimeCount 2 N X m d else 0 := by
  unfold coprimeMass
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : Nat.Coprime m d
  · simp only [hm, if_true, Nat.coprime_mul_iff_left, true_and]
    have h := weighted_prime_sum_eq_layers N X m
      (fun r => if Nat.Coprime r d then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  · simp only [Nat.coprime_mul_iff_left, hm, false_and, if_false, mul_zero,
      Finset.sum_const_zero]

/-- Finite source-to-prime-progression interface for the original signed
error, with no norm or modulus-dependent coefficient introduced. -/
theorem signedError_eq_layer_errors (N : ℕ) (X : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hQ : ∀ d ∈ Q, 0 < d ∧ Nat.Coprime N d) :
    p5z_labelledDistributionError (labels N X) p5z_u9_product
        (fun _ => 1) N Q rho =
      ∑ d ∈ Q, rho d * ∑ m ∈ Finset.range N,
        (layerError 1 N X m d + layerError 2 N X m d) := by
  rw [signedError_eq_switchedPrimeAP N X Q rho hQ]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  rw [APCount_eq_layer_rows, coprimeMass_eq_layer_rows,
    Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  unfold layerError
  by_cases hm : Nat.Coprime m d <;> simp only [hm, if_true, if_false]
  · ring
  · ring

/-- Concrete grouped progression norm bound. The two original layers are
kept separately, every original semiprime multiplicity is paid, and no
analytical bound is an assumption of this theorem. -/
theorem abs_signedError_le_grouped_layer_errors (N : ℕ) (X : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hQ : ∀ d ∈ Q, 0 < d ∧ Nat.Coprime N d) :
    |p5z_labelledDistributionError (labels N X) p5z_u9_product
        (fun _ => 1) N Q rho| ≤
      ∑ m ∈ Finset.range N, ∑ d ∈ Q, |rho d| *
        (|layerError 1 N X m d| + |layerError 2 N X m d|) := by
  rw [signedError_eq_layer_errors N X Q rho hQ]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_add _ _) (abs_nonneg _)

end

end ImbalancedChen.U9SemiprimeSwitch
