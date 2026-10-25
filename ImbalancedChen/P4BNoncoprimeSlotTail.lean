import ImbalancedChen.P5zMarkedPrimeFamilyCorrections
import ImbalancedChen.P4BLabelledOuterPushforward

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
A signed full-product noncoprime divisor union, retaining the same rho.
No source roughness is presumed: individual prime reciprocal costs remain
visible. The carrier includes products above N and repeated prime slots.
This is only arithmetic correction payment, not the signed P3 discrepancy
estimate, nor a production of the full22 physical coefficient or its range.
-/
namespace ImbalancedChen.P4BNoncoprimeSlotTail
noncomputable section
open Classical
open scoped BigOperators

/-- Keep the individual original prime-slot costs instead of assuming a
common roughness threshold. Repeated slots merely overcount the union. -/
theorem noncoprime_totient_sum_le_slot_cost {rank N : ℕ}
    (t : Fin rank → Fin (N + 1)) (ht : t ∈ Part3.labelledPrimeTuples rank N)
    (D : Finset ℕ) (Q : ℕ) (hD : D ⊆ Finset.Icc 1 Q) :
    (∑ d ∈ D, if Nat.Coprime (Part3.labelledProduct t) d then (0 : ℝ)
      else 1 / (Nat.totient d : ℝ)) ≤
      ∑ i : Fin rank, (4 / (((t i).val : ℝ) - 1)) *
        (1 + Real.log (max 1 (Q : ℝ))) := by
  have hp : ∀ i, Nat.Prime (t i).val := (Finset.mem_filter.mp ht).2
  have hpoint (d : ℕ) :
      (if Nat.Coprime (Part3.labelledProduct t) d then (0 : ℝ)
        else 1 / (Nat.totient d : ℝ)) ≤
      ∑ i : Fin rank, if (t i).val ∣ d then 1 / (Nat.totient d : ℝ) else 0 := by
    by_cases hc : Nat.Coprime (Part3.labelledProduct t) d
    · rw [if_pos hc]
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    · have hex : ∃ i : Fin rank, ¬ Nat.Coprime (t i).val d := by
        by_contra hn
        apply hc
        apply Nat.coprime_prod_left_iff.mpr
        intro i hi
        by_contra hbad
        exact hn ⟨i, hbad⟩
      obtain ⟨i, hi⟩ := hex
      have hdiv : (t i).val ∣ d := by
        by_contra hn
        exact hi ((hp i).coprime_iff_not_dvd.mpr hn)
      have hsingle := Finset.single_le_sum
        (fun j (_hj : j ∈ (Finset.univ : Finset (Fin rank))) =>
          show 0 ≤ (if (t j).val ∣ d then 1 / (Nat.totient d : ℝ) else 0) by positivity)
        (Finset.mem_univ i)
      simpa only [if_neg hc, if_pos hdiv] using hsingle
  calc
    _ ≤ ∑ d ∈ D, ∑ i : Fin rank,
        if (t i).val ∣ d then 1 / (Nat.totient d : ℝ) else 0 :=
      Finset.sum_le_sum (fun d _ => hpoint d)
    _ = ∑ i : Fin rank, ∑ d ∈ D,
        if (t i).val ∣ d then 1 / (Nat.totient d : ℝ) else 0 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      currentChenUpsilon9_dvd_reciprocalTotient_sum_le D Q (t i).val (hp i) hD)

/-- Signed weights are charged by their actual total variation, retaining
all original labelled fibres. No positivity of W or lower prime bound is
needed. The only coefficient premise is a finite absolute amplitude bound. -/
theorem signed_correction_le_weighted_slot_cost {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (hS : S ⊆ Part3.labelledPrimeTuples rank N)
    (W : (Fin rank → Fin (N + 1)) → ℝ)
    (D : Finset ℕ) (Q : ℕ) (hD : D ⊆ Finset.Icc 1 Q)
    (rho : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hrho : ∀ d ∈ D, |rho d| ≤ M) :
    |p5z_labelledCoprimeCorrection S Part3.labelledProduct W D rho| ≤
      ∑ t ∈ S, |W t| * (M * (∑ i : Fin rank,
        (4 / (((t i).val : ℝ) - 1)) * (1 + Real.log (max 1 (Q : ℝ))))) := by
  rw [p5z_markedCoprimeCorrection_eq_neg_sum, abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro t ht
  calc
    _ ≤ ∑ d ∈ D, |W t * (rho d *
        (if Nat.Coprime (Part3.labelledProduct t) d then 0 else 1 / (Nat.totient d : ℝ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, |W t| * (M *
        (if Nat.Coprime (Part3.labelledProduct t) d then 0 else 1 / (Nat.totient d : ℝ))) := by
      apply Finset.sum_le_sum
      intro d hd
      have hb : 0 ≤ (if Nat.Coprime (Part3.labelledProduct t) d then (0 : ℝ)
        else 1 / (Nat.totient d : ℝ)) := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg hb]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hrho d hd) hb) (abs_nonneg _)
    _ = |W t| * (M * ∑ d ∈ D,
        if Nat.Coprime (Part3.labelledProduct t) d then 0 else 1 / (Nat.totient d : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (noncoprime_totient_sum_le_slot_cost t (hS ht) D Q hD) hM) (abs_nonneg _)

/-- The complete outer product carrier has exactly the same correction
as its labelled family, including m >= N and either sign of V. -/
theorem outer_correction_eq_labelled (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (D : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ d ∈ D, rho d *
      ((finiteCoprimeMass (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N V) d -
        finiteSourceMass (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N V)) / (Nat.totient d : ℝ))) =
      p5z_labelledCoprimeCorrection (Part3.labelledPrimeTuples 2 N)
        Part3.labelledProduct V D rho := by
  unfold p5z_labelledCoprimeCorrection p5z_labelledCoprimeMass p5z_labelledMass
  simp_rw [P4BLabelledOuterPushforward.finiteCoprimeMass_eq_labelled,
    P4BLabelledOuterPushforward.finiteSourceMass_eq_labelled]

/-- Arithmetic union bound for the literal same-rho signed OUTER
FULLPRODUCT correction. No fullproduct roughness is manufactured. -/
theorem outer_signed_correction_le_slot_cost (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ)
    (D : Finset ℕ) (Q : ℕ) (hD : D ⊆ Finset.Icc 1 Q)
    (rho : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hrho : ∀ d ∈ D, |rho d| ≤ M) :
    |∑ d ∈ D, rho d *
      ((finiteCoprimeMass (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N V) d -
        finiteSourceMass (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N V)) / (Nat.totient d : ℝ))| ≤
      ∑ t ∈ Part3.labelledPrimeTuples 2 N, |V t| * (M * (∑ i : Fin 2,
        (4 / (((t i).val : ℝ) - 1)) * (1 + Real.log (max 1 (Q : ℝ))))) := by
  rw [outer_correction_eq_labelled]
  exact signed_correction_le_weighted_slot_cost _ (fun _ h => h) V D Q hD rho M hM hrho

/-- Zero coefficient entries can be removed before imposing a range.
This identity applies to any kernel, with the same signed coefficient. -/
theorem signed_sum_eq_active (D : Finset ℕ) (rho F : ℕ → ℝ) :
    (∑ d ∈ D, rho d * F d) =
      ∑ d ∈ D.filter (fun d => rho d ≠ 0), rho d * F d := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : rho d = 0 <;> simp [h]

/-- Only nonzero physical moduli need the polynomial support cap.
The proof uses the divisor-union estimate after an exact active restriction;
it never bounds the correction by the number of displayed moduli. -/
theorem outer_signed_correction_le_slot_cost_of_active_range (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ)
    (D : Finset ℕ) (Q : ℕ) (rho : ℕ → ℝ)
    (hD : ∀ d ∈ D, rho d ≠ 0 → d ∈ Finset.Icc 1 Q)
    (M : ℝ) (hM : 0 ≤ M) (hrho : ∀ d ∈ D, |rho d| ≤ M) :
    |∑ d ∈ D, rho d *
      ((finiteCoprimeMass (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N V) d -
        finiteSourceMass (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N V)) / (Nat.totient d : ℝ))| ≤
      ∑ t ∈ Part3.labelledPrimeTuples 2 N, |V t| * (M * (∑ i : Fin 2,
        (4 / (((t i).val : ℝ) - 1)) * (1 + Real.log (max 1 (Q : ℝ))))) := by
  rw [signed_sum_eq_active D rho]
  exact outer_signed_correction_le_slot_cost N V _ Q
    (by
      intro d hd
      obtain ⟨hdD, hdactive⟩ := Finset.mem_filter.mp hd
      exact hD d hdD hdactive)
    rho M hM (fun d hd => hrho d (Finset.mem_filter.mp hd).1)

end
end ImbalancedChen.P4BNoncoprimeSlotTail
