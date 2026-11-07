import ImbalancedChen.P5U7ActualComponentProductWeights

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Exact finite total-variation mass of the actual component arithmetic
collars. Interior weights are literal marked-fibre restrictions. Positivity
proves their L1 error equals the lost label count, then controls every
bounded signed physical test uniformly. No distribution theorem is assumed.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology
open scoped BigOperators
open Classical

def p5U7ActualInteriorPrimeProductWeight (N : ℕ) (eta : ℝ) (m : ℕ) : ℝ :=
  (((p5U7ActualInteriorThree N eta).filter (fun x => p5U7ThreeProduct x=m)).card : ℝ)

def p5U7ActualInteriorSemiprimeProductWeight (N : ℕ) (eta : ℝ) (m : ℕ) : ℝ :=
  (((p5U7ActualInteriorFour N eta).filter (fun x => p5U7FourProduct x=m)).card : ℝ)

theorem p5U7ActualInteriorPrimeProductWeight_le_full (N : ℕ) (eta : ℝ) (m : ℕ) :
    p5U7ActualInteriorPrimeProductWeight N eta m ≤ p5U7ActualPrimeProductWeight N m := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hx,heq⟩ := Finset.mem_filter.mp hx
  rw [p5U7ActualInteriorThree_eq_original_filter] at hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,heq⟩

theorem p5U7ActualInteriorSemiprimeProductWeight_le_full (N : ℕ) (eta : ℝ) (m : ℕ) :
    p5U7ActualInteriorSemiprimeProductWeight N eta m ≤ p5U7ActualSemiprimeProductWeight N m := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hx,heq⟩ := Finset.mem_filter.mp hx
  rw [p5U7ActualInteriorFour_eq_original_filter] at hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,heq⟩

theorem p5U7ActualInteriorPrimeProductWeight_Fubini (N : ℕ) (eta : ℝ) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range N,p5U7ActualInteriorPrimeProductWeight N eta m*H m) =
      ∑ x ∈ p5U7ActualInteriorThree N eta,H (p5U7ThreeProduct x) := by
  have hmap : ∀ x ∈ p5U7ActualInteriorThree N eta,p5U7ThreeProduct x ∈ Finset.range N := by
    intro x hx
    rw [p5U7ActualInteriorThree_eq_original_filter] at hx
    exact Finset.mem_range.mpr (p5U7ArithmeticThree_data (Finset.mem_filter.mp hx).1).2.2.2.2.2.2.2.1
  simpa only [p5U7ActualInteriorPrimeProductWeight,Finset.sum_const,nsmul_eq_mul] using
    Finset.sum_fiberwise_of_maps_to' hmap H

theorem p5U7ActualInteriorSemiprimeProductWeight_Fubini (N : ℕ) (eta : ℝ) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range N,p5U7ActualInteriorSemiprimeProductWeight N eta m*H m) =
      ∑ x ∈ p5U7ActualInteriorFour N eta,H (p5U7FourProduct x) := by
  have hmap : ∀ x ∈ p5U7ActualInteriorFour N eta,p5U7FourProduct x ∈ Finset.range N := by
    intro x hx
    rw [p5U7ActualInteriorFour_eq_original_filter] at hx
    exact Finset.mem_range.mpr (p5U7ArithmeticFour_data (Finset.mem_filter.mp hx).1).2.2.2.2.2.2.2.2.2.1
  simpa only [p5U7ActualInteriorSemiprimeProductWeight,Finset.sum_const,nsmul_eq_mul] using
    Finset.sum_fiberwise_of_maps_to' hmap H

theorem p5U7ActualInteriorPrimeProductWeight_mass (N : ℕ) (eta : ℝ) :
    (∑ m ∈ Finset.range N,p5U7ActualInteriorPrimeProductWeight N eta m) =
      ((p5U7ActualInteriorThree N eta).card : ℝ) := by
  simpa only [mul_one,Finset.sum_const,nsmul_eq_mul] using
    p5U7ActualInteriorPrimeProductWeight_Fubini N eta (fun _ => 1)

theorem p5U7ActualInteriorSemiprimeProductWeight_mass (N : ℕ) (eta : ℝ) :
    (∑ m ∈ Finset.range N,p5U7ActualInteriorSemiprimeProductWeight N eta m) =
      ((p5U7ActualInteriorFour N eta).card : ℝ) := by
  simpa only [mul_one,Finset.sum_const,nsmul_eq_mul] using
    p5U7ActualInteriorSemiprimeProductWeight_Fubini N eta (fun _ => 1)

/-- Exact L1 arithmetic collar mass; every lost label is paid once. -/
theorem p5U7ActualPrimeProductWeight_collar_L1 (N : ℕ) (eta : ℝ) :
    (∑ m ∈ Finset.range N,
      |p5U7ActualPrimeProductWeight N m-p5U7ActualInteriorPrimeProductWeight N eta m|) =
      ((p5U7ActualPrimeCollar N eta).card : ℝ) := by
  have ha (m : ℕ) : |p5U7ActualPrimeProductWeight N m-
      p5U7ActualInteriorPrimeProductWeight N eta m| =
      p5U7ActualPrimeProductWeight N m-p5U7ActualInteriorPrimeProductWeight N eta m :=
    abs_of_nonneg (sub_nonneg.mpr (p5U7ActualInteriorPrimeProductWeight_le_full N eta m))
  simp_rw [ha]
  rw [Finset.sum_sub_distrib,p5U7ActualPrimeProductWeight_mass,
    p5U7ActualInteriorPrimeProductWeight_mass,p5U7ActualPrimeCollar_card_split N eta]
  ring

theorem p5U7ActualSemiprimeProductWeight_collar_L1 (N : ℕ) (eta : ℝ) :
    (∑ m ∈ Finset.range N,
      |p5U7ActualSemiprimeProductWeight N m-p5U7ActualInteriorSemiprimeProductWeight N eta m|) =
      ((p5U7ActualSemiprimeCollar N eta).card : ℝ) := by
  have ha (m : ℕ) : |p5U7ActualSemiprimeProductWeight N m-
      p5U7ActualInteriorSemiprimeProductWeight N eta m| =
      p5U7ActualSemiprimeProductWeight N m-p5U7ActualInteriorSemiprimeProductWeight N eta m :=
    abs_of_nonneg (sub_nonneg.mpr (p5U7ActualInteriorSemiprimeProductWeight_le_full N eta m))
  simp_rw [ha]
  rw [Finset.sum_sub_distrib,p5U7ActualSemiprimeProductWeight_mass,
    p5U7ActualInteriorSemiprimeProductWeight_mass,p5U7ActualSemiprimeCollar_card_split N eta]
  ring

private theorem p5U7Component_weighted_error_le_L1 (N : ℕ) (w v H : ℕ → ℝ)
    (B : ℝ) (hH : ∀ m ∈ Finset.range N,|H m| ≤ B) :
    |(∑ m ∈ Finset.range N,w m*H m)-(∑ m ∈ Finset.range N,v m*H m)| ≤
      B*(∑ m ∈ Finset.range N,|w m-v m|) := by
  calc
    _ = |∑ m ∈ Finset.range N,(w m-v m)*H m| := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ ∑ m ∈ Finset.range N,|(w m-v m)*H m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range N,B*|w m-v m| := by
      apply Finset.sum_le_sum
      intro m hm
      rw [abs_mul]
      nlinarith only [mul_le_mul_of_nonneg_left (hH m hm) (abs_nonneg (w m-v m))]
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Uniform signed physical-test payment by the actual prime collar. -/
theorem p5U7ActualPrimeProductWeight_bounded_test_collar (N : ℕ) (eta B : ℝ)
    (H : ℕ → ℝ) (hH : ∀ m ∈ Finset.range N,|H m| ≤ B) :
    |(∑ m ∈ Finset.range N,p5U7ActualPrimeProductWeight N m*H m)-
      (∑ m ∈ Finset.range N,p5U7ActualInteriorPrimeProductWeight N eta m*H m)| ≤
      B*((p5U7ActualPrimeCollar N eta).card : ℝ) := by
  simpa only [p5U7ActualPrimeProductWeight_collar_L1] using
    p5U7Component_weighted_error_le_L1 N (p5U7ActualPrimeProductWeight N)
      (p5U7ActualInteriorPrimeProductWeight N eta) H B hH

theorem p5U7ActualSemiprimeProductWeight_bounded_test_collar (N : ℕ) (eta B : ℝ)
    (H : ℕ → ℝ) (hH : ∀ m ∈ Finset.range N,|H m| ≤ B) :
    |(∑ m ∈ Finset.range N,p5U7ActualSemiprimeProductWeight N m*H m)-
      (∑ m ∈ Finset.range N,p5U7ActualInteriorSemiprimeProductWeight N eta m*H m)| ≤
      B*((p5U7ActualSemiprimeCollar N eta).card : ℝ) := by
  simpa only [p5U7ActualSemiprimeProductWeight_collar_L1] using
    p5U7Component_weighted_error_le_L1 N (p5U7ActualSemiprimeProductWeight N)
      (p5U7ActualInteriorSemiprimeProductWeight N eta) H B hH

/-- One positive eta is chosen before N and controls both exact physical
L1 collar errors simultaneously. -/
theorem p5U7ActualComponentProductWeights_collar_L1_eventually_small
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ eta : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0, ∀ᶠ N : ℕ in atTop,
      (Real.log (N : ℝ)/(N : ℝ))*(∑ m ∈ Finset.range N,
        |p5U7ActualPrimeProductWeight N m-p5U7ActualInteriorPrimeProductWeight N eta m|) < epsilon ∧
      (Real.log (N : ℝ)/(N : ℝ))*(∑ m ∈ Finset.range N,
        |p5U7ActualSemiprimeProductWeight N m-p5U7ActualInteriorSemiprimeProductWeight N eta m|) < epsilon := by
  simpa only [p5U7ActualPrimeProductWeight_collar_L1,p5U7ActualSemiprimeProductWeight_collar_L1] using
    p5U7ActualComponentCollars_eventually_small epsilon he

end
end ImbalancedChen
