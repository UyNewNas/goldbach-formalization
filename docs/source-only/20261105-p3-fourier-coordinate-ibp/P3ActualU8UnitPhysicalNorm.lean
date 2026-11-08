import ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget
import ImbalancedChen.P5zPositiveFamilyBudget
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY: genuine U8 quotient-one labels and signed physical
modulus norm. Both congruence count and EXACT coprime mean belong
to [0,card S] for every positive physical modulus; their difference
therefore has absolute value <= card S (not 2*card S).
The actual unit source has card S <= N^(2/3). The signed rho is
unchanged across all labels. No bound on the ACTUAL rho_T is presumed.
Unit quotient q=1 is NOT a physical modulus or an empty Gamma word.
UNCOMPILED; NO CI OR KERNEL VERIFICATION.
-/

namespace ImbalancedChen.P3ActualU8UnitPhysicalNorm
noncomputable section
open scoped BigOperators
open Classical

private theorem indicator_sum_bounds {α : Type*} (S : Finset α)
    (P : α → Prop) :
    0 ≤ (∑ t ∈ S, if P t then (1 : ℝ) else 0) ∧
      (∑ t ∈ S, if P t then (1 : ℝ) else 0) ≤ (S.card : ℝ) := by
  classical
  constructor
  · apply Finset.sum_nonneg
    intro t ht
    split_ifs <;> norm_num
  · calc
      (∑ t ∈ S, if P t then (1 : ℝ) else 0) ≤
          ∑ t ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs <;> norm_num
      _ = (S.card : ℝ) := by simp

/-- Exact count/mean signed physical discrepancy; positive moduli, one
unchanged (possibly negative) rho, original labels and multiplicity.
No distributional estimate is a premise. -/
theorem labelled_unit_signed_error_le_l1 {α : Type*} (S : Finset α)
    (f : α → ℕ) (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hQ : ∀ q ∈ Q, 0 < q) :
    |p5z_labelledDistributionError S f (fun _ => (1 : ℝ))
        N Q rho| ≤ (S.card : ℝ) * (∑ q ∈ Q, |rho q|) := by
  classical
  have hpoint (q : ℕ) (hq : q ∈ Q) :
      |p5z_labelledCongruenceMass S f (fun _ => (1 : ℝ)) N q -
        p5z_labelledCoprimeMass S f (fun _ => (1 : ℝ)) q /
          (Nat.totient q : ℝ)| ≤ (S.card : ℝ) := by
    obtain ⟨hcong0, hcong1⟩ :=
      indicator_sum_bounds S (fun t => Nat.ModEq q (f t) N)
    obtain ⟨hcop0, hcop1⟩ :=
      indicator_sum_bounds S (fun t => Nat.Coprime (f t) q)
    have hphiNat : 1 ≤ Nat.totient q := by
      have hp : 0 < Nat.totient q := Nat.totient_pos.mpr (hQ q hq)
      omega
    have hphi : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
      exact_mod_cast hphiNat
    have hphi0 : (0 : ℝ) < (Nat.totient q : ℝ) := by linarith
    have hdiv0 :
        0 ≤ (∑ t ∈ S, if Nat.Coprime (f t) q then (1 : ℝ) else 0) /
          (Nat.totient q : ℝ) := div_nonneg hcop0 hphi0.le
    have hdiv1 :
        (∑ t ∈ S, if Nat.Coprime (f t) q then (1 : ℝ) else 0) /
          (Nat.totient q : ℝ) ≤ (S.card : ℝ) := by
      apply (div_le_iff₀ hphi0).2
      have hm : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
      have hprod : 0 ≤ (S.card : ℝ) *
          ((Nat.totient q : ℝ) - 1) :=
        mul_nonneg hm (by linarith)
      nlinarith only [hcop1, hprod]
    change |(∑ t ∈ S, if Nat.ModEq q (f t) N then (1 : ℝ) else 0) -
      (∑ t ∈ S, if Nat.Coprime (f t) q then (1 : ℝ) else 0) /
        (Nat.totient q : ℝ)| ≤ (S.card : ℝ)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold p5z_labelledDistributionError
  calc
    _ ≤ ∑ q ∈ Q,
        |rho q * (p5z_labelledCongruenceMass S f
          (fun _ => (1 : ℝ)) N q -
          p5z_labelledCoprimeMass S f (fun _ => (1 : ℝ)) q /
            (Nat.totient q : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Q, |rho q| * (S.card : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpoint q hq) (abs_nonneg _)
    _ = (S.card : ℝ) * (∑ q ∈ Q, |rho q|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- Explicit actual U8 unit-fibre bound, still conditional on no
integer-rho_T norm. The N^(2/3) factor is from the literal
pre-existing source injection, NOT a new asymptotic supplier. -/
theorem actual_u8_unit_error_le_physical_l1 (N : ℕ) (hN : 1 ≤ N)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hQ : ∀ q ∈ Q, 0 < q) :
    |p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        (fun p : ℕ × ℕ => p.1 * p.2) (fun _ => (1 : ℝ)) N Q rho| ≤
      (N : ℝ) ^ (2 / 3 : ℝ) * (∑ q ∈ Q, |rho q|) := by
  have hfinite := labelled_unit_signed_error_le_l1
    (currentChenUpsilon8UnitFibres N)
    (fun p : ℕ × ℕ => p.1 * p.2) N Q rho hQ
  have hcard := currentChenUpsilon8_unitFibres_card_le_power hN
  have hnonneg : 0 ≤ ∑ q ∈ Q, |rho q| := by
    apply Finset.sum_nonneg
    intro q hq
    exact abs_nonneg _
  exact hfinite.trans (mul_le_mul_of_nonneg_right hcard hnonneg)

end
end ImbalancedChen.P3ActualU8UnitPhysicalNorm
