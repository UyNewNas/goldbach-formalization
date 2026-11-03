import ImbalancedChen.P4AFiniteCapTaggedPayment

/-! SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.
The active support belongs to the exact finite-cap tagged rho paid in the
preceding file. The single budget is ell + tau*J0 < 1/1000.
-/

namespace ImbalancedChen.P4AFiniteCapTaggedConstructor

noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport

theorem compiled_rough_support {h n : ℕ} (values : Fin n → ℝ)
    (select : List ℕ → Fin n) (gate : List ℕ → Bool)
    (history : Fin h → List ℕ → Bool)
    (omega : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N)
    (z tau : ℝ) (htau : 0 < tau) {d : ℕ}
    (hd : coefficient (keep values select gate N) (tag (J0 omega) select gate history)
      N cap ((N : ℝ) ^ omega) z tau d ≠ 0) :
    d.primeFactorsList.length < J0 omega ∧
      (d : ℝ) < (N : ℝ) ^ ((299 / 500 : ℝ) + tau * (J0 omega : ℝ)) := by
  obtain ⟨e, heraw, hecell, _htag, _hlabels⟩ := active_has_raw_witness
    (keep values select gate N) (tag (J0 omega) select gate history)
    N cap ((N : ℝ) ^ omega) z tau hd
  have hrank : d.primeFactorsList.length < J0 omega := by
    rw [← cell_rank_preserved _ _ _ _ _ _ hecell]
    exact raw_rank_lt values select gate omega homega N cap hN z heraw
  have hdU : d ∈ universe N cap ((N : ℝ) ^ omega) z := by
    by_contra hn
    exact hd (by simp only [coefficient, if_neg hn])
  have hprod := same_cell_product_le _ N cap hN _ z tau htau hdU hecell
  have hraw := raw_support_lt values select gate N cap hN ((N : ℝ) ^ omega) z heraw
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  refine ⟨hrank, ?_⟩
  calc
    (d : ℝ) ≤ (N : ℝ) ^ (tau * (d.primeFactorsList.length : ℝ)) * (e : ℝ) := hprod
    _ < (N : ℝ) ^ (tau * (d.primeFactorsList.length : ℝ)) *
        (N : ℝ) ^ (299 / 500 : ℝ) :=
      mul_lt_mul_of_pos_left hraw (Real.rpow_pos_of_pos hn0 _)
    _ = (N : ℝ) ^ ((299 / 500 : ℝ) + tau * (d.primeFactorsList.length : ℝ)) := by
      rw [Real.rpow_add hn0]
      ring
    _ ≤ (N : ℝ) ^ ((299 / 500 : ℝ) + tau * (J0 omega : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hn.le
      have hr : (d.primeFactorsList.length : ℝ) ≤ (J0 omega : ℝ) := by
        exact_mod_cast hrank.le
      exact add_le_add_left (mul_le_mul_of_nonneg_left hr htau.le) _

/-- Generic physical factorization is instantiated at this very rho;
the small factor is bounded using its actual sign-selected beta weight. -/
theorem compiledRho_support {h n : ℕ} (values : Fin n → ℝ)
    (select : List ℕ → Fin n) (gate : List ℕ → Bool)
    (history : Fin h → List ℕ → Bool)
    (omega ell tau : ℝ) (homega : 0 < omega) (htau : 0 < tau)
    (hbudget : ell + tau * (J0 omega : ℝ) < 1 / 1000)
    (N cap : ℕ) (hN : 2 ≤ N) (z : ℝ) {q : ℕ}
    (hq : P4AUpperTaggedBetaAttachment.rho (keep values select gate N)
      (tag (J0 omega) select gate history) N cap ((N : ℝ) ^ omega) z tau
        ((N : ℝ) ^ ell) q ≠ 0) :
    (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  let retained := keep values select gate N
  let tags := tag (J0 omega) select gate history
  let w := (N : ℝ) ^ omega
  let L := (N : ℝ) ^ ell
  have hm : q ∈ P4AUpperTaggedBetaAttachment.support N cap w z := by
    by_contra hn
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hn)
  obtain ⟨⟨a, d⟩, had, hprod⟩ := Finset.mem_image.mp hm
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  have hv := P4AUpperTaggedBetaAttachment.rho_at_product retained tags N cap w z tau L ha hd
  have hp : coefficient retained tags N cap w z tau d *
      (if 0 ≤ coefficient retained tags N cap w z tau d
       then actualSmallRosserPlus N cap w L a else actualSmallRosserMinus N cap w L a) ≠ 0 := by
    rw [← hv, hprod]
    exact hq
  obtain ⟨hc, hb⟩ := mul_ne_zero_iff.mp hp
  have haL : (a : ℝ) < L := by
    split_ifs at hb with hs
    · exact (actualSmallRosserPlus_active hb).2.1
    · exact (actualSmallRosserMinus_active hb).2.1
  have hdR := (compiled_rough_support values select gate history omega homega
    N cap hN z tau htau hc).2
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  calc
    (q : ℝ) = (a : ℝ) * (d : ℝ) := by rw [← hprod, Nat.cast_mul]
    _ ≤ (N : ℝ) ^ ell * (d : ℝ) :=
      mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg _)
    _ < (N : ℝ) ^ ell *
        (N : ℝ) ^ ((299 / 500 : ℝ) + tau * (J0 omega : ℝ)) :=
      mul_lt_mul_of_pos_left hdR (Real.rpow_pos_of_pos hn0 _)
    _ = (N : ℝ) ^ (ell + (299 / 500 : ℝ) + tau * (J0 omega : ℝ)) := by
      rw [add_assoc, Real.rpow_add hn0]
    _ ≤ (N : ℝ) ^ (599 / 1000 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hn.le
      linarith

/-- This width restriction and the payment width can be intersected;
both precede N, and the existing payment works for every smaller width. -/
theorem exists_preN_support_width {n h : ℕ} (values : Fin n → ℝ)
    (omega ell : ℝ) (homega : 0 < omega) (hell : ell < 1 / 1000) :
    ∃ tau0 : ℝ, 0 < tau0 ∧
      ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
        ell + tau * (J0 omega : ℝ) < 1 / 1000 ∧
        ∀ N cap : ℕ, 2 ≤ N → ∀ z : ℝ,
        ∀ (select : List ℕ → Fin n) (gate : List ℕ → Bool)
          (history : Fin h → List ℕ → Bool) (q : ℕ),
        P4AUpperTaggedBetaAttachment.rho (keep values select gate N)
          (tag (J0 omega) select gate history) N cap ((N : ℝ) ^ omega) z tau
            ((N : ℝ) ^ ell) q ≠ 0 →
          (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  let tau0 : ℝ := (1 / 1000 - ell) / (2 * ((J0 omega : ℝ) + 1))
  have hj : 0 ≤ (J0 omega : ℝ) := Nat.cast_nonneg _
  have hden : 0 < 2 * ((J0 omega : ℝ) + 1) := by positivity
  have ht0 : 0 < tau0 := div_pos (by linarith) hden
  have htEq : tau0 * (2 * ((J0 omega : ℝ) + 1)) = 1 / 1000 - ell :=
    div_mul_cancel₀ _ hden.ne'
  refine ⟨tau0, ht0, ?_⟩
  intro tau htau htmax
  have hcost : tau * (J0 omega : ℝ) ≤ tau0 * (J0 omega : ℝ) :=
    mul_le_mul_of_nonneg_right htmax hj
  have hbudget : ell + tau * (J0 omega : ℝ) < 1 / 1000 := by nlinarith
  refine ⟨hbudget, ?_⟩
  intro N cap hN z select gate history q hq
  exact compiledRho_support values select gate history omega ell tau homega htau
    hbudget N cap hN z hq

end
end ImbalancedChen.P4AFiniteCapTaggedConstructor
