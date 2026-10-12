import ImbalancedChen.ActualPrimeBoxOuterUniformity
import ImbalancedChen.ActualRosserOddBoxUnion
import ImbalancedChen.ActualRosserEvenBoxUnion

/-!
# Fixed boundary boxes with varying level and outer exponent

The threshold depends on a fixed finite family and a lower outer exponent.
Both the actual outer exponent and the level exponent are quantified after
that threshold. Level-dependent geometric gates remain explicit finite
inequalities; no analytic density assumption is supplied by the caller.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- A single threshold for a finite family of possibly different dimensions.
The fixed reference gain bounds the sum of actual masses at every larger
outer exponent. Empty families require no special hypothesis. -/
theorem exists_actualPrimeBoxEulerMass_sum_uniform_outer_lower_threshold
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (d : ι → ℕ)
    (a b : ∀ j, Fin (d j) → ℝ) (q : ∀ j, Fin (d j))
    (ha : ∀ j ∈ S, ∀ i, 0 < a j i) (hab : ∀ j ∈ S, ∀ i, a j i < b j i)
    (u₀ : ℝ) (hu₀ : 0 < u₀) (hbu : ∀ j ∈ S, b j (q j) ≤ u₀)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ u : ℝ, u₀ ≤ u → ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        (∑ j ∈ S, (u₀ / b j (q j)) * (∏ i, Real.log (b j i / a j i))) - eta ≤
          ∑ j ∈ S, actualPrimeBoxEulerMass N cap (a j) (b j) u (q j) := by
  let eps := eta / ((S.card : ℝ) + 1)
  have heps : 0 < eps := div_pos heta (by positivity)
  have heach (j : S) : ∃ n : ℕ, 2 ≤ n ∧ ∀ N : ℕ, n ≤ N → Even N →
      ∀ u : ℝ, u₀ ≤ u → ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        (u₀ / b j.val (q j.val)) * (∏ i, Real.log (b j.val i / a j.val i)) - eps ≤
          actualPrimeBoxEulerMass N cap (a j.val) (b j.val) u (q j.val) :=
    exists_actualPrimeBoxEulerMass_uniform_outer_lower_threshold (a j.val) (b j.val)
      (ha j.val j.property) (hab j.val j.property) u₀ hu₀ (q j.val)
      (hbu j.val j.property) eps heps
  choose n hn2 hn using heach
  refine ⟨max 2 (Finset.univ.sup n), le_max_left _ _, ?_⟩
  intro N hN hEven u hu cap hcap
  have hsum :
      (∑ j ∈ S, ((u₀ / b j (q j)) * (∏ i, Real.log (b j i / a j i)) - eps)) ≤
        ∑ j ∈ S, actualPrimeBoxEulerMass N cap (a j) (b j) u (q j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjN : n ⟨j, hj⟩ ≤ N :=
      (Finset.le_sup (f := n) (Finset.mem_univ ⟨j, hj⟩)).trans
        ((le_max_right _ _).trans hN)
    exact hn ⟨j, hj⟩ N hjN hEven u hu cap hcap
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hloss : (S.card : ℝ) * eps ≤ eta := by
    dsimp [eps]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (S.card : ℝ) + 1)).mpr
    nlinarith
  linarith

/-- The common prime-mass threshold is independent of both later exponents.
The boxes must satisfy the actual boundary gates at those exponents. -/
theorem exists_actualSmallRosserPlusDensity_oddBoxUnion_uniform_lower_threshold
    (K : Finset ℕ) {ι : ℕ → Type*} [∀ k, DecidableEq (ι k)]
    (J : ∀ k, Finset (ι k)) (a b : ∀ k, ι k → Fin (2 * k + 1) → ℝ)
    (u₀ : ℝ) (hu₀ : 0 < u₀)
    (ha : ∀ k ∈ K, ∀ j ∈ J k, ∀ i, 0 < a k j i)
    (hab : ∀ k ∈ K, ∀ j ∈ J k, ∀ i, a k j i < b k j i)
    (hsep : ∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k),
      b k j i.succ ≤ a k j i.castSucc)
    (hbu : ∀ k ∈ K, ∀ j ∈ J k, b k j 0 ≤ u₀)
    (hdisj : ∀ k ∈ K, ∀ i ∈ J k, ∀ j ∈ J k, i ≠ j →
      ∃ t, b k i t ≤ a k j t ∨ b k j t ≤ a k i t)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ u beta : ℝ, u₀ ≤ u → u ≤ beta →
      (∀ k ∈ K, ∀ j ∈ J k, (∑ i : Fin (2 * k), b k j i.castSucc) ≤ beta) →
      (∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k), Even i.val →
        (∑ t : Fin (2 * k) with t.val < i.val, b k j t.castSucc) +
          3 * b k j i.castSucc ≤ beta) →
      (∀ k ∈ K, ∀ j ∈ J k,
        beta ≤ (∑ i : Fin (2 * k), a k j i.castSucc) + 3 * a k j (Fin.last (2 * k))) →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (∑ k ∈ K, ∑ j ∈ J k, (u₀ / b k j (Fin.last (2 * k))) *
          (∏ i, Real.log (b k j i / a k j i))) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hbuLast (k : ℕ) (hk : k ∈ K) (j : ι k) (hj : j ∈ J k) :
      b k j (Fin.last (2 * k)) ≤ u₀ := by
    have hb : Antitone (b k j) := Fin.antitone_iff_succ_le.mpr
      (fun i => (hsep k hk j hj i).trans (hab k hk j hj i.castSucc).le)
    exact (hb (Fin.zero_le _)).trans (hbu k hk j hj)
  obtain ⟨N0, hN0, hmass⟩ :=
    exists_actualPrimeBoxEulerMass_sum_uniform_outer_lower_threshold
      (K.sigma J) (fun z => 2 * z.1 + 1) (fun z => a z.1 z.2) (fun z => b z.1 z.2)
      (fun z => Fin.last (2 * z.1))
      (fun z hz => ha z.1 (Finset.mem_sigma.mp hz).1 z.2 (Finset.mem_sigma.mp hz).2)
      (fun z hz => hab z.1 (Finset.mem_sigma.mp hz).1 z.2 (Finset.mem_sigma.mp hz).2)
      u₀ hu₀
      (fun z hz => hbuLast z.1 (Finset.mem_sigma.mp hz).1 z.2 (Finset.mem_sigma.mp hz).2)
      eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven u beta hu hubeta hprod hprefix hshell cap hcap
  have hm := hmass N hN hEven u hu cap hcap
  rw [Finset.sum_sigma, Finset.sum_sigma] at hm
  have hfull := actualSmallRosserPlusDensity_ratio_ge_oddBoxUnion K J a b
    N cap (by omega) hEven u beta (hu₀.trans_le (hu.trans hubeta)) hubeta hab hsep
    (fun k hk j hj => (hbu k hk j hj).trans hu) hprod hprefix hshell hdisj hcap
  linarith

/-- The even-boundary analogue subtracts the same fixed reference gains
from one; its threshold likewise precedes both varying exponents. -/
theorem exists_actualSmallRosserMinusDensity_evenBoxUnion_uniform_upper_threshold
    (K : Finset ℕ) {ι : ℕ → Type*} [∀ k, DecidableEq (ι k)]
    (J : ∀ k, Finset (ι k)) (a b : ∀ k, ι k → Fin (2 * k + 2) → ℝ)
    (u₀ : ℝ) (hu₀ : 0 < u₀)
    (ha : ∀ k ∈ K, ∀ j ∈ J k, ∀ i, 0 < a k j i)
    (hab : ∀ k ∈ K, ∀ j ∈ J k, ∀ i, a k j i < b k j i)
    (hsep : ∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k + 1),
      b k j i.succ ≤ a k j i.castSucc)
    (hbu : ∀ k ∈ K, ∀ j ∈ J k, b k j 0 ≤ u₀)
    (hdisj : ∀ k ∈ K, ∀ i ∈ J k, ∀ j ∈ J k, i ≠ j →
      ∃ t, b k i t ≤ a k j t ∨ b k j t ≤ a k i t)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ u beta : ℝ, u₀ ≤ u → u ≤ beta →
      (∀ k ∈ K, ∀ j ∈ J k, (∑ i : Fin (2 * k + 1), b k j i.castSucc) ≤ beta) →
      (∀ k ∈ K, ∀ j ∈ J k, ∀ i : Fin (2 * k + 1), Odd i.val →
        (∑ t : Fin (2 * k + 1) with t.val < i.val, b k j t.castSucc) +
          3 * b k j i.castSucc ≤ beta) →
      (∀ k ∈ K, ∀ j ∈ J k,
        beta ≤ (∑ i : Fin (2 * k + 1), a k j i.castSucc) +
          3 * a k j (Fin.last (2 * k + 1))) →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
          1 - (∑ k ∈ K, ∑ j ∈ J k, (u₀ / b k j (Fin.last (2 * k + 1))) *
            (∏ i, Real.log (b k j i / a k j i))) + eta := by
  have hbuLast (k : ℕ) (hk : k ∈ K) (j : ι k) (hj : j ∈ J k) :
      b k j (Fin.last (2 * k + 1)) ≤ u₀ := by
    have hb : Antitone (b k j) := Fin.antitone_iff_succ_le.mpr
      (fun i => (hsep k hk j hj i).trans (hab k hk j hj i.castSucc).le)
    exact (hb (Fin.zero_le _)).trans (hbu k hk j hj)
  obtain ⟨N0, hN0, hmass⟩ :=
    exists_actualPrimeBoxEulerMass_sum_uniform_outer_lower_threshold
      (K.sigma J) (fun z => 2 * z.1 + 2) (fun z => a z.1 z.2) (fun z => b z.1 z.2)
      (fun z => Fin.last (2 * z.1 + 1))
      (fun z hz => ha z.1 (Finset.mem_sigma.mp hz).1 z.2 (Finset.mem_sigma.mp hz).2)
      (fun z hz => hab z.1 (Finset.mem_sigma.mp hz).1 z.2 (Finset.mem_sigma.mp hz).2)
      u₀ hu₀
      (fun z hz => hbuLast z.1 (Finset.mem_sigma.mp hz).1 z.2 (Finset.mem_sigma.mp hz).2)
      eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven u beta hu hubeta hprod hprefix hshell cap hcap
  have hm := hmass N hN hEven u hu cap hcap
  rw [Finset.sum_sigma, Finset.sum_sigma] at hm
  have hfull := actualSmallRosserMinusDensity_ratio_le_evenBoxUnion K J a b
    N cap (by omega) hEven u beta (hu₀.trans_le (hu.trans hubeta)) hubeta hab hsep
    (fun k hk j hj => (hbu k hk j hj).trans hu) hprod hprefix hshell hdisj hcap
  linarith

end

end ImbalancedChen
