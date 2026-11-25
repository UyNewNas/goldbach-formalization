import ImbalancedChen.P2FiniteMarkedGamma5RadialTupleCount
import ImbalancedChen.P5U7ActualRoughTargetExclusion
import ImbalancedChen.PowerErrorBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

Target-divisor deletion for one complete ordered-prime ambient at the
actual frozen cutoff cut(N) = N^(frozenLeafCutoffFloor / 2) and rank K.
Every tuple has unit weight. All ranks from zero through K and repeated
prime coordinates are retained. The product map is charged by the
existing k^k fibre bound, never treated as injective.

The arithmetic integer estimate is the original
p5U7ActualBadRough_card_le_log, and the decay is the original
tendsto_nat_log_pow_div_rpow. Neither supplier is reproved here.
This is the N-coprimality deletion needed when comparing ambient prime
tuples with primeWindow N, separate from a geometric boundary strip.
It does not identify the complete selected inner mass with ordinaryBad.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5TargetExclusion
noncomputable section
open Filter Finset Real LiLiuPrereqBuchstab
open Part5OriginalH430ClassicalFixedClampGeometry (prime_divisor_floor)
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2FiniteMarkedGamma5RadialRoughMass (cut cutExponent cutExponent_pos)
open P2FiniteMarkedGamma5RadialTupleCount (multiplicity)
open scoped Classical Topology BigOperators

/-- Ordered prime tuples with the actual rough floor and complete
product at most 2N, whose product is not coprime to the target N. -/
def noncoprimeTuples (N k : ℕ) : Finset (Fin k → Fin (2 * N + 1)) :=
  (Part3.labelledPrimeTuples k (2 * N)).filter (fun t =>
    (∀ i, cut N ≤ ((t i).val : ℝ)) ∧
      (Part3.labelledProduct t : ℝ) ≤ 2 * (N : ℝ) ∧
      ¬ Nat.Coprime (Part3.labelledProduct t) N)

/-- One unit-weight ambient, summed over the original fixed rank range. -/
def noncoprimeCount (N : ℕ) : ℝ :=
  ∑ k : Fin (frozenSourceRankBound + 1), ((noncoprimeTuples N k.val).card : ℝ)

/-- Every excluded complete product belongs to the existing arithmetic
exception carrier. This also covers rank zero without any special premise. -/
theorem product_mem_bad {N k : ℕ} {t : Fin k → Fin (2 * N + 1)}
    (ht : t ∈ noncoprimeTuples N k) :
    Part3.labelledProduct t ∈ p5U7ActualBadRough N (2 * (N : ℝ)) (cut N) := by
  obtain ⟨hprime, hfloor, hcap, hcop⟩ := mem_filter.mp ht
  have htpr := (mem_filter.mp hprime).2
  let L := List.ofFn (fun i : Fin k => (t i).val)
  have hL : ∀ q ∈ L, q.Prime ∧ cut N ≤ (q : ℝ) := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨htpr i, hfloor i⟩
  have hprod : L.prod = Part3.labelledProduct t := by
    simp only [L, List.prod_ofFn, Part3.labelledProduct]
  apply mem_filter.mpr
  refine ⟨mem_roughNumbers.mpr
    ⟨Finset.prod_pos (fun i _ => (htpr i).pos), hcap, ?_⟩, hcop⟩
  intro q hq hd
  exact prime_divisor_floor hL q hq (hprod.symm ▸ hd)

/-- The original finite product-fibre theorem retains every ordering and
every repetition. In particular its k = 0 case is not discarded. -/
theorem rank_bound (N k : ℕ) :
    ((noncoprimeTuples N k).card : ℝ) ≤ ((k ^ k : ℕ) : ℝ) *
      ((p5U7ActualBadRough N (2 * (N : ℝ)) (cut N)).card : ℝ) := by
  let S := noncoprimeTuples N k
  have hsub : S ⊆ Part3.labelledPrimeTuples k (2 * N) := filter_subset _ _
  have hcard : S.card =
      ∑ m ∈ p5U7ActualBadRough N (2 * (N : ℝ)) (cut N),
        (S.filter (fun t => Part3.labelledProduct t = m)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ ht => product_mem_bad ht)
  change (S.card : ℝ) ≤ _
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ _m ∈ p5U7ActualBadRough N (2 * (N : ℝ)) (cut N),
        ((k ^ k : ℕ) : ℝ) :=
      sum_le_sum (fun m _ => by
        exact_mod_cast p5z_marked_prime_product_fibre_card_le S hsub m)
    _ = _ := by simp [mul_comm]

/-- The original symbolic all-rank multiplicity has no history or colour
multiplier. It is fixed before the target N tends to infinity. -/
theorem all_ranks_bound (N : ℕ) :
    noncoprimeCount N ≤ multiplicity *
      ((p5U7ActualBadRough N (2 * (N : ℝ)) (cut N)).card : ℝ) := by
  have hh := Finset.sum_le_sum
    (s := (univ : Finset (Fin (frozenSourceRankBound + 1))))
    (fun k _ => rank_bound N k.val)
  rw [← sum_mul] at hh
  exact hh

theorem rank_card_le_noncoprimeCount (N k : ℕ)
    (hk : k ≤ frozenSourceRankBound) :
    ((noncoprimeTuples N k).card : ℝ) ≤ noncoprimeCount N := by
  let j : Fin (frozenSourceRankBound + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  change ((noncoprimeTuples N j.val).card : ℝ) ≤
    ∑ i : Fin (frozenSourceRankBound + 1), ((noncoprimeTuples N i.val).card : ℝ)
  exact Finset.single_le_sum (fun i _ => Nat.cast_nonneg _) (mem_univ j)

/-- The genuine source deletion cost has a fixed power-saving majorant.
No source asymptotic, J bound, sieve coefficient or target estimate is a premise. -/
theorem normalized_all_ranks_le {N : ℕ} (hN : 1 < N) :
    P2FiniteMarkedGamma5RadialRoughMass.norm N * noncoprimeCount N ≤
      (2 * multiplicity / log 2) *
        ((log (N : ℝ)) ^ 2 / (N : ℝ) ^ cutExponent) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have hcut : 0 < cut N := rpow_pos_of_pos h0 _
  have hM : 0 ≤ multiplicity := by
    unfold multiplicity
    exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hbad := p5U7ActualBadRough_card_le_log
    (N := N) (x := 2 * (N : ℝ)) (z := cut N) (by omega) (by positivity) hcut
  have hbound := (all_ranks_bound N).trans
    (mul_le_mul_of_nonneg_left hbad hM)
  have hnorm : 0 ≤ P2FiniteMarkedGamma5RadialRoughMass.norm N :=
    div_nonneg (log_pos hNr).le h0.le
  apply (mul_le_mul_of_nonneg_left hbound hnorm).trans_eq
  dsimp only [P2FiniteMarkedGamma5RadialRoughMass.norm, cut] at hcut ⊢
  field_simp [h0.ne', hcut.ne', (log_pos (by norm_num : (1 : ℝ) < 2)).ne'] <;> ring

/-- All ranks have one absolute ordinary-mass limit at the actual cutoff. -/
theorem normalized_noncoprimeCount_tendsto :
    Tendsto (fun N : ℕ =>
      P2FiniteMarkedGamma5RadialRoughMass.norm N * noncoprimeCount N)
      atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => (2 * multiplicity / log 2) *
      ((log (N : ℝ)) ^ 2 / (N : ℝ) ^ cutExponent)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_log_pow_div_rpow 2 cutExponent_pos).const_mul
        (2 * multiplicity / log 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hu
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast hN
    have hc : 0 ≤ noncoprimeCount N := by
      unfold noncoprimeCount
      exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    exact mul_nonneg
      (div_nonneg (log_pos hNr).le (Nat.cast_nonneg N)) hc
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact normalized_all_ranks_le hN

theorem absolute_noncoprime_payment {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      P2FiniteMarkedGamma5RadialRoughMass.norm N * noncoprimeCount N ≤ ε := by
  filter_upwards [normalized_noncoprimeCount_tendsto.eventually (gt_mem_nhds he)]
    with N hN
  exact hN.le

/-- A single threshold pays every original bounded rank, not one new
epsilon for each rank or each moving prime tuple. -/
theorem absolute_noncoprime_rank_payment {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, k ≤ frozenSourceRankBound →
      P2FiniteMarkedGamma5RadialRoughMass.norm N *
        ((noncoprimeTuples N k).card : ℝ) ≤ ε := by
  filter_upwards [absolute_noncoprime_payment he, eventually_gt_atTop (1 : ℕ)]
    with N hpaid hN
  intro k hk
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hnorm : 0 ≤ P2FiniteMarkedGamma5RadialRoughMass.norm N :=
    div_nonneg (log_pos hNr).le (Nat.cast_nonneg N)
  exact (mul_le_mul_of_nonneg_left (rank_card_le_noncoprimeCount N k hk) hnorm).trans hpaid

end
end ImbalancedChen.P2FiniteMarkedGamma5TargetExclusion
