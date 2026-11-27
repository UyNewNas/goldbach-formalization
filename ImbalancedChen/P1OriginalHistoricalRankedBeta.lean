import ImbalancedChen.P1OriginalHistoricalCanonicalOwnerWord
import ImbalancedChen.P4ASpliceDifferenceLowerModulus
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
The actual historical coefficient, split by the full rough word rank.
The original rough Mobius sign chooses beta before the owner mask is applied.
All cutoffs stay on the complete modulus, and the rank bound precedes N.
This is a finite signed identity, not a rectangular-atom or medium licence.
-/
namespace ImbalancedChen.P1OriginalHistoricalRankedBeta
noncomputable section
open Classical
open scoped BigOperators
open P1OriginalHistoricalCoefficientDictionary
open P1OriginalHistoricalRoughOwnerPartition
open P1OriginalHistoricalCanonicalOwnerWord
open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)

def roughRank (b : ℕ) : ℕ := b.primeFactorsList.length

def rankBound (rho : ℝ) : ℕ := ⌊(599 / 1000 : ℝ) / rho⌋₊

def rankBeta (N cap : ℕ) (w L : ℝ) (r a : ℕ) : ℝ :=
  if 0 ≤ (-1 : ℝ) ^ r then actualSmallRosserPlus N cap w L a
  else actualSmallRosserMinus N cap w L a

private theorem common_squarefree (old fresh : List ℕ → Bool) (N cap : ℕ)
    (w z : ℝ) {b : ℕ} (hb : b ∈ commonRoughSupport old fresh N cap w z) : Squarefree b := by
  rcases Finset.mem_union.mp hb with hf | ho
  · exact fixedRoughSupport_squarefree fresh N cap w z hf
  · exact fixedRoughSupport_squarefree old N cap w z ho

theorem roughRank_eq_card (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {b : ℕ} (hb : b ∈ commonRoughSupport old fresh N cap w z) :
    roughRank b = b.primeFactors.card := by
  have hs := common_squarefree old fresh N cap w z hb
  rw [roughRank, ← List.toFinset_card_of_nodup hs.nodup_primeFactorsList, Nat.toFinset_factors]

theorem moebius_eq_rank_sign (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {b : ℕ} (hb : b ∈ commonRoughSupport old fresh N cap w z) :
    (ArithmeticFunction.moebius b : ℝ) = (-1 : ℝ) ^ roughRank b := by
  have h : ArithmeticFunction.moebius b = (-1 : ℤ) ^ roughRank b := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree (common_squarefree old fresh N cap w z hb),
      ArithmeticFunction.cardFactors_apply]
    rfl
  exact_mod_cast h

theorem attachedMobius_eq_rank_beta (old fresh : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) {b r : ℕ} (hb : b ∈ commonRoughSupport old fresh N cap w z)
    (hr : roughRank b = r) (a : ℕ) :
    attachedMobius N cap w L a b = (-1 : ℝ) ^ r * rankBeta N cap w L r a := by
  unfold attachedMobius signAttachedCoefficient
  rw [moebius_eq_rank_sign old fresh N cap w z hb, hr]
  rfl

/-- A bound fixed before N, derived using the original complete .599 filter. -/
theorem remaining_rough_rank_le {N cap a b : ℕ} (hN : 1 < N)
    (old fresh : List ℕ → Bool) (rho z B : ℝ) (hrho : 0 < rho)
    (ha : a ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ rho))
    (hb : b ∈ commonRoughSupport old fresh N cap ((N : ℝ) ^ rho) z)
    (hq : a * b ∈ remainingModuli B N
      (trueDDeltaSupport old fresh N cap ((N : ℝ) ^ rho) z)) :
    roughRank b ≤ rankBound rho := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hlow : ((N : ℝ) ^ rho) ^ b.primeFactors.card ≤ (b : ℝ) := by
    rcases Finset.mem_union.mp hb with hf | ho
    · exact P4ASpliceDifferenceLowerModulus.retained_pow_primeFactors_card_le
        fresh N cap (Real.rpow_nonneg hn0.le _) z hf
    · exact P4ASpliceDifferenceLowerModulus.retained_pow_primeFactors_card_le
        old N cap (Real.rpow_nonneg hn0.le _) z ho
  have hapos : 0 < a := Nat.pos_of_ne_zero (actualSmallRosserSupport_squarefree _ _ _ ha).ne_zero
  have hbq : (b : ℝ) ≤ ((a * b : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_mul_of_pos_left b hapos)
  have hupper : ((a * b : ℕ) : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) :=
    (Finset.mem_filter.mp hq).2.2
  have hp : (N : ℝ) ^ (rho * (b.primeFactors.card : ℝ)) <
      (N : ℝ) ^ (599 / 1000 : ℝ) := by
    rw [Real.rpow_mul hn0.le, Real.rpow_natCast]
    exact hlow.trans_lt (hbq.trans_lt hupper)
  have hc := (Real.rpow_lt_rpow_left_iff hn).mp hp
  rw [roughRank_eq_card old fresh N cap ((N : ℝ) ^ rho) z hb]
  apply (Nat.le_floor_iff (div_nonneg (by norm_num : (0 : ℝ) ≤ 599 / 1000) hrho.le)).mpr
  exact (le_div_iff₀ hrho).mpr (by simpa only [mul_comm] using hc.le)

def activeFibre (B : ℝ) (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ) : Finset ℕ :=
  (fibre old fresh N cap w z state).filter (fun b =>
    ∃ a ∈ actualSmallRosserSupport N cap w,
      a * b ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z))

def rankedFibre (B : ℝ) (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ) (r : ℕ) : Finset ℕ :=
  (activeFibre B old fresh N cap w z state).filter (fun b => roughRank b = r)

theorem activeFibre_rank_le {N cap : ℕ} (hN : 1 < N) (old fresh : List ℕ → Bool)
    (rho z B : ℝ) (hrho : 0 < rho) (state : FirstExitDepthState ℕ) {b : ℕ}
    (hb : b ∈ activeFibre B old fresh N cap ((N : ℝ) ^ rho) z state) :
    roughRank b ≤ rankBound rho := by
  obtain ⟨hf, a, ha, hq⟩ := Finset.mem_filter.mp hb
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1
  exact remaining_rough_rank_le hN old fresh rho z B hrho ha hc hq

/-- This is the same actual tail, with the total rank fixed before beta. -/
theorem ranked_word_realization (B : ℝ) (old fresh : List ℕ → Bool) (N cap : ℕ)
    (w z : ℝ) (state : FirstExitDepthState ℕ) (r : ℕ) {b : ℕ}
    (hb : b ∈ rankedFibre B old fresh N cap w z state r) :
    ∃ tail : List ℕ,
      b.primeFactorsList.reverse = state.selectedPrefix.reverse ++ tail ∧
      r = state.selectedPrefix.length + tail.length ∧ List.Sublist tail state.remaining ∧
      ((old state.selectedPrefix = true ∧
        FirstExitValidSelection (oddFirstExitPolicy old) state.selectedPrefix state.positive tail) ∨
       (fresh state.selectedPrefix = true ∧
        FirstExitValidSelection (oddFirstExitPolicy fresh) state.selectedPrefix state.positive tail)) := by
  obtain ⟨ha, hr⟩ := Finset.mem_filter.mp hb
  have hf := (Finset.mem_filter.mp ha).1
  obtain ⟨tail, he, ht, hv⟩ := realized_canonical_word old fresh N cap w z state b
    (fibre_realizes old fresh N cap w z state b hf)
  refine ⟨tail, he, ?_, ht, hv⟩
  have hlen := congrArg List.length he
  simpa only [List.length_reverse, List.length_append, ← hr, roughRank] using hlen

/-- The original complex test, with both fixed scalars outside all factors.
The beta choice uses original rank parity, not the sign after the mask. -/
theorem remaining_test_eq_ranked_owner_sum {N cap : ℕ} (hN : 1 < N)
    (old fresh : List ℕ → Bool) (rho z B L : ℝ) (hrho : 0 < rho) (G : ℕ → ℂ) :
    (∑ q ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap ((N : ℝ) ^ rho) z),
      (trueDDeltaRho old fresh N cap ((N : ℝ) ^ rho) z L q : ℂ) * G q) =
    ∑ state ∈ owners old fresh N cap ((N : ℝ) ^ rho) z,
      ((if fresh state.selectedPrefix = true then (1 : ℝ) else -1) : ℂ) *
        ∑ r ∈ Finset.range (rankBound rho + 1), ((-1 : ℝ) ^ r : ℂ) *
          ∑ b ∈ rankedFibre B old fresh N cap ((N : ℝ) ^ rho) z state r,
            ∑ a ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ rho),
              (rankBeta N cap ((N : ℝ) ^ rho) L r a : ℂ) *
                (if a * b ∈ remainingModuli B N
                  (trueDDeltaSupport old fresh N cap ((N : ℝ) ^ rho) z) then G (a * b) else 0) := by
  rw [remaining_test_eq_fixed_signed_owner_sum]
  apply Finset.sum_congr rfl
  intro state _
  congr 1
  let F : ℕ → ℂ := fun b =>
    ∑ a ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ rho),
      (attachedMobius N cap ((N : ℝ) ^ rho) L a b : ℂ) *
        (if a * b ∈ remainingModuli B N
          (trueDDeltaSupport old fresh N cap ((N : ℝ) ^ rho) z) then G (a * b) else 0)
  have hactive : (∑ b ∈ fibre old fresh N cap ((N : ℝ) ^ rho) z state, F b) =
      ∑ b ∈ activeFibre B old fresh N cap ((N : ℝ) ^ rho) z state, F b := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hout
    apply Finset.sum_eq_zero
    intro a ha
    have hn : a * b ∉ remainingModuli B N
        (trueDDeltaSupport old fresh N cap ((N : ℝ) ^ rho) z) := by
      intro hq
      exact hout (Finset.mem_filter.mpr ⟨hb, a, ha, hq⟩)
    simp only [if_neg hn, mul_zero]
  change (∑ b ∈ fibre old fresh N cap ((N : ℝ) ^ rho) z state, F b) = _
  rw [hactive]
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (fun b hb => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (activeFibre_rank_le (cap := cap) hN old fresh rho z B hrho state hb))) F
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨ha, hbr⟩ := Finset.mem_filter.mp hb
  have hf := (Finset.mem_filter.mp ha).1
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [attachedMobius_eq_rank_beta old fresh N cap ((N : ℝ) ^ rho) z L hc hbr a,
    Complex.ofReal_mul, Complex.ofReal_pow]
  ring

end
end ImbalancedChen.P1OriginalHistoricalRankedBeta
