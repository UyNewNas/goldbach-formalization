import ImbalancedChen.P5OriginalPresievedRoughRank
import ImbalancedChen.ActualPrimeSlotSquarefreeSymmetry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual retained ordinary rough divisor is realized by its unique
distinct descending prime slots from the ORIGINAL rough universe. Its
strict cutoff and all original upper-prefix gates remain literal, and its
roughWeight is the exact Mobius parity sign on those slots.
-/
namespace ImbalancedChen.P5Z.OriginalPresievedRoughPrimeSlots
noncomputable section
open Classical
open scoped BigOperators
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalOrdinaryResidualArithmeticFactor OriginalPresievedRoughRank
open U1011OriginalSixteenArithmeticProducts
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

def canonicalSlots (N cap : ℕ) (w Z : ℝ) (d : ℕ) : List ℕ :=
  (roughPrimeUniverse N cap w Z).filter (fun p => p ∈ d.primeFactors)

theorem canonicalSlots_descending (N cap : ℕ) (w Z : ℝ) (d : ℕ) :
    (canonicalSlots N cap w Z d).Pairwise (· > ·) :=
  (roughPrimeUniverse_pairwise_gt N cap w Z).sublist List.filter_sublist

theorem canonicalSlots_nodup (N cap : ℕ) (w Z : ℝ) (d : ℕ) :
    (canonicalSlots N cap w Z d).Nodup := (canonicalSlots_descending N cap w Z d).nodup

theorem canonicalSlots_prime_data {N cap d : ℕ} {w Z : ℝ} {p : ℕ}
    (hp : p ∈ canonicalSlots N cap w Z d) :
    Nat.Prime p ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < Z :=
  (mem_roughPrimeUniverse.mp (List.mem_filter.mp hp).1).2

theorem canonicalSlots_toFinset {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    (canonicalSlots N cap w Z d).toFinset = d.primeFactors := by
  ext p
  simp only [canonicalSlots, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro hp
    exact ⟨fixedRoughSupport_primeFactors_mem (ordinaryRetainOdd L) N cap w Z hd hp, hp⟩

theorem canonicalSlots_prod {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    (canonicalSlots N cap w Z d).prod = d := by
  have hp : (∏ p ∈ (canonicalSlots N cap w Z d).toFinset, p) =
      (canonicalSlots N cap w Z d).prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) (canonicalSlots_nodup N cap w Z d)
  rw [← hp, canonicalSlots_toFinset hd]
  exact Nat.prod_primeFactors_of_squarefree (fixedRoughSupport_squarefree _ _ _ _ _ hd)

theorem canonicalSlots_length {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    (canonicalSlots N cap w Z d).length = d.primeFactors.card := by
  rw [← List.toFinset_card_of_nodup (canonicalSlots_nodup N cap w Z d), canonicalSlots_toFinset hd]

theorem roughWeight_eq_moebius {N cap d : ℕ} {w Z L : ℝ} (hL : 1 < L)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    roughWeight N cap w Z L d = (ArithmeticFunction.moebius d : ℝ) := by
  rw [← ordinary_rough_coefficient N cap w Z L hL d]
  change ((if d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z
    then ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) = _
  rw [if_pos hd]

/-- These are the actual original upper gates on the SAME residual d,
including the strict total cutoff; no replacement D-well test is used. -/
theorem canonicalSlots_original_upper_gates {N cap d : ℕ} {w Z L : ℝ} (hL : 1 < L)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    ordinaryRosserPrefixAdmissible false L (canonicalSlots N cap w Z d).reverse := by
  have hmu : ArithmeticFunction.moebius d ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr (fixedRoughSupport_squarefree _ _ _ _ _ hd)
  have hnz : roughWeight N cap w Z L d ≠ 0 := by
    rw [roughWeight_eq_moebius hL hd]
    exact_mod_cast hmu
  have ha := upperWeight_active hnz
  change ((canonicalSlots N cap w Z d).reverse.prod : ℝ) < L ∧
    UpperAdmissibleSet L (canonicalSlots N cap w Z d).reverse.toFinset
  rw [List.prod_reverse, List.toFinset_reverse, canonicalSlots_prod hd, canonicalSlots_toFinset hd]
  exact ⟨ha.2.1, ha.2.2⟩

theorem roughWeight_eq_slot_sign {N cap d : ℕ} {w Z L : ℝ} (hL : 1 < L)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    roughWeight N cap w Z L d = (-1 : ℝ) ^ (canonicalSlots N cap w Z d).length := by
  rw [roughWeight_eq_moebius hL hd]
  conv_lhs => rw [← canonicalSlots_prod hd]
  exact_mod_cast actualPrimeVector_moebius_eq_sign (canonicalSlots N cap w Z d)
    (fun p hp => (canonicalSlots_prime_data hp).1) (canonicalSlots_nodup N cap w Z d)

def rowSlots (n N : ℕ) (eta : ℚ) (w : ℝ) (t : Four) (d : ℕ) : List ℕ :=
  canonicalSlots N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    w (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) d

/-- Actual original residual-slot realization with a rank selected only
from nu0,betaEta. All prime ceilings, target exclusions and upper gates
are retained; the COMMON beta integer e never enters this slot tuple. -/
theorem actual_row_prime_slots {n N d : ℕ} {eta : ℚ} {E : ℕ × ℕ → Prop}
    (hN : 1 < N) (heta : 0 < eta) (nu0 betaEta : ℝ)
    (hrho : 0 < roughExponent nu0 betaEta) {t : Four} (ht : t ∈ tuples n N E)
    (hw : (N : ℝ) ^ roughExponent nu0 betaEta ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hd : d ∈ fixedRoughSupport
      (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      ((N : ℝ) ^ roughExponent nu0 betaEta) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) :
    let ps := rowSlots n N eta ((N : ℝ) ^ roughExponent nu0 betaEta) t d
    ps.Pairwise (· > ·) ∧ ps.Nodup ∧ ps.prod = d ∧ ps.length ≤ rankBound nu0 betaEta ∧
      (∀ p ∈ ps, Nat.Prime p ∧ ¬p ∣ N ∧ (N : ℝ) ^ roughExponent nu0 betaEta ≤ (p : ℝ) ∧
        (p : ℝ) < U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) ∧
      ordinaryRosserPrefixAdmissible false (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) ps.reverse ∧
      roughWeight N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        ((N : ℝ) ^ roughExponent nu0 betaEta) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
        (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) d = (-1 : ℝ) ^ ps.length := by
  have hL := (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta
    (Finset.mem_filter.mp ht).1).2.1
  refine ⟨canonicalSlots_descending _ _ _ _ _, canonicalSlots_nodup _ _ _ _ _,
    canonicalSlots_prod hd, ?_, ?_, canonicalSlots_original_upper_gates hL hd,
    roughWeight_eq_slot_sign hL hd⟩
  · rw [rowSlots, canonicalSlots_length hd]
    exact actual_rough_rank_bound hN heta nu0 betaEta hrho ht hw hd
  · intro p hp
    exact canonicalSlots_prime_data hp

end
end ImbalancedChen.P5Z.OriginalPresievedRoughPrimeSlots
