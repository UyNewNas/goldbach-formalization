import ImbalancedChen.P2MarkedSourceRankCore
import ImbalancedChen.P2FiniteMarkedGamma5FrozenConstants
import ImbalancedChen.P2FiniteMarkedGamma5LogExtension
import ImbalancedChen.Part5OriginalH430HistoryScaleCore
import ImbalancedChen.Part5OriginalH430HistoryRoughnessCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The complete original U4 marked Gamma5 list has a fixed rank bound.
Every hypothesis below is an existing LevelIndex / badLabels /
roughNumbers source condition. Neither the common floor nor the rank
bound is admitted as a new hypothesis. The historical prime coherence,
roughness and scale suppliers are reused without re-proving them.

The arithmetic-history import closure is not yet qualified in the
current checkout. This draft is not an accepted actual source supplier.
It supplies neither a complete Family, a collar payment, nor a PP/VM
estimate. The equality-inclusive bad square is never made an ordinary
feedback child.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5ActualRank

noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels pair_data)
open P2EnhancedBadGamma5ConstantCutoff (original_cutoff)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430SeedHistoryMass Part5OriginalH430HistoryQuotientCounts
open P2FiniteMarkedGamma5LogExtension P2MarkedSourceRankCore
open scoped Classical BigOperators

/-- All original slots, with their original order and multiplicities. -/
def sourceSlots {N n p dep : ℕ} {t : ℝ}
    (l : LevelIndex N n .U4 t p dep) (qs : List ℕ) (m : ℕ) : List ℕ :=
  ((levelOccurrence l).current.old ++ qs) ++ m.primeFactorsList

/-- Old slots inherit primality and the common cutoff from their actual
selected history. A prime-factor set is used only to establish a lower
bound; the slot list itself is not deduplicated. -/
theorem enhanced_position_old_prime_floor {N n p dep : ℕ} {t : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ originalBand N .U4)
    (l : LevelIndex N n .U4 t p dep) :
    ∀ q ∈ (levelOccurrence l).current.old,
      q.Prime ∧ (N : ℝ) ^ frozenLeafCutoffFloor ≤ (q : ℝ) := by
  have ho := (levelOccurrence_source l).1
  have hc := rootHistory_coherent (by omega : 1 < N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  have hd : 0 < wordProduct l := (scale_and_alpha hN ht ht' hn hp l).1
  have hf := (history_integer_roughness hN ht ht' hn hp ho).2.2.1
  intro q hq
  have hprime : q.Prime := (hc.letters q hq).1
  refine ⟨hprime, hf q (Nat.mem_primeFactors.mpr ⟨hprime, ?_, hd.ne'⟩)⟩
  change q ∣ (levelOccurrence l).current.old.prod
  exact List.dvd_prod hq

/-- The actual old/pair/rough source supplies the common lower floor,
the exact complete product, the product cap, and the full slot count.
The tail is primeFactorsList, so m=1 and repeated prime factors remain
literal cases of this one theorem. -/
theorem enhanced_position_source_data {N n p dep m : ℕ} {t : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ originalBand N .U4)
    (l : LevelIndex N n .U4 t p dep) {qs : List ℕ}
    (hq : qs ∈ badLabels N (rootQ N n .U4 t p) (wordProduct l))
    (hm : m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ))
      (cutoff (rootQ N n .U4 t p) (wordProduct l) (227 / 50))) :
    (∀ q ∈ sourceSlots l qs m,
      q.Prime ∧ (N : ℝ) ^ frozenLeafCutoffFloor ≤ (q : ℝ)) ∧
      (sourceSlots l qs m).prod = wordProduct l * qs.prod * m ∧
      (sourceSlots l qs m).prod ≤ N ∧
      (sourceSlots l qs m).length =
        (levelOccurrence l).current.old.length + 2 + m.primeFactorsList.length := by
  have hpair := (mem_filter.mp hq).1
  have hm0 : 0 < m := (mem_roughNumbers.mp hm).1
  have hd : 0 < wordProduct l := (scale_and_alpha hN ht ht' hn hp l).1
  have hcut := (history_integer_roughness hN ht ht' hn hp
    (levelOccurrence_source l).1).2.2.2
  have hold := enhanced_position_old_prime_floor hN ht ht' hn hp l
  have hproduct : (sourceSlots l qs m).prod = wordProduct l * qs.prod * m := by
    simp only [sourceSlots, List.prod_append, Nat.prod_primeFactorsList hm0.ne',
      wordProduct, parentProduct]
  have hcap := actual_raw hd hq hm Gate.product (mem_program.mpr trivial)
  change fullProduct (wordProduct l) (sourcePair qs) (canonicalTail m) ≤ N at hcap
  rw [source_fullProduct hpair hm0] at hcap
  refine ⟨?_, hproduct, by simpa only [hproduct] using hcap, ?_⟩
  · intro q hqslot
    rcases List.mem_append.mp hqslot with hpre | htail
    · rcases List.mem_append.mp hpre with hqold | hqpair
      · exact hold q hqold
      · have hw := mem_primeWindow.mp ((pair_data hpair).2.2 q hqpair)
        refine ⟨hw.1, hcut.trans ?_⟩
        simpa only [original_cutoff] using hw.2.2.1
    · have hprime : q.Prime := Nat.prime_of_mem_primeFactorsList htail
      exact ⟨hprime, hcut.trans ((mem_roughNumbers.mp hm).2.2 q hprime
        (Nat.dvd_of_mem_primeFactorsList htail))⟩
  · simp only [sourceSlots, List.length_append, (pair_data hpair).1]

/-- The true complete marked atom has the fixed history-determined
rank. No rank or cutoff assertion is an additional caller hypothesis. -/
theorem enhanced_position_source_rank {N n p dep m : ℕ} {t : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ originalBand N .U4)
    (l : LevelIndex N n .U4 t p dep) {qs : List ℕ}
    (hq : qs ∈ badLabels N (rootQ N n .U4 t p) (wordProduct l))
    (hm : m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ))
      (cutoff (rootQ N n .U4 t p) (wordProduct l) (227 / 50))) :
    (levelOccurrence l).current.old.length + 2 + m.primeFactorsList.length ≤
      frozenSourceRankBound := by
  obtain ⟨hfloor, _hproduct, hcap, hlen⟩ :=
    enhanced_position_source_data hN ht ht' hn hp l hq hm
  have hx : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hrank := list_length_le_floor_inv hx frozenLeafCutoffFloor_pos
    (sourceSlots l qs m) (fun q hq => (hfloor q hq).2)
    (by exact_mod_cast hcap)
  simpa only [hlen, frozenSourceRankBound] using hrank

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualRank
