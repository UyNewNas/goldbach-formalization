import ImbalancedChen.P4AOriginalFull87TargetPrimeDeletion
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import ImbalancedChen.PrimeHistoryLogCoordinates
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED / ZERO KERNEL CREDIT.

The exact original87 SOURCE has coordinate t₈ > 53/13824.
For an ACTUAL owned rank-eight predecessor frontier history, the eighth
selected prime is N^t₈ and so (p_last)^261 > N, since 53*261 > 13824.
The number 260 in the deletion factor is obtained, not assumed.

This is a rank-EIGHT prefix result only. After further ordinary parity
selections, the true last exit prime may be smaller, and this theorem
does NOT control those deeper exits. No unsigned/signed mean, limiting
exit series, density reserve or external analytic input is postulated.
-/

namespace ImbalancedChen.P4AOriginalFull87EighthCutoff
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell Source)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87EighthKernelControl (cutoff source_coordinate_lower)
open P4AOriginalFull87OwnedEighthSource
  (frontier retainedOwner retainedOwner_some_iff states_eq_owner_filter)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87TargetPrimeDeletion

/-- At an existing owned eighth source, both the physical frontier
membership and the EXACT source cell follow from the same policy list.
In particular, membership alone is not replaced by an independent
source hypothesis later in this module. -/
theorem owned_rank8_frontier_source
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    s ∈ frontier n e q om N cap w z ∧
    Source c (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) := by
  rw [states_eq_owner_filter] at hs
  obtain ⟨hf, ho⟩ := List.mem_filter.mp hs
  have howner : retainedOwner (width r) (N : ℝ) s.selectedPrefix = some c :=
    of_decide_eq_true ho
  have ht := (retainedOwner_some_iff
    (width r) (N : ℝ) s.selectedPrefix c).mp howner
  refine ⟨hf, ?_⟩
  have htrim := ht.2
  change primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix ∈
    trim c (width r) at htrim
  exact trim_subset_source c (width_pos r) htrim

/-- Pure real-to-integer bridge. This takes only the actual source
coordinate and its proven prime-history reconstruction; there is NO
caller-supplied N^δ lower bound, rounding rule or new distribution
hypothesis. The exact integer 261 is certified by norm_num. -/
theorem source_rank8_last_prime_power_gap
    (N : ℕ) (hN : 1 < (N : ℝ)) (history : List ℕ) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates (N : ℝ) 8 history))
    (hreconstruct :
      (N : ℝ) ^ primeHistoryLogCoordinates (N : ℝ) 8 history (7 : Fin 8) =
        (primeHistoryTuple 8 history (7 : Fin 8) : ℝ)) :
    N < (primeHistoryTuple 8 history (7 : Fin 8)) ^ 261 := by
  have hcoord : cutoff <
      primeHistoryLogCoordinates (N : ℝ) 8 history (7 : Fin 8) :=
    source_coordinate_lower hs (7 : Fin 8)
  have hp : (N : ℝ) ^ cutoff <
      (primeHistoryTuple 8 history (7 : Fin 8) : ℝ) := by
    calc
      (N : ℝ) ^ cutoff <
          (N : ℝ) ^ primeHistoryLogCoordinates (N : ℝ) 8 history (7 : Fin 8) :=
        Real.rpow_lt_rpow_of_exponent_lt hN hcoord
      _ = _ := hreconstruct
  have h261 : (1 : ℝ) < cutoff * (261 : ℝ) := by
    norm_num [cutoff]
  have hbase : (N : ℝ) < ((N : ℝ) ^ cutoff) ^ (261 : ℕ) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (N : ℝ) ^ (cutoff * (261 : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hN h261
      _ = ((N : ℝ) ^ cutoff) ^ (261 : ℕ) :=
        Real.rpow_mul_natCast (le_of_lt (zero_lt_one.trans hN)) cutoff 261
  have hpow :
      ((N : ℝ) ^ cutoff) ^ (261 : ℕ) <
        (primeHistoryTuple 8 history (7 : Fin 8) : ℝ) ^ (261 : ℕ) :=
    pow_lt_pow_left₀ hp (Real.rpow_nonneg (by positivity) _) (by decide)
  have hreal : (N : ℝ) <
      (primeHistoryTuple 8 history (7 : Fin 8) : ℝ) ^ (261 : ℕ) :=
    hbase.trans hpow
  exact_mod_cast hreal

/-- The strict bound is instantiated on the REAL rank-eight predecessor
state and original87 owner/trim, not a synthetic square-test state. -/
theorem owned_rank8_last_prime_power_gap
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    N < (primeHistoryTuple 8 s.selectedPrefix (7 : Fin 8)) ^ 261 := by
  obtain ⟨hf, hsource⟩ :=
    owned_rank8_frontier_source r n e q om N cap w z c s hs
  have hgeom := primeHistoryLogCoordinates_frontier 8
    (sixthPolicy n e q om (N : ℝ)) (fun _ : ℕ => (1 : ℝ))
    N cap hN w z s hf
  exact source_rank8_last_prime_power_gap N hN s.selectedPrefix c
    hsource (hgeom.2 (7 : Fin 8)).2

/-- For every even target and EVERY original87 owned rank-eight state:
the omitted target-prime multiplier from the actual eighth selected prime
has an explicit, target-independent CARDINALITY budget 260.
This does not transfer to a smaller post-eighth last exit prime. -/
theorem owned_rank8_target_deletion_sandwich
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (hEven : 2 ∣ N) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hi : ℕ) :
    let pLast := primeHistoryTuple 8 s.selectedPrefix (7 : Fin 8)
    0 ≤ targetDeletionFactor N pLast hi ∧
    targetDeletionFactor N pLast hi ≤ 1 ∧
    1 - (260 : ℝ) / ((pLast : ℝ) - 1) ≤
      targetDeletionFactor N pLast hi := by
  dsimp only
  obtain ⟨hf, _⟩ :=
    owned_rank8_frontier_source r n e q om N cap w z c s hs
  have hm : primeHistoryTuple 8 s.selectedPrefix (7 : Fin 8) ∈
      roughPrimeUniverse N cap w z :=
    primeHistoryTuple_frontier_mem 8
      (sixthPolicy n e q om (N : ℝ)) (fun _ : ℕ => (1 : ℝ))
      N cap w z s hf (7 : Fin 8)
  have hpPrime := mem_roughPrimeUniverse_prime hm
  have hpNot := mem_roughPrimeUniverse_not_dvd hm
  have hpNeTwo :
      primeHistoryTuple 8 s.selectedPrefix (7 : Fin 8) ≠ 2 := by
    intro he
    apply hpNot
    simpa [he] using hEven
  have hpThree :
      3 ≤ primeHistoryTuple 8 s.selectedPrefix (7 : Fin 8) := by
    have htwo := hpPrime.two_le
    omega
  have hnat : 0 < N := by
    have hR : (0 : ℝ) < N := lt_trans (by norm_num) hN
    exact_mod_cast hR
  exact target_deletion_power_gap_sandwich
    N (primeHistoryTuple 8 s.selectedPrefix (7 : Fin 8))
    hi 260 hnat hpThree
    (owned_rank8_last_prime_power_gap r n e q om N cap hN w z c s hs)

end
end ImbalancedChen.P4AOriginalFull87EighthCutoff
