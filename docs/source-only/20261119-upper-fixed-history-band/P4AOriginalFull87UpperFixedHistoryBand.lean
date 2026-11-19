import ImbalancedChen.P4AOriginalFull87ActualUpperCeilingZ
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A fixed-exponent ORIGINAL upper-half support band, on exactly the ACTUAL
fifthExclusive + ordered sixth occurrence source. Unlike the already
known fifth-power N^(299/600) support, the strict prime window 2*P<N,
the EXACT complete Rosser quotient, its active level L=N^epsilon,
and the actual sixth p<z=N^(19/96) force a sharper fifth-history bound:

           N^(9601/12000) < 2 * fifth.selectedAfter.prod.

The exact rational identity is 19/96 + 1/500 = 2399/12000.
The hypothesis epsilon<=1/500 and N>1 is essential. This theorem
instantiates literal frozen upper parameters at the actual producer
interface; it does NOT establish that every separate upstream generic
(w,z,L) caller has these literal arguments.

No new admission mask, different parent, new external analytic input,
smooth PP use, signed saving, or reserve payment is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperFixedHistoryBand
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm upperPrimeFibreEventValue)
open P4AOriginalFull87FifthHistoryCeilingPrune
  (original_upper_fibre_nonzero_power_and_level)
open P4AOriginalFull87UpperPrimeLiveZWindow
  (actual_fifth_sixth_strictly_below_z)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)

/-- Pay the frozen epsilon upper bound and both exponent identities
without changing the original strict endpoint. A source term's
N<2*L*z*h inequality implies a fixed N^(9601/12000) lower band. -/
private theorem fixed_upper_exponent_to_history_band
    (N h : ℕ) (epsilon : ℝ)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hbound : (N : ℝ) <
      2 * (((N : ℝ) ^ epsilon) *
        ((N : ℝ) ^ ((19 : ℝ) / 96)) * (h : ℝ))) :
    (N : ℝ) ^ ((9601 : ℝ) / 12000) < 2 * (h : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNge : (1 : ℝ) ≤ (N : ℝ) := le_of_lt hN
  have hepsPow :
      (N : ℝ) ^ epsilon ≤ (N : ℝ) ^ ((1 : ℝ) / 500) :=
    Real.rpow_le_rpow_of_exponent_le hNge heps
  have hupperPow :
      (N : ℝ) ^ epsilon * (N : ℝ) ^ ((19 : ℝ) / 96) ≤
        (N : ℝ) ^ ((2399 : ℝ) / 12000) := by
    calc
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 500) *
          (N : ℝ) ^ ((19 : ℝ) / 96) :=
        mul_le_mul_of_nonneg_right hepsPow
          (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ ((2399 : ℝ) / 12000) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        norm_num
  have hscaled :=
    mul_le_mul_of_nonneg_right hupperPow (Nat.cast_nonneg h)
  have hnBound :
      (N : ℝ) <
        2 * ((N : ℝ) ^ ((2399 : ℝ) / 12000) * (h : ℝ)) := by
    nlinarith only [hbound, hscaled]
  have hpow :
      (N : ℝ) ^ ((2399 : ℝ) / 12000) *
        (N : ℝ) ^ ((9601 : ℝ) / 12000) = (N : ℝ) := by
    rw [← Real.rpow_add hNpos]
    convert Real.rpow_one (N : ℝ) using 1 <;> norm_num
  have hfactorPos :
      0 < (N : ℝ) ^ ((2399 : ℝ) / 12000) :=
    Real.rpow_pos_of_pos hNpos _
  apply (mul_lt_mul_left hfactorPos).mp
  calc
    (N : ℝ) ^ ((2399 : ℝ) / 12000) *
        (N : ℝ) ^ ((9601 : ℝ) / 12000) = (N : ℝ) := hpow
    _ < 2 * ((N : ℝ) ^ ((2399 : ℝ) / 12000) * (h : ℝ)) :=
      hnBound
    _ = (N : ℝ) ^ ((2399 : ℝ) / 12000) * (2 * (h : ℝ)) := by ring

/-- The ORIGINAL full upper fibre must have a genuinely large fifth
selected product. The result is stronger than the older N^(299/600)
fifth-power band, but applies only to this strict upper prime fibre;
it is not a bound for all sixth receiver contributions. -/
theorem original_upper_nonzero_requires_frozen_fifth_band
    (N cap : ℕ) (w epsilon : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hpz : (p : ℝ) < (N : ℝ) ^ ((19 : ℝ) / 96))
    (hnon : upperPrimeFibreTerm N cap w ((N : ℝ) ^ epsilon)
      X P pre p ≠ 0) :
    (N : ℝ) ^ ((9601 : ℝ) / 12000) <
      2 * (pre.prod : ℝ) := by
  let a : ℕ := (N - P) / (p :: pre).prod
  have hg :
      2 * P < N ∧ X < N - P ∧
      a ∈ P4AOriginalFull87PlusBetaPowerFilter.largeFifthRosserIndices
        N cap w X pre ∧
      a * (p :: pre).prod = N - P := by
    unfold upperPrimeFibreTerm at hnon
    split_ifs at hnon with hgate
    · simpa only [a] using hgate
    · contradiction
  have haL : (a : ℝ) < (N : ℝ) ^ epsilon :=
    (original_upper_fibre_nonzero_power_and_level
      N cap w ((N : ℝ) ^ epsilon) X P pre p hnon).2
  have hprod : a * (p * pre.prod) = N - P := by
    simpa only [List.prod_cons] using hg.2.2.2
  have hnat : N < 2 * (a * (p * pre.prod)) := by
    omega
  have hreal :
      (N : ℝ) < 2 * ((a : ℝ) * (p : ℝ) * (pre.prod : ℝ)) := by
    have hcast :
        (N : ℝ) < ((2 * (a * (p * pre.prod)) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast
    nlinarith only [hcast]
  have hmult :
      (a : ℝ) * (p : ℝ) ≤
        (N : ℝ) ^ epsilon * (N : ℝ) ^ ((19 : ℝ) / 96) := by
    calc
      (a : ℝ) * (p : ℝ) ≤
          (N : ℝ) ^ epsilon * (p : ℝ) :=
        mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg _)
      _ ≤ (N : ℝ) ^ epsilon * (N : ℝ) ^ ((19 : ℝ) / 96) :=
        mul_le_mul_of_nonneg_left hpz.le
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hscaled :
      2 * ((a : ℝ) * (p : ℝ) * (pre.prod : ℝ)) ≤
        2 * ((N : ℝ) ^ epsilon *
          (N : ℝ) ^ ((19 : ℝ) / 96) * (pre.prod : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hmult
      (Nat.cast_nonneg pre.prod)
    nlinarith only [hh]
  exact fixed_upper_exponent_to_history_band N pre.prod epsilon
    hN heps (lt_of_lt_of_le hreal hscaled)

/-- At the literal frozen upper endpoint z=N^(19/96), an ACTUAL
fifth-exclusive event with small selected product has zero ORIGINAL
upper-prime coefficient at every P. The real sharedRankFour parent,
actual receiver generation, ordered sixth suffix and original sign
are used. BOTH/sixthFromBoth remain wholly outside this deletion. -/
theorem actual_fifth_upper_prime_zero_below_frozen_band
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X P : ℕ)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96)))
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w
        ((N : ℝ) ^ epsilon) X (receiverTest N) state)
    (hsmall : 2 * (fifth.selectedAfter.prod : ℝ) ≤
      (N : ℝ) ^ ((9601 : ℝ) / 12000)) :
    upperPrimeFibreEventValue N cap w ((N : ℝ) ^ epsilon)
      X P (.fifthExclusive fifth) = 0 := by
  have hzero : ∀ p ∈ fifth.remainingAfter,
      upperPrimeFibreTerm N cap w ((N : ℝ) ^ epsilon)
        X P fifth.selectedAfter p = 0 := by
    intro p hp
    by_contra hnon
    have hpz := actual_fifth_sixth_strictly_below_z
      delta n e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96)) ((N : ℝ) ^ epsilon) X
      state hstate fifth hfifth p hp
    have hlarge := original_upper_nonzero_requires_frozen_fifth_band
      N cap w epsilon X P fifth.selectedAfter p hN heps hpz hnon
    exact (not_lt_of_ge hsmall) hlarge
  have hsum :
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeFibreTerm N cap w ((N : ℝ) ^ epsilon)
            X P fifth.selectedAfter p)).sum = 0 := by
    have hmap :
        fifth.remainingAfter.map (fun p =>
          signedTreeCoefficient true fifth.massAfter *
            upperPrimeFibreTerm N cap w ((N : ℝ) ^ epsilon)
              X P fifth.selectedAfter p) =
        fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro p hp
      simp [hzero p hp]
    rw [hmap]
    simp
  cases hk : fifth.kind with
  | rawOnly => simpa [upperPrimeFibreEventValue, hk] using hsum
  | both => simp [upperPrimeFibreEventValue, hk]
  | licensedOnly => simp [upperPrimeFibreEventValue, hk, hsum]

/-- A nonzero ORIGINAL upper fifthExclusive value gives a quantitative
necessary lower band for its same actual fifth product. No false
unconditional coverage or signed saving is inferred. -/
theorem actual_fifth_upper_nonzero_requires_frozen_band
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X P : ℕ)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w
      ((N : ℝ) ^ ((19 : ℝ) / 96)))
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w
        ((N : ℝ) ^ epsilon) X (receiverTest N) state)
    (hnon : upperPrimeFibreEventValue N cap w ((N : ℝ) ^ epsilon)
      X P (.fifthExclusive fifth) ≠ 0) :
    (N : ℝ) ^ ((9601 : ℝ) / 12000) <
      2 * (fifth.selectedAfter.prod : ℝ) := by
  by_contra hnot
  exact hnon (actual_fifth_upper_prime_zero_below_frozen_band
    delta n e q om N cap w epsilon X P hN heps
    state hstate fifth hfifth (le_of_not_gt hnot))

end
end ImbalancedChen.P4AOriginalFull87UpperFixedHistoryBand
