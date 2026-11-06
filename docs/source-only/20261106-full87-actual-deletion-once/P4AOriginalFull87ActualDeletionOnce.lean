import ImbalancedChen.P4AOriginalFull87FailedListPotential
import ImbalancedChen.P4AOriginalFull87Post8SuffixExit
import ImbalancedChen.P4AOriginalFull87TargetPrimeDeletion
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import ImbalancedChen.P4AOriginalFull87ActualEighthCarrier
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO FORMAL CREDIT.

P1.4: pay the target-prime deletion factor ONCE for the actual failed
select occurrence, using its own eighth-state parent or finite cap.
The upstream pair-list potential already certifies the real physical
chosen list and the rank shift (rank = 11 + 2*m, exponent = m+2).

This module does NOT identify the h=1 event correction with the g_N
coefficient, assert a signed saving, or pay a second rounding reserve.
The historical eighth source and its already-scheduled RealizedHistory
are retained; no historical odd-square tests are re-admitted at the
new frozen level. The new proof concerns ranks at least eleven ONLY.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualDeletionOnce
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87EighthKernelControl (cutoff cutoff_pos)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87OwnedEighthSource
  (states_eq_owner_filter retainedOwner retainedOwner_some_iff)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87FailedListPotential (owned87_failed_actual_pair_list_gap)
open P4AOriginalFull87TargetPrimeDeletion
  (targetDeletionFactor target_deletion_power_gap_sandwich)

/-- The literal finite-list logarithmic gap implies an INTEGER power gap.
There is no artificially indexed t, no hypothesis about an unobserved
odd-square test, and no new analytic prime-distribution input. -/
theorem list_log_gap_integer_power
    (N p K k : ℕ) (hN : 1 < (N : ℝ)) (hp : 1 < (p : ℝ))
    (s8 beta : ℝ)
    (hfloor : cutoff < beta - s8)
    (hgap : beta - s8 ≤ (3 : ℝ) ^ k *
      (Real.log (p : ℝ) / Real.log (N : ℝ)))
    (hKpos : 0 < K)
    (hK : (3 : ℝ) ^ k < cutoff * (K : ℝ)) :
    N < p ^ K := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hBpos : (0 : ℝ) < (3 : ℝ) ^ k :=
    pow_pos (by norm_num) _
  have hcut : cutoff < (3 : ℝ) ^ k *
      (Real.log (p : ℝ) / Real.log (N : ℝ)) :=
    hfloor.trans_le hgap
  have hmul := mul_lt_mul_of_pos_right hcut hKreal
  have hstrong : (3 : ℝ) ^ k <
      (3 : ℝ) ^ k *
        ((Real.log (p : ℝ) / Real.log (N : ℝ)) * (K : ℝ)) := by
    calc
      (3 : ℝ) ^ k < cutoff * (K : ℝ) := hK
      _ < ((3 : ℝ) ^ k *
          (Real.log (p : ℝ) / Real.log (N : ℝ))) * (K : ℝ) := hmul
      _ = _ := by ring
  have hscale : (1 : ℝ) <
      (Real.log (p : ℝ) / Real.log (N : ℝ)) * (K : ℝ) := by
    by_contra hnot
    have hle : (Real.log (p : ℝ) / Real.log (N : ℝ)) * (K : ℝ) ≤ 1 :=
      le_of_not_gt hnot
    have hscaled := mul_le_mul_of_nonneg_left hle hBpos.le
    have hbound : (3 : ℝ) ^ k *
        ((Real.log (p : ℝ) / Real.log (N : ℝ)) * (K : ℝ)) ≤
          (3 : ℝ) ^ k := by
      simpa only [mul_one] using hscaled
    exact (not_lt_of_ge hbound) hstrong
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN
  have hcancel :
      ((Real.log (p : ℝ) / Real.log (N : ℝ)) * (K : ℝ)) *
        Real.log (N : ℝ) =
      (K : ℝ) * Real.log (p : ℝ) := by
    field_simp [ne_of_gt hlogN]
    <;> ring
  have hlog : Real.log (N : ℝ) < (K : ℝ) * Real.log (p : ℝ) := by
    have hscaled := mul_lt_mul_of_pos_right hscale hlogN
    rw [one_mul, hcancel] at hscaled
    exact hscaled
  have hlogPow : Real.log (N : ℝ) <
      Real.log ((p : ℝ) ^ K) := by
    simpa only [Real.log_pow] using hlog
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    (by norm_num : (0 : ℝ) < 1).trans hN
  have hppos : (0 : ℝ) < (p : ℝ) :=
    (by norm_num : (0 : ℝ) < 1).trans hp
  have hexp : Real.exp (Real.log (N : ℝ)) <
      Real.exp (Real.log ((p : ℝ) ^ K)) :=
    Real.exp_lt_exp.mpr hlogPow
  have hreal : (N : ℝ) < (p : ℝ) ^ K := by
    simpa only [Real.exp_log hNpos, Real.exp_log (pow_pos hppos K)] using hexp
  exact_mod_cast hreal

/-- On one ACTUAL original87 owner/trim state and one ACTUAL rejected
occurrence of odd rank >= 11, use the same event's finite-log potential,
its same frozen parent/finiteCap, and the existing positive eighth floor
to pay the target-dividing primes by their exact factor set.

RealizedHistory is the existing scheduled source-membership conclusion,
not a surrogate exit estimate. The even-target assumption excludes 2
from the actual target-deleted remaining carrier. The integer budget
k=261*3^(m+2) is charged to this target deletion multiplier ONCE.
No g_N coefficient identity or signed density is claimed here. -/
theorem owned87_later_failed_target_deletion_once
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hEven : 2 ∣ N)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => 1) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ firstExitRejectedAttempts
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining)
    (hlater : 8 < a.older.length) (hi : ℕ) :
    ∃ m : ℕ, a.older.length = 10 + 2 * m ∧
      0 ≤ targetDeletionFactor N a.rejected hi ∧
      targetDeletionFactor N a.rejected hi ≤ 1 ∧
      1 - (((261 * 3 ^ (m + 2) : ℕ) : ℝ)) /
        ((a.rejected : ℝ) - 1) ≤
          targetDeletionFactor N a.rejected hi := by
  obtain ⟨before, chosen, m, hrem, _hsub, holder, hchosen, hgap⟩ :=
    owned87_failed_actual_pair_list_gap (width r) n e q om N cap
      hN w z c s hs useParent a ha hlater
  obtain ⟨hlen8, _, _, _, hexactRemaining⟩ :=
    owned87_eighth_state_exact_carrier (width r) n e q om
      N cap w z c s hs
  obtain ⟨last, tail, _hprefix, _hlastMember, hremaining⟩ :=
    hexactRemaining
  have hpMem : a.rejected ∈ s.remaining := by
    rw [hrem]
    simp
  have hpRough :
      a.rejected ∈ roughPrimeUniverse N cap w (last : ℝ) := by
    rw [hremaining] at hpMem
    exact hpMem
  have hpPrime : Nat.Prime a.rejected :=
    mem_roughPrimeUniverse_prime hpRough
  have hpNotDiv : ¬a.rejected ∣ N :=
    mem_roughPrimeUniverse_not_dvd hpRough
  have hpThree : 3 ≤ a.rejected := by
    have hpTwo := hpPrime.two_le
    have hpNeTwo : a.rejected ≠ 2 := by
      intro he
      apply hpNotDiv
      simpa [he] using hEven
    omega
  have hpReal : (1 : ℝ) < (a.rejected : ℝ) := by
    exact_mod_cast (show 1 < a.rejected by omega)
  have hOwner : retainedOwner (width r) (N : ℝ)
      s.selectedPrefix = some c := by
    have hsrc := hs
    rw [states_eq_owner_filter] at hsrc
    exact of_decide_eq_true (List.mem_filter.mp hsrc).2
  have htrim : primeHistoryLogCoordinates (N : ℝ) 8
      s.selectedPrefix ∈ trim c (width r) := by
    have ht := (retainedOwner_some_iff (width r)
      (N : ℝ) s.selectedPrefix c).mp hOwner
    simpa [P4AOriginalFull87SourceDispatch.point8] using ht.2
  have hfloors :=
    P4AOriginalFull87Post8SuffixExit.owned87_old_and_new_residual_floor
      r n hn e q om (N : ℝ) s.selectedPrefix hlen8 c htrim hr
  dsimp only at hfloors
  let s8 : ℝ := ∑ i : Fin 8,
    primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix i
  let beta : ℝ :=
    if useParent then
      actualParent n e q om (N : ℝ) s.selectedPrefix
    else
      (finiteCap n c
        (P4AOriginalFull87SourceDispatch.point8
          (N : ℝ) s.selectedPrefix) : ℝ)
  have hfloor : cutoff < beta - s8 := by
    cases useParent with
    | false =>
        simpa [beta, s8, P4AOriginalFull87EighthKernelControl.total,
          P4AOriginalFull87SourceDispatch.point8] using hfloors.2
    | true =>
        simpa [beta, s8, P4AOriginalFull87EighthKernelControl.total,
          P4AOriginalFull87SourceDispatch.point8] using hfloors.1
  have hgapReal : beta - s8 ≤ (3 : ℝ) ^ (m + 2) *
      (Real.log (a.rejected : ℝ) / Real.log (N : ℝ)) := by
    simpa [beta, s8] using hgap
  let k : ℕ := 261 * 3 ^ (m + 2)
  have hkpos : 0 < k := by
    dsimp [k]
    positivity
  have hfactor : (3 : ℝ) ^ (m + 2) < cutoff * (k : ℝ) := by
    dsimp [k]
    simpa only [show (m + 1) + 1 = m + 2 by omega] using
      (P4AOriginalFull87Post8SuffixExit.post8_uniform_integer_factor (m + 1))
  have hcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ k
  have hK : (3 : ℝ) ^ (m + 2) <
      cutoff * ((k + 1 : ℕ) : ℝ) :=
    hfactor.trans_le (mul_le_mul_of_nonneg_left hcast cutoff_pos.le)
  have hpower : N < a.rejected ^ (k + 1) :=
    list_log_gap_integer_power N a.rejected (k + 1) (m + 2)
      hN hpReal s8 beta hfloor hgapReal (by omega) hK
  have hNnat : 0 < N := by
    have hR : (0 : ℝ) < (N : ℝ) :=
      (by norm_num : (0 : ℝ) < 1).trans hN
    exact_mod_cast hR
  obtain ⟨hfactor0, hfactor1, hfactorLower⟩ :=
    target_deletion_power_gap_sandwich N a.rejected hi k
      hNnat hpThree hpower
  have hrank : a.older.length = 10 + 2 * m := by
    rw [holder, List.length_append, List.length_reverse, hchosen, hlen8]
    omega
  refine ⟨m, hrank, hfactor0, hfactor1, ?_⟩
  simpa [k] using hfactorLower

end
end ImbalancedChen.P4AOriginalFull87ActualDeletionOnce
