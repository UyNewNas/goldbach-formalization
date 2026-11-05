import ImbalancedChen.P4AOriginalFull87FixedRankExit
import ImbalancedChen.P4AOriginalFull87EighthKernelIntegration
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO KERNEL CREDIT.

P1.4: The old rank-eight source was admitted at historical levels. It is
incorrect to require its earlier odd square tests at either new frozen
ordinary continuation level. An ordinary continuation starts AFTER rank
eight, and only post-eight odd tests use its frozen level.

This packet restarts the fixed-rank exit potential at the genuine eighth
prefix mass, separately for the own-sixth actualParent and the rounded
finiteCap. Both have residual beta - S8 > t8 > cutoff on the SAME
realized original87 source, by actual_eighth_kernel_transport.

The fixed integer target-deletion bound is 261 * 3^(m+1) at a later
odd exit rank 9+2*m. The post-eight guard extraction from actual
ordinaryParityRosserPolicy and real prime-history reconstruction remain
unproved. No earlier inherited tests are transported or postulated.
-/

namespace ImbalancedChen.P4AOriginalFull87Post8SuffixExit
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FixedRankExit
  (evenPrefixMass odd_first_exit_last_log_lower
    fixed_odd_exit_integer_power_gap fixed_odd_exit_deletion_sandwich)
open P4AOriginalFull87SourceDictionary (Cell total)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87EighthKernelControl (cutoff cutoff_pos)
open P4AOriginalFull87EighthKernelIntegration
  (actualParent actual_eighth_kernel_transport)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87TargetPrimeDeletion (targetDeletionFactor)

/-- A continuation beginning after eight selected primes, in processing
order. The first new prime is index eight, i.e. the ninth prime. -/
def tailLogs (t : ℕ → ℝ) : ℕ → ℝ := fun i => t (8 + i)

/-- Sum of the first 2*k post-eight logs, never the inherited history. -/
def tailEvenMass (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  evenPrefixMass (tailLogs t) k

/-- Only post-eight successful odd squares are required. There is NO
same-level hypothesis about ranks 1,3,5,7 from the historical policy.
At a later odd exit rank 9+2*m this gives a bound in the *remaining*
level beta-S8, not the full level beta. -/
theorem post8_first_odd_exit_log_lower
    (t : ℕ → ℝ) (s8 beta : ℝ) (m : ℕ)
    (hprior : ∀ k < m,
      s8 + tailEvenMass t k + 3 * tailLogs t (2 * k) < beta)
    (hpair : ∀ k < m, tailLogs t (2 * k + 1) ≤ tailLogs t (2 * k))
    (hexit : beta ≤
      s8 + tailEvenMass t m + 3 * tailLogs t (2 * m)) :
    beta - s8 ≤ (3 : ℝ) ^ (m + 1) * tailLogs t (2 * m) := by
  have hp : ∀ k < m,
      evenPrefixMass (tailLogs t) k + 3 * tailLogs t (2 * k) <
        beta - s8 := by
    intro k hk
    have hh := hprior k hk
    dsimp [tailEvenMass] at hh
    linarith
  have he : beta - s8 ≤
      evenPrefixMass (tailLogs t) m + 3 * tailLogs t (2 * m) := by
    dsimp [tailEvenMass] at hexit
    linarith
  exact odd_first_exit_last_log_lower (tailLogs t)
    (beta - s8) m hp hpair he

/-- A fixed-rank power gap obtained from the POST-eight guards only.
The prefix mass is not silently discarded: beta-s8 is the level. -/
theorem post8_integer_power_gap
    (N p K m : ℕ) (hN : 1 < (N : ℝ))
    (t : ℕ → ℝ) (s8 floor beta : ℝ)
    (hfloor : 0 < floor) (hresidual : floor ≤ beta - s8)
    (hprior : ∀ k < m,
      s8 + tailEvenMass t k + 3 * tailLogs t (2 * k) < beta)
    (hpair : ∀ k < m, tailLogs t (2 * k + 1) ≤ tailLogs t (2 * k))
    (hexit : beta ≤
      s8 + tailEvenMass t m + 3 * tailLogs t (2 * m))
    (hreconstruct :
      (N : ℝ) ^ tailLogs t (2 * m) = (p : ℝ))
    (hK : (3 : ℝ) ^ (m + 1) < floor * (K : ℝ)) :
    N < p ^ K := by
  have hp : ∀ k < m,
      evenPrefixMass (tailLogs t) k + 3 * tailLogs t (2 * k) <
        beta - s8 := by
    intro k hk
    have hh := hprior k hk
    dsimp [tailEvenMass] at hh
    linarith
  have he : beta - s8 ≤
      evenPrefixMass (tailLogs t) m + 3 * tailLogs t (2 * m) := by
    dsimp [tailEvenMass] at hexit
    linarith
  exact fixed_odd_exit_integer_power_gap N p K m hN
    (tailLogs t) floor (beta - s8) hfloor hresidual
    hp hpair he hreconstruct hK

/-- The existing *realized* original87 source and genuine own-sixth
parent certify the two residual floors. In particular no fabricated
level beta is needed. The second bound follows by ordered comparison
through the same physical eighth prefix, not by cap monotonicity. -/
theorem owned87_old_and_new_residual_floor
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om N : ℝ) (history : List ℕ)
    (hlen : history.length = 8) (c : Cell)
    (ht : primeHistoryLogCoordinates N 8 history ∈ trim c (width r))
    (hr : RealizedHistory e q om N history c) :
    let v := primeHistoryLogCoordinates N 8 history
    cutoff < actualParent n e q om N history - total v ∧
    cutoff < (finiteCap n c v : ℝ) - total v := by
  dsimp only
  have h := actual_eighth_kernel_transport
    r n hn e q om N history hlen c ht hr
  dsimp only at h
  obtain ⟨hcut, hparent, hcomparison, hnew, _, _⟩ := h
  constructor
  · exact hcut.trans hparent
  · linarith

/-- 261 * cutoff > 1 exactly; hence every fixed post-eight exit depth
has a target-independent integer power gap. No asymptotic assumption. -/
theorem post8_uniform_integer_factor (m : ℕ) :
    (3 : ℝ) ^ (m + 1) <
      cutoff * (((261 * 3 ^ (m + 1) : ℕ) : ℝ)) := by
  have h261 : (1 : ℝ) < cutoff * 261 := by norm_num [cutoff]
  have hp : 0 < (3 : ℝ) ^ (m + 1) := pow_pos (by norm_num) _
  have hh := mul_lt_mul_of_pos_right h261 hp
  calc
    (3 : ℝ) ^ (m + 1) = 1 * (3 : ℝ) ^ (m + 1) := by ring
    _ < (cutoff * 261) * (3 : ℝ) ^ (m + 1) := hh
    _ = cutoff * (((261 * 3 ^ (m + 1) : ℕ) : ℝ)) := by
      push_cast
      ring

/-- A real post-eight first-exit at either actual frozen level has the
literal target-prime deletion budget. All post-eight square guards and
the last-prime reconstruction are visible as separate, unpaid obligations,
not smuggled through the source or RealizedHistory predicates.

The factor count is conservative by one: the power certificate uses
K=k+1 with k=261*3^(m+1). Earlier historical odd tests are unnecessary. -/
theorem owned87_post8_ordinary_deletion
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ)
    (hN : 1 < (N : ℝ)) (history : List ℕ)
    (hlen : history.length = 8) (c : Cell)
    (ht : primeHistoryLogCoordinates (N : ℝ) 8 history ∈ trim c (width r))
    (hr : RealizedHistory e q om (N : ℝ) history c)
    (t : ℕ → ℝ) (m p hi : ℕ) (hp : 3 ≤ p)
    (beta : ℝ)
    (hlevel : beta = actualParent n e q om (N : ℝ) history ∨
      beta = (finiteCap n c
        (primeHistoryLogCoordinates (N : ℝ) 8 history) : ℝ))
    (hprior : ∀ k < m,
      total (primeHistoryLogCoordinates (N : ℝ) 8 history) +
        tailEvenMass t k + 3 * tailLogs t (2 * k) < beta)
    (hpair : ∀ k < m,
      tailLogs t (2 * k + 1) ≤ tailLogs t (2 * k))
    (hexit : beta ≤
      total (primeHistoryLogCoordinates (N : ℝ) 8 history) +
        tailEvenMass t m + 3 * tailLogs t (2 * m))
    (hreconstruct :
      (N : ℝ) ^ tailLogs t (2 * m) = (p : ℝ)) :
    0 ≤ targetDeletionFactor N p hi ∧
    targetDeletionFactor N p hi ≤ 1 ∧
    1 - (((261 * 3 ^ (m + 1) : ℕ) : ℝ)) / ((p : ℝ) - 1) ≤
      targetDeletionFactor N p hi := by
  let s8 := total (primeHistoryLogCoordinates (N : ℝ) 8 history)
  have hres := owned87_old_and_new_residual_floor r n hn
    e q om (N : ℝ) history hlen c ht hr
  dsimp only at hres
  have hfloor : cutoff ≤ beta - s8 := by
    rcases hlevel with h | h
    · rw [h]
      exact hres.1.le
    · rw [h]
      exact hres.2.le
  have hpast : ∀ k < m,
      evenPrefixMass (tailLogs t) k + 3 * tailLogs t (2 * k) <
        (beta - s8) := by
    intro k hk
    have hh := hprior k hk
    dsimp [tailEvenMass, s8] at *
    linarith
  have hex : beta - s8 ≤
      evenPrefixMass (tailLogs t) m + 3 * tailLogs t (2 * m) := by
    dsimp [tailEvenMass, s8] at *
    linarith
  have hbase := post8_uniform_integer_factor m
  have hk : (((261 * 3 ^ (m + 1) : ℕ) : ℝ)) ≤
      (((261 * 3 ^ (m + 1) : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ (261 * 3 ^ (m + 1))
  have hK : (3 : ℝ) ^ (m + 1) <
      cutoff * (((261 * 3 ^ (m + 1) : ℕ) + 1 : ℕ) : ℝ) :=
    hbase.trans_le
      (mul_le_mul_of_nonneg_left hk cutoff_pos.le)
  exact fixed_odd_exit_deletion_sandwich N p hi
    (261 * 3 ^ (m + 1)) m hN hp
    (tailLogs t) cutoff (beta - s8)
    cutoff_pos hfloor hpast hpair hex hreconstruct hK

end
end ImbalancedChen.P4AOriginalFull87Post8SuffixExit
