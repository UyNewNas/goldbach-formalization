import ImbalancedChen.Part5OriginalH430HistoryRoughnessCore
import Mathlib.Data.Nat.GCD.BigOperators

namespace ImbalancedChen.P2FiniteMarkedGamma5ActualParentChildren
noncomputable section
open P5OriginalActionMassBound
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430HistoryQuotientCounts (history_ceiling_le_letter)

variable {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
variable (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
variable (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
variable (ho : o ∈ rootHistory N n k t p)

include hN ht ht' hn hp ho

/-- A strict candidate at an already reconstructed parent is distinct
from every prime in its old word. No child membership is required. -/
theorem below_ceiling_coprime_parent {q : ℕ} (hq : q.Prime)
    (hbelow : physicalPrime N q < o.current.node.physical.ceiling) :
    q.Coprime (parentProduct o.current.old) := by
  have H := rootHistory_coherent (show 1 < N by omega) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) ho
  apply Nat.coprime_list_prod_right_iff.mpr
  intro a ha
  apply (Nat.coprime_primes hq (H.letters a ha).1).mpr
  intro he
  exact (not_lt_of_ge (history_ceiling_le_letter hN ht ht' hn hp ho a ha)) (he ▸ hbelow)

/-- The original single carrier at this parent, with just target
coprimality left among the independent coprimality tests. -/
theorem single_iff (rule : SingleRule) (q : Fin (N+1)) :
    q ∈ singleChildren rule N (rootQ N n k t p) o.current.old o.current.node.physical.ceiling ↔
      (q.val.Prime ∧ q.val.Coprime N) ∧
      parentWindow N (rootQ N n k t p) o.current.old o.current.node.physical.ceiling ∧
      singleDomain rule (rootQ N n k t p) o.current.old q.val ∧
      physicalPrime N q.val < o.current.node.physical.ceiling ∧
      ((parentProduct o.current.old * q.val : ℕ) : ℝ) < rootQ N n k t p := by
  rw [mem_singleChildren]
  constructor
  · rintro ⟨⟨hprime,hcop⟩,hg⟩
    exact ⟨⟨hprime,(Nat.coprime_mul_iff_right.mp hcop).1⟩,hg⟩
  · rintro ⟨⟨hprime,hcop⟩,hw,hd,hbelow,hcap⟩
    exact ⟨⟨hprime,Nat.coprime_mul_iff_right.mpr
      ⟨hcop,below_ceiling_coprime_parent hN ht ht' hn hp ho hprime hbelow⟩⟩,hw,hd,hbelow,hcap⟩

/-- Native pair coordinates retain the strict small/large order, both
strict ceiling tests, and the same-Q cap on the appended large/small word. -/
theorem pair_iff (bank : Fin 36) (piece : Fin 4) (v : Fin (N+1) × Fin (N+1)) :
    v ∈ pairChildren bank piece N (rootQ N n k t p) o.current.old o.current.node.physical.ceiling ↔
      ((v.1.val.Prime ∧ v.1.val.Coprime N) ∧ (v.2.val.Prime ∧ v.2.val.Coprime N)) ∧
      parentWindow N (rootQ N n k t p) o.current.old o.current.node.physical.ceiling ∧
      v.1.val < v.2.val ∧
      pairPoint (rootQ N n k t p) o.current.old v.1.val v.2.val ∈
        P5OriginalFeedbackDomains.W2PairDomain (originalW2At bank) piece ∧
      physicalPrime N v.1.val < o.current.node.physical.ceiling ∧
      physicalPrime N v.2.val < o.current.node.physical.ceiling ∧
      ((parentProduct o.current.old * v.2.val * v.1.val : ℕ) : ℝ) < rootQ N n k t p := by
  rw [mem_pairChildren]
  constructor
  · rintro ⟨⟨⟨ha,hca⟩,⟨hb,hcb⟩⟩,hg⟩
    exact ⟨⟨⟨ha,(Nat.coprime_mul_iff_right.mp hca).1⟩,
      ⟨hb,(Nat.coprime_mul_iff_right.mp hcb).1⟩⟩,hg⟩
  · rintro ⟨⟨⟨ha,hca⟩,⟨hb,hcb⟩⟩,hw,hord,hd,hlo,hhi,hcap⟩
    exact ⟨⟨⟨ha,Nat.coprime_mul_iff_right.mpr
        ⟨hca,below_ceiling_coprime_parent hN ht ht' hn hp ho ha hlo⟩⟩,
      ⟨hb,Nat.coprime_mul_iff_right.mpr
        ⟨hcb,below_ceiling_coprime_parent hN ht ht' hn hp ho hb hhi⟩⟩⟩,
      hw,hord,hd,hlo,hhi,hcap⟩

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualParentChildren
