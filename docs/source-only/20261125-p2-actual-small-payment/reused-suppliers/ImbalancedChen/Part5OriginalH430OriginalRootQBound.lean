import ImbalancedChen.Part5OriginalH430ActualMarkedRootConsumer

/-!
P5.6 / h34: remove the primitive Q <= N assumption from the actual
original U3/U4 positive-marked-source consumer.

The original selected prime already lies in the frozen U3/U4 root band.
The root's physical total t + sourceResidual is <= 1, and the actual
frozen level is no larger than that total. Therefore the literal
rootQ = N^(frozenLevel) is <= N, without any new count, marked-source,
owner, or distribution hypothesis.

The original q-versus-5Phi positive-part debt and the literal
rough-prime/cutoff checks are deliberately NOT discharged here.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalRootQBound

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430ActualResolvedMarkedPushforward
open Part5OriginalH430ActualMarkedRootConsumer
open Part5UpperTables.OriginalU34

/-- The upper Q gate of the actual positive-source comparison follows
directly from the ORIGINAL U3/U4 selected-prime band and frozen root
geometry, uniformly in the root precision, p, and the genuine tag.
No assumption about selected-count historical owner or q=d is used. -/
theorem original_root_Q_le_target
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (hN : 2 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hp : p ∈ originalBand N root) :
    rootQ N n root tau p ≤ (N : ℝ) := by
  have hb : physicalPrime N p ∈ rootBand root :=
    original_band_geometry hN hp
  have hlevel : rootLevel N n root tau p ≤ 1 :=
    ((frozenLevel_bounds (root_total_bounds ht ht' hb) n).1).trans
      (root_total_bounds ht ht' hb).2
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  change (N : ℝ) ^ (rootLevel N n root tau p) ≤ (N : ℝ)
  calc
    (N : ℝ) ^ (rootLevel N n root tau p) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase hlevel
    _ = (N : ℝ) := by simp

/-- The true generated marked family is consumed with NO caller-supplied
Q <= N condition. The real original q count and its unpaid positive
discrepancy remain exactly those of the previous source theorem. -/
theorem original_q_le_actual_budget_without_Q_gate
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
        (g : Fin 430),
        0 ≤ tau → tau ≤ 1/12 →
        1 / ((n : ℝ) + 1) ≤ 11/384 →
        p ∈ originalBand N root →
        (∀ l : Index N n root tau p g,
          l ∈ activePositions N n root tau p g →
          ∀ q ∈ (parentProduct (levelOccurrence l).current.old).primeFactors,
            (N : ℝ)^eta ≤ (q : ℝ)) →
        (∀ l : Index N n root tau p g,
          l ∈ activePositions N n root tau p g →
          (N : ℝ)^eta ≤ cutoff (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) (227/50)) →
        ((originalReceiver N p).card : ℝ) ≤
          actualMarkedRootBudget N n root tau p g epsilon := by
  obtain ⟨T, hT, hsource⟩ :=
    original_q_le_actual_resolved_marked_budget heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT he n root tau p g ht ht' hn hp hrough hcut
  have hN : 2 ≤ N := by omega
  exact hsource N hNT he n root tau p g ht ht' hn hp
    (original_root_Q_le_target N n root tau p hN ht ht' hp)
    hrough hcut

/-- All ORIGINAL U3/U4 labelled q receipts obey the summed actual
marked-source budget without a separate physical Q <= N gate. The U4
overlap is still counted under both tags. The root depth choice and
every other unproved source gate remain explicit; there is no payment
of the q-versus-marked deficit or replacement of selected-count owner. -/
theorem original_U34_le_actual_budgets_without_Q_gate
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430),
        0 ≤ tau → tau ≤ 1/12 →
        1 / ((n : ℝ) + 1) ≤ 11/384 →
        (∀ (k : Root) (p : ℕ), p ∈ originalBand N k →
          (∀ l : Index N n k tau p (depth k p),
            l ∈ activePositions N n k tau p (depth k p) →
            ∀ q ∈ (parentProduct (levelOccurrence l).current.old).primeFactors,
              (N : ℝ)^eta ≤ (q : ℝ)) ∧
          (∀ l : Index N n k tau p (depth k p),
            l ∈ activePositions N n k tau p (depth k p) →
            (N : ℝ)^eta ≤ cutoff (rootQ N n k tau p)
              (parentProduct (levelOccurrence l).current.old) (227/50))) →
        currentChenUpsilon3 N + currentChenUpsilon4 N ≤
          (∑ p ∈ originalBand N .U3,
            actualMarkedRootBudget N n .U3 tau p (depth .U3 p) epsilon) +
          (∑ p ∈ originalBand N .U4,
            actualMarkedRootBudget N n .U4 tau p (depth .U4 p) epsilon) := by
  obtain ⟨T, hT, hsource⟩ :=
    original_U34_le_actual_resolved_budgets heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT he n tau depth ht ht' hn hgates
  have hN : 2 ≤ N := by omega
  apply hsource N hNT he n tau depth ht ht' hn
  intro k p hp
  obtain ⟨hrough, hcut⟩ := hgates k p hp
  exact ⟨original_root_Q_le_target N n k tau p hN ht ht' hp,
    hrough, hcut⟩

end
end ImbalancedChen.Part5OriginalH430OriginalRootQBound
