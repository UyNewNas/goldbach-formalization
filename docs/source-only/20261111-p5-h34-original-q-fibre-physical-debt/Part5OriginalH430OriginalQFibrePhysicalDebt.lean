import ImbalancedChen.Part5OriginalH430OriginalPrimeBandPhysicalGap

/-!
P5.6 / h34 — lift the ACTUAL physical CLOSED-CELL source ledger from
the original U3/U4 prime bands to every ORIGINAL selected (tag,p,q)
arithmetic receipt.

The previous packet summed one physical gap per original root prime p.
This packet tracks the actual q-fibre multiplicity: each original q
occurrence contributes once to the U3 or U4 tagged receiver sum, and
twice on the overlap through distinct root tags. The physical gap stays
root/p-dependent, not q-dependent; the lemma is an exact finite
Fubini identity, NOT a history-owner injection.

The resulting bound explicitly charges each real physical source
residual and selected-row error as many times as the original q-fibre
contains receipts. It does NOT claim this multiplied debt is small,
identify one history position with q, or close the genuine count owner,
root 7/2 weights, filters, base/seed/floor or PP/same-rho obligations.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalQFibrePhysicalDebt

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430PhysicalJointSourceDebt
open Part5OriginalH430OriginalPrimeBandPhysicalGap

/-- Any root/p scalar is repeated at every ACTUAL original q receipt.
The tagged arithmetic source is unchanged: Sum.inl = U3, Sum.inr = U4. -/
def originalTaggedRootLift (N : ℕ) (f : Root → ℕ → ℝ) : ℝ :=
  ∑ z ∈ originalTagged N,
    match z with
    | .inl x => f .U3 x.1
    | .inr x => f .U4 x.1

/-- Equivalent original p-fibre sum, with the TRUE number of q receipts
as multiplicity; the q count is NOT a physical history mark. -/
def originalQFibreRootSum (N : ℕ) (f : Root → ℕ → ℝ) : ℝ :=
  (∑ p ∈ originalBand N .U3,
    ((originalReceiver N p).card : ℝ) * f .U3 p) +
  (∑ p ∈ originalBand N .U4,
    ((originalReceiver N p).card : ℝ) * f .U4 p)

/-- Exact tagged q-fibre Fubini formula. Both original tags survive. -/
theorem original_tagged_root_lift_eq_q_fibres
    (N : ℕ) (f : Root → ℕ → ℝ) :
    originalTaggedRootLift N f = originalQFibreRootSum N f := by
  simp [originalTaggedRootLift, originalQFibreRootSum,
    originalTagged, originalPairs, Finset.sum_disjSum,
    Finset.sum_sigma, Finset.sum_const, nsmul_eq_mul]

/-- Actual read-minus-child physical gap, replicated by ORIGINAL
q receipts rather than incorrectly treating one root as one q. -/
def originalQFibrePhysicalGap (N n : ℕ) (tau : ℝ)
    (depth : Root → ℕ → Fin 430) : ℝ :=
  originalQFibreRootSum N
    (fun root p => actualRootPhysicalClosedCellGap
      N n root tau p (depth root p))

/-- Each true q receipt carries the corresponding local unpaid
physical successor-minus-predecessor-row residual. -/
def originalQFibrePhysicalSourceDebt (N n : ℕ) (tau : ℝ)
    (depth : Root → ℕ → Fin 430) : ℝ :=
  originalQFibreRootSum N
    (fun root p => actualPhysicalJointSourceResidualMass
      N n root tau p (depth root p))

/-- The selected coefficient error is copied once per original
q receipt and tag, not silently paid by one root-history mark. -/
def originalQFibreSelectedRowError (N n : ℕ) (tau : ℝ)
    (depth : Root → ℕ → Fin 430) : ℝ :=
  originalQFibreRootSum N
    (fun root p => actualSelectedError
      N n root tau p (depth root p))

/-- Direct comparison to the ACTUAL tagged U3/U4 q source. -/
theorem original_q_fibre_physical_gap_is_tagged
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) :
    originalTaggedRootLift N
      (fun root p => actualRootPhysicalClosedCellGap
        N n root tau p (depth root p)) =
      originalQFibrePhysicalGap N n tau depth := by
  exact original_tagged_root_lift_eq_q_fibres N _

/-- Exact U4 overlap for the q-weighted PHYSICAL debt, rather than
one shared historical root. No claim about collision payment. -/
theorem original_q_fibre_physical_source_overlap
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430)
    (hN : 1 ≤ N) :
    originalQFibrePhysicalSourceDebt N n tau depth =
      (∑ p ∈ upperExclusiveBand N,
        ((originalReceiver N p).card : ℝ) *
          actualPhysicalJointSourceResidualMass
            N n .U3 tau p (depth .U3 p)) +
      (∑ p ∈ originalBand N .U4,
        ((originalReceiver N p).card : ℝ) *
          (actualPhysicalJointSourceResidualMass
            N n .U3 tau p (depth .U3 p) +
           actualPhysicalJointSourceResidualMass
            N n .U4 tau p (depth .U4 p))) := by
  have hd : Disjoint (upperExclusiveBand N)
      (originalBand N .U4) := by
    apply Finset.disjoint_left.mpr
    intro p hp h4
    exact (Finset.mem_sdiff.mp hp).2 h4
  unfold originalQFibrePhysicalSourceDebt originalQFibreRootSum
  rw [original_u3_band_partition N hN, Finset.sum_union hd]
  simp only [mul_add, Finset.sum_add_distrib]
  ac_rfl

/-- No arbitrary signs in the absolute source residual: all original
q multiplicities and local absolute masses are nonnegative. -/
theorem original_q_fibre_source_debt_nonneg
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) :
    0 ≤ originalQFibrePhysicalSourceDebt N n tau depth := by
  unfold originalQFibrePhysicalSourceDebt originalQFibreRootSum
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (Nat.cast_nonneg _)
      (actual_physical_joint_source_residual_nonneg
        N n .U3 tau p (depth .U3 p))
  · apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (Nat.cast_nonneg _)
      (actual_physical_joint_source_residual_nonneg
        N n .U4 tau p (depth .U4 p))

/-- The original q-fibre multiplicity transports any local
CLOSED-CELL estimate; no q/history injection is a hypothesis. -/
private theorem original_q_fibre_abs_sum_le
    (N : ℕ) (root : Root) (a b : ℕ → ℝ)
    (h : ∀ p ∈ originalBand N root, |a p| ≤ b p) :
    |∑ p ∈ originalBand N root,
        ((originalReceiver N p).card : ℝ) * a p| ≤
      ∑ p ∈ originalBand N root,
        ((originalReceiver N p).card : ℝ) * b p := by
  calc
    _ ≤ ∑ p ∈ originalBand N root,
      |((originalReceiver N p).card : ℝ) * a p| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg
        ((originalReceiver N p).card))]
      exact mul_le_mul_of_nonneg_left (h p hp)
        (Nat.cast_nonneg ((originalReceiver N p).card))

/-- Quantitative q-fibre lifting of the genuine physical local
closed-cell bound. Charges are multiplied by the EXACT number of
original q receipts in each p fibre, retaining BOTH U4 tags.
This remains unpaid and is NOT a bound on the true selected COUNT. -/
theorem original_q_fibre_physical_gap_abs_bound
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) :
    |originalQFibrePhysicalGap N n tau depth| ≤
      originalQFibrePhysicalSourceDebt N n tau depth +
        originalQFibreSelectedRowError N n tau depth := by
  have h3 := original_q_fibre_abs_sum_le N .U3
    (fun p => actualRootPhysicalClosedCellGap
      N n .U3 tau p (depth .U3 p))
    (fun p => actualPhysicalJointSourceResidualMass
      N n .U3 tau p (depth .U3 p) +
      actualSelectedError N n .U3 tau p (depth .U3 p))
    (by
      intro p hp
      exact actual_root_physical_closedcell_gap_abs_le
        N n .U3 tau p (depth .U3 p))
  have h4 := original_q_fibre_abs_sum_le N .U4
    (fun p => actualRootPhysicalClosedCellGap
      N n .U4 tau p (depth .U4 p))
    (fun p => actualPhysicalJointSourceResidualMass
      N n .U4 tau p (depth .U4 p) +
      actualSelectedError N n .U4 tau p (depth .U4 p))
    (by
      intro p hp
      exact actual_root_physical_closedcell_gap_abs_le
        N n .U4 tau p (depth .U4 p))
  have houter := (abs_add_le _ _).trans (add_le_add h3 h4)
  unfold originalQFibrePhysicalGap originalQFibrePhysicalSourceDebt
    originalQFibreSelectedRowError originalQFibreRootSum
  simpa only [mul_add, Finset.sum_add_distrib,
    add_assoc, add_left_comm, add_comm] using houter

end
end ImbalancedChen.Part5OriginalH430OriginalQFibrePhysicalDebt
