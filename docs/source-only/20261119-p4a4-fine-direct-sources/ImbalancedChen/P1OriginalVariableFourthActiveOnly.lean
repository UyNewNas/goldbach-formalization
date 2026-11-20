import ImbalancedChen.P1OriginalVariableFourthFullSourceActivation

/-!
Exact cancellation of both original Theta fallback branches.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

Every producer candidate is at most cap-2e, strictly below the ORIGINAL
initial exponent Theta-2e. Thus a true Theta seed can never be improved by
any licensed row, even on overlaps or producer-box walls. Inactive and
active-unselected original rawQ3 branches contribute exactly zero.
Only active adopted third ancestors remain in the full positive-box source.
Their ACTUAL third coordinate is at least omega; their mesh lower endpoint
need not be at least omega. No fourth selected-cell premise is introduced.
-/

namespace ImbalancedChen.P1OriginalVariableFourthActiveOnly
noncomputable section
open scoped Classical BigOperators
open Set HistoricalThirdCoarse VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseContinuation P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthFullSourceActivation
open HistoricalThirdCoarse.P1OriginalFourth

/-- The strict gap is independent of e, the row and its licensing status. -/
theorem bufferedCandidate_lt_initial (e : ℝ) (r : ProducerRow) (t : Point) :
    r.bufferedCandidate e t < initial e := by
  rw [r.bufferedCandidate_eq]
  have hcap : VariableEnvelope.cap < extendedDistributionCap := by
    norm_num [VariableEnvelope.cap, extendedDistributionCap]
  have hv := v_le_cap (∑ i ∈ r.selected, t i)
  dsimp [initial]
  linarith

/-- The initial seed wins globally, including every eligible overlapping
row. No whole-box geometry or licence hypothesis is needed. -/
theorem producerProfile_initial (e : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (t : Point) :
    producerProfile4 e rows licensed (initial e) t = initial e := by
  apply producerProfile4_eq_seed_of_dominated
  intro r _hr _he
  exact (bufferedCandidate_lt_initial e r t).le

/-- Even the literal fourth level equals the original frozen rawQ3 when
its actual seed is initial. This statement keeps arbitrary histories. -/
theorem producerLevel4_eq_frozen_of_seed_initial
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (history : List ℕ)
    (hseed : seedExponent e chi m omega N history = initial e) :
    producerLevel4 e chi m omega N rows licensed history = frozenLevel e chi m omega N history := by
  rw [P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed]
  unfold producerLevel4 level4 exponent4
  split_ifs with hlen
  · simp only [hseed]
    exact congrArg (fun x : ℝ => N ^ x) (producerProfile_initial e rows licensed _)
  · rfl

/-- All finite labels with a genuine Gamma seed; no whole-active mesh
criterion is imposed. Rough activation is tested pointwise in sourceBranch. -/
def activeAdoptedLabels (e chi : ℝ) (m : ℕ) : Finset (Label m) :=
  Finset.univ.filter (fun label => label.2 = true ∧ prefix3 label.1 ∈ cells e chi m)

theorem mem_activeAdoptedLabels (e chi : ℝ) (m : ℕ) (label : Label m) :
    label ∈ activeAdoptedLabels e chi m ↔ label.2 = true ∧ prefix3 label.1 ∈ cells e chi m := by
  simp [activeAdoptedLabels]

theorem branchSeed_initial_of_not_activeAdopted (e chi : ℝ) (m : ℕ) (label : Label m)
    (hl : label ∉ activeAdoptedLabels e chi m) : branchSeed e chi m label = initial e := by
  exact if_neg (fun h => hl ((mem_activeAdoptedLabels e chi m label).mpr h))

/-- The full branch's arithmetic coefficient vanishes before integration,
prime summation or limiting. There is no sign assertion about either
finite Rosser PLUS residual separately. -/
theorem branch_residual_difference_zero (e chi : ℝ) (m : ℕ) (label : Label m)
    (hl : label ∉ activeAdoptedLabels e chi m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (p : Fin 4 → ℕ) :
    fourthTuplePlusResidualP1 N cap (branchSeed e chi m label) p -
      fourthTuplePlusResidualP1 N cap
        (producerProfile4 e rows licensed (branchSeed e chi m label) (actualPrimeTupleLog N p)) p = 0 := by
  rw [branchSeed_initial_of_not_activeAdopted e chi m label hl, producerProfile_initial, sub_self]

/-- The continuous source difference cancels on the same fallback branches. -/
theorem branch_extended_difference_zero (e chi : ℝ) (m : ℕ) (label : Label m)
    (hl : label ∉ activeAdoptedLabels e chi m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (t : Point) :
    P1FourthFullCellIntegral.extendedProfile (branchSeed e chi m label) t -
      P1FourthFullCellIntegral.extendedProfile
        (producerProfile4 e rows licensed (branchSeed e chi m label) t) t = 0 := by
  rw [branchSeed_initial_of_not_activeAdopted e chi m label hl, producerProfile_initial, sub_self]

/-- This is the exact actual rough lower bound, valid even on a coarse
cell straddling omega. No lower endpoint of the mesh is substituted for t2. -/
theorem activeAdopted_source_rough (e chi : ℝ) (m : ℕ) (omega : ℝ) (label : Label m)
    (hl : label ∈ activeAdoptedLabels e chi m) {t : Point}
    (ht : t ∈ sourceBranch e chi m omega label) : omega ≤ t 2 := by
  have hflag := ((mem_activeAdoptedLabels e chi m label).mp hl).1
  have ha := ht.1.2
  simpa only [activationRegion, mem_setOf_eq, hflag, if_true] using ha

/-- Exact arithmetic contribution of one full-source branch. -/
def branchResidualSum (e chi : ℝ) (m : ℕ) (omega a : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (label : Label m) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ sourceBranch e chi m omega label then
        fourthTuplePlusResidualP1 N cap (branchSeed e chi m label) p -
          fourthTuplePlusResidualP1 N cap
            (producerProfile4 e rows licensed (branchSeed e chi m label) (actualPrimeTupleLog N p)) p
       else 0)

theorem branchResidualSum_zero_of_not_activeAdopted
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (N cap : ℕ) (label : Label m)
    (hl : label ∉ activeAdoptedLabels e chi m) :
    branchResidualSum e chi m omega a rows licensed N cap label = 0 := by
  unfold branchResidualSum
  apply Finset.sum_eq_zero
  intro p hp
  rw [branch_residual_difference_zero e chi m label hl rows licensed N cap p]
  simp

/-- All inactive and active-unselected branches are removed by proved
exact cancellation, not by a coverage or negligible-complement assumption. -/
theorem all_branch_sums_eq_activeAdopted
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (N cap : ℕ) :
    (∑ label : Label m, branchResidualSum e chi m omega a rows licensed N cap label) =
      ∑ label ∈ activeAdoptedLabels e chi m, branchResidualSum e chi m omega a rows licensed N cap label := by
  rw [activeAdoptedLabels, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro label _hl
  by_cases h : label.2 = true ∧ prefix3 label.1 ∈ cells e chi m
  · rw [if_pos h]
  · rw [if_neg h]
    exact branchResidualSum_zero_of_not_activeAdopted e chi m omega a rows licensed N cap label
      (fun hl => h ((mem_activeAdoptedLabels e chi m label).mp hl))

/-- Full original positive-box correction, now only over active adopted
third ancestors. Its actual rough gate remains omega <= t2 even when the
coarse cell crosses omega. All firstStop/current-cube gates remain inside
sourceBranch. No selectedFourthCells/J4 premise occurs. -/
theorem full_variable_correction_eq_activeAdopted
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 ≤ a) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    (∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) then
          literalTupleResidualDifference (rawLevel e chi m omega (N : ℝ))
            (producerLevel4 e chi m omega (N : ℝ) rows licensed) N cap p else 0)) =
      ∑ label ∈ activeAdoptedLabels e chi m, branchResidualSum e chi m omega a rows licensed N cap label := by
  rw [full_variable_correction_eq_all_branch_residuals e chi m omega a ha N cap hN hcap rows licensed]
  exact all_branch_sums_eq_activeAdopted e chi m omega a rows licensed N cap

end
end ImbalancedChen.P1OriginalVariableFourthActiveOnly
