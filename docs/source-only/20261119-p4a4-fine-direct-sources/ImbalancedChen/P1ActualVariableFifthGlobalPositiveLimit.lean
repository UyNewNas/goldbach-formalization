import ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly
import ImbalancedChen.P1ActualVariableFifthPositiveCellLimit

/-!
Genuine global fixed-positive source mean for ACTUAL variable fifth.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.
The cell means are concrete actual old4/new5 profile theorems. No D,
owned-row bridge, stored cap, desired mean or h45 checker is assumed.
-/

namespace ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly
noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFifthContinuation
open P1OriginalCoarseFifthContinuation

section PositiveMean
variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m)) (rows5 : Finset (FifthRow m))

/-- Actual selected variable5-minus-ACTUAL-old4 integral, with both strict
own-cube gates and the original initial firstStop/rawQ3 source. -/
def selectedIntegral (a : ℝ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    P1ActualVariableFifthPositiveCellLimit.variableCellIntegral e chi m omega a j rows4 licensed4 rows5

/-- Definitional same-source identification, with no cap substitution. -/
theorem positiveCellCharge_eq_profile_source (a : ℝ) (N cap : ℕ)
    (j : P1OriginalVariableFifthContinuation.Label5 m) :
    positiveCellCharge e chi m omega rows4 licensed4 J5 rows5 a N cap j =
      P1ActualVariableFifthProfiles.positiveCellCharge e chi m omega rows4 licensed4 J5 rows5 a N cap j := rfl

/-- Aggregate the genuinely proved ACTUAL per-owner source limits. -/
theorem tendsto_positiveCharge_selectedIntegral
    (a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ)) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCharge e chi m omega rows4 licensed4 J5 rows5 a N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedIntegral e chi m omega rows4 licensed4 J5 rows5 a)) := by
  unfold positiveCharge selectedIntegral
  apply tendsto_finsetSum (selectedFifthCells e chi m omega J5)
  intro j hj
  simpa only [positiveCellCharge_eq_profile_source] using
    P1ActualVariableFifthPositiveCellLimit.tendsto_positiveCellCharge
      e chi m omega a ha haRho rows4 licensed4 J5 rows5 j hj cap hcap

/-- Exact global finite assembly connects the true actual fifth saving
minus its canonical small-coordinate signed source to the actual integral. -/
theorem tendsto_normalizedSaving_sub_smallRemainder
    (a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ)) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedSaving e chi m omega rows4 licensed4 J5 rows5 N (cap N) -
      smallRemainder e chi m omega rows4 licensed4 J5 rows5 a N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedIntegral e chi m omega rows4 licensed4 J5 rows5 a)) := by
  apply (tendsto_positiveCharge_selectedIntegral e chi m omega rows4 licensed4 J5 rows5 a ha haRho cap hcap).congr'
  apply Eventually.of_forall
  intro N
  rw [normalizedSaving_eq_positive_add_smallRemainder e chi m omega rows4 licensed4 J5 rows5 a N (cap N),
    add_sub_cancel_right]

end PositiveMean
end
end ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly

