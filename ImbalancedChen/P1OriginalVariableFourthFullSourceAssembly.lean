import ImbalancedChen.P1OriginalVariableFourthFullActivePositiveLimit
import ImbalancedChen.P1OriginalVariableFourthFullSmallSource

/-!
Exact FULL original variable-fourth normalized source assembly.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The entire actual admitted rank-four source splits into the full positive
prime box and the canonical literal full small-coordinate signed remainder.
The positive-box identity is proved from actual prime and logarithmic data,
not from a selected-fourth-label support claim. The original base firstStop,
rawQ3, all pointwise producer rows and the empty-history coefficient remain.
-/

namespace ImbalancedChen.P1OriginalVariableFourthFullSourceAssembly
noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthSourceCoefficient
open P1OriginalVariableFourthFullActivePositiveLimit
open P1OriginalVariableFourthActiveOnly
open P1OriginalVariableFourthFullSmallRemainder

/-- The complete positive-box correction, with true original admission. -/
def fullPositiveSource (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (N cap : ℕ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) then
        literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
          (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p else 0)

/-- Exact arithmetic carrier identity on the whole original frontier.
Adequate cap coverage, prime positivity and the log/rpow inverse supply
both directions, without any fourth selected-cell hypothesis. -/
theorem positive_admitted_filter_eq_box_filter
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) :
    (firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
        (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i) =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))).filter
        (fun p => p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hlo⟩
    have hd := (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 4
      (HistoricalThirdCoarse.policy e chi m omega (N : ℝ)) N cap 0
        ((N : ℝ) ^ (19 / 96 : ℝ)) hcap p).mp hp
    have hpos : ∀ i, 0 < p i := fun i => (hd.2.1 i).1.pos
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    refine ⟨mem_actualPrimeBoxTuples_iff.mpr (fun i => ?_), hp⟩
    have hpow := Real.rpow_le_rpow_of_exponent_le hNr (hlo i)
    rw [actualPrimeTupleLog_rpow hN p hpos i] at hpow
    exact ⟨(hd.2.1 i).1, (hd.2.1 i).2.1, hpow, (hd.2.1 i).2.2.2⟩
  · rintro ⟨hpbox, hp⟩
    have hx := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hpbox).2
    exact ⟨hp, fun i => (mem_logPrimeBox.mp hx i).1⟩

/-- The positive carrier identity works for any actual arithmetic summand. -/
theorem positive_admitted_sum_eq_box_sum
    (e chi : ℝ) (m : ℕ) (omega a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) (f : (Fin 4 → ℕ) → ℝ) :
    (∑ p ∈ (firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
        (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
      (∏ i, 1 / ((p i : ℝ) - 1)) * f p) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
            (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) then f p else 0) := by
  rw [positive_admitted_filter_eq_box_filter e chi m omega a N cap hN hcap, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

/-- The literal entire source, before any small-coordinate deletion. -/
def fullAdmittedSource (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (N cap : ℕ) : ℝ :=
  ∑ p ∈ firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p

/-- Every actual omitted coordinate remains in the canonical full signed
remainder. Finite residuals need no assumed sign for this partition. -/
theorem fullAdmittedSource_eq_positive_add_fullSmall
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    fullAdmittedSource e chi m omega rows licensed N cap =
      fullPositiveSource e chi m omega a rows licensed N cap +
        fullSmallSource e chi m omega a rows licensed N cap := by
  have hpos := positive_admitted_sum_eq_box_sum (e : ℝ) chi m omega a N cap hN hcap
    (literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
      (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap)
  change _ = fullPositiveSource e chi m omega a rows licensed N cap at hpos
  rw [← hpos]
  unfold fullAdmittedSource fullSmallSource fullSmallTuples P1OriginalFourthSmallPrimeStratification.admitted
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hlarge : ∀ i, a ≤ actualPrimeTupleLog N p i
  · have hsmall : ¬ ∃ i, actualPrimeTupleLog N p i < a := by
      rintro ⟨i, hi⟩
      exact (not_lt_of_ge (hlarge i)) hi
    simp only [if_pos hlarge, if_neg hsmall, add_zero]
  · have hsmall : ∃ i, actualPrimeTupleLog N p i < a := by
      push_neg at hlarge
      exact hlarge
    simp only [if_neg hlarge, if_pos hsmall, zero_add]

/-- Exact normalized actual saving, retaining original initial firstStop
and rawQ3 on the entire admitted source rather than selected fourth cells. -/
theorem actualSaving_normalized_eq_positive_add_fullSmall
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    actualHistoricalFourthSaving (initialPolicy (e : ℝ) m (N : ℝ))
        (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed)
        N cap ((N : ℝ) ^ (19 / 96 : ℝ)) * Real.log (N : ℝ) / singularSeries N =
      fullPositiveSource e chi m omega a rows licensed N cap +
        fullSmallSource e chi m omega a rows licensed N cap := by
  rw [actualHistoricalFourthSaving_eq_literalTupleSum]
  exact fullAdmittedSource_eq_positive_add_fullSmall e chi m omega a N cap hN hcap rows licensed

/-- The literal originalT3-minus-variableQ4 retained-polynomial difference
has the SAME full normalized source. Empty history and d=1 are retained in
both polynomials, with no independent coefficient deletion. -/
theorem originalPolicySaving_normalized_eq_positive_add_fullSmall
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    (firstExitRetainedPolynomial (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) -
      firstExitRetainedPolynomial (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) rows licensed)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) *
        Real.log (N : ℝ) / singularSeries N =
      fullPositiveSource e chi m omega a rows licensed N cap +
        fullSmallSource e chi m omega a rows licensed N cap := by
  rw [original_policy_difference_eq_fourth_saving (e : ℝ) chi m omega N cap
    ((N : ℝ) ^ (19 / 96 : ℝ)) rows licensed (by exact_mod_cast (show 1 ≤ N by omega))]
  exact actualSaving_normalized_eq_positive_add_fullSmall e chi m omega a N cap hN hcap rows licensed

/-- Fixed-positive actual saving after subtracting its literal full small
remainder has the genuine full active-branch integral mean. -/
theorem tendsto_actualSaving_sub_fullSmall
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFourthSaving (initialPolicy (e : ℝ) m (N : ℝ))
          (rawLevel (e : ℝ) chi m omega (N : ℝ))
          (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed)
          N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) * Real.log (N : ℝ) / singularSeries N -
        fullSmallSource e chi m omega a rows licensed N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∑ label ∈ activeAdoptedLabels (e : ℝ) chi m,
        refinedBranchIntegral (e : ℝ) chi m omega a rows licensed label)) := by
  apply (tendsto_full_positive_original_correction (e : ℝ) chi m omega a ha haRho rows licensed cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  rw [actualSaving_normalized_eq_positive_add_fullSmall e chi m omega a N (cap N) hN hc rows licensed]
  simp only [add_sub_cancel_right, fullPositiveSource]

end
end ImbalancedChen.P1OriginalVariableFourthFullSourceAssembly

