import ImbalancedChen.P1OriginalFourthSmallCellPointwise
import ImbalancedChen.P1OriginalVariableFourthSourceLimit

/-!
# Actual variable-fourth small-prime pointwise tail

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The finite maximum retains the ORIGINAL raw-Q3 seed. This proves the
physical quotient order at every actual tuple, including overlaps and
losing candidates, without a whole-cell constant-cap comparison check.
The genuine signed actual PLUS tail then gives the terminal-coordinate
majorant on the original selected small cell. Its coefficient precedes
all policies, producer rows, eligibility predicates, cutoffs and primes.
No arithmetic residual sign, tail estimate or mean is assumed.
-/

namespace ImbalancedChen.P1OriginalVariableFourthSmallCellPointwise

noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse
open HistoricalThirdCoarse.P1OriginalUpperResidual
open P1OriginalCoarseContinuation P1OriginalCoarseFourthResidual
open P1OriginalFourthSmallPrimeStratification
open P1OriginalVariableFourthContinuation
open P2OriginalFourthCapProducerInterface

private theorem tupleHistory_eq_fourthHistory (p : Fin 4 → ℕ) :
    tupleHistory p = fourthHistory p := by
  simp [tupleHistory, fourthHistory, List.ofFn_succ]

/-- The literal inherited seed pays the new physical level, rather than
an assumed cell-wise lower bound for a producer candidate. -/
theorem oldLevel_le_producerLevel4
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ) (hN : 1 < N)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (p : Fin 4 → ℕ) :
    oldLevel e chi m omega N p ≤
      producerLevel4 e chi m omega (N : ℝ) rows licensed (tupleHistory p) := by
  rw [oldLevel_eq_frozenThird, ← tupleHistory_eq_fourthHistory]
  exact producer_frozenThird_le_level4 e chi m omega (N : ℝ)
    (by exact_mod_cast hN.le) rows licensed (tupleHistory p)

private theorem literalDifference_eq_normalized
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (p : Fin 4 → ℕ) :
    literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p =
      (actualSmallRosserPlusDensity N cap (p 3 : ℝ)
          (oldLevel (e : ℝ) chi m omega N p / (∏ i, p i : ℕ)) -
        actualSmallRosserPlusDensity N cap (p 3 : ℝ)
          (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed
            (tupleHistory p) / (∏ i, p i : ℕ))) *
        Real.log (N : ℝ) / singularSeries N := by
  unfold literalTupleResidualDifference
  have ha : rosserAncestor 3 (tupleHistory p) = thirdHistory p := by
    rw [tupleHistory_eq_fourthHistory, thirdAncestor_fourthHistory]
  rw [ha]
  rfl

/-- The exact original variable-Q4 arithmetic summand is controlled by a
multiple of the last log-prime coordinate and a displayed moving error.
There is no `h34Check`, fixed eligibility partition, or producer cap licence
among the hypotheses: finite maximization itself retains the rawQ3 seed. -/
theorem exists_variable_smallCell_pointwise_linear_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ),
        0 < omega → 0 < a → 2 * a ≤ omega →
      ∀ (J4 : Finset (FourthCell m)) (j : FourthCell m),
        j ∈ selectedFourthCells e chi m omega J4 →
      ∀ (rows : Finset ProducerRow) (licensed : ProducerRow → Prop),
      ∀ (N cap : ℕ), 2 ≤ N → Even N →
      ∀ p ∈ smallCellTuples e chi m omega a N cap j,
      ∀ L : ℝ, 2 ≤ L → L ^ 13 ≤ omega * Real.log (N : ℝ) →
        Real.exp 1 ≤ omega * Real.log (N : ℝ) →
        |literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
            (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p| ≤
          (2 * C / omega ^ 2) * actualPrimeTupleLog N p (Fin.last 3) +
            (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L) := by
  obtain ⟨C, hC, hsource⟩ :=
    P1OriginalSmallCutoffActualTail.exists_actualPlus_signed_linear_cutoff_majorant
  refine ⟨C, hC, ?_⟩
  intro e chi m omega a homega ha haomega J4 j hj rows licensed
    N cap hN hEven p hp L hL hbudget hlog
  have hN1 : 1 < N := by omega
  obtain ⟨had, hsmall, hcell⟩ := Finset.mem_filter.mp hp
  have hdata := admitted_log_data e chi m omega N cap hN1 p had
  have hprime := hdata.2.1
  have hpos : ∀ i, 0 < p i := fun i => (hprime i).pos
  have hpOriginal : p ∈ admittedTuples (e : ℝ) chi m omega (19 / 96 : ℝ) N cap := had
  have hcap := (admitted_last_bounds (e : ℝ) chi m omega (19 / 96 : ℝ)
    N cap hN1 p hpOriginal).2
  have hlevels := oldLevel_le_producerLevel4 (e : ℝ) chi m omega N hN1 rows licensed p
  have hquotient : oldLevel (e : ℝ) chi m omega N p / (∏ i, p i : ℕ) ≤
      producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed
        (tupleHistory p) / (∏ i, p i : ℕ) :=
    div_le_div_of_nonneg_right hlevels (Nat.cast_nonneg _)
  rw [literalDifference_eq_normalized]
  by_cases hy4 : (4 : ℝ) ≤ p 3
  · have hactive := selected_first_three_ge_omega e chi m omega J4 j hj
      (actualPrimeTupleLog N p) hcell hdata.1 (2 : Fin 3)
    have hcube := old_third_cube_log (e : ℝ) chi m omega (19 / 96 : ℝ)
      N cap hN1 p hpOriginal
    have hgap := HistoricalThirdCoarse.P1OriginalSmallCoordinate.fourth_numerator_gap
      omega (oldExponent (e : ℝ) chi m omega N p)
      (oldExponent (e : ℝ) chi m omega N p) (actualPrimeTupleLog N p)
      hactive hcube (hdata.1 (by decide : (2 : Fin 4) < 3)) le_rfl
    have hold := HistoricalThirdCoarse.P1OriginalSmallCoordinate.actual_quotient_gt_rpow_of_gap
      hN1 p hpos (oldExponent (e : ℝ) chi m omega N p) omega hgap.2
    rw [← oldLevel_eq_rpow] at hold
    have hy1 : (1 : ℝ) < p 3 := by exact_mod_cast (hprime 3).one_lt
    have hcut : (p 3 : ℝ) ≤ (N : ℝ) ^ a :=
      (HistoricalThirdCoarse.P1OriginalSmallCoordinate.last_log_le_iff_prime_le_rpow
        hN1 p hpos a).mp hsmall.le
    have hs := P1OriginalSmallCutoffActualTail.parameter_lower_of_small_power_cutoff
      N hN (p 3 : ℝ) a omega hy1 haomega hcut
    exact hsource N cap hN hEven (p 3 : ℝ)
      (oldLevel (e : ℝ) chi m omega N p / (∏ i, p i : ℕ))
      (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed
        (tupleHistory p) / (∏ i, p i : ℕ))
      omega L hcap hy4 homega hL hs hbudget hlog hold.le (hold.le.trans hquotient)
  · have hy3 : (p 3 : ℝ) ≤ 3 := by
      have hlt : p 3 < 4 := by exact_mod_cast (lt_of_not_ge hy4)
      exact_mod_cast (show p 3 ≤ 3 by omega)
    have hy1 : (1 : ℝ) < p 3 := by exact_mod_cast (hprime 3).one_lt
    have hold := (old_last_lt_quotient (e : ℝ) chi m omega (19 / 96 : ℝ)
      N cap hN1 p hpOriginal).le
    have hz := P1OriginalSmallCutoffActualTail.actualPlus_sub_eq_zero_of_cutoff_le_three
      N cap hEven (p 3 : ℝ)
      (oldLevel (e : ℝ) chi m omega N p / (∏ i, p i : ℕ))
      (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed
        (tupleHistory p) / (∏ i, p i : ℕ))
      hcap hy1 hy3 hold (hold.trans hquotient)
    rw [hz, zero_mul, zero_div, abs_zero]
    have hlast := hdata.2.2 (Fin.last 3)
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN1)
    have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    positivity

end
end ImbalancedChen.P1OriginalVariableFourthSmallCellPointwise
