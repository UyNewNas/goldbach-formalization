import ImbalancedChen.P1OriginalVariableFourthSmallCellPointwise
import ImbalancedChen.P1OriginalFourthUniformSmallRemainder

/-!
# Uniform actual variable-fourth selected small-prime remainder

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The source is the original selected fourth admitted carrier with its
literal rawQ3 and variable producerLevel4. The existing genuine prime
first moment and the actual signed PLUS pointwise tail pay every tuple.
The same moving parameter 3 log log N discharges all analytic budgets.
The constant is chosen before the cutoff, cap, producer rows and licences.
No h34Check for a constant cap, positive-source limiting target, or assumed
small-prime remainder estimate is used.
-/

namespace ImbalancedChen.P1OriginalVariableFourthSmallRemainder

noncomputable section
open scoped Classical BigOperators
open Filter Topology
open HistoricalThirdCoarse P1OriginalCoarseContinuation
open P1OriginalCoarseFourthResidual P1OriginalFourthSmallPrimeStratification
open P1OriginalVariableFourthContinuation P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthSmallCellPointwise

def smallCellSource (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (j : FourthCell m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) : ℝ :=
  ∑ p ∈ smallCellTuples e chi m omega a N cap j,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p

def selectedSmallSource (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFourthCells e chi m omega J4,
    smallCellSource e chi m omega a j rows licensed N cap

/-- The small set is the original existential small-coordinate filter;
strict actual prime order identifies it with the terminal coordinate. -/
theorem smallCellSource_eq_original_filter
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (j : FourthCell m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (hN : 1 < N) :
    smallCellSource e chi m omega a j rows licensed N cap =
      ∑ p ∈ (admitted e chi m omega N cap).filter (fun p =>
          (∃ i, actualPrimeTupleLog N p i < a) ∧
            actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
            (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p := by
  unfold smallCellSource
  rw [smallCellTuples_eq_original_filter e chi m omega a N cap hN j]

private theorem weight_nonneg
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (N cap : ℕ) (hN : 1 < N) (j : FourthCell m) (p : Fin 4 → ℕ)
    (hp : p ∈ smallCellTuples e chi m omega a N cap j) :
    0 ≤ ∏ i, 1 / ((p i : ℝ) - 1) := by
  have hprime := (admitted_log_data e chi m omega N cap hN p
    (Finset.mem_filter.mp hp).1).2.1
  apply Finset.prod_nonneg
  intro i _
  have hi : (1 : ℝ) < p i := by exact_mod_cast (hprime i).one_lt
  positivity

/-- Actual even targets delete prime two. The factor logN/log3 converts
the moving error into the same genuine terminal-prime first moment. -/
private theorem last_coordinate_pays_unit
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N) (j : FourthCell m)
    (p : Fin 4 → ℕ) (hp : p ∈ smallCellTuples e chi m omega a N cap j) :
    1 ≤ (Real.log (N : ℝ) / Real.log 3) * actualPrimeTupleLog N p (Fin.last 3) := by
  have had := (Finset.mem_filter.mp hp).1
  have hd := (mem_firstExitAdmittedTuples_iff_of_decreasing 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))
    (roughPrimeUniverse_pairwise_gt N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) p).mp had
  have hq := hd.2.1 (Fin.last 3)
  have hprime := mem_roughPrimeUniverse_prime hq
  have h2N : 2 ∣ N := by
    obtain ⟨u, hu⟩ := hEven
    exact ⟨u, by omega⟩
  have hne : p (Fin.last 3) ≠ 2 := by
    intro heq
    exact mem_roughPrimeUniverse_not_dvd hq (heq ▸ h2N)
  have hthree : 3 ≤ p (Fin.last 3) := by
    have := hprime.two_le
    omega
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogp : Real.log (3 : ℝ) ≤ Real.log (p (Fin.last 3) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hthree)
  have heq : (Real.log (N : ℝ) / Real.log 3) *
      actualPrimeTupleLog N p (Fin.last 3) =
      Real.log (p (Fin.last 3) : ℝ) / Real.log 3 := by
    unfold actualPrimeTupleLog
    field_simp [hlogN.ne', hlog3.ne']
  rw [heq]
  exact (one_le_div hlog3).mpr hlogp

/-- Genuine finite selected-source bound, before choosing the moving
parameter. Only explicit scalar budgets remain to be discharged. -/
theorem exists_selectedSmallSource_abs_le_with_budgets :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ),
        0 < omega → 0 < a → 2 * a ≤ omega →
      ∀ (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
        (licensed : ProducerRow → Prop),
      ∀ (N cap : ℕ), 2 ≤ N → Even N →
      ∀ L : ℝ, 2 ≤ L → L ^ 13 ≤ omega * Real.log (N : ℝ) →
        Real.exp 1 ≤ omega * Real.log (N : ℝ) →
        Real.log (2 : ℝ) * Real.log (3 : ℝ) ≤ a * Real.log (N : ℝ) *
          (Real.log (3 : ℝ) - Real.log (2 : ℝ)) →
        ((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
          (Real.log (N : ℝ) / Real.log 3) ≤ 1 →
        |selectedSmallSource e chi m omega a J4 rows licensed N cap| ≤
          ((selectedFourthCells e chi m omega J4).card : ℝ) *
            (2 * C / omega ^ 2 + 1) *
            (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
            (4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
  obtain ⟨C, hC, hpoint⟩ := exists_variable_smallCell_pointwise_linear_bound
  obtain ⟨K, hK, hmoment⟩ :=
    P1OriginalFourthFiniteBinBudget.exists_original_smallCell_weighted_moment_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro e chi m omega a homega ha haomega J4 rows licensed
    N cap hN hEven L hL hbudget hlog hscale hExp
  have hN1 : 1 < N := by omega
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  let A : ℝ := 2 * C / omega ^ 2 + 1
  let E : ℝ := (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hcell : ∀ j ∈ selectedFourthCells e chi m omega J4,
      |smallCellSource e chi m omega a j rows licensed N cap| ≤
        A * (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
          (4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
    intro j hj
    have hpbound : ∀ p ∈ smallCellTuples e chi m omega a N cap j,
        |literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
            (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p| ≤
          A * actualPrimeTupleLog N p (Fin.last 3) := by
      intro p hp
      have ht0 := (admitted_log_data e chi m omega N cap hN1 p
        (Finset.mem_filter.mp hp).1).2.2 (Fin.last 3)
      have hu := last_coordinate_pays_unit e chi m omega a N cap hN1 hEven j p hp
      have hpay : E ≤ actualPrimeTupleLog N p (Fin.last 3) := by
        have hleft := mul_le_mul_of_nonneg_left hu hE
        have hright := mul_le_mul_of_nonneg_right hExp ht0.le
        dsimp [E] at hleft ⊢
        nlinarith only [hleft, hright]
      have hb := hpoint e chi m omega a homega ha haomega J4 j hj rows licensed
        N cap hN hEven p hp L hL hbudget hlog
      dsimp [A]
      linarith
    have hsum : |smallCellSource e chi m omega a j rows licensed N cap| ≤
        A * ∑ p ∈ smallCellTuples e chi m omega a N cap j,
          (∏ i, 1 / ((p i : ℝ) - 1)) * actualPrimeTupleLog N p (Fin.last 3) := by
      unfold smallCellSource
      calc
        _ ≤ ∑ p ∈ smallCellTuples e chi m omega a N cap j,
            |(∏ i, 1 / ((p i : ℝ) - 1)) *
              literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
                (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ smallCellTuples e chi m omega a N cap j,
            A * ((∏ i, 1 / ((p i : ℝ) - 1)) * actualPrimeTupleLog N p (Fin.last 3)) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [abs_mul, abs_of_nonneg (weight_nonneg e chi m omega a N cap hN1 j p hp)]
          simpa only [mul_left_comm] using
            mul_le_mul_of_nonneg_left (hpbound p hp)
              (weight_nonneg e chi m omega a N cap hN1 j p hp)
        _ = _ := (Finset.mul_sum _ _ _).symm
    have hm := mul_le_mul_of_nonneg_left
      (hmoment e chi m omega a ha J4 N cap hN1 hEven j hj hscale) hA
    exact hsum.trans (by simpa only [mul_assoc] using hm)
  unfold selectedSmallSource
  calc
    _ ≤ ∑ j ∈ selectedFourthCells e chi m omega J4,
        |smallCellSource e chi m omega a j rows licensed N cap| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ selectedFourthCells e chi m omega J4,
        A * (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
          (4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ))) :=
      Finset.sum_le_sum hcell
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, A]
      ring

/-- Uniform actual variable-source O(a), including all producer overlaps.
The explicit constant is chosen before a, N, cap, rows and licences. -/
theorem exists_eventually_selectedSmallSource_abs_le_linear
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) :
    ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 0 < a → 2 * a ≤ omega →
      ∀ᶠ N : ℕ in atTop, Even N → ∀ cap : ℕ,
      ∀ (rows : Finset ProducerRow) (licensed : ProducerRow → Prop),
        |selectedSmallSource e chi m omega a J4 rows licensed N cap| ≤ D * a := by
  obtain ⟨C, K, hC, hK, hsource⟩ := exists_selectedSmallSource_abs_le_with_budgets
  let B := (|Real.log ((19 / 96 : ℝ) / omega)| + 1) ^ 3
  let A := 2 * C / omega ^ 2 + 1
  let T := 4 + 6 * K * (1 / Real.log 3 + 1)
  let q : ℝ := (selectedFourthCells e chi m omega J4).card
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hT : 0 < T := by
    dsimp [T]
    have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hK0 : 0 < K := by linarith
    positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  refine ⟨(q + 1) * A * B * T, by positivity, ?_⟩
  intro a ha haomega
  have hprefix : ∀ᶠ N : ℕ in atTop,
      (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 ≤ B := by
    have h := (tendsto_actualPrimeReciprocalMass homega homegaRho).eventually
      (gt_mem_nhds (show Real.log ((19 / 96 : ℝ) / omega) <
        |Real.log ((19 / 96 : ℝ) / omega)| + 1 by
          linarith [le_abs_self (Real.log ((19 / 96 : ℝ) / omega))]))
    filter_upwards [h] with N hN
    have hM : 0 ≤ actualPrimeReciprocalMass N omega (19 / 96 : ℝ) := by
      unfold actualPrimeReciprocalMass
      apply Finset.sum_nonneg
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
      positivity
    exact pow_le_pow_left₀ hM hN.le 3
  filter_upwards [P1OriginalFourthUniformSmallRemainder.eventually_moving_budgets
    C omega a homega ha, hprefix] with N hb hprefixN hEven cap rows licensed
  dsimp only at hb
  obtain ⟨hN, hL, hpower, hlog, hscale, hexp, hinv⟩ := hb
  have hraw := hsource e chi m omega a homega ha haomega J4 rows licensed
    N cap hN hEven (3 * Real.log (Real.log (N : ℝ))) hL hpower hlog hscale hexp
  have hterm : 4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ)) ≤ T * a := by
    dsimp [T]
    have hm := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 6 * K by linarith)
    nlinarith
  have hterm0 : 0 ≤ 4 * a + 6 * K *
      (a / Real.log 3 + 1 / Real.log (N : ℝ)) := by
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hK0 : 0 < K := by linarith
    positivity
  calc
    _ ≤ q * A * (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
        (4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ))) := hraw
    _ ≤ q * A * B * (T * a) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprefixN (mul_nonneg hq hA.le))
        hterm hterm0 (by positivity)
    _ ≤ ((q + 1) * A * B * T) * a := by
      have hpos : 0 ≤ A * B * T * a := by positivity
      nlinarith

end
end ImbalancedChen.P1OriginalVariableFourthSmallRemainder
