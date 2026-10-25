import ImbalancedChen.P1OriginalVariableFourthFullSmallSource

/-!
# Uniform tail of the FULL actual original variable-fourth source

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

Absolute values are taken BEFORE enlarging any carrier. Actual fallback
summands vanish identically. Every surviving active branch embeds into
one genuine selected small cell at omega/2, with the same actual signed
PLUS residual. Nonnegative weighted absolute sums on those cells are
bounded by the true terminal-prime first moment. The explicit moving
parameter then gives O(a) on ALL original admitted fourth tuples.
There is no comparison of absolute signed subset and whole sums.
-/

namespace ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder

noncomputable section
open scoped Classical BigOperators
open Filter Topology Set HistoricalThirdCoarse
open P1OriginalCoarseContinuation P1OriginalCoarseFourthResidual
open P1OriginalFourthSmallPrimeStratification
open P1OriginalVariableFourthContinuation P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthFullSourceActivation P1OriginalVariableFourthActiveOnly
open P1OriginalVariableFourthSmallCellPointwise

def tupleWeight (p : Fin 4 → ℕ) : ℝ := ∏ i, 1 / ((p i : ℝ) - 1)

def actualDifference (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
    (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p

private theorem tupleWeight_nonneg_of_admitted
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (p : Fin 4 → ℕ) (hp : p ∈ admitted e chi m omega N cap) : 0 ≤ tupleWeight p := by
  have hprime := (admitted_log_data e chi m omega N cap hN p hp).2.1
  apply Finset.prod_nonneg
  intro i _
  have hi : (1 : ℝ) < p i := by exact_mod_cast (hprime i).one_lt
  positivity

/-- The terminal prime is at least three for an even target, on the
literal target-deleted carrier. This pays the moving exponential error. -/
private theorem last_coordinate_pays_unit
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N)
    (p : Fin 4 → ℕ) (hp : p ∈ admitted e chi m omega N cap) :
    1 ≤ (Real.log (N : ℝ) / Real.log 3) * actualPrimeTupleLog N p (Fin.last 3) := by
  have hd := (mem_firstExitAdmittedTuples_iff_of_decreasing 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))
    (roughPrimeUniverse_pairwise_gt N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) p).mp hp
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
      actualPrimeTupleLog N p (Fin.last 3) = Real.log (p (Fin.last 3) : ℝ) / Real.log 3 := by
    unfold actualPrimeTupleLog
    field_simp [hlogN.ne', hlog3.ne']
  rw [heq]
  exact (one_le_div hlog3).mpr hlogp

/-- Absolute term mass on a genuine enlarged cell, not the absolute value
of its signed total. The actual pointwise PLUS theorem and prime first
moment produce the bound; no cell tail inequality is assumed. -/
theorem exists_absolute_smallCell_mass_bound :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ),
        0 < omega → 0 < a → 2 * a ≤ omega →
      ∀ (J4 : Finset (FourthCell m)) (j : FourthCell m),
        j ∈ selectedFourthCells e chi m omega J4 →
      ∀ (rows : Finset ProducerRow) (licensed : ProducerRow → Prop),
      ∀ (N cap : ℕ), 2 ≤ N → Even N →
      ∀ L : ℝ, 2 ≤ L → L ^ 13 ≤ omega * Real.log (N : ℝ) →
        Real.exp 1 ≤ omega * Real.log (N : ℝ) →
        Real.log (2 : ℝ) * Real.log (3 : ℝ) ≤ a * Real.log (N : ℝ) *
          (Real.log (3 : ℝ) - Real.log (2 : ℝ)) →
        ((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
          (Real.log (N : ℝ) / Real.log 3) ≤ 1 →
        (∑ p ∈ smallCellTuples e chi m omega a N cap j,
          tupleWeight p * |actualDifference e chi m omega rows licensed N cap p|) ≤
          (2 * C / omega ^ 2 + 1) *
            (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
            (4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
  obtain ⟨C, hC, hpoint⟩ := exists_variable_smallCell_pointwise_linear_bound
  obtain ⟨K, hK, hmoment⟩ :=
    P1OriginalFourthFiniteBinBudget.exists_original_smallCell_weighted_moment_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro e chi m omega a homega ha haomega J4 j hj rows licensed
    N cap hN hEven L hL hbudget hlog hscale hExp
  have hN1 : 1 < N := by omega
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  let A : ℝ := 2 * C / omega ^ 2 + 1
  let E : ℝ := (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hsum : (∑ p ∈ smallCellTuples e chi m omega a N cap j,
      tupleWeight p * |actualDifference e chi m omega rows licensed N cap p|) ≤
      A * ∑ p ∈ smallCellTuples e chi m omega a N cap j,
        tupleWeight p * actualPrimeTupleLog N p (Fin.last 3) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have had := (Finset.mem_filter.mp hp).1
    have ht0 := (admitted_log_data e chi m omega N cap hN1 p had).2.2 (Fin.last 3)
    have hu := last_coordinate_pays_unit e chi m omega N cap hN1 hEven p had
    have hpay : E ≤ actualPrimeTupleLog N p (Fin.last 3) := by
      have hleft := mul_le_mul_of_nonneg_left hu hE
      have hright := mul_le_mul_of_nonneg_right hExp ht0.le
      dsimp [E] at hleft ⊢
      nlinarith only [hleft, hright]
    have hb := hpoint e chi m omega a homega ha haomega J4 j hj rows licensed
      N cap hN hEven p hp L hL hbudget hlog
    have hpbound : |actualDifference e chi m omega rows licensed N cap p| ≤
        A * actualPrimeTupleLog N p (Fin.last 3) := by
      dsimp [actualDifference, A]
      linarith
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hpbound
      (tupleWeight_nonneg_of_admitted e chi m omega N cap hN1 p had)
  have hm := mul_le_mul_of_nonneg_left
    (hmoment e chi m omega a ha J4 N cap hN1 hEven j hj hscale) hA
  exact hsum.trans (by simpa only [A, tupleWeight, mul_assoc] using hm)

/-- The complete original small source is controlled by an ALL-ABSOLUTE
finite enlarged-cell sum. This is the precise step preventing cancellation
in an enlarged signed carrier from being used as a subset bound. -/
theorem exists_fullSmallSource_abs_le_with_budgets :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ),
        0 < omega → 0 < a → 4 * a ≤ omega →
        logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2 →
      ∀ (rows : Finset ProducerRow) (licensed : ProducerRow → Prop),
      ∀ (N cap : ℕ), 2 ≤ N → Even N →
      ∀ L : ℝ, 2 ≤ L → L ^ 13 ≤ (omega / 2) * Real.log (N : ℝ) →
        Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ) →
        Real.log (2 : ℝ) * Real.log (3 : ℝ) ≤ a * Real.log (N : ℝ) *
          (Real.log (3 : ℝ) - Real.log (2 : ℝ)) →
        ((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
          (Real.log (N : ℝ) / Real.log 3) ≤ 1 →
        |fullSmallSource e chi m omega a rows licensed N cap| ≤
          (Fintype.card (Label m) : ℝ) * (2 * C / (omega / 2) ^ 2 + 1) *
            (actualPrimeReciprocalMass N (omega / 2) (19 / 96 : ℝ)) ^ 3 *
            (4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
  obtain ⟨C, K, hC, hK, hcell⟩ := exists_absolute_smallCell_mass_bound
  refine ⟨C, K, hC, hK, ?_⟩
  intro e chi m omega a homega ha haomega hmesh rows licensed
    N cap hN hEven L hL hbudget hlog hscale hExp
  have hN1 : 1 < N := by omega
  let B : ℝ := (2 * C / (omega / 2) ^ 2 + 1) *
    (actualPrimeReciprocalMass N (omega / 2) (19 / 96 : ℝ)) ^ 3 *
      (4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ)))
  have hM : 0 ≤ actualPrimeReciprocalMass N (omega / 2) (19 / 96 : ℝ) := by
    unfold actualPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
    have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hK0 : 0 < K := by linarith
    positivity
  have hbranch : ∀ label : Label m,
      (∑ p ∈ branchSmallTuples e chi m omega a N cap label,
        tupleWeight p * |actualDifference e chi m omega rows licensed N cap p|) ≤ B := by
    intro label
    by_cases hl : label ∈ activeAdoptedLabels (e : ℝ) chi m
    · by_cases hempty : branchSmallTuples e chi m omega a N cap label = ∅
      · simpa only [hempty, Finset.sum_empty] using hB
      · obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hj := active_branch_label_selected_half_of_occupied
          e chi m omega a hmesh N cap label hl p0 hp0
        have hsub := active_branch_small_subset_half_cell
          e chi m omega a homega.le hmesh N cap hN1 label hl
        calc
          _ = ∑ p ∈ branchSmallTuples e chi m omega a N cap label,
              tupleWeight p * |actualDifference e chi m (omega / 2) rows licensed N cap p| := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [actualDifference, active_branch_literalResidual_eq_half
              e chi m omega a homega.le rows licensed N cap hN1 label hl p hp]
            rfl
          _ ≤ ∑ p ∈ smallCellTuples e chi m (omega / 2) a N cap label.1,
              tupleWeight p * |actualDifference e chi m (omega / 2) rows licensed N cap p| := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro p hp _hnot
            exact mul_nonneg (tupleWeight_nonneg_of_admitted e chi m (omega / 2) N cap hN1 p
              (Finset.mem_filter.mp hp).1) (abs_nonneg _)
          _ ≤ B := hcell e chi m (omega / 2) a (by positivity) ha (by linarith)
            Finset.univ label.1 hj rows licensed N cap hN hEven
            L hL hbudget hlog hscale hExp
    · have hz : (∑ p ∈ branchSmallTuples e chi m omega a N cap label,
          tupleWeight p * |actualDifference e chi m omega rows licensed N cap p|) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        rw [actualDifference, literalResidual_zero_on_fallback_branch
          e chi m omega a rows licensed N cap hN1 label hl p hp, abs_zero, mul_zero]
      simpa only [hz] using hB
  calc
    _ ≤ ∑ p ∈ fullSmallTuples e chi m omega a N cap,
        tupleWeight p * |actualDifference e chi m omega rows licensed N cap p| := by
      unfold fullSmallSource
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (tupleWeight_nonneg_of_admitted e chi m omega N cap hN1 p
        (Finset.mem_filter.mp hp).1)]
      exact le_rfl
    _ = ∑ label : Label m, ∑ p ∈ branchSmallTuples e chi m omega a N cap label,
        tupleWeight p * |actualDifference e chi m omega rows licensed N cap p| :=
      sum_fullSmallTuples_eq_sum_branches e chi m omega a N cap hN1 _
    _ ≤ ∑ _label : Label m, B := Finset.sum_le_sum (fun label _ => hbranch label)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, B]
      ring

/-- Uniform O(a) on the FULL actual original variable-fourth small-prime
source, including every original admitted tuple. D and the threshold
precede cap, producer rows and licensing predicates. -/
theorem exists_eventually_fullSmallSource_abs_le_linear
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 0 < a → 4 * a ≤ omega →
      ∀ᶠ N : ℕ in atTop, Even N → ∀ cap : ℕ,
      ∀ (rows : Finset ProducerRow) (licensed : ProducerRow → Prop),
        |fullSmallSource e chi m omega a rows licensed N cap| ≤ D * a := by
  obtain ⟨C, K, hC, hK, hsource⟩ := exists_fullSmallSource_abs_le_with_budgets
  let B := (|Real.log ((19 / 96 : ℝ) / (omega / 2))| + 1) ^ 3
  let A := 2 * C / (omega / 2) ^ 2 + 1
  let T := 4 + 6 * K * (1 / Real.log 3 + 1)
  let q : ℝ := Fintype.card (Label m)
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
      (actualPrimeReciprocalMass N (omega / 2) (19 / 96 : ℝ)) ^ 3 ≤ B := by
    have h := (tendsto_actualPrimeReciprocalMass (show 0 < omega / 2 by positivity)
      (show omega / 2 < (19 / 96 : ℝ) by linarith)).eventually
      (gt_mem_nhds (show Real.log ((19 / 96 : ℝ) / (omega / 2)) <
        |Real.log ((19 / 96 : ℝ) / (omega / 2))| + 1 by
          linarith [le_abs_self (Real.log ((19 / 96 : ℝ) / (omega / 2)))]))
    filter_upwards [h] with N hN
    have hM : 0 ≤ actualPrimeReciprocalMass N (omega / 2) (19 / 96 : ℝ) := by
      unfold actualPrimeReciprocalMass
      apply Finset.sum_nonneg
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
      positivity
    exact pow_le_pow_left₀ hM hN.le 3
  filter_upwards [P1OriginalFourthUniformSmallRemainder.eventually_moving_budgets
    C (omega / 2) a (by positivity) ha, hprefix] with N hb hprefixN hEven cap rows licensed
  dsimp only at hb
  obtain ⟨hN, hL, hpower, hlog, hscale, hexp, hinv⟩ := hb
  have hraw := hsource e chi m omega a homega ha haomega hmesh rows licensed
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
    _ ≤ q * A * (actualPrimeReciprocalMass N (omega / 2) (19 / 96 : ℝ)) ^ 3 *
        (4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ))) := hraw
    _ ≤ q * A * B * (T * a) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprefixN (mul_nonneg hq hA.le))
        hterm hterm0 (by positivity)
    _ ≤ ((q + 1) * A * B * T) * a := by
      have hpos : 0 ≤ A * B * T * a := by positivity
      nlinarith

end
end ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder
