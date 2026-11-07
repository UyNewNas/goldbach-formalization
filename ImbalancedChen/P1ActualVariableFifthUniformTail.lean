import ImbalancedChen.P1ActualVariableFifthTailPointwise
import ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly
import ImbalancedChen.P1OriginalFifthMiddleShellMovingLimit
import Mathlib.Topology.Order.LiminfLimsup

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The canonical ACTUAL VARIABLE5 smallRemainder is controlled at the moving
cutoff and on the entire middle shell. Its O(a) bound follows from actual
finite-max level inheritance and the original arithmetic shell moment.
There is no stored-cap checker, coarse old5, all15 surrogate, target tail
or assumed prime mean. Definitions are imported from the canonical owner.
-/

namespace ImbalancedChen.P1ActualVariableFifthUniformTail
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseFifthContinuation
open P1OriginalFifthWeightedSourceReduction
open P1OriginalFifthEnvelopeTerminalReduction
open P1OriginalFifthMovingHarmonicEnvelope
open P1OriginalFifthMovingScaleLimit
open P1OriginalFifthMiddleShellBinMoment
open P1OriginalFifthMiddleShellFiniteBudget
open P1OriginalFifthMiddleShellMovingLimit
open P1ActualVariableFifthGlobalSourceAssembly
open P1ActualVariableFifthTailPointwise

section Source
variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))

theorem smallRemainder_abs_le_bound_mul_terminalMass
    (a C : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hpoint : ∀ j ∈ selectedFifthCells e chi m omega J5,
      ∀ p ∈ (sourceCarrier e chi m omega N cap).filter (fun p => actualPrimeTupleLog N p 4 < a),
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j →
      |tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p| ≤ C) :
    |smallRemainder e chi m omega rows4 licensed4 J5 rows5 a N cap| ≤
      C * terminalPrimeMass e chi m omega a J5 N cap := by
  unfold smallRemainder
  simp_rw [smallCellRemainder_eq_terminal e chi m omega rows4 licensed4 J5 rows5 a N cap hN]
  unfold terminalCellRemainder terminalPrimeMass
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · rw [if_pos ht, if_pos ht, abs_mul, mul_one]
    have hh := mul_le_mul_of_nonneg_left (hpoint j hj p hp ht) (abs_nonneg (∏ i, 1 / ((p i : ℝ) - 1)))
    convert hh using 1 <;> ring
  · simp only [if_neg ht, mul_zero, abs_zero]

theorem actual_smallRemainder_movingCutoff_tendsto_zero
    (homega : 0 < omega) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => smallRemainder e chi m omega rows4 licensed4 J5 rows5
      (movingCutoff omega N) N (cap N)) evenTargets (𝓝 0) := by
  obtain ⟨C, hC, hpoint⟩ := exists_variable5_tupleDifference_exp_bound
  let D : ℝ := C * ((selectedFifthCells e chi m omega J5).card : ℝ)
  have hmajor : Tendsto (fun N : ℕ => D * normalizedMovingMajorant N) evenTargets (𝓝 0) := by
    simpa only [mul_zero] using
      (normalizedMovingMajorant_tendsto_zero.const_mul D).mono_left inf_le_left
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hmajor
  filter_upwards [(eventually_moving_scale_budgets omega homega).filter_mono inf_le_left, hcap,
    (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
      (Filter.eventually_mem_principal _).filter_mono inf_le_right)] with N hb hc he
  obtain ⟨hN, _ha0, ha, hT, haT, hbudget, hlog⟩ := hb
  have hN' : 1 < N := by omega
  have hfinite := smallRemainder_abs_le_bound_mul_terminalMass e chi m omega rows4 licensed4 J5 rows5
    (movingCutoff omega N) ((C * Real.exp (-movingBudget N)) * |Real.log (N : ℝ) / singularSeries N|)
    N (cap N) hN' (by
      intro j hj p hp ht
      obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
      exact hpoint e chi m omega (movingCutoff omega N) (movingBudget N) homega (by linarith)
        hT haT rows4 licensed4 J5 rows5 N (cap N) hN' he.2 hc hbudget hlog p hp j hj ht hs.le)
  calc
    _ ≤ _ := hfinite
    _ ≤ ((C * Real.exp (-movingBudget N)) * |Real.log (N : ℝ) / singularSeries N|) *
        (((selectedFifthCells e chi m omega J5).card : ℝ) *
          (2 * (1 + Real.log (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ)) : ℝ))) ^ 5) :=
      mul_le_mul_of_nonneg_left (terminalPrimeMass_le_moving_harmonic_bound
        e chi m omega (movingCutoff omega N) J5 N (cap N) hN' hc) (by positivity)
    _ = D * normalizedMovingMajorant N := by
      dsimp [D, normalizedMovingMajorant, harmonicFactor]
      ring

/-- A canonical actual signed shell is the same weighted shell finset used
by the independent arithmetic moment theorem; the source summand differs. -/
theorem signedShellCell_eq_shared_sum (delta a : ℝ) (N cap : ℕ) (j : Label5 m) :
    signedShellCell e chi m omega rows4 licensed4 J5 rows5 delta a N cap j =
      ∑ p ∈ shellCell e chi m omega delta a N cap j,
        (∏ i, 1 / ((p i : ℝ) - 1)) * tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p := by
  unfold signedShellCell shellCell
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hd : delta ≤ actualPrimeTupleLog N p 4
  · by_cases ha : actualPrimeTupleLog N p 4 < a
    · by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j <;> simp [hd, ha, ht]
    · simp [hd, ha]
  · simp [hd]

theorem signedShell_abs_le_quadraticMoments
    (delta a C : ℝ) (ha : 0 < a) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (hpoint : ∀ j ∈ selectedFifthCells e chi m omega J5,
      ∀ p ∈ shellCell e chi m omega delta a N cap j,
      |tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p| ≤
        C * (actualPrimeTupleLog N p 4) ^ 2) :
    |signedShell e chi m omega rows4 licensed4 J5 rows5 delta a N cap| ≤
      C * ∑ j ∈ selectedFifthCells e chi m omega J5, shellMoment e chi m omega delta a N cap j := by
  unfold signedShell
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [signedShellCell_eq_shared_sum e chi m omega rows4 licensed4 J5 rows5 delta a N cap j]
  unfold shellMoment
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  let r := owner a N p
  have hpbin : p ∈ shellBin e chi m omega delta a N cap j r := Finset.mem_filter.mpr ⟨hp, rfl⟩
  have hw := actualPrimeBoxWeight_nonneg
    (shellBin_subset_prime_box e chi m omega delta a ha J5 N cap hN hcap j hj r hpbin)
  rw [abs_mul, abs_of_nonneg hw]
  have hh := mul_le_mul_of_nonneg_left (hpoint j hj p hp) hw
  convert hh using 1 <;> ring

/-- Actual finite-max VARIABLE5 uniform O(a), with D preceding a and cap.
The only geometric hypotheses are 0<omega<rho; max inheritance replaces
both stored comparison checkers. Every actual row family is retained. -/
theorem exists_eventually_actual_smallRemainder_abs_le_linear
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ)) :
    ∃ D : ℝ, 0 < D ∧ ∀ a : ℝ, 0 < a → a ≤ min (19 / 96 : ℝ) (omega / 6) →
      ∀ cap : ℕ → ℕ,
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      ∀ᶠ N : ℕ in evenTargets,
        |smallRemainder e chi m omega rows4 licensed4 J5 rows5 a N (cap N)| ≤ D * a := by
  obtain ⟨C, hC, hpoint⟩ := exists_eventually_variable5_tupleDifference_quadratic
  obtain ⟨M, hM, hmoment⟩ := exists_original_moving_middle_shell_quadratic_Oa omega homega homegaRho
  let q : ℝ := C / omega ^ 3
  let n : ℝ := ((selectedFifthCells e chi m omega J5).card : ℝ)
  let D : ℝ := 1 + q * n * M
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro a ha hamax cap hcap
  have haRho := hamax.trans (min_le_left _ _)
  have haomega := hamax.trans (min_le_right _ _)
  have hdelta := actual_smallRemainder_movingCutoff_tendsto_zero
    e chi m omega rows4 licensed4 J5 rows5 homega cap hcap
  have hdeltaAbs : ∀ᶠ N : ℕ in evenTargets,
      |smallRemainder e chi m omega rows4 licensed4 J5 rows5 (movingCutoff omega N) N (cap N)| < a := by
    simpa only [abs_zero] using hdelta.abs.eventually (gt_mem_nhds ha)
  filter_upwards [hdeltaAbs,
    ((movingCutoff_tendsto_zero omega).eventually (gt_mem_nhds ha)).filter_mono inf_le_left,
    (hpoint omega homega).filter_mono inf_le_left,
    hmoment e chi m a ha haRho J5, hcap,
    (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
      (Filter.eventually_mem_principal _).filter_mono inf_le_right),
    (eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left]
    with N hsmall hda hp hm hc he hN
  have hN' : 1 < N := by omega
  have hs := signedShell_abs_le_quadraticMoments e chi m omega rows4 licensed4 J5 rows5
    (movingCutoff omega N) a q ha N (cap N) hN' hc (by
      intro j hj p hmem
      obtain ⟨hcarrier, hmiddle, hlast, ht⟩ := Finset.mem_filter.mp hmem
      exact hp e chi m (cap N) he.2 hc rows4 licensed4 J5 rows5 a haomega p hcarrier j hj ht hmiddle hlast)
  have hsum : (∑ j ∈ selectedFifthCells e chi m omega J5,
      shellMoment e chi m omega (movingCutoff omega N) a N (cap N) j) ≤ n * (M * a) := by
    calc
      _ ≤ ∑ _j ∈ selectedFifthCells e chi m omega J5, M * a :=
        Finset.sum_le_sum (fun j hj => hm (cap N) hc j hj)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, n]
  have hshell := hs.trans (mul_le_mul_of_nonneg_left hsum hq)
  calc
    _ = |smallRemainder e chi m omega rows4 licensed4 J5 rows5 (movingCutoff omega N) N (cap N) +
        signedShell e chi m omega rows4 licensed4 J5 rows5 (movingCutoff omega N) a N (cap N)| :=
      congrArg abs (smallRemainder_split e chi m omega rows4 licensed4 J5 rows5
        (movingCutoff omega N) a hda.le N (cap N) hN')
    _ ≤ |smallRemainder e chi m omega rows4 licensed4 J5 rows5 (movingCutoff omega N) N (cap N)| +
        |signedShell e chi m omega rows4 licensed4 J5 rows5 (movingCutoff omega N) a N (cap N)| := abs_add _ _
    _ ≤ a + q * (n * (M * a)) := add_le_add hsmall.le hshell
    _ = D * a := by dsimp [D]; ring

end Source
end
end ImbalancedChen.P1ActualVariableFifthUniformTail
