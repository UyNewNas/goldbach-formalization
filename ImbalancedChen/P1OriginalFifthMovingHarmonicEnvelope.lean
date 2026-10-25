import ImbalancedChen.P1OriginalFifthPositiveStratumMass
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

All-window arithmetic bounds, including windows whose endpoints move with N.
No fixed-positive-window prime asymptotic is used. The crude harmonic bound
loses five logarithms but is effective against the *whole* actual lower
deficit source exp(-T), not just the source's explicit error term.

The final theorem constructs uniformly legal tuple budgets from the actual
third-parent geometry and four scalar inequalities at N. Its constants are
chosen before all targets and moving cutoffs. It does not assume a remainder
bound, a density limit, a shell estimate, or an interchange of limits.
-/

namespace ImbalancedChen.P1OriginalFifthMovingHarmonicEnvelope

noncomputable section

open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open P1OriginalFifthWeightedSourceReduction
open P1OriginalFifthEnvelopeTerminalReduction
open P1OriginalFifthPositiveStratumMass
open HistoricalThirdCoarse.P1OriginalCoarseFifth

/-- The auxiliary parameter is constructed at the unchanged physical
residual. A log-coordinate cutoff and a true numerator gap suffice. -/
theorem sourceBudget_of_log_cutoff_and_gap
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i)
    (lambda c a T : ℝ) (hsmall : actualPrimeTupleLog N p 4 ≤ a)
    (hgap : c < lambda - ∑ i, actualPrimeTupleLog N p i)
    (hT : 2 ≤ T) (haT : a * T ≤ c)
    (hbudget : T ^ 13 ≤ c * Real.log (N : ℝ))
    (hlog : Real.exp 1 ≤ c * Real.log (N : ℝ)) :
    P1OriginalSmallCutoffActualLowerTail.sourceBudget (p 4 : ℝ)
      (P1OriginalSmallCutoffActualLowerTail.residualLevel N lambda p) T := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hlow := HistoricalThirdCoarse.P1OriginalSmallCoordinate.actual_quotient_gt_rpow_of_gap
    hN p hpos lambda c hgap
  have hcut : (p 4 : ℝ) ≤ (N : ℝ) ^ a := by
    rw [← actualPrimeTupleLog_rpow hN p hpos 4]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hsmall
  have hpower : (p 4 : ℝ) ^ T ≤ (N : ℝ) ^ c := by
    calc
      _ ≤ ((N : ℝ) ^ a) ^ T :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hcut (by linarith)
      _ = (N : ℝ) ^ (a * T) := (Real.rpow_mul hn0.le a T).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le haT
  have hlogR : c * Real.log (N : ℝ) ≤ Real.log (Nat.ceil
      (P1OriginalSmallCutoffActualLowerTail.residualLevel N lambda p) : ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hn0 c)
      (hlow.le.trans (Nat.le_ceil
        (P1OriginalSmallCutoffActualLowerTail.residualLevel N lambda p)))
    simpa only [Real.log_rpow hn0] using hh
  exact ⟨hT, hpower.trans hlow.le, hbudget.trans hlogR, hlog.trans hlogR⟩

/-- On the actual selected original joint cell the inherited third cube
constructs BOTH legal source budgets and BOTH strict own-cube gates.
Only the finite inherited-cap compatibility and four scalar inequalities
at N are inputs. There is no pointwise source-bound assumption. -/
theorem original_selected_legal_uniform_budget
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a T : ℝ)
    (homega : 0 < omega) (ha : a ≤ omega / 6)
    (hT : 2 ≤ T) (haT : a * T ≤ omega / 2)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (hbudget : T ^ 13 ≤ (omega / 2) * Real.log (N : ℝ))
    (hlog : Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (h34 : HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (thirdOwner j)) ≤ (old5 e chi m omega J4 cap4 j : ℝ))
    (p : Fin 5 → ℕ) (hp : p ∈ sourceCarrier e chi m omega N cap)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hsmall : actualPrimeTupleLog N p 4 < a) :
    (∀ i, 0 < p i) ∧ 1 < (p 4 : ℝ) ∧ (p 4 : ℝ) ≤ (cap : ℝ) ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^
        P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^
        P1OriginalSmallCutoffActualLowerTail.newExponent e chi m omega J4 cap4 J5 cap5 N p ∧
      P1OriginalSmallCutoffActualLowerTail.sourceBudget (p 4 : ℝ)
        (P1OriginalSmallCutoffActualLowerTail.residualLevel N
          (P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p) p) T ∧
      P1OriginalSmallCutoffActualLowerTail.sourceBudget (p 4 : ℝ)
        (P1OriginalSmallCutoffActualLowerTail.residualLevel N
          (P1OriginalSmallCutoffActualLowerTail.newExponent e chi m omega J4 cap4 J5 cap5 N p) p) T := by
  have hc : p ∈ candidates (e : ℝ) chi m omega N cap := by
    simpa only [sourceCarrier, candidates] using hp
  have hd := (mem_candidates_iff_log_on_cell (e : ℝ) chi m omega N cap hN hcap p j ht).mp hc
  have hpos : ∀ i, 0 < p i := fun i => (hd.1 i).1.pos
  have hprepos := P1OriginalCoarseFifthResidual.tupleHistory_pos p hpos
  have hprelog : primeHistoryLogCoordinates (N : ℝ) 5
      (P1OriginalCoarseFifthResidual.tupleHistory p) ∈ logPrimeMeshCell 0 (19 / 96) m j := by
    simpa only [P1OriginalCoarseFifthResidual.tupleHistory_log] using ht
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hold : P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p =
      (old5 e chi m omega J4 cap4 j : ℝ) := by
    change (P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 (N : ℝ)
      (rosserAncestor 4 (P1OriginalCoarseFifthResidual.tupleHistory p)) : ℝ) = _
    rw [inherited_fourth_on_selected_fifth_cell e chi m omega J4 cap4 J5 (N : ℝ)
      (P1OriginalCoarseFifthResidual.tupleHistory p) hn
      (by simp [P1OriginalCoarseFifthResidual.tupleHistory]) hprepos j hj hprelog]
  have hnew : P1OriginalSmallCutoffActualLowerTail.newExponent e chi m omega J4 cap4 J5 cap5 N p =
      (cap5 j : ℝ) := by
    change (effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 (N : ℝ)
      (P1OriginalCoarseFifthResidual.tupleHistory p) : ℝ) = _
    rw [effectiveExponent5Q_on_selected_cell e chi m omega J4 cap4 J5 cap5 (N : ℝ)
      (P1OriginalCoarseFifthResidual.tupleHistory p)
      (by simp [P1OriginalCoarseFifthResidual.tupleHistory]) j hj hprelog]
  have hg := (mem_jointRegion (e : ℝ) chi m omega j _).mp hd.2
  have hactive := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_cell_rough
    e chi m omega J5 j hj ht
  have hcurrent := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    e chi m omega J5 j hj ht
  have hcube : actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
      3 * actualPrimeTupleLog N p 2 < HistoricalThirdCoarse.levelExponent (e : ℝ)
        (HistoricalThirdCoarse.box m (thirdOwner j)) := by
    simpa only [hcurrent] using hg.2.2.2.2
  have hlevel : (old5 e chi m omega J4 cap4 j : ℝ) ≤ cap5 j := by
    exact_mod_cast h45Check_sound e chi m omega J4 cap4 J5 cap5 h45 j hj
  have hgo := (HistoricalThirdCoarse.P1OriginalSmallCoordinate.fifth_numerator_gap
    omega _ (old5 e chi m omega J4 cap4 j : ℝ) (actualPrimeTupleLog N p)
    hactive hcube (hg.2.1 (by decide : (2 : Fin 5) < 3)) h34).2
  have hgn := (HistoricalThirdCoarse.P1OriginalSmallCoordinate.fifth_numerator_gap
    omega _ (cap5 j : ℝ) (actualPrimeTupleLog N p)
    hactive hcube (hg.2.1 (by decide : (2 : Fin 5) < 3)) (h34.trans hlevel)).2
  have hgapOld : omega / 2 <
      P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p -
        ∑ i, actualPrimeTupleLog N p i := by rw [hold]; linarith
  have hgapNew : omega / 2 <
      P1OriginalSmallCutoffActualLowerTail.newExponent e chi m omega J4 cap4 J5 cap5 N p -
        ∑ i, actualPrimeTupleLog N p i := by rw [hnew]; linarith
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (hd.1 4).1.one_lt
  · exact (hd.1 4).2.2.2.le.trans hcap
  · apply (actualPrimeTupleOwnCube_iff hN p hpos _).mpr
    unfold primeTupleOwnCubeForm
    change (∑ i, actualPrimeTupleLog N p i) + 2 * actualPrimeTupleLog N p 4 < _
    linarith
  · apply (actualPrimeTupleOwnCube_iff hN p hpos _).mpr
    unfold primeTupleOwnCubeForm
    change (∑ i, actualPrimeTupleLog N p i) + 2 * actualPrimeTupleLog N p 4 < _
    linarith
  · exact sourceBudget_of_log_cutoff_and_gap N hN p hpos _ (omega / 2) a T
      hsmall.le hgapOld hT haT hbudget hlog
  · exact sourceBudget_of_log_cutoff_and_gap N hN p hpos _ (omega / 2) a T
      hsmall.le hgapNew hT haT hbudget hlog

/-- An elementary bound valid for arbitrary real endpoints, targets and caps.
It uses every positive integer as a majorant, so there is no moving-window
prime-distribution hypothesis. -/
theorem roughPrimeFinset_mass_le_twice_one_add_log
    (N cap : ℕ) (w z : ℝ) :
    (∑ p ∈ roughPrimeFinset N cap w z, 1 / ((p : ℝ) - 1)) ≤
      2 * (1 + Real.log (cap : ℝ)) := by
  have hterm : ∀ p ∈ roughPrimeFinset N cap w z,
      1 / ((p : ℝ) - 1) ≤ 2 * (p : ℝ)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ hp1 hp0).mpr
    linarith
  have hsubset : roughPrimeFinset N cap w z ⊆ Finset.Icc 1 cap := by
    intro p hp
    have hh := mem_roughPrimeFinset.mp hp
    exact Finset.mem_Icc.mpr ⟨hh.2.1.one_lt.le, hh.1.le⟩
  have hharm : (harmonic cap : ℝ) =
      ∑ p ∈ Finset.Icc 1 cap, (p : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    _ ≤ ∑ p ∈ roughPrimeFinset N cap w z, 2 * (p : ℝ)⁻¹ :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ Finset.Icc 1 cap, 2 * (p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p _hp _hnot
      positivity
    _ = 2 * (harmonic cap : ℝ) := by rw [hharm, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log cap) (by norm_num)

/-- This finite product estimate also includes k=0, where both products
are one. It is valid for moving a and b and retains the target exclusions. -/
theorem actualPrimeBoxMass_le_harmonic_product
    (N : ℕ) {k : ℕ} (a b : Fin k → ℝ) :
    actualPrimeBoxMass N a b ≤
      ∏ i, 2 * (1 + Real.log (Nat.ceil ((N : ℝ) ^ b i) : ℝ)) := by
  rw [actualPrimeBoxMass_eq_prod]
  apply Finset.prod_le_prod
  · intro i _hi
    unfold actualPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
    exact one_div_nonneg.mpr (by linarith)
  · intro i _hi
    exact roughPrimeFinset_mass_le_twice_one_add_log N
      (Nat.ceil ((N : ℝ) ^ b i)) ((N : ℝ) ^ a i) ((N : ℝ) ^ b i)

/-- The original terminal mass is exactly its zero-lower-endpoint stratum.
The original candidate carrier and selected historical joint mesh remain
unchanged; only zero is inserted as an automatically satisfied inequality. -/
theorem terminalPrimeMass_eq_zero_stratum
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J5 : Finset (Label5 m)) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) :
    terminalPrimeMass e chi m omega a J5 N cap =
      stratumSelectedMass e chi m omega 0 a J5 N cap := by
  unfold terminalPrimeMass stratumSelectedMass stratumCellMass
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hface : actualPrimeTupleLog N p 4 < a
  · by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
    · have hwhole := logPrimeMeshCell_subset_box (by norm_num) m j ht
      have hzero : 0 ≤ actualPrimeTupleLog N p 4 :=
        (mem_logPrimeBox.mp hwhole 4).1
      have hbox := stratum_cell_subset_prime_box e chi m omega 0 a
        N cap hN hcap j (Finset.mem_filter.mpr ⟨hp, hzero, hface, ht⟩)
      have hw := actualPrimeBoxWeight_nonneg hbox
      simp only [hface, ht, hzero, and_self, if_true, mul_one,
        abs_of_nonneg hw]
    · simp [hface, ht]
  · simp [hface]

/-- A quantitative all-moving-window estimate on the literal original
rank-four first-exit fifth carrier. There is no positive lower exponent,
no threshold depending on a, and no asymptotic prime-box input. -/
theorem terminalPrimeMass_le_moving_harmonic_bound
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J5 : Finset (Label5 m)) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) :
    terminalPrimeMass e chi m omega a J5 N cap ≤
      ((selectedFifthCells e chi m omega J5).card : ℝ) *
        (2 * (1 + Real.log (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ)) : ℝ))) ^ 5 := by
  rw [terminalPrimeMass_eq_zero_stratum e chi m omega a J5 N cap hN hcap]
  calc
    _ ≤ ((selectedFifthCells e chi m omega J5).card : ℝ) *
        actualPrimeBoxMass N (fun _ : Fin 5 => 0) (fun _ => (19 / 96 : ℝ)) :=
      stratumSelectedMass_le_card_mul_primeBoxMass
        e chi m omega 0 a J5 N cap hN hcap
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        actualPrimeBoxMass_le_harmonic_product N
          (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))

/-- Both pieces of the actual Suzuki envelope are controlled. In particular
the A exp(-t) main deficit is included, not discarded as an error. -/
theorem tailEnvelope_le_uniform_exp
    (A B K R t T : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT : T ≤ t) (hlog : 1 ≤ Real.log (Nat.ceil R : ℝ)) :
    P1OriginalSmallCutoffActualLowerTail.tailEnvelope A B K R t ≤
      (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T) := by
  have he : Real.exp (-t) ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith)
  have hp : (Real.log (Nat.ceil R : ℝ)) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
  have hBexp : 0 ≤ B * Real.exp (Real.sqrt K) := by positivity
  unfold P1OriginalSmallCutoffActualLowerTail.tailEnvelope
  calc
    _ ≤ A * Real.exp (-t) + B * Real.exp (Real.sqrt K) * Real.exp (-t) := by
      apply add_le_add_left
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
        (mul_nonneg hBexp (Real.exp_pos _).le)
    _ ≤ A * Real.exp (-T) + B * Real.exp (Real.sqrt K) * Real.exp (-T) :=
      add_le_add (mul_le_mul_of_nonneg_left he hA)
        (mul_le_mul_of_nonneg_left he hBexp)
    _ = _ := by ring

/-- The finite Euler product supplies no amplification. -/
theorem actualSmallEulerProduct_le_one (N cap : ℕ) (y : ℝ) :
    actualSmallEulerProduct N cap y ≤ 1 := by
  unfold actualSmallEulerProduct
  apply Finset.prod_le_one
  · intro p hp
    have hprime := (mem_actualSmallPrimeFinset.mp hp).2.1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    apply sub_nonneg.mpr
    apply (div_le_one (by linarith : 0 < (p : ℝ) - 1)).mpr
    linarith
  · intro p hp
    have hprime := (mem_actualSmallPrimeFinset.mp hp).2.1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    exact sub_le_self _ (one_div_nonneg.mpr (by linarith))

/-- Pointwise arithmetic envelope domination from explicit auxiliary
parameters and residual logarithms, without an assumed density estimate. -/
theorem sourceEnvelope_le_uniform_exp
    (A B K : ℝ) (e : ℚ) (chi : ℝ) (m : ℕ) (omega T : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (told tnew : (Fin 5 → ℕ) → ℝ) (p : Fin 5 → ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ho : T ≤ told p) (hn : T ≤ tnew p)
    (hlogOld : 1 ≤ Real.log (Nat.ceil
      (P1OriginalSmallCutoffActualLowerTail.residualLevel N
        (P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p) p) : ℝ))
    (hlogNew : 1 ≤ Real.log (Nat.ceil
      (P1OriginalSmallCutoffActualLowerTail.residualLevel N
        (P1OriginalSmallCutoffActualLowerTail.newExponent
          e chi m omega J4 cap4 J5 cap5 N p) p) : ℝ)) :
    sourceEnvelope A B K e chi m omega J4 cap4 J5 cap5 N cap told tnew p ≤
      2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T) := by
  unfold sourceEnvelope
  have hold := tailEnvelope_le_uniform_exp A B K _ (told p) T hA hB ho hlogOld
  have hnew := tailEnvelope_le_uniform_exp A B K _ (tnew p) T hA hB hn hlogNew
  have hsum0 : 0 ≤
      P1OriginalSmallCutoffActualLowerTail.tailEnvelope A B K
        (P1OriginalSmallCutoffActualLowerTail.residualLevel N
          (P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p) p)
        (told p) +
      P1OriginalSmallCutoffActualLowerTail.tailEnvelope A B K
        (P1OriginalSmallCutoffActualLowerTail.residualLevel N
          (P1OriginalSmallCutoffActualLowerTail.newExponent
            e chi m omega J4 cap4 J5 cap5 N p) p) (tnew p) := by
    unfold P1OriginalSmallCutoffActualLowerTail.tailEnvelope
    positivity
  calc
    _ ≤ 1 * _ := mul_le_mul_of_nonneg_right
      (actualSmallEulerProduct_le_one N cap (p 4 : ℝ)) hsum0
    _ ≤ _ := by
      rw [one_mul]
      linarith [hold, hnew]

/-- Quantitative weightedtuple bound for the original moving fifth face.
It estimates the complete main-plus-error actual source envelope. The
inputs are pointwise auxiliary parameters, never a target remainder bound.
They may depend on N, on the tuple, and on the chosen moving a. -/
theorem terminalEnvelopeSum_le_moving_exp_harmonic
    (A B K : ℝ) (e : ℚ) (chi : ℝ) (m : ℕ) (omega a T : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (told tnew : (Fin 5 → ℕ) → ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hparameters : ∀ j ∈ selectedFifthCells e chi m omega J5,
      ∀ p ∈ (sourceCarrier e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p 4 < a),
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j →
      T ≤ told p ∧ T ≤ tnew p ∧
      1 ≤ Real.log (Nat.ceil (P1OriginalSmallCutoffActualLowerTail.residualLevel N
        (P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p) p) : ℝ) ∧
      1 ≤ Real.log (Nat.ceil (P1OriginalSmallCutoffActualLowerTail.residualLevel N
        (P1OriginalSmallCutoffActualLowerTail.newExponent
          e chi m omega J4 cap4 J5 cap5 N p) p) : ℝ)) :
    terminalEnvelopeSum A B K e chi m omega a J4 cap4 J5 cap5 N cap told tnew ≤
      (2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T)) *
        (((selectedFifthCells e chi m omega J5).card : ℝ) *
          (2 * (1 + Real.log (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ)) : ℝ))) ^ 5) := by
  have hpoint : ∀ j ∈ selectedFifthCells e chi m omega J5,
      ∀ p ∈ (sourceCarrier e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p 4 < a),
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j →
      sourceEnvelope A B K e chi m omega J4 cap4 J5 cap5 N cap told tnew p ≤
        2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T) := by
    intro j hj p hp ht
    obtain ⟨ho, hn, hlo, hln⟩ := hparameters j hj p hp ht
    exact sourceEnvelope_le_uniform_exp A B K e chi m omega T J4 cap4 J5 cap5
      N cap told tnew p hA hB ho hn hlo hln
  calc
    _ ≤ (2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T)) *
        terminalPrimeMass e chi m omega a J5 N cap :=
      terminalEnvelopeSum_le_pointwise_bound_mul_mass A B K e chi m omega a
        (2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T))
        J4 cap4 J5 cap5 N cap told tnew hpoint
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (terminalPrimeMass_le_moving_harmonic_bound e chi m omega a J5 N cap hN hcap)
      (by positivity)

/-- The literal signed original fifth remainder has an explicit bound for
EVERY moving a,T satisfying four scalar source-budget inequalities. Both
gates and legal tuple budgets are proved from the original third geometry.
In particular the conclusion has no supplied source-envelope or uniform
remainder premise. The finite h34 compatibility remains visible.

For example a=omega/(16 log log N), T=8 log log N has a*T=omega/2;
the remaining scalar inequalities are eventual elementary log inequalities.
This module does not assert the final iterated a-to-zero mean passage. -/
theorem exists_original_smallRemainder_moving_exp_harmonic_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
    ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a T : ℝ)
    (homega : 0 < omega) (ha : a ≤ omega / 6)
    (hT : 2 ≤ T) (haT : a * T ≤ omega / 2)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (h34 : ∀ j ∈ selectedFifthCells e chi m omega J5,
      HistoricalThirdCoarse.levelExponent (e : ℝ)
        (HistoricalThirdCoarse.box m (thirdOwner j)) ≤ (old5 e chi m omega J4 cap4 j : ℝ))
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (hbudget : T ^ 13 ≤ (omega / 2) * Real.log (N : ℝ))
    (hlog : Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ)),
      |P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N cap| ≤
        |Real.log (N : ℝ) / singularSeries N| *
          ((2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T)) *
            (((selectedFifthCells e chi m omega J5).card : ℝ) *
              (2 * (1 + Real.log (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ)) : ℝ))) ^ 5)) := by
  obtain ⟨A, B, K, hA, hB, hK, hpoint⟩ :=
    P1OriginalSmallCutoffActualLowerTail.exists_originalDifference_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro e chi m omega a T homega ha hT haT J4 cap4 J5 cap5 h45 h34
    N cap hN hEven hcap hbudget hlog
  have hlegal : ∀ j ∈ selectedFifthCells e chi m omega J5,
      ∀ p ∈ (sourceCarrier e chi m omega N cap).filter
        (fun p => ∃ i, actualPrimeTupleLog N p i < a),
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j →
      (∀ i, 0 < p i) ∧ 1 < (p 4 : ℝ) ∧ (p 4 : ℝ) ≤ (cap : ℝ) ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^
        P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^
        P1OriginalSmallCutoffActualLowerTail.newExponent e chi m omega J4 cap4 J5 cap5 N p ∧
      P1OriginalSmallCutoffActualLowerTail.sourceBudget (p 4 : ℝ)
        (P1OriginalSmallCutoffActualLowerTail.residualLevel N
          (P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p) p) T ∧
      P1OriginalSmallCutoffActualLowerTail.sourceBudget (p 4 : ℝ)
        (P1OriginalSmallCutoffActualLowerTail.residualLevel N
          (P1OriginalSmallCutoffActualLowerTail.newExponent e chi m omega J4 cap4 J5 cap5 N p) p) T := by
    intro j hj p hp ht
    obtain ⟨hp, hsmall⟩ := Finset.mem_filter.mp hp
    have hc : p ∈ candidates (e : ℝ) chi m omega N cap := by
      simpa only [sourceCarrier, candidates] using hp
    have hd := (mem_candidates_iff_log_on_cell (e : ℝ) chi m omega N cap hN hcap p j ht).mp hc
    have hanti := ((mem_jointRegion (e : ℝ) chi m omega j _).mp hd.2).2.1
    have hf := P1OriginalFifthAllFacesAnalyticTail.last_lt_of_any_coordinate_lt
      (actualPrimeTupleLog N p) hanti hsmall
    exact original_selected_legal_uniform_budget e chi m omega a T homega ha hT haT
      N cap hN hcap hbudget hlog J4 cap4 J5 cap5 h45 j hj (h34 j hj) p hp ht hf
  let told : (Fin 5 → ℕ) → ℝ := fun _ => T
  let tnew : (Fin 5 → ℕ) → ℝ := fun _ => T
  have hbound : |P1OriginalFifthLimit.smallRemainder e chi m omega a
      J4 cap4 J5 cap5 N cap| ≤ |Real.log (N : ℝ) / singularSeries N| *
        weightedEnvelopeSum A B K e chi m omega a J4 cap4 J5 cap5
          N cap told tnew := by
    rw [smallRemainder_eq_weighted_actual_source e chi m omega a
      J4 cap4 J5 cap5 N cap hN]
    have hsum :
        |∑ j ∈ selectedFifthCells e chi m omega J5,
          ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
            (fun p => ∃ i, actualPrimeTupleLog N p i < a),
          (∏ i, 1 / ((p i : ℝ) - 1)) *
            (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
              P1OriginalSmallCutoffActualLowerTail.originalDifference
                e chi m omega J4 cap4 J5 cap5 N cap p *
                  Real.log (N : ℝ) / singularSeries N else 0)| ≤
        ∑ j ∈ selectedFifthCells e chi m omega J5,
          ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
            (fun p => ∃ i, actualPrimeTupleLog N p i < a),
          |∏ i, 1 / ((p i : ℝ) - 1)| *
            (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
              sourceEnvelope A B K e chi m omega J4 cap4 J5 cap5
                N cap told tnew p *
                  |Real.log (N : ℝ) / singularSeries N| else 0) := by
      calc
        _ ≤ ∑ j ∈ selectedFifthCells e chi m omega J5,
            |∑ p ∈ (sourceCarrier e chi m omega N cap).filter
              (fun p => ∃ i, actualPrimeTupleLog N p i < a),
              (∏ i, 1 / ((p i : ℝ) - 1)) *
                (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
                  P1OriginalSmallCutoffActualLowerTail.originalDifference
                    e chi m omega J4 cap4 J5 cap5 N cap p *
                      Real.log (N : ℝ) / singularSeries N else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          apply Finset.sum_le_sum
          intro p hp
          by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
          · obtain ⟨hpos, hy, hcap, hgate4, hgate5, ho, hn⟩ := hlegal j hj p hp ht
            have hb := hpoint e chi m omega J4 cap4 J5 cap5 N cap p
              hEven hpos hy hcap hgate4 hgate5 (told p) (tnew p) ho hn
            have hshape :
                P1OriginalSmallCutoffActualLowerTail.originalDifference
                    e chi m omega J4 cap4 J5 cap5 N cap p *
                      Real.log (N : ℝ) / singularSeries N =
                  P1OriginalSmallCutoffActualLowerTail.originalDifference
                    e chi m omega J4 cap4 J5 cap5 N cap p *
                      (Real.log (N : ℝ) / singularSeries N) := by ring
            rw [if_pos ht, if_pos ht, abs_mul, hshape, abs_mul]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hb (abs_nonneg _)) (abs_nonneg _)
          · simp only [if_neg ht, mul_zero, abs_zero]
    calc
      _ ≤ _ := hsum
      _ = |Real.log (N : ℝ) / singularSeries N| *
          weightedEnvelopeSum A B K e chi m omega a J4 cap4 J5 cap5
            N cap told tnew := by
        unfold weightedEnvelopeSum
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro p _hp
        split_ifs <;> ring
  
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [weightedEnvelopeSum_eq_terminalEnvelopeSum A B K e chi m omega a
    J4 cap4 J5 cap5 N cap hN hcap (fun _ => T) (fun _ => T)]
  apply terminalEnvelopeSum_le_moving_exp_harmonic A B K e chi m omega a T
    J4 cap4 J5 cap5 N cap hN hcap (fun _ => T) (fun _ => T) hA.le hB.le
  intro j hj p hp ht
  obtain ⟨hp, hf⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, _, _, _, _, ho, hn⟩ := original_selected_legal_uniform_budget
    e chi m omega a T homega ha hT haT N cap hN hcap hbudget hlog
      J4 cap4 J5 cap5 h45 j hj (h34 j hj) p hp ht hf
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1))
  exact ⟨le_rfl, le_rfl, he.trans ho.2.2.2, he.trans hn.2.2.2⟩

end

end ImbalancedChen.P1OriginalFifthMovingHarmonicEnvelope
