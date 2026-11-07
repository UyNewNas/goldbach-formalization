import ImbalancedChen.Part5OriginalH430ClassicalTailBV
import ImbalancedChen.P4BLogSavingBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Complete the actual initial U3 classical-tail row error. The Q supplier
already pays its true-li AP component. Here the literal-li constant and
the signed centre-prime deletion are paid at the unchanged row modulus,
then the result is inserted into the existing immutable arithmetic count.

This is an ordinary initial count estimate. No adopted positive seed,
old H/h analytic licence, H430 interpretation, or hstarts is asserted.
All proof bodies below, including finite simplifications, are UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalClassicalTailFullError

noncomputable section
open Set Finset Filter Topology Wu2008DoubleSieve
open scoped Classical BigOperators
open Part5UpperTables.OriginalU34 Part5UpperTables.OriginalU34.CountEntrance
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430ClassicalTailBV
open P2ActualMarkedCountState (Query rootLevel)
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.BombieriVinogradov

/-- The original inclusive tail boundary, inside the original strict
outer prime selector. No root square condition is added. -/
def tailPrimes (N : ℕ) : Finset ℕ :=
  (originalU3Primes N).filter (fun p => tailCutoff ≤ primeCoordinate N p)

def tailRowError (side : Bool) (N : ℕ) (tau : ℝ) : ℝ :=
  ∑ p ∈ originalU3Primes N,
    if tailCutoff ≤ primeCoordinate N p then rowError side N p (U3Residual tau) else 0

/-- Both deterministic atoms keep their original signs under the signed
Rosser coefficient. The modulus is the complete product p*q. -/
def tailLiCentreCorrection (side : Bool) (N : ℕ) (tau : ℝ) : ℝ :=
  ∑ p ∈ originalU3Primes N, ∑ q ∈ tailActive side N tau p,
    rowWeight side N p (U3Residual tau) q *
      ((2 / Real.log 2) / (Nat.totient (p*q) : ℝ) - chenCentrePrimeAPCount N N (p*q))

theorem tailRowError_eq_tailPrimes (side : Bool) (N : ℕ) (tau : ℝ) :
    tailRowError side N tau = ∑ p ∈ tailPrimes N, rowError side N p (U3Residual tau) := by
  simp only [tailRowError, tailPrimes, sum_filter]

private theorem row_sum_eq_active (side : Bool) (N p : ℕ) (r : ℝ → ℝ)
    (f : ℕ → ℝ) :
    (∑ q ∈ rowDivisors N p r, rowWeight side N p r q * f q) =
      ∑ q ∈ rowActive side N p r, rowWeight side N p r q * f q := by
  symm
  apply sum_subset (filter_subset _ _)
  intro q hq hnot
  have hz : rowWeight side N p r q = 0 := by
    by_contra hne
    exact hnot (mem_filter.mpr ⟨hq, hne⟩)
  simp only [hz, zero_mul]

/-- The paid AP term is a component of the literal original rowError;
there is no source equality or error decomposition premise. -/
theorem tailRowError_eq_trueLi_components (side : Bool) (N : ℕ) (tau : ℝ) :
    tailRowError side N tau =
      tailSignedPrimeAP side N tau + tailLiCentreCorrection side N tau := by
  unfold tailRowError tailSignedPrimeAP tailLiCentreCorrection
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  by_cases ht : tailCutoff ≤ primeCoordinate N p
  · simp only [if_pos ht, tailActive]
    simp only [if_pos ht]
    rw [rowError_eq_trueLi_components, row_sum_eq_active, ← sum_add_distrib]
    apply sum_congr rfl
    intro q _
    ring
  · simp only [if_neg ht, tailActive, if_neg ht, sum_empty, add_zero]

private theorem tailActive_card_le {N p : ℕ} {tau : ℝ}
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hp : p ∈ originalU3Primes N) (side : Bool) :
    ((tailActive side N tau p).card : ℝ) ≤ (N : ℝ)^(1/2 : ℝ) := by
  have hpc := primeCoordinate_mem hN hp
  have hr := U3Residual_bounds htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hpp : 0 < p := by
    have h := (chenSinglePrimeSelector_sieve_data hp).1
    omega
  by_cases ht : tailCutoff ≤ primeCoordinate N p
  · simpa only [tailActive, if_pos ht] using rowActive_card_le hN hpp hr.2 side
  · simp only [tailActive, if_neg ht, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _

/-- Existing deterministic centre bounds and phi(m)>=1 pay the actual
recentring atom. No prime-distribution estimate is used in this step. -/
private theorem liCentre_atom_abs_le {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    |(2 / Real.log 2) / (Nat.totient m : ℝ) - chenCentrePrimeAPCount N N m| ≤
      (2 / Real.log 2) * (1 + Real.log (N : ℝ)) := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hc : 0 ≤ (2 / Real.log 2 : ℝ) := by positivity
  have hphi : (1 : ℝ) ≤ Nat.totient m := by
    exact_mod_cast (show 1 ≤ Nat.totient m from Nat.totient_pos.mpr hm)
  have hphipos : (0 : ℝ) < Nat.totient m := lt_of_lt_of_le zero_lt_one hphi
  have ha0 : 0 ≤ (2 / Real.log 2) / (Nat.totient m : ℝ) := by positivity
  have ha : (2 / Real.log 2) / (Nat.totient m : ℝ) ≤ 2 / Real.log 2 :=
    (div_le_iff₀ hphipos).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hphi hc])
  have hb0 := chenCentrePrimeAPCount_nonneg N N m
  have hb := (chenCentrePrimeAPCount_le_divisorCount N N m).trans
    (chenPrimeDivisorCount_le_log N hN)
  have hlogN := Real.log_natCast_nonneg N
  have habs : |(2 / Real.log 2) / (Nat.totient m : ℝ) -
      chenCentrePrimeAPCount N N m| ≤
      (2 / Real.log 2) / (Nat.totient m : ℝ) + chenCentrePrimeAPCount N N m :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  refine habs.trans ((add_le_add ha hb).trans ?_)
  have hB : 0 ≤ Real.log (N : ℝ) / Real.log 2 := div_nonneg hlogN hlogtwo.le
  nlinarith only [hB]

/-- A finite, unconditional sublinear budget for exactly the missing
two atoms. K's actual row/selector cardinality bounds are reused. -/
theorem tailLiCentreCorrection_abs_le {N : ℕ} {tau : ℝ}
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (side : Bool) :
    |tailLiCentreCorrection side N tau| ≤
      (2 / Real.log 2) * (N : ℝ)^(5/6 : ℝ) * (1 + Real.log (N : ℝ)) := by
  let B : ℝ := (2 / Real.log 2) * (1 + Real.log (N : ℝ))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (div_nonneg (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
      (add_nonneg zero_le_one (Real.log_natCast_nonneg N))
  have hpoint (p : ℕ) (hp : p ∈ originalU3Primes N) :
      |∑ q ∈ tailActive side N tau p,
        rowWeight side N p (U3Residual tau) q *
          ((2 / Real.log 2) / (Nat.totient (p*q) : ℝ) -
            chenCentrePrimeAPCount N N (p*q))| ≤ (N : ℝ)^(1/2 : ℝ) * B := by
    have hterm (q : ℕ) (hq : q ∈ tailActive side N tau p) :
        |rowWeight side N p (U3Residual tau) q *
          ((2 / Real.log 2) / (Nat.totient (p*q) : ℝ) -
            chenCentrePrimeAPCount N N (p*q))| ≤ B := by
      have hm := (tail_complete_modulus hN htau htauhi hp hq).1
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right
        (ordinaryRosserWeight_abs_le_one side N p
          (rootLevel (rowTotalLevel N p (U3Residual tau)) p) q
          (rowCutoff N p (U3Residual tau))) (abs_nonneg _)).trans
        (by simpa only [one_mul] using liCentre_atom_abs_le (by omega : 0 < N) hm)
    calc
      _ ≤ ∑ q ∈ tailActive side N tau p,
          |rowWeight side N p (U3Residual tau) q *
            ((2 / Real.log 2) / (Nat.totient (p*q) : ℝ) -
              chenCentrePrimeAPCount N N (p*q))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ tailActive side N tau p, B := sum_le_sum hterm
      _ = ((tailActive side N tau p).card : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (tailActive_card_le hN htau htauhi hp side) hB
  unfold tailLiCentreCorrection
  calc
    _ ≤ ∑ p ∈ originalU3Primes N,
        |∑ q ∈ tailActive side N tau p,
          rowWeight side N p (U3Residual tau) q *
            ((2 / Real.log 2) / (Nat.totient (p*q) : ℝ) -
              chenCentrePrimeAPCount N N (p*q))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ originalU3Primes N, (N : ℝ)^(1/2 : ℝ) * B := sum_le_sum hpoint
    _ = ((originalU3Primes N).card : ℝ) * ((N : ℝ)^(1/2 : ℝ) * B) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ)^(1/3 : ℝ) * ((N : ℝ)^(1/2 : ℝ) * B) :=
      mul_le_mul_of_nonneg_right (selector_card_le_third_power hN (le_refl (1/3 : ℝ)))
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) hB)
    _ = _ := by
      rw [show (5/6 : ℝ) = 1/3 + 1/2 by norm_num,
        Real.rpow_add (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)]
      dsimp [B]
      ring

/-- The threshold is before tau and the two signs; no count premise. -/
theorem eventually_tailLiCentreCorrection_logAccuracy (A : ℕ)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 → ∀ side : Bool,
      |tailLiCentreCorrection side N tau| ≤ epsilon * (N : ℝ) / Real.log (N : ℝ)^A := by
  filter_upwards [eventually_powerLog_le_logAccuracy (2 / Real.log 2) (5/6) 0 A
    (by norm_num) (epsilon/2) (half_pos he),
    eventually_powerLog_le_logAccuracy (2 / Real.log 2) (5/6) 1 A
      (by norm_num) (epsilon/2) (half_pos he), eventually_ge_atTop (2 : ℕ)]
    with N hzero hone hN
  intro tau htau htauhi side
  have h := tailLiCentreCorrection_abs_le hN htau htauhi side
  simp only [pow_zero, mul_one] at hzero
  simp only [pow_one] at hone
  nlinarith only [h, hzero, hone]

theorem eventually_tailLiCentreCorrection_normalized (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 → ∀ side : Bool,
      |tailLiCentreCorrection side N tau| ≤ epsilon * singularNormalization N := by
  filter_upwards [eventually_powerLog_le_singularNormalization (2 / Real.log 2) (5/6) 0
    (by norm_num) (epsilon/2) (half_pos he),
    eventually_powerLog_le_singularNormalization (2 / Real.log 2) (5/6) 1
      (by norm_num) (epsilon/2) (half_pos he), eventually_ge_atTop (2 : ℕ)]
    with N hzero hone hN
  intro tau htau htauhi side
  have h := tailLiCentreCorrection_abs_le hN htau htauhi side
  simp only [pow_zero, mul_one] at hzero
  simp only [pow_one] at hone
  nlinarith only [h, hzero, hone]

/-- The FULL original error is now paid. Fixed tau is chosen before N;
the AP threshold is not claimed uniform as tau tends to zero. -/
theorem eventually_tailRowError_normalized {tau : ℝ}
    (htau : 0 < tau) (htauhi : tau ≤ 1/12) (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ side : Bool,
      |tailRowError side N tau| ≤ epsilon * singularNormalization N := by
  obtain ⟨C, hC, hAP⟩ := eventually_tailSignedPrimeAP_log_saving htau htauhi 3 (by norm_num)
  filter_upwards [hAP, eventually_logSaving_le_singularNormalization C hC.le 3 (by norm_num)
    (epsilon/2) (half_pos he),
    eventually_tailLiCentreCorrection_normalized (epsilon/2) (half_pos he)]
    with N hAPN hlog hcorrection
  intro side
  have hrawAP : |tailSignedPrimeAP side N tau| ≤ C*(N : ℝ)/Real.log (N : ℝ)^(3 : ℕ) := by
    simpa only [Real.rpow_ofNat] using hAPN side
  have hpaidAP : |tailSignedPrimeAP side N tau| ≤ (epsilon/2) * singularNormalization N :=
    hrawAP.trans hlog.2
  rw [tailRowError_eq_trueLi_components]
  exact (abs_add_le _ _).trans (by
    have hc := hcorrection tau htau.le htauhi side
    linarith)

def tailCount (N : ℕ) (tau : ℝ) : ℝ :=
  ∑ p ∈ tailPrimes N,
    ((chenSiftedQuotientPrimeSource N p (rowCutoff N p (U3Residual tau))).card : ℝ)

def tailSeed (side : Bool) (N : ℕ) (tau eta : ℝ) : ℝ :=
  ∑ p ∈ tailPrimes N, rowSeed side N p (U3Residual tau) eta

def tailStateLower (N : ℕ) (tau : ℝ) (bank : List Query) (rounds : ℕ) : ℝ :=
  ∑ p ∈ tailPrimes N,
    (rowState N p (U3Residual tau) bank rounds).lower p (rowCutoff N p (U3Residual tau))

def tailStateUpper (N : ℕ) (tau : ℝ) (bank : List Query) (rounds : ℕ) : ℝ :=
  ∑ p ∈ tailPrimes N,
    (rowState N p (U3Residual tau) bank rounds).upper p (rowCutoff N p (U3Residual tau))

/-- Actual arithmetic counts between the unchanged initial Rosser main
terms, with both errors paid. The middle old-state enclosure is the
existing immutable recursion, not a new assumed count licence. -/
theorem eventually_tail_count_initial_enclosure {tau eta epsilon : ℝ}
    (htau : 0 < tau) (htauhi : tau ≤ 1/12) (heta : 0 < eta) (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ bank : List Query, ∀ rounds : ℕ,
      tailSeed false N tau eta - epsilon * singularNormalization N ≤
          tailStateLower N tau bank rounds ∧
      tailStateLower N tau bank rounds ≤ tailCount N tau ∧
      tailCount N tau ≤ tailStateUpper N tau bank rounds ∧
      tailStateUpper N tau bank rounds ≤
          tailSeed true N tau eta + epsilon * singularNormalization N := by
  obtain ⟨N0, hN0, hseed⟩ := row_seed_and_joint_count heta
  filter_upwards [eventually_ge_atTop N0,
    eventually_tailRowError_normalized htau htauhi epsilon he]
    with N hN herr
  intro hEven bank rounds
  have hN2 : 2 ≤ N := by omega
  have hrow (p : ℕ) (hp : p ∈ tailPrimes N) := by
    have hp' := (mem_filter.mp hp).1
    have hpc := primeCoordinate_mem hN2 hp'
    have hr := U3Residual_bounds htau.le htauhi ⟨hpc.1, hpc.2.le⟩
    exact hseed N hN hEven (1/3) p hp' (U3Residual tau) hr.1 hr.2 bank rounds
  have hlo := sum_le_sum (fun p hp => (hrow p hp).1)
  have hmidlo := sum_le_sum (fun p hp => (hrow p hp).2.1)
  have hmidhi := sum_le_sum (fun p hp => (hrow p hp).2.2.1)
  have hhi := sum_le_sum (fun p hp => (hrow p hp).2.2.2)
  have hloerr := (abs_le.mp (herr false)).1
  have hhierr := (abs_le.mp (herr true)).2
  rw [tailRowError_eq_tailPrimes] at hloerr hhierr
  simp only [sum_add_distrib] at hlo hhi
  change tailSeed false N tau eta +
    (∑ p ∈ tailPrimes N, rowError false N p (U3Residual tau)) ≤
      tailStateLower N tau bank rounds at hlo
  change tailStateUpper N tau bank rounds ≤ tailSeed true N tau eta +
    (∑ p ∈ tailPrimes N, rowError true N p (U3Residual tau)) at hhi
  exact ⟨by linarith, hmidlo, hmidhi, by linarith⟩

end
end ImbalancedChen.Part5OriginalClassicalTailFullError
