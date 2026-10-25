import ImbalancedChen.P1OriginalCoarseFifthContinuationCells
import ImbalancedChen.P1OriginalHistoricalSmallCoordinateGap
import ImbalancedChen.P1OriginalSmallCutoffActualUpperTail
import ImbalancedChen.ActualLowerRosserBoundaryExpansion
import ImbalancedChen.ActualThirdPrefixTailIntegralCore
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLiteralAllDepthLowerRosserExact

/-!
# Same-cutoff actual lower residual differences in the original small-last region

The Euler baseline is cancelled exactly before taking absolute values. The
actual lower deficit is the pinned finite even-depth actual Suzuki T, not an
asymptotic lower profile. The shared upper-tail task supplies its exponential
bound with an explicit auxiliary-parameter power budget. No fixed positive
lower exponent for the terminal prime is imposed in that bound.

This source-only file proves pointwise arithmetic estimates. It does not
assert uniform summability of the adaptive source error over all small-last
tuples, or discharge the original I5 smallRemainder as a tends-to-zero mean.
-/

namespace ImbalancedChen.P1OriginalSmallCutoffActualLowerTail
noncomputable section
open scoped Classical List BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open P1OriginalSmallCutoffActualTail

/-- The actual deficit from the same target-deleted Euler product. -/
def lowerDeficit (N cap : ℕ) (y R : ℝ) : ℝ :=
  actualSmallEulerProduct N cap y - actualSmallRosserMinusDensity N cap y R

/-- The same cutoff is essential for exact baseline cancellation. -/
theorem actualMinus_sub_eq_deficit_sub (N cap : ℕ) (y Rold Rnew : ℝ) :
    actualSmallRosserMinusDensity N cap y Rnew - actualSmallRosserMinusDensity N cap y Rold =
      lowerDeficit N cap y Rold - lowerDeficit N cap y Rnew := by
  unfold lowerDeficit
  ring

theorem lowerDeficit_nonneg (N cap : ℕ) (hEven : Even N) (y R : ℝ)
    (hcap : y ≤ (cap : ℝ)) (hy : 1 < y) (hyR : y ≤ R) :
    0 ≤ lowerDeficit N cap y R := by
  have hratio := actualSmallRosserMinusDensity_ratio_le_selected_boundary N cap hEven y R hcap
    (hy.trans_le hyR)
    (fun p hp => (mem_actualSmallPrimeFinset.mp hp).2.2.2.trans_le hyR)
    ∅ (fun _ => ∅) (by simp) (by simp)
  have hV := actualSmallEulerProduct_pos N cap y hEven
  have hbound : actualSmallRosserMinusDensity N cap y R / actualSmallEulerProduct N cap y ≤ 1 := by
    simpa using hratio
  unfold lowerDeficit
  apply sub_nonneg.mpr
  simpa only [one_mul] using (div_le_iff₀ hV).mp hbound

theorem abs_actualMinus_sub_le_deficits (N cap : ℕ) (hEven : Even N)
    (y Rold Rnew : ℝ) (hcap : y ≤ (cap : ℝ)) (hy : 1 < y)
    (hold : y ≤ Rold) (hnew : y ≤ Rnew) :
    |actualSmallRosserMinusDensity N cap y Rnew - actualSmallRosserMinusDensity N cap y Rold| ≤
      lowerDeficit N cap y Rold + lowerDeficit N cap y Rnew := by
  rw [actualMinus_sub_eq_deficit_sub]
  have ho := lowerDeficit_nonneg N cap hEven y Rold hcap hy hold
  have hn := lowerDeficit_nonneg N cap hEven y Rnew hcap hy hnew
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For the signed saving upper bound only the old deficit is needed.
No monotonicity of the finite lower weights or the two levels is asserted. -/
theorem actualMinus_sub_le_old_deficit (N cap : ℕ) (hEven : Even N)
    (y Rold Rnew : ℝ) (hcap : y ≤ (cap : ℝ)) (hy : 1 < y) (hnew : y ≤ Rnew) :
    actualSmallRosserMinusDensity N cap y Rnew - actualSmallRosserMinusDensity N cap y Rold ≤
      lowerDeficit N cap y Rold := by
  rw [actualMinus_sub_eq_deficit_sub]
  exact sub_le_self _ (lowerDeficit_nonneg N cap hEven y Rnew hcap hy hnew)

/-- Exact finite lower-source identity at any smaller legal auxiliary t.
R, ceil R, the actual coefficient and the actual cutoff y are unchanged. -/
theorem lowerDeficit_eq_actualT (N cap : ℕ) (hEven : Even N)
    (y R t : ℝ) (hcap : y ≤ (cap : ℝ)) (hy : 1 < y) (hyR : y ≤ R)
    (ht : 2 ≤ t) (hpower : y ^ t ≤ R) :
    lowerDeficit N cap y R =
      suzukiActualT (goldbachB8PlusBoundingSieve N hEven y)
        (2 * ((suzukiSupportedBelow (goldbachB8PlusBoundingSieve N hEven y)
          (Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t)))).card + 1))
        (Nat.ceil R) (Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t))) := by
  let S := goldbachB8PlusBoundingSieve N hEven y
  let D : ℕ := Nat.ceil R
  let z : ℕ := Nat.ceil ((D : ℝ) ^ (1 / t))
  obtain ⟨hD, hcover, _hz⟩ := root_covers_actual_cutoff y R t hy hyR ht hpower
  have hcut : ∀ p ∈ S.prodPrimes.primeFactors, p < z :=
    actual_suzuki_cutoff_all_primes N hEven y R t hcover
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hinv : 1 / t ≤ (1 : ℝ) := (div_le_iff₀ (by linarith : 0 < t)).mpr (by linarith)
  have hzD : z ≤ D := by
    apply Nat.ceil_le.mpr
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hDreal hinv
  have hmain := actualSmallRosserMinusDensity_eq_b8_mainSum_natCeil N cap hEven y R hcap
  rw [mainSum_lowerRosserWeight_eq_suzukiLowerDensity_of_all_lt S D hcut,
    lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_all_supported S (by omega : 1 < D) hzD,
    sourceDiscreteEuler_eq_suzukiVProduct_nat S z,
    actual_suzukiVProduct_eq_euler N cap hEven y R t hcap hcover] at hmain
  change actualSmallRosserMinusDensity N cap y R = actualSmallEulerProduct N cap y -
    suzukiActualT (goldbachB8PlusBoundingSieve N hEven y)
      (2 * ((suzukiSupportedBelow (goldbachB8PlusBoundingSieve N hEven y)
        (Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t)))).card + 1))
      (Nat.ceil R) (Nat.ceil ((Nat.ceil R : ℝ) ^ (1 / t))) at hmain
  unfold lowerDeficit
  linarith only [hmain]

/-- The two pieces are the proved source tail and the actual explicit source
error. This notation carries no asymptotic or summability assertion. -/
def tailEnvelope (A B K R t : ℝ) : ℝ :=
  A * Real.exp (-t) + B * Real.exp (Real.sqrt K) * Real.exp (-t) *
    (Real.log (Nat.ceil R : ℝ)) ^ (-(1 / 3 : ℝ))

/-- Genuine all-target, all-cutoff lower deficit bound, reusing the upper
task's pinned actual-T supplier. No analytic supplier is assumed by the caller. -/
theorem exists_actualMinus_deficit_exp_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      ∀ N cap : ℕ, Even N → ∀ y R t : ℝ,
        y ≤ (cap : ℝ) → 1 < y → y ≤ R → 2 ≤ t → y ^ t ≤ R →
        t ^ 13 ≤ Real.log (Nat.ceil R : ℝ) →
        Real.exp 1 ≤ Real.log (Nat.ceil R : ℝ) →
        0 ≤ lowerDeficit N cap y R ∧
          lowerDeficit N cap y R ≤ actualSmallEulerProduct N cap y * tailEnvelope A B K R t := by
  obtain ⟨A, B, K, hA, hB, hK, hsource⟩ := exists_actual_goldbachT_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro N cap hEven y R t hcap hy hyR ht hpower hbudget hlog
  refine ⟨lowerDeficit_nonneg N cap hEven y R hcap hy hyR, ?_⟩
  rw [lowerDeficit_eq_actualT N cap hEven y R t hcap hy hyR ht hpower]
  exact hsource N cap hEven y R t _ hcap hy hyR ht hpower hbudget hlog (by omega)

/-- Same-cutoff signed difference with its exactly cancelled Euler baseline.
The auxiliary parameters may move with N, y and the residual levels. -/
theorem exists_actualMinus_pair_exp_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      ∀ N cap : ℕ, Even N → ∀ y Rold Rnew told tnew : ℝ,
        y ≤ (cap : ℝ) → 1 < y → y ≤ Rold → y ≤ Rnew →
        2 ≤ told → 2 ≤ tnew → y ^ told ≤ Rold → y ^ tnew ≤ Rnew →
        told ^ 13 ≤ Real.log (Nat.ceil Rold : ℝ) →
        tnew ^ 13 ≤ Real.log (Nat.ceil Rnew : ℝ) →
        Real.exp 1 ≤ Real.log (Nat.ceil Rold : ℝ) →
        Real.exp 1 ≤ Real.log (Nat.ceil Rnew : ℝ) →
        |actualSmallRosserMinusDensity N cap y Rnew - actualSmallRosserMinusDensity N cap y Rold| ≤
          actualSmallEulerProduct N cap y *
            (tailEnvelope A B K Rold told + tailEnvelope A B K Rnew tnew) := by
  obtain ⟨A, B, K, hA, hB, hK, hbound⟩ := exists_actualMinus_deficit_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro N cap hEven y Rold Rnew told tnew hcap hy hold hnew htold htnew
    hpowerOld hpowerNew hbudgetOld hbudgetNew hlogOld hlogNew
  have ho := hbound N cap hEven y Rold told hcap hy hold htold hpowerOld hbudgetOld hlogOld
  have hn := hbound N cap hEven y Rnew tnew hcap hy hnew htnew hpowerNew hbudgetNew hlogNew
  calc
    _ ≤ lowerDeficit N cap y Rold + lowerDeficit N cap y Rnew :=
      abs_actualMinus_sub_le_deficits N cap hEven y Rold Rnew hcap hy hold hnew
    _ ≤ actualSmallEulerProduct N cap y * tailEnvelope A B K Rold told +
        actualSmallEulerProduct N cap y * tailEnvelope A B K Rnew tnew := add_le_add ho.2 hn.2
    _ = _ := by ring

theorem exists_actualMinus_signed_exp_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      ∀ N cap : ℕ, Even N → ∀ y Rold Rnew t : ℝ,
        y ≤ (cap : ℝ) → 1 < y → y ≤ Rold → y ≤ Rnew → 2 ≤ t → y ^ t ≤ Rold →
        t ^ 13 ≤ Real.log (Nat.ceil Rold : ℝ) →
        Real.exp 1 ≤ Real.log (Nat.ceil Rold : ℝ) →
        actualSmallRosserMinusDensity N cap y Rnew - actualSmallRosserMinusDensity N cap y Rold ≤
          actualSmallEulerProduct N cap y * tailEnvelope A B K Rold t := by
  obtain ⟨A, B, K, hA, hB, hK, hbound⟩ := exists_actualMinus_deficit_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro N cap hEven y Rold Rnew t hcap hy hold hnew ht hpower hbudget hlog
  exact (actualMinus_sub_le_old_deficit N cap hEven y Rold Rnew hcap hy hnew).trans
    (hbound N cap hEven y Rold t hcap hy hold ht hpower hbudget hlog).2

def history5 (p : Fin 5 → ℕ) : List ℕ := (List.ofFn p).reverse

theorem history5_prod (p : Fin 5 → ℕ) : (history5 p).prod = ∏ i, p i := by
  simp [history5, List.prod_ofFn]

theorem history5_head (p : Fin 5 → ℕ) : (history5 p).headD 0 = p 4 := by
  simp [history5, List.ofFn_succ]

def residualLevel (N : ℕ) (lambda : ℝ) (p : Fin 5 → ℕ) : ℝ :=
  (N : ℝ) ^ lambda / (∏ i, p i : ℕ)

def tupleGatedMinus (N cap : ℕ) (lambda : ℝ) (p : Fin 5 → ℕ) : ℝ :=
  actualOwnCubeGatedMinusDensity N cap (fun _ => (N : ℝ) ^ lambda) (history5 p)

theorem tupleGatedMinus_of_gate (N cap : ℕ) (lambda : ℝ) (p : Fin 5 → ℕ)
    (hgate : (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ lambda) :
    tupleGatedMinus N cap lambda p = actualSmallRosserMinusDensity N cap (p 4 : ℝ)
      (residualLevel N lambda p) := by
  simp only [tupleGatedMinus, actualOwnCubeGatedMinusDensity, history5_prod,
    history5_head, if_pos hgate, residualLevel]

theorem tuple_gated_sub_cancel (N cap : ℕ) (lambda4 lambda5 : ℝ) (p : Fin 5 → ℕ)
    (h4 : (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ lambda4)
    (h5 : (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ lambda5) :
    tupleGatedMinus N cap lambda5 p - tupleGatedMinus N cap lambda4 p =
      lowerDeficit N cap (p 4 : ℝ) (residualLevel N lambda4 p) -
        lowerDeficit N cap (p 4 : ℝ) (residualLevel N lambda5 p) := by
  rw [tupleGatedMinus_of_gate N cap lambda5 p h5,
    tupleGatedMinus_of_gate N cap lambda4 p h4, actualMinus_sub_eq_deficit_sub]

def oldExponent (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (P1OriginalCoarseFifthContinuation.Label4 m))
    (cap4 : P1OriginalCoarseFifthContinuation.Label4 m → ℚ)
    (N : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  (P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 (N : ℝ)
    (rosserAncestor 4 (history5 p)) : ℝ)

def newExponent (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (P1OriginalCoarseFifthContinuation.Label4 m))
    (cap4 : P1OriginalCoarseFifthContinuation.Label4 m → ℚ)
    (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
    (cap5 : P1OriginalCoarseFifthContinuation.Label5 m → ℚ)
    (N : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  P1OriginalCoarseFifthContinuation.effectiveExponent5 e chi m omega J4 cap4 J5 cap5
    (N : ℝ) (history5 p)

/-- Literal new5-minus-old4 actual gated lower residual, at exactly p5. -/
def originalDifference (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (P1OriginalCoarseFifthContinuation.Label4 m))
    (cap4 : P1OriginalCoarseFifthContinuation.Label4 m → ℚ)
    (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
    (cap5 : P1OriginalCoarseFifthContinuation.Label5 m → ℚ)
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  actualOwnCubeGatedMinusDensity N cap
      (P1OriginalCoarseFifthContinuation.level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) (history5 p) -
    actualOwnCubeGatedMinusDensity N cap
      (fun pre => P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)
        (rosserAncestor 4 pre)) (history5 p)

theorem originalDifference_eq_tuple (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (P1OriginalCoarseFifthContinuation.Label4 m))
    (cap4 : P1OriginalCoarseFifthContinuation.Label4 m → ℚ)
    (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
    (cap5 : P1OriginalCoarseFifthContinuation.Label5 m → ℚ)
    (N cap : ℕ) (p : Fin 5 → ℕ) :
    originalDifference e chi m omega J4 cap4 J5 cap5 N cap p =
      tupleGatedMinus N cap (newExponent e chi m omega J4 cap4 J5 cap5 N p) p -
        tupleGatedMinus N cap (oldExponent e chi m omega J4 cap4 N p) p := by rfl

theorem residualLevel_ge_cutoff_of_gate (N : ℕ) (lambda : ℝ) (p : Fin 5 → ℕ)
    (hpos : ∀ i, 0 < p i) (hy : 1 < (p 4 : ℝ))
    (hgate : (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ lambda) :
    (p 4 : ℝ) ≤ residualLevel N lambda p := by
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hsquare : (p 4 : ℝ) ≤ (p 4 : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hy.le (by linarith : 0 ≤ (p 4 : ℝ))
    simpa only [mul_one, pow_two] using hmul
  have hquot : (p 4 : ℝ) ^ 2 < residualLevel N lambda p := by
    apply (lt_div_iff₀ hP).mpr
    simpa only [mul_comm] using hgate
  exact hsquare.trans hquot.le

/-- Pointwise original-policy cancellation. The gates are consequences of
the real active third parent and terminal cutoff, not supplied gate premises. -/
theorem original_small_last_gates_and_cancel
    (e : ℚ) (chi : ℝ) (m n : ℕ) (omega : ℝ) (homega : 0 < omega)
    (J4 : Finset (P1OriginalCoarseFifthContinuation.Label4 m))
    (cap4 : P1OriginalCoarseFifthContinuation.Label4 m → ℚ)
    (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
    (cap5 : P1OriginalCoarseFifthContinuation.Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) (j3 : HistoricalThirdCoarse.Cell m)
    (hj3 : j3 ∈ HistoricalThirdCoarse.cells (e : ℝ) chi m)
    (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (ht : actualPrimeTupleLog N (HistoricalThirdCoarse.P1OriginalSmallCoordinate.prefix4 p) ∈
      HistoricalThirdCoarse.P1OriginalFourth.jointCell m n j3 j4)
    (hp : p ∈ firstExitFrontierTuples 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))))
    (a : ℝ) (ha : 0 < a) (haomega : a ≤ omega / 3)
    (hsmall : actualPrimeTupleLog N p 4 ≤ a)
    (h34 : HistoricalThirdCoarse.levelExponent (e : ℝ) (HistoricalThirdCoarse.box m j3) ≤
      oldExponent e chi m omega J4 cap4 N p)
    (h45 : oldExponent e chi m omega J4 cap4 N p ≤ newExponent e chi m omega J4 cap4 J5 cap5 N p) :
    (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ oldExponent e chi m omega J4 cap4 N p ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ newExponent e chi m omega J4 cap4 J5 cap5 N p ∧
      originalDifference e chi m omega J4 cap4 J5 cap5 N cap p =
        lowerDeficit N cap (p 4 : ℝ) (residualLevel N (oldExponent e chi m omega J4 cap4 N p) p) -
          lowerDeficit N cap (p 4 : ℝ)
            (residualLevel N (newExponent e chi m omega J4 cap4 J5 cap5 N p) p) := by
  have hg := HistoricalThirdCoarse.P1OriginalSmallCoordinate.actual_fifth_small_last
    (e : ℝ) chi m n omega homega N cap hN hcap p j3 hj3 j4 hwhole ht hp
    a (oldExponent e chi m omega J4 cap4 N p)
    (newExponent e chi m omega J4 cap4 J5 cap5 N p) ha haomega hsmall h34 h45
  refine ⟨hg.2.2.2.2.1, hg.2.2.2.2.2, ?_⟩
  rw [originalDifference_eq_tuple]
  exact tuple_gated_sub_cancel N cap _ _ p hg.2.2.2.2.1 hg.2.2.2.2.2

/-- Explicit analytic budget at the unchanged actual residual level. -/
def sourceBudget (y R t : ℝ) : Prop :=
  2 ≤ t ∧ y ^ t ≤ R ∧ t ^ 13 ≤ Real.log (Nat.ceil R : ℝ) ∧
    Real.exp 1 ≤ Real.log (Nat.ceil R : ℝ)

/-- The closed actual arithmetic tail kernel after the two gates have opened.
Constants are chosen before all targets, primes, levels and moving budgets. -/
theorem exists_tuple_gated_exp_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      ∀ N cap : ℕ, Even N → ∀ lambda4 lambda5 : ℝ, ∀ p : Fin 5 → ℕ,
        (∀ i, 0 < p i) → 1 < (p 4 : ℝ) → (p 4 : ℝ) ≤ (cap : ℝ) →
        (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ lambda4 →
        (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ lambda5 →
        ∀ told tnew : ℝ,
          sourceBudget (p 4 : ℝ) (residualLevel N lambda4 p) told →
          sourceBudget (p 4 : ℝ) (residualLevel N lambda5 p) tnew →
          |tupleGatedMinus N cap lambda5 p - tupleGatedMinus N cap lambda4 p| ≤
            actualSmallEulerProduct N cap (p 4 : ℝ) *
              (tailEnvelope A B K (residualLevel N lambda4 p) told +
                tailEnvelope A B K (residualLevel N lambda5 p) tnew) := by
  obtain ⟨A, B, K, hA, hB, hK, hpair⟩ := exists_actualMinus_pair_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro N cap hEven lambda4 lambda5 p hpos hy hcap hgate4 hgate5 told tnew hold hnew
  rw [tupleGatedMinus_of_gate N cap lambda5 p hgate5,
    tupleGatedMinus_of_gate N cap lambda4 p hgate4]
  exact hpair N cap hEven (p 4 : ℝ) (residualLevel N lambda4 p) (residualLevel N lambda5 p)
    told tnew hcap hy
    (residualLevel_ge_cutoff_of_gate N lambda4 p hpos hy hgate4)
    (residualLevel_ge_cutoff_of_gate N lambda5 p hpos hy hgate5)
    hold.1 hnew.1 hold.2.1 hnew.2.1 hold.2.2.1 hnew.2.2.1 hold.2.2.2 hnew.2.2.2

/-- The exponential arithmetic bound instantiated at the original actual Q4
and Q5 lookups. The preceding small-last theorem supplies both gate premises
from active-third geometry. The only remaining source restrictions are the
displayed moving auxiliary budgets, not a tail or mean estimate. -/
theorem exists_originalDifference_exp_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
        (J4 : Finset (P1OriginalCoarseFifthContinuation.Label4 m))
        (cap4 : P1OriginalCoarseFifthContinuation.Label4 m → ℚ)
        (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
        (cap5 : P1OriginalCoarseFifthContinuation.Label5 m → ℚ)
        (N cap : ℕ) (p : Fin 5 → ℕ),
        Even N → (∀ i, 0 < p i) → 1 < (p 4 : ℝ) → (p 4 : ℝ) ≤ (cap : ℝ) →
        (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ oldExponent e chi m omega J4 cap4 N p →
        (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ newExponent e chi m omega J4 cap4 J5 cap5 N p →
        ∀ told tnew : ℝ,
          sourceBudget (p 4 : ℝ) (residualLevel N (oldExponent e chi m omega J4 cap4 N p) p) told →
          sourceBudget (p 4 : ℝ)
            (residualLevel N (newExponent e chi m omega J4 cap4 J5 cap5 N p) p) tnew →
          |originalDifference e chi m omega J4 cap4 J5 cap5 N cap p| ≤
            actualSmallEulerProduct N cap (p 4 : ℝ) *
              (tailEnvelope A B K (residualLevel N (oldExponent e chi m omega J4 cap4 N p) p) told +
                tailEnvelope A B K
                  (residualLevel N (newExponent e chi m omega J4 cap4 J5 cap5 N p) p) tnew) := by
  obtain ⟨A, B, K, hA, hB, hK, hbound⟩ := exists_tuple_gated_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro e chi m omega J4 cap4 J5 cap5 N cap p hEven hpos hy hcap hgate4 hgate5 told tnew ho hn
  rw [originalDifference_eq_tuple]
  exact hbound N cap hEven (oldExponent e chi m omega J4 cap4 N p)
    (newExponent e chi m omega J4 cap4 J5 cap5 N p) p hpos hy hcap hgate4 hgate5 told tnew ho hn

/-- Signed original saving bound needing an auxiliary budget only on old4.
The new5 lower density is bounded above by its exact same Euler baseline. -/
theorem exists_originalDifference_signed_exp_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
        (J4 : Finset (P1OriginalCoarseFifthContinuation.Label4 m))
        (cap4 : P1OriginalCoarseFifthContinuation.Label4 m → ℚ)
        (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
        (cap5 : P1OriginalCoarseFifthContinuation.Label5 m → ℚ)
        (N cap : ℕ) (p : Fin 5 → ℕ),
        Even N → (∀ i, 0 < p i) → 1 < (p 4 : ℝ) → (p 4 : ℝ) ≤ (cap : ℝ) →
        (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ oldExponent e chi m omega J4 cap4 N p →
        (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ newExponent e chi m omega J4 cap4 J5 cap5 N p →
        ∀ t : ℝ,
          sourceBudget (p 4 : ℝ) (residualLevel N (oldExponent e chi m omega J4 cap4 N p) p) t →
          originalDifference e chi m omega J4 cap4 J5 cap5 N cap p ≤
            actualSmallEulerProduct N cap (p 4 : ℝ) *
              tailEnvelope A B K (residualLevel N (oldExponent e chi m omega J4 cap4 N p) p) t := by
  obtain ⟨A, B, K, hA, hB, hK, hbound⟩ := exists_actualMinus_signed_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro e chi m omega J4 cap4 J5 cap5 N cap p hEven hpos hy hcap hgate4 hgate5 t hb
  rw [originalDifference_eq_tuple,
    tupleGatedMinus_of_gate N cap _ p hgate5, tupleGatedMinus_of_gate N cap _ p hgate4]
  exact hbound N cap hEven (p 4 : ℝ)
    (residualLevel N (oldExponent e chi m omega J4 cap4 N p) p)
    (residualLevel N (newExponent e chi m omega J4 cap4 J5 cap5 N p) p) t hcap hy
    (residualLevel_ge_cutoff_of_gate N _ p hpos hy hgate4)
    (residualLevel_ge_cutoff_of_gate N _ p hpos hy hgate5)
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2

end
end ImbalancedChen.P1OriginalSmallCutoffActualLowerTail
