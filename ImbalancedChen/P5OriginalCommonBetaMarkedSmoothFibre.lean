import ImbalancedChen.P5OriginalJointPresievedCentrePayment
import ImbalancedChen.P5ZU1011NativeUnmaskedLowBoxAtoms
import ImbalancedChen.P5ZU1011SameRhoSmoothMainApproximation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal geometric smoothing ON THE ORIGINAL TRUE jointMarks. The low
band is unmasked; the high geometric expression uses the original paired
row subtraction. The original source filter, common beta coefficient,
selected row and physical modulus remain in every fibre. This coefficient
is NOT identified with an independent outer smooth prime-box coefficient:
outside-source tuple multiplicity/support is a separate obligation.
-/
namespace ImbalancedChen.P5Z.OriginalCommonBetaMarkedSmoothFibre
noncomputable section
open Set Classical
open scoped BigOperators
open U11Integral U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalMaskSmoothBoxRealization
open U1011NativeUnmaskedLowBoxAtoms (lowSmoothCover)
open U1011FourDimensionalSmoothBoxAtoms U1011AffineSmoothBoxCover
open U1011SameRhoSmoothMainApproximation (cover_bounds)
open OriginalOrdinaryPresievedSigma (Mark modulus rowCoefficient)
open OriginalJointPresievedCompiler OriginalJointCommonBetaModel
open OriginalCommonBetaActualParameters OriginalJointPresievedArithmeticSupport

def geometricCost (S : Finset Row) (m fine : ℕ) : ℝ :=
  (Fintype.card (Grid m) : ℝ) * (Fintype.card State : ℝ) *
    ((S.card : ℝ) + 2) * (Fintype.card (Grid fine) : ℝ)

theorem geometricCost_nonneg (S : Finset Row) (m fine : ℕ) : 0 ≤ geometricCost S m fine := by
  unfold geometricCost
  positivity

/-- The SAME finite low/high geometric multiplier used by the original
state/owner decomposition, now evaluated on the true NEW common-beta marks. -/
def geometricMultiplier (inner : Bool) (S : Finset Row) (m fine : ℕ) (δ : ℝ) (v : LogFour) : ℝ :=
  ∑ k : Grid m,
    if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
      ∑ s : State, lowSmoothCover inner s m k fine δ v + signedSmoothCover inner S s m k fine δ v

theorem signedCover_abs_le (inner : Bool) (S : Finset Row) (s : State)
    (m : ℕ) (k : Grid m) (fine : ℕ) (δ : ℝ) (v : LogFour) :
    |signedSmoothCover inner S s m k fine δ v| ≤
      ((S.card : ℝ) + 1) * (Fintype.card (Grid fine) : ℝ) := by
  let M : ℝ := Fintype.card (Grid fine)
  let a := smoothCover inner δ
    (if inner then innerCells (baseGates s m k) fine else outerCells (baseGates s m k) fine) v
  let b (r : Row) := smoothCover (!inner) δ
    (if inner then outerCells (removedGates s m k r) fine else innerCells (removedGates s m k r) fine) v
  have ha : 0 ≤ a ∧ a ≤ M := cover_bounds inner δ _ v
  have hb : ∀ r : Row, 0 ≤ b r ∧ b r ≤ M := fun r => cover_bounds (!inner) δ _ v
  have hs0 : 0 ≤ ∑ r ∈ S, b r := Finset.sum_nonneg (fun r _ => (hb r).1)
  have hs1 : (∑ r ∈ S, b r) ≤ (S.card : ℝ) * M := by
    calc
      _ ≤ ∑ _r ∈ S, M := Finset.sum_le_sum (fun r _ => (hb r).2)
      _ = (S.card : ℝ) * M := by simp
  change |a - ∑ r ∈ S, b r| ≤ ((S.card : ℝ) + 1) * M
  rw [abs_le]
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hSM : 0 ≤ (S.card : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) hM
  constructor <;> nlinarith

theorem geometricMultiplier_abs_le (inner : Bool) (S : Finset Row)
    (m fine : ℕ) (δ : ℝ) (v : LogFour) :
    |geometricMultiplier inner S m fine δ v| ≤ geometricCost S m fine := by
  let H : ℝ := ((S.card : ℝ) + 2) * (Fintype.card (Grid fine) : ℝ)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hpoint (k : Grid m) (s : State) :
      |lowSmoothCover inner s m k fine δ v + signedSmoothCover inner S s m k fine δ v| ≤ H := by
    have hlo := cover_bounds inner δ
      (if inner then innerCells (U1011NativeUnmaskedLowBoxAtoms.lowGates s m k) fine
        else outerCells (U1011NativeUnmaskedLowBoxAtoms.lowGates s m k) fine) v
    have hlow : |lowSmoothCover inner s m k fine δ v| ≤ (Fintype.card (Grid fine) : ℝ) := by
      rw [abs_of_nonneg hlo.1]
      exact hlo.2
    have hhigh := signedCover_abs_le inner S s m k fine δ v
    exact (abs_add _ _).trans ((add_le_add hlow hhigh).trans_eq (by dsimp [H]; ring))
  unfold geometricMultiplier
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k : Grid m, (Fintype.card State : ℝ) * H := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs
      · simp only [abs_zero]
        exact mul_nonneg (Nat.cast_nonneg _) hH
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          ((Finset.sum_le_sum (fun s _ => hpoint k s)).trans_eq (by simp))
    _ = geometricCost S m fine := by simp [geometricCost, H]; ring

def markedSmoothSigma (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (nu epsilon : ℝ) (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ a ∈ (jointMarks m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E).filter (fun a => modulus a = q),
    rowCoefficient m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * epsilon)) a.1 a.2 *
      geometricMultiplier inner S m fine δ (coordinates N a.1)

def errorSigma (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (nu epsilon : ℝ) (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  markedSmoothSigma inner S m N eta nu epsilon fine δ E q -
    jointPresievedSigma m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * epsilon)) E q

/-- Exact SAME-mark/SAME-policy/SAME-beta/SAME-q correction. The source
filter remains explicit; no outside-source box coefficient is substituted. -/
theorem errorSigma_eq_original_fibre (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (nu epsilon : ℝ) (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) (q : ℕ) :
    errorSigma inner S m N eta nu epsilon fine δ E q =
      ∑ a ∈ (jointMarks m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E).filter (fun a => modulus a = q),
        rowCoefficient m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * epsilon)) a.1 a.2 *
          (geometricMultiplier inner S m fine δ (coordinates N a.1) - 1) := by
  unfold errorSigma markedSmoothSigma jointPresievedSigma
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem errorSigma_zero_off_support (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (nu epsilon : ℝ) (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) {q : ℕ}
    (hq : q ∉ jointSupport m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E) :
    errorSigma inner S m N eta nu epsilon fine δ E q = 0 := by
  rw [errorSigma_eq_original_fibre]
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha, hmod⟩ := Finset.mem_filter.mp ha
  exact (hq (Finset.mem_image.mpr ⟨a, ha, hmod⟩)).elim

theorem errorSigma_at_mark {m N : ℕ} {eta : ℚ} {nu epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget m eta nu) (inner : Bool) (S : Finset Row)
    (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) {a : Mark}
    (ha : a ∈ jointMarks m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E) :
    errorSigma inner S m N eta nu epsilon fine δ E (modulus a) =
      jointPresievedSigma m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * epsilon)) E (modulus a) *
        (geometricMultiplier inner S m fine δ (coordinates N a.1) - 1) := by
  have hw (t : Four) (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples m N E) :=
    (parameters_on_joint_row hN heta hnu he heBudget ht).1
  have hf : (jointMarks m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E).filter
      (fun b => modulus b = modulus a) = {a} := by
    ext b
    constructor
    · intro hb
      obtain ⟨hb, hmod⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_singleton.mpr (joint_modulus_injective hN heta E hw hb ha hmod)
    · intro hb
      have heq := Finset.mem_singleton.mp hb
      subst b
      exact Finset.mem_filter.mpr ⟨ha, rfl⟩
  rw [errorSigma_eq_original_fibre, hf, Finset.sum_singleton, jointSigma_eq_row hN heta hw ha]

/-- Original physical injection controls the marked smooth correction.
The cost is fixed once both meshes and the geometric row set are fixed. -/
theorem errorSigma_abs_le {m N : ℕ} {eta : ℚ} {nu epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget m eta nu) (inner : Bool) (S : Finset Row)
    (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) (q : ℕ) :
    |errorSigma inner S m N eta nu epsilon fine δ E q| ≤ geometricCost S m fine + 1 := by
  by_cases hq : q ∈ jointSupport m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    rw [errorSigma_at_mark hN heta hnu he heBudget inner S fine δ E ha, abs_mul]
    have hw (t : Four) (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples m N E) :=
      (parameters_on_joint_row hN heta hnu he heBudget ht).1
    have hunit := jointSigma_abs_le_one hN heta E hw (modulus a)
    have hgeo : |geometricMultiplier inner S m fine δ (coordinates N a.1) - 1| ≤ geometricCost S m fine + 1 := by
      have hh := abs_sub_le (geometricMultiplier inner S m fine δ (coordinates N a.1)) 0 1
      have hh' : |geometricMultiplier inner S m fine δ (coordinates N a.1) - 1| ≤
          |geometricMultiplier inner S m fine δ (coordinates N a.1)| + 1 := by
        simpa only [sub_zero, zero_sub, abs_neg, abs_one] using hh
      exact hh'.trans (add_le_add_right (geometricMultiplier_abs_le inner S m fine δ _) 1)
    exact (mul_le_mul hunit hgeo (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  · rw [errorSigma_zero_off_support inner S m N eta nu epsilon fine δ E hq, abs_zero]
    linarith [geometricCost_nonneg S m fine]

theorem errorSigma_arithmetic_support {m N q : ℕ} {eta : ℚ} {nu epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget m eta nu) (inner : Bool) (S : Finset Row)
    (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop)
    (hq : errorSigma inner S m N eta nu epsilon fine δ E q ≠ 0) :
    0 < q ∧ Squarefree q ∧ q.Coprime N ∧ (q : ℝ) < (N : ℝ) ^ (153 / 256 : ℝ) := by
  have hmem : q ∈ jointSupport m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E := by
    by_contra hn
    exact hq (errorSigma_zero_off_support inner S m N eta nu epsilon fine δ E hn)
  obtain ⟨a, ha, hmod⟩ := Finset.mem_image.mp hmem
  have htrue : jointPresievedSigma m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * epsilon)) E q ≠ 0 := by
    intro hz
    apply hq
    rw [← hmod, errorSigma_at_mark hN heta hnu he heBudget inner S fine δ E ha, hmod, hz, zero_mul]
  have hs := actual_joint_arithmetic_support hN heta hnu he heBudget E htrue
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2⟩

end
end ImbalancedChen.P5Z.OriginalCommonBetaMarkedSmoothFibre
