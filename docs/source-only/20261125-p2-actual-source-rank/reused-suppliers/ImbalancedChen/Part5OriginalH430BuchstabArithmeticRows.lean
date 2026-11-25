import ImbalancedChen.Part5OriginalH430BuchstabCeilingPayment
import ImbalancedChen.Part5OriginalH430ImmutableBankProfiles

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal arithmetic rows for both original Buchstab directions. The
upper-parent row reads old h; the lower-parent row reads old H. Each
single child occurs once with the original scalar one. Every closed-knot
atom is retained. Strict/closed differences are bounded coefficientwise,
BEFORE summing against old arrays or summing parent histories.

The last theorem gives one pre-N threshold for every actual seed-only
430 predecessor, both directions and all finite nonnegative labelled
families at one Q. It pays only the ceiling discrepancy. Interior
prime-to-native-integral passage, full Member ownership, base costs and
the complete nested 441-level realization remain separate obligations.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabArithmeticRows

noncomputable section
open Set Classical
open scoped BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430BuchstabCeilingDictionary
open Part5OriginalH430BuchstabCeilingPayment
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles

/-- Unlike W1 and W2, neither Buchstab row has a divisor 2 or 5. -/
theorem buchstab_scalar_one (up : Bool) (s : ℝ) :
    singleEdgeScalar (.buchstab up s) = 1 := rfl

def rowFrom (up : Bool) (N : ℕ) (Q : ℝ) (old : List ℕ)
    (S : Finset (Fin (N+1))) : RowAtom → ℝ
  | .inl b => if up then 0 else
      ∑ q ∈ S, pointAtom (thetaAtom N Q (parentProduct old*q.val)) false
        (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) b
  | .inr b => if up then
      ∑ q ∈ S, pointAtom (thetaAtom N Q (parentProduct old*q.val)) true
        (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) b
      else 0

def strictRow (up : Bool) (N : ℕ) (Q chi : ℝ) (old : List ℕ) (p : PhysicalNode) :
    RowAtom → ℝ :=
  rowFrom up N Q old (singleChildren (.buchstab up p.argument) N Q old chi)

def closedRow (up : Bool) (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode) :
    RowAtom → ℝ := rowFrom up N Q old (closedChildren up N old p)

def ceilingRow (up : Bool) (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode) :
    RowAtom → ℝ := rowFrom up N Q old (ceilingChildren up N old p)

/-- Exact old-array value, including all singleton knot atoms. -/
theorem rowFrom_value (up : Bool) (N : ℕ) (Q : ℝ) (old : List ℕ)
    (S : Finset (Fin (N+1))) (oldH oldh : Fin 200 → ℤ) :
    (∑ b : RowAtom, rowFrom up N Q old S b*oldAtomValue oldH oldh b) =
      ∑ q ∈ S, thetaAtom N Q (parentProduct old*q.val) *
        tableFunction up (if up then oldh else oldH)
          (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) := by
  cases up <;>
    simp only [Fintype.sum_sum_type, rowFrom, oldAtomValue, Bool.false_eq_true,
      if_false, if_true, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  all_goals
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    exact pointAtom_value _ _ _ _

/-- The actual production row is not an arbitrary input row. -/
theorem strictRow_value (up : Bool) (N : ℕ) (Q chi : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) :
    (∑ b : RowAtom, strictRow up N Q chi old p b*oldAtomValue oldH oldh b) =
      ∑ q ∈ singleChildren (.buchstab up p.argument) N Q old chi,
        thetaAtom N Q (parentProduct old*q.val) *
          tableFunction up (if up then oldh else oldH)
            (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) :=
  rowFrom_value up N Q old _ oldH oldh

theorem closedRow_eq_add {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hs : 1 ≤ p.argument) (b : RowAtom) :
    closedRow up N Q old p b =
      strictRow up N Q chi old p b + ceilingRow up N Q old p b := by
  cases up <;> cases b <;>
    simp only [closedRow, strictRow, ceilingRow, rowFrom, Bool.false_eq_true,
      if_false, if_true, add_zero]
  all_goals exact closedChildren_sum hw hL hC hs _

/-- Each retained coefficient is nonnegative and bounded by the actual
arithmetic ceiling mass. No norm12 claim is involved. -/
theorem ceilingRow_bounds {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (b : RowAtom) :
    0 ≤ ceilingRow up N Q old p b ∧
      ceilingRow up N Q old p b ≤ ceilingMass up N Q old p := by
  have hpoint (lower : Bool) (c : FloorAtom) :
      0 ≤ (∑ q ∈ ceilingChildren up N old p,
        pointAtom (thetaAtom N Q (parentProduct old*q.val)) lower
          (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) c) ∧
      (∑ q ∈ ceilingChildren up N old p,
        pointAtom (thetaAtom N Q (parentProduct old*q.val)) lower
          (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) c) ≤
        ceilingMass up N Q old p := by
    constructor
    · apply Finset.sum_nonneg
      intro q hq
      exact pointAtom_nonneg
        (childTheta_nonneg hN hw hL (mem_ceilingChildren.mp hq).1) lower _ c
    · apply Finset.sum_le_sum
      intro q hq
      have ht := childTheta_nonneg hN hw hL (mem_ceilingChildren.mp hq).1
      by_cases hb : P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val ∈
          tableAtomSet lower c
      · simp only [pointAtom, Set.indicator_of_mem hb, mul_one, le_refl]
      · simpa only [pointAtom, Set.indicator_of_notMem hb, mul_zero] using ht
  cases up <;> cases b with
  | inl c =>
      first
      | exact hpoint false c
      | exact ⟨le_rfl, ceilingMass_nonneg hN hw hL⟩
  | inr c =>
      first
      | exact hpoint true c
      | exact ⟨le_rfl, ceilingMass_nonneg hN hw hL⟩

def oldAtomL1 (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : RowAtom, |oldAtomValue oldH oldh b|

theorem oldAtomL1_nonneg (oldH oldh : Fin 200 → ℤ) : 0 ≤ oldAtomL1 oldH oldh :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Absolute values are taken coefficient by coefficient, not after
application to one signed old-array profile. -/
def absoluteCeilingError (up : Bool) (N : ℕ) (Q chi : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : RowAtom, |closedRow up N Q old p b-strictRow up N Q chi old p b| *
    |oldAtomValue oldH oldh b|

theorem absoluteCeilingError_nonneg (up : Bool) (N : ℕ) (Q chi : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) :
    0 ≤ absoluteCeilingError up N Q chi old p oldH oldh :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem absoluteCeilingError_le {up : Bool} {N : ℕ} {Q chi A : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hs : 1 ≤ p.argument) (hA : 4 ≤ A) (hfloor : A ≤ primeFloor N Q old)
    (oldH oldh : Fin 200 → ℤ) :
    absoluteCeilingError up N Q chi old p oldH oldh ≤
      ((4/A)*thetaAtom N Q (parentProduct old))*oldAtomL1 oldH oldh := by
  unfold absoluteCeilingError oldAtomL1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have he : closedRow up N Q old p b-strictRow up N Q chi old p b =
      ceilingRow up N Q old p b := by
    linarith only [closedRow_eq_add hw hL hC hs b]
  rw [he, abs_of_nonneg (ceilingRow_bounds hN hw hL b).1]
  exact mul_le_mul_of_nonneg_right
    ((ceilingRow_bounds hN hw hL b).2.trans (ceilingMass_le hN hw hL hA hfloor))
    (abs_nonneg _)

/-- A finite envelope of the actual immutable seed-only predecessors.
It is not a numerical evaluation, a saved-table licence or row norm12. -/
def immutable430AtomL1 : ℝ :=
  ∑ g : Fin 430, oldAtomL1 (precedingH g) (precedingh g)

theorem immutable430AtomL1_nonneg : 0 ≤ immutable430AtomL1 :=
  Finset.sum_nonneg (fun g _ => oldAtomL1_nonneg _ _)

theorem preceding_oldAtomL1_le (g : Fin 430) :
    oldAtomL1 (precedingH g) (precedingh g) ≤ immutable430AtomL1 := by
  exact Finset.single_le_sum (fun k _ => oldAtomL1_nonneg _ _) (Finset.mem_univ g)

theorem immutable430_ceiling_error_le {up : Bool} {N : ℕ} {Q chi A : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hs : 1 ≤ p.argument) (hA : 4 ≤ A) (hfloor : A ≤ primeFloor N Q old)
    (g : Fin 430) :
    absoluteCeilingError up N Q chi old p (precedingH g) (precedingh g) ≤
      ((4/A)*immutable430AtomL1)*thetaAtom N Q (parentProduct old) := by
  have hc : 0 ≤ (4/A)*thetaAtom N Q (parentProduct old) :=
    mul_nonneg (div_nonneg (by norm_num) (by linarith))
      (thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1)
  calc
    _ ≤ ((4/A)*thetaAtom N Q (parentProduct old))*
        oldAtomL1 (precedingH g) (precedingh g) :=
      absoluteCeilingError_le hN hw hL hC hs hA hfloor _ _
    _ ≤ ((4/A)*thetaAtom N Q (parentProduct old))*immutable430AtomL1 :=
      mul_le_mul_of_nonneg_left (preceding_oldAtomL1_le g) hc
    _ = _ := by ring

/-- Full labelled outer sum for the ceiling correction, with no assumption
that total Theta is positive and no collapse of equal-product histories. -/
theorem labelled_ceiling_error_le {ι : Type*} {N : ℕ} (Q A : ℝ)
    (S : Finset ι) (old : ι → List ℕ) (p : ι → PhysicalNode)
    (chi sigma : ι → ℝ) (up : ι → Bool) (g : ι → Fin 430)
    (hN : 4 ≤ N) (hA : 4 ≤ A)
    (hw : ∀ i ∈ S, parentWindow N Q (old i) (chi i))
    (hL : ∀ i ∈ S, residual (p i) = physicalLevel N Q (old i))
    (hC : ∀ i ∈ S, (p i).ceiling = chi i)
    (hs : ∀ i ∈ S, 1 ≤ (p i).argument)
    (hsigma : ∀ i ∈ S, 0 ≤ sigma i)
    (hfloor : ∀ i ∈ S, A ≤ primeFloor N Q (old i)) :
    (∑ i ∈ S, sigma i*absoluteCeilingError (up i) N Q (chi i) (old i) (p i)
        (precedingH (g i)) (precedingh (g i))) ≤
      ((4/A)*immutable430AtomL1)*
        parentTheta N Q S (fun i => parentProduct (old i)) sigma := by
  unfold parentTheta
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left
    (immutable430_ceiling_error_le hN (hw i hi) (hL i hi) (hC i hi)
      (hs i hi) hA (hfloor i hi) (g i)) (hsigma i hi)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- Actual pre-N uniform supplier of ONLY the retained ceiling error.
The threshold is chosen before the old words, direction/generation
assignments and arbitrary positive labelled family at the common Q. -/
theorem immutable430_uniform_ceiling_error {Lmin epsilon : ℝ}
    (hmin : 0 < Lmin) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (old : ι → List ℕ) (p : ι → PhysicalNode) (chi sigma : ι → ℝ)
      (up : ι → Bool) (g : ι → Fin 430),
      (∀ i ∈ S, parentWindow N Q (old i) (chi i)) →
      (∀ i ∈ S, residual (p i) = physicalLevel N Q (old i)) →
      (∀ i ∈ S, (p i).ceiling = chi i) →
      (∀ i ∈ S, 1 ≤ (p i).argument) → (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, Lmin ≤ physicalLevel N Q (old i)) →
      (∑ i ∈ S, sigma i*absoluteCeilingError (up i) N Q (chi i) (old i) (p i)
          (precedingH (g i)) (precedingh (g i))) ≤
        epsilon*parentTheta N Q S (fun i => parentProduct (old i)) sigma := by
  let A : ℝ := max 4 (4*immutable430AtomL1/epsilon)
  have hA : 4 ≤ A := le_max_left _ _
  have hA0 : 0 < A := by linarith
  have hcoef : (4/A)*immutable430AtomL1 ≤ epsilon := by
    have hraw : 4*immutable430AtomL1 ≤ A*epsilon :=
      (div_le_iff₀ he).mp (le_max_right _ _)
    have heq : (4/A)*immutable430AtomL1 = (4*immutable430AtomL1)/A := by ring
    rw [heq]
    apply (div_le_iff₀ hA0).mpr
    nlinarith only [hraw]
  obtain ⟨T, hT⟩ := exists_uniform_primeFloor hmin hA
  refine ⟨T, ?_⟩
  intro N hN Q ι S old p chi sigma up g hw hL hC hs hsigma hminL
  obtain ⟨hN4, hfloor⟩ := hT N hN
  have htotal : 0 ≤ parentTheta N Q S (fun i => parentProduct (old i)) sigma := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hsigma i hi)
      (thetaAtom_nonneg hN4 (hw i hi).2.1 (parentWindow_logs (hw i hi)).2.1)
  exact (labelled_ceiling_error_le Q A S old p chi sigma up g hN4 hA hw hL hC hs hsigma
    (fun i hi => hfloor Q (old i) (hminL i hi))).trans
      (mul_le_mul_of_nonneg_right hcoef htotal)

/-- The zero-total-mass case is an absolute equality, before normalization. -/
theorem labelled_ceiling_error_eq_zero {ι : Type*} {N : ℕ} (Q A : ℝ)
    (S : Finset ι) (old : ι → List ℕ) (p : ι → PhysicalNode)
    (chi sigma : ι → ℝ) (up : ι → Bool) (g : ι → Fin 430)
    (hN : 4 ≤ N) (hA : 4 ≤ A)
    (hw : ∀ i ∈ S, parentWindow N Q (old i) (chi i))
    (hL : ∀ i ∈ S, residual (p i) = physicalLevel N Q (old i))
    (hC : ∀ i ∈ S, (p i).ceiling = chi i)
    (hs : ∀ i ∈ S, 1 ≤ (p i).argument)
    (hsigma : ∀ i ∈ S, 0 ≤ sigma i)
    (hfloor : ∀ i ∈ S, A ≤ primeFloor N Q (old i))
    (hzero : parentTheta N Q S (fun i => parentProduct (old i)) sigma = 0) :
    (∑ i ∈ S, sigma i*absoluteCeilingError (up i) N Q (chi i) (old i) (p i)
        (precedingH (g i)) (precedingh (g i))) = 0 := by
  apply le_antisymm
  · simpa only [hzero, mul_zero] using
      labelled_ceiling_error_le Q A S old p chi sigma up g hN hA hw hL hC hs hsigma hfloor
  · exact Finset.sum_nonneg (fun i hi =>
      mul_nonneg (hsigma i hi) (absoluteCeilingError_nonneg _ _ _ _ _ _ _ _))

end
end ImbalancedChen.Part5OriginalH430BuchstabArithmeticRows
