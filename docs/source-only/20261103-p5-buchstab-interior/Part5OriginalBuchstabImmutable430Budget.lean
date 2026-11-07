import ImbalancedChen.Part5OriginalBuchstabActualRowLimits

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Both actual original Buchstab arithmetic rows, all literal seed-only430
predecessors and arbitrary nonnegative labelled parent families at one Q.
Interior, prefix deletion, closed-knot atoms and strict-ceiling correction
are all paid before cancellation. The two original count bases, full
Member/owner source binding and the nested 441 realization remain open.
-/
namespace ImbalancedChen.Part5OriginalBuchstabImmutable430Budget

noncomputable section
open Set Filter MeasureTheory
open scoped Classical BigOperators Topology
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430ArithmeticParentMass
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430BuchstabArithmeticRows
open Part5OriginalH430MovingBuchstabAtoms Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalBuchstabCompactAtoms Part5OriginalBuchstabNativeAtomDictionary
open Part5OriginalBuchstabActualRowLimits

/-- The actual dw/w integral selected by the original physical ceiling.
No table value is clamped, and no base term is assigned the value zero. -/
def idealProfile (up : Bool) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∫ w in Icc (physicalStart up p) 5,
    buchstabKernel w * tableFunction up (if up then oldh else oldH) w

theorem atomMass_value (up : Bool) (c : ℝ) (nums : Fin 200 → ℤ) :
    (∑ b : FloorAtom, atomMass up b c * floorAtomValue nums b) =
      ∫ w in Icc c 5, buchstabKernel w * tableFunction up nums w := by
  have h := weightedTable_integral_atom_sum up nums measurable_id measurableSet_Icc
    (buchstabKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc)
  change (∫ w in Icc c 5, buchstabKernel w * tableFunction up nums w) =
    ∑ b : FloorAtom, floorAtomValue nums b *
      ∫ w in Icc c 5 ∩ tablePullback up id b, buchstabKernel w at h
  rw [h]
  apply Finset.sum_congr rfl
  intro b hb
  have hS : MeasurableSet (Icc c 5 ∩ tableAtomSet up b) :=
    measurableSet_Icc.inter (measurableSet_tableAtomSet up b)
  simp only [atomMass,startAtomDensity,integral_indicator hS,
    tablePullback,preimage_id,mul_comm]

/-- The ideal row is the original positive Buchstab action, not an
abstract row whose desired integral value is an input. -/
theorem integralRow_value {up : Bool} {p : PhysicalNode}
    (hg : directionGuard up p) (oldH oldh : Fin 200 → ℤ) :
    (∑ b : RowAtom, integralRow up p b * oldAtomValue oldH oldh b) =
      idealProfile up p oldH oldh := by
  have hc := physicalStart_ge_one hg
  cases up <;>
    simp only [Fintype.sum_sum_type,integralRow,oldAtomValue,idealProfile,
      Bool.false_eq_true,if_false,if_true,zero_mul,Finset.sum_const_zero,zero_add,add_zero]
  all_goals
    simp_rw [normalizedAtomIntegral_eq_atomMass hc]
    exact atomMass_value _ _ _

def closedAbsoluteError (up : Bool) (N : ℕ) (Q : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : RowAtom, |closedRow up N Q old p b -
    thetaAtom N Q (parentProduct old)*integralRow up p b| * |oldAtomValue oldH oldh b|

def strictAbsoluteError (up : Bool) (N : ℕ) (Q chi : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : RowAtom, |strictRow up N Q chi old p b -
    thetaAtom N Q (parentProduct old)*integralRow up p b| * |oldAtomValue oldH oldh b|

theorem closedAbsoluteError_nonneg (up : Bool) (N : ℕ) (Q : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) :
    0 ≤ closedAbsoluteError up N Q old p oldH oldh :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem strictAbsoluteError_nonneg (up : Bool) (N : ℕ) (Q chi : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) :
    0 ≤ strictAbsoluteError up N Q chi old p oldH oldh :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- A coefficientwise triangle inequality, before old-array summation. -/
theorem strictAbsoluteError_le (up : Bool) (N : ℕ) (Q chi : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) :
    strictAbsoluteError up N Q chi old p oldH oldh ≤
      closedAbsoluteError up N Q old p oldH oldh +
      absoluteCeilingError up N Q chi old p oldH oldh := by
  unfold strictAbsoluteError closedAbsoluteError absoluteCeilingError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b hb
  have h := abs_sub_le (strictRow up N Q chi old p b)
    (closedRow up N Q old p b)
    (thetaAtom N Q (parentProduct old)*integralRow up p b)
  rw [abs_sub_comm (strictRow up N Q chi old p b)] at h
  have hm := mul_le_mul_of_nonneg_right h (abs_nonneg (oldAtomValue oldH oldh b))
  nlinarith only [hm]

/-- One pre-N threshold for the complete original predecessor list.
The finite L1 envelope is only a threshold device, not the row norm12. -/
theorem immutable430_uniform_closed_error {Lmin epsilon : ℝ}
    (hmin : 0 < Lmin) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q chi : ℝ, ∀ old : List ℕ,
      ∀ p : PhysicalNode, ∀ up : Bool, ∀ g : Fin 430,
      parentWindow N Q old chi → residual p = physicalLevel N Q old →
      p.ceiling = chi → directionGuard up p → Lmin ≤ physicalLevel N Q old →
      closedAbsoluteError up N Q old p (precedingH g) (precedingh g) ≤
        epsilon*thetaAtom N Q (parentProduct old) := by
  let eta := epsilon/(immutable430AtomL1+1)
  have hM := immutable430AtomL1_nonneg
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heb : eta*immutable430AtomL1 ≤ epsilon := by
    have hh : eta*(immutable430AtomL1+1) = epsilon := by
      dsimp [eta]; field_simp [show immutable430AtomL1+1 ≠ 0 by linarith]
    nlinarith
  obtain ⟨T,hT⟩ := uniform_closedRow_error hmin heta
  refine ⟨max 4 T, ?_⟩
  intro N hN Q chi old p up g hw hL hC hg hminL
  have ht := thetaAtom_nonneg (by omega : 4 ≤ N) hw.2.1 (parentWindow_logs hw).2.1
  have hcoeff := hT N (by omega) Q chi old p up hw hL hC hg hminL
  calc
    _ ≤ (eta*thetaAtom N Q (parentProduct old))*oldAtomL1 (precedingH g) (precedingh g) := by
      unfold closedAbsoluteError oldAtomL1
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun b hb =>
        mul_le_mul_of_nonneg_right (hcoeff b) (abs_nonneg _))
    _ ≤ (eta*thetaAtom N Q (parentProduct old))*immutable430AtomL1 :=
      mul_le_mul_of_nonneg_left (preceding_oldAtomL1_le g) (mul_nonneg heta.le ht)
    _ = (eta*immutable430AtomL1)*thetaAtom N Q (parentProduct old) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right heb ht

/-- Both original strict Buchstab rows: all interior and ceiling errors,
all closed knots, all seed-only430 predecessors, one physical Q, arbitrary
finite positive labelled families. No positivity of total Theta is assumed. -/
theorem immutable430_uniform_buchstab_rows {Lmin epsilon : ℝ}
    (hmin : 0 < Lmin) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (old : ι → List ℕ) (p : ι → PhysicalNode) (chi sigma : ι → ℝ)
      (up : ι → Bool) (g : ι → Fin 430),
      (∀ i ∈ S, parentWindow N Q (old i) (chi i)) →
      (∀ i ∈ S, residual (p i) = physicalLevel N Q (old i)) →
      (∀ i ∈ S, (p i).ceiling = chi i) →
      (∀ i ∈ S, 1 ≤ (p i).argument) →
      (∀ i ∈ S, directionGuard (up i) (p i)) →
      (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, Lmin ≤ physicalLevel N Q (old i)) →
      (∑ i ∈ S, sigma i*strictAbsoluteError (up i) N Q (chi i) (old i) (p i)
        (precedingH (g i)) (precedingh (g i))) ≤
          epsilon*parentTheta N Q S (fun i => parentProduct (old i)) sigma := by
  obtain ⟨Ti,hi⟩ := immutable430_uniform_closed_error hmin
    (by positivity : 0 < epsilon/2)
  obtain ⟨Tc,hc⟩ := immutable430_uniform_ceiling_error hmin
    (by positivity : 0 < epsilon/2)
  refine ⟨max Ti Tc, ?_⟩
  intro N hN Q ι S old p chi sigma up g hw hL hC hs hg hsigma hminL
  have hint : (∑ i ∈ S, sigma i*closedAbsoluteError (up i) N Q (old i) (p i)
      (precedingH (g i)) (precedingh (g i))) ≤
      (epsilon/2)*parentTheta N Q S (fun i => parentProduct (old i)) sigma := by
    unfold parentTheta
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hsi
    have hh := mul_le_mul_of_nonneg_left
      (hi N (by omega) Q (chi i) (old i) (p i) (up i) (g i)
        (hw i hsi) (hL i hsi) (hC i hsi) (hg i hsi) (hminL i hsi)) (hsigma i hsi)
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have hceil := hc N (by omega) Q S old p chi sigma up g hw hL hC hs hsigma hminL
  have htri : (∑ i ∈ S, sigma i*strictAbsoluteError (up i) N Q (chi i) (old i) (p i)
      (precedingH (g i)) (precedingh (g i))) ≤
      (∑ i ∈ S, sigma i*closedAbsoluteError (up i) N Q (old i) (p i)
        (precedingH (g i)) (precedingh (g i))) +
      ∑ i ∈ S, sigma i*absoluteCeilingError (up i) N Q (chi i) (old i) (p i)
        (precedingH (g i)) (precedingh (g i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hsi
    have hh := mul_le_mul_of_nonneg_left
      (strictAbsoluteError_le (up i) N Q (chi i) (old i) (p i) _ _) (hsigma i hsi)
    simpa only [mul_add] using hh
  linarith

/-- Absolute zero-mass treatment needs neither normalized rows nor a
convention for dividing by zero. The bound is the actual previous theorem. -/
theorem labelled_error_zero {ι : Type*} {N : ℕ} {Q epsilon : ℝ}
    (S : Finset ι) (old : ι → List ℕ) (p : ι → PhysicalNode)
    (chi sigma : ι → ℝ) (up : ι → Bool) (g : ι → Fin 430)
    (hsigma : ∀ i ∈ S, 0 ≤ sigma i)
    (hbound : (∑ i ∈ S, sigma i*strictAbsoluteError (up i) N Q (chi i) (old i) (p i)
        (precedingH (g i)) (precedingh (g i))) ≤
      epsilon*parentTheta N Q S (fun i => parentProduct (old i)) sigma)
    (hzero : parentTheta N Q S (fun i => parentProduct (old i)) sigma = 0) :
    (∑ i ∈ S, sigma i*strictAbsoluteError (up i) N Q (chi i) (old i) (p i)
      (precedingH (g i)) (precedingh (g i))) = 0 := by
  apply le_antisymm
  · simpa only [hzero,mul_zero] using hbound
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (hsigma i hi)
      (strictAbsoluteError_nonneg _ _ _ _ _ _ _ _))

/-- A signed applied-row estimate follows FROM coefficientwise absolute
control, never in the reverse direction. -/
theorem actual_strict_profile_error {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode} (hg : directionGuard up p)
    (oldH oldh : Fin 200 → ℤ) :
    |(∑ q ∈ singleChildren (.buchstab up p.argument) N Q old chi,
        thetaAtom N Q (parentProduct old*q.val)*tableFunction up (if up then oldh else oldH)
          (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val)) -
      thetaAtom N Q (parentProduct old)*idealProfile up p oldH oldh| ≤
        strictAbsoluteError up N Q chi old p oldH oldh := by
  rw [← strictRow_value,← integralRow_value hg,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  have heq : strictRow up N Q chi old p b*oldAtomValue oldH oldh b -
      thetaAtom N Q (parentProduct old)*(integralRow up p b*oldAtomValue oldH oldh b) =
      (strictRow up N Q chi old p b-thetaAtom N Q (parentProduct old)*integralRow up p b)*
        oldAtomValue oldH oldh b := by ring
  rw [heq,abs_mul]

end
end ImbalancedChen.Part5OriginalBuchstabImmutable430Budget
