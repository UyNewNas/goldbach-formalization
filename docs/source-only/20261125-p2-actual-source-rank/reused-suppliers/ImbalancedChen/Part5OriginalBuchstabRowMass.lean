import ImbalancedChen.Part5OriginalBuchstabImmutable430Budget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two actual Buchstab arithmetic rows are positive and have total mass
at most five times the same parent Theta, eventually uniformly before the
parent and its direction. The ideal mass is at most four. The number 802
is used only to allocate a vanishing coefficient error; no saved table
is evaluated. The manuscript's row budget twelve is unchanged.

This supplies a LOCAL row-mass input, not the identification of all
physical Member histories or the common nested 441-level realization.
-/
namespace ImbalancedChen.Part5OriginalBuchstabRowMass

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430BuchstabCeilingDictionary Part5OriginalH430BuchstabCeilingPayment
open Part5OriginalH430BuchstabArithmeticRows Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalBuchstabActualRowLimits Part5OriginalBuchstabImmutable430Budget

/-- Every coefficient in the literal strict carrier is nonnegative. -/
theorem strictRow_nonneg {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hs : 1 ≤ p.argument) (b : RowAtom) :
    0 ≤ strictRow up N Q chi old p b := by
  have hsum (lower : Bool) (a : FloorAtom) :
      0 ≤ ∑ q ∈ singleChildren (.buchstab up p.argument) N Q old chi,
        pointAtom (thetaAtom N Q (parentProduct old*q.val)) lower
          (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) a := by
    apply Finset.sum_nonneg
    intro q hq
    have hc := ((mem_singleChildren_iff hw hL hC hs).mp hq).1
    exact pointAtom_nonneg (childTheta_nonneg hN hw hL hc) lower _ a
  cases up <;> cases b <;>
    first | exact hsum _ _ | exact le_rfl

/-- Positive ceiling coefficients show that the strict row is no larger
than the corresponding closed row, coefficient by coefficient. -/
theorem strictRow_le_closedRow {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hs : 1 ≤ p.argument) (b : RowAtom) :
    strictRow up N Q chi old p b ≤ closedRow up N Q old p b := by
  rw [closedRow_eq_add hw hL hC hs b]
  exact le_add_of_nonneg_right (ceilingRow_bounds hN hw hL b).1

/-- Constant-one data only measure the row; they are not an analytic seed. -/
theorem integralRow_mass {up : Bool} {p : PhysicalNode}
    (hg : directionGuard up p) :
    (∑ b : RowAtom, integralRow up p b) =
      Part5OriginalBuchstabImmutable430Budget.idealProfile up p oneNumerators oneNumerators := by
  have h := integralRow_value hg oneNumerators oneNumerators
  have hone (b : RowAtom) : oldAtomValue oneNumerators oneNumerators b = 1 := by
    cases b <;> exact one_floorAtomValue _
  simpa only [hone,mul_one] using h

/-- The genuine dw/w mass, with its original table support, is at most four. -/
theorem integralRow_mass_le_four {up : Bool} {p : PhysicalNode}
    (hg : directionGuard up p) : (∑ b : RowAtom, integralRow up p b) ≤ 4 := by
  rw [integralRow_mass hg]
  let D := Icc (physicalStart up p) 5
  have hD : MeasurableSet D := measurableSet_Icc
  have hk : IntegrableOn buchstabKernel D :=
    buchstabKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc
  have ht := integrableOn_weightedTable up oneNumerators measurable_id hD hk
  have hle : (∫ w in D, weightedTable up oneNumerators id buchstabKernel w) ≤
      ∫ w in D, buchstabKernel w := by
    apply setIntegral_mono_on ht hk hD
    intro w hw
    exact (weightedTable_bounds up oneNumerators_bounded id buchstabKernel w
      (buchstabKernel_nonneg w)).2
  have hm : buchstabMass D ≤ 4 := buchstabMass_le_four (fun w hw =>
    ⟨(physicalStart_ge_one hg).trans hw.1,hw.2⟩)
  simpa only [Part5OriginalBuchstabImmutable430Budget.idealProfile,ite_self,
    weightedTable,id_eq,D] using hle.trans hm

theorem rowAtom_card : Fintype.card RowAtom = 802 := by
  norm_num [RowAtom,FloorAtom]

/-- A threshold for a concrete arithmetic row-mass supply. The fixed
residual floor is explicit; its full-history construction is not assumed
away by a norm12 or a count-licence field. -/
theorem uniform_strictRow_mass {Lmin : ℝ} (hmin : 0 < Lmin) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q chi : ℝ, ∀ old : List ℕ,
      ∀ p : PhysicalNode, ∀ up : Bool,
      parentWindow N Q old chi → residual p = physicalLevel N Q old →
      p.ceiling = chi → 1 ≤ p.argument → directionGuard up p →
      Lmin ≤ physicalLevel N Q old →
      (∀ b : RowAtom, 0 ≤ strictRow up N Q chi old p b) ∧
      (∑ b : RowAtom, strictRow up N Q chi old p b) ≤
        5*thetaAtom N Q (parentProduct old) := by
  obtain ⟨T,hT⟩ := uniform_closedRow_error hmin
    (by norm_num : (0:ℝ) < 1/802)
  refine ⟨max 4 T, ?_⟩
  intro N hN Q chi old p up hw hL hC hs hg hminL
  have hN4 : 4 ≤ N := by omega
  have htheta := thetaAtom_nonneg hN4 hw.2.1 (parentWindow_logs hw).2.1
  have hc := hT N (by omega) Q chi old p up hw hL hC hg hminL
  refine ⟨fun b => strictRow_nonneg hN4 hw hL hC hs b, ?_⟩
  calc
    _ ≤ ∑ b : RowAtom, closedRow up N Q old p b :=
      Finset.sum_le_sum (fun b hb => strictRow_le_closedRow hN4 hw hL hC hs b)
    _ ≤ ∑ b : RowAtom, (thetaAtom N Q (parentProduct old)*integralRow up p b +
        (1/802:ℝ)*thetaAtom N Q (parentProduct old)) := by
      apply Finset.sum_le_sum
      intro b hb
      have hh := (abs_le.mp (hc b)).2
      linarith
    _ = thetaAtom N Q (parentProduct old)*(∑ b : RowAtom, integralRow up p b) +
        thetaAtom N Q (parentProduct old) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,rowAtom_card,nsmul_eq_mul]
      ring
    _ ≤ thetaAtom N Q (parentProduct old)*4 + thetaAtom N Q (parentProduct old) :=
      add_le_add_right (mul_le_mul_of_nonneg_left (integralRow_mass_le_four hg) htheta) _
    _ = _ := by ring

/-- Positive labelled outer mass, at one literal Q. This stronger local
bound is compatible with the unchanged manuscript row budget twelve. -/
theorem uniform_labelled_row_mass {Lmin : ℝ} (hmin : 0 < Lmin) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (old : ι → List ℕ) (p : ι → PhysicalNode) (chi sigma : ι → ℝ) (up : ι → Bool),
      (∀ i ∈ S, parentWindow N Q (old i) (chi i)) →
      (∀ i ∈ S, residual (p i) = physicalLevel N Q (old i)) →
      (∀ i ∈ S, (p i).ceiling = chi i) →
      (∀ i ∈ S, 1 ≤ (p i).argument) →
      (∀ i ∈ S, directionGuard (up i) (p i)) →
      (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, Lmin ≤ physicalLevel N Q (old i)) →
      0 ≤ (∑ i ∈ S, sigma i*∑ b : RowAtom, strictRow (up i) N Q (chi i) (old i) (p i) b) ∧
      (∑ i ∈ S, sigma i*∑ b : RowAtom, strictRow (up i) N Q (chi i) (old i) (p i) b) ≤
        5*parentTheta N Q S (fun i => parentProduct (old i)) sigma := by
  obtain ⟨T,hT⟩ := uniform_strictRow_mass hmin
  refine ⟨T, ?_⟩
  intro N hN Q ι S old p chi sigma up hw hL hC hs hg hsigma hminL
  have hrow (i : ι) (hi : i ∈ S) := hT N hN Q (chi i) (old i) (p i) (up i)
    (hw i hi) (hL i hi) (hC i hi) (hs i hi) (hg i hi) (hminL i hi)
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hsigma i hi) (Finset.sum_nonneg (fun b hb => (hrow i hi).1 b))
  · unfold parentTheta
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_assoc,mul_comm,mul_left_comm] using
      mul_le_mul_of_nonneg_left (hrow i hi).2 (hsigma i hi)

end
end ImbalancedChen.Part5OriginalBuchstabRowMass
