import ImbalancedChen.Part5OriginalH430BuchstabAbsoluteSupplier

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two actual Buchstab arithmetic rows have mass at most 5 times their
same-Q parent Theta, hence fit inside the original norm12 allowance.
This is derived from their true atom limits and the original integral
mass bound 4, not assumed as a feedback-norm field. The upper residual
bound is also derived from parentWindow. The final joint supplier keeps
only the genuinely needed positive lower residual floor.

This is a local arithmetic-row supply, not full Member ownership, a
Buchstab COUNT inequality, an ordinary/switched base licence, or h34.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabLocalMass

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430MovingBuchstabAtoms Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalH430BuchstabCeilingDictionary Part5OriginalH430BuchstabCeilingPayment
open Part5OriginalH430BuchstabArithmeticRows
open Part5OriginalH430BuchstabInteriorDictionary
open Part5OriginalH430BuchstabAbsoluteSupplier

/-- No free compact upper endpoint is needed for actual same-Q parents. -/
theorem physicalLevel_le_one {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) : physicalLevel N Q old ≤ 1 := by
  have hl := parentWindow_logs hw
  have hB : (0:ℝ) < parentProduct old := by exact_mod_cast hw.2.1
  have hB1 : (1:ℝ) ≤ parentProduct old := by exact_mod_cast hw.2.1
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hR : residualLevel Q old ≤ (N:ℝ) := by
    apply (div_le_iff₀ hB).mpr
    calc
      Q ≤ (N:ℝ) := hw.2.2.2.1
      _ ≤ (N:ℝ)*(parentProduct old:ℝ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hB1 hN0
  apply (div_le_iff₀ hl.1).mpr
  simpa only [one_mul] using Real.log_le_log (zero_lt_one.trans hl.2.1) hR

/-- The original constant-one table keeps every closed atom. Its value
is at most one; the finite atom count is not paid 401 times in the main term. -/
theorem atomMass_sum_le_four (lower : Bool) {c : ℝ} (hc : 1 ≤ c) :
    (∑ b : FloorAtom, atomMass lower b c) ≤ 4 := by
  have hpoint (w : ℝ) : (∑ b : FloorAtom, startAtomDensity lower b c w) ≤
      (Icc (1:ℝ) 5).indicator (fun _ => (1:ℝ)) w := by
    by_cases hw : w ∈ Icc c 5
    · have hamb : w ∈ Icc (1:ℝ) 5 := ⟨hc.trans hw.1,hw.2⟩
      have he : (∑ b : FloorAtom, startAtomDensity lower b c w) =
          buchstabKernel w*tableFunction lower oneNumerators w := by
        unfold tableFunction
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hatom : w ∈ tableAtomSet lower b
        · simp only [startAtomDensity,indicator_of_mem ⟨hw,hatom⟩,
            indicator_of_mem hatom,one_floorAtomValue,mul_one]
        · simp only [startAtomDensity,
            indicator_of_notMem (show w ∉ Icc c 5 ∩ tableAtomSet lower b from
              fun h => hatom h.2),indicator_of_notMem hatom,mul_zero]
      rw [he,indicator_of_mem hamb]
      calc
        _ ≤ buchstabKernel w*1 := mul_le_mul_of_nonneg_left
          (one_table_bounds lower w).2 (buchstabKernel_nonneg w)
        _ ≤ 1 := by simpa only [mul_one] using buchstabKernel_le_one w
    · have hz : (∑ b : FloorAtom, startAtomDensity lower b c w) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        exact indicator_of_notMem (fun h => hw h.1) _
      rw [hz]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hi : Integrable (fun w => ∑ b : FloorAtom, startAtomDensity lower b c w) :=
    integrable_finsetSum _ (fun b _ => startAtomDensity_integrable lower b c)
  have hj : Integrable ((Icc (1:ℝ) 5).indicator (fun _ => (1:ℝ))) :=
    (continuousOn_const.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  have h := integral_mono hi hj hpoint
  rw [integral_finsetSum _ (fun b _ => startAtomDensity_integrable lower b c)] at h
  simpa only [atomMass,integral_indicator_one measurableSet_Icc,Real.volume_real_Icc,
    show max (5-(1:ℝ)) 0 = 4 by norm_num] using h

theorem integralRow_sum_le_four {up : Bool} {p : PhysicalNode}
    (hg : directionGuard up p) : (∑ b : RowAtom, integralRow up p b) ≤ 4 := by
  cases up <;> simp only [Fintype.sum_sum_type,integralRow,Bool.false_eq_true,
    if_false,if_true,Finset.sum_const_zero,zero_add,add_zero]
  all_goals exact atomMass_sum_le_four _ (physicalStart_ge_one hg)

theorem strictRow_nonneg {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode} (hN : 4 ≤ N)
    (hw : parentWindow N Q old chi) (hL : residual p = physicalLevel N Q old)
    (hC : p.ceiling = chi) (hs : 1 ≤ p.argument) (b : RowAtom) :
    0 ≤ strictRow up N Q chi old p b := by
  have hpoint (lower : Bool) (c : FloorAtom) :
      0 ≤ ∑ q ∈ singleChildren (.buchstab up p.argument) N Q old chi,
        pointAtom (thetaAtom N Q (parentProduct old*q.val)) lower
          (P2EnhancedLowerPrimeChildCarriers.buchstabArgument Q old q.val) c := by
    apply Finset.sum_nonneg
    intro q hq
    exact pointAtom_nonneg (childTheta_nonneg hN hw hL
      ((mem_singleChildren_iff hw hL hC hs).mp hq).1) lower _ c
  cases up <;> cases b <;>
    simp only [strictRow,rowFrom,Bool.false_eq_true,if_false,if_true]
  all_goals first | exact hpoint _ _ | exact le_rfl

/-- Positive arithmetic row mass, with a pre-N threshold. The bound 5
is deliberately loose and strictly below the original global allowance 12. -/
theorem uniform_buchstab_row_mass {Lmin : ℝ} (hmin : 0 < Lmin) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q chi : ℝ, ∀ old : List ℕ,
      ∀ p : PhysicalNode, ∀ up : Bool,
      parentWindow N Q old chi → residual p = physicalLevel N Q old →
      p.ceiling = chi → 1 ≤ p.argument → directionGuard up p →
      Lmin ≤ physicalLevel N Q old →
      (∀ b : RowAtom, 0 ≤ strictRow up N Q chi old p b) ∧
      (∑ b : RowAtom, strictRow up N Q chi old p b) ≤ 5*thetaAtom N Q (parentProduct old) := by
  let C : ℝ := Fintype.card RowAtom
  let delta : ℝ := 1/(C+1)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdelta : C*delta ≤ 1 := by
    dsimp [delta]
    rw [mul_one_div]
    exact (div_le_one (by linarith : 0 < C+1)).mpr (by linarith)
  obtain ⟨T,hT⟩ := uniform_closed_row_atom_error hmin (le_max_left Lmin 1) hd
  refine ⟨max 4 T, ?_⟩
  intro N hN Q chi old p up hw hL hceil hs hg hfloor
  have hN4 : 4 ≤ N := by omega
  have ht : 0 ≤ thetaAtom N Q (parentProduct old) :=
    thetaAtom_nonneg hN4 hw.2.1 (parentWindow_logs hw).2.1
  have hcompact : physicalLevel N Q old ∈ Icc Lmin (max Lmin 1) :=
    ⟨hfloor,(physicalLevel_le_one hw).trans (le_max_right _ _)⟩
  have he := hT N (by omega) Q chi old p up hw hL hceil hg hcompact
  refine ⟨fun b => strictRow_nonneg hN4 hw hL hceil hs b, ?_⟩
  calc
    _ ≤ ∑ b : RowAtom, closedRow up N Q old p b := by
      apply Finset.sum_le_sum
      intro b hb
      rw [closedRow_eq_add hw hL hceil hs b]
      exact le_add_of_nonneg_right (ceilingRow_bounds hN4 hw hL b).1
    _ ≤ ∑ b : RowAtom, (thetaAtom N Q (parentProduct old)*integralRow up p b+
        delta*thetaAtom N Q (parentProduct old)) := by
      apply Finset.sum_le_sum
      intro b hb
      have hbnd := (abs_le.mp (he b)).2
      linarith
    _ = thetaAtom N Q (parentProduct old)*(∑ b : RowAtom, integralRow up p b)+
        (C*delta)*thetaAtom N Q (parentProduct old) := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul,C]
      ring
    _ ≤ thetaAtom N Q (parentProduct old)*4+1*thetaAtom N Q (parentProduct old) :=
      add_le_add (mul_le_mul_of_nonneg_left (integralRow_sum_le_four hg) ht)
        (mul_le_mul_of_nonneg_right hdelta ht)
    _ = _ := by ring

/-- Simultaneous actual error and mass supply for both Buchstab rows,
with only a positive lower residual floor left for the full graph to supply.
The final count/base/history obligations are not parameters disguised as data. -/
theorem immutable430_uniform_buchstab_supply {Lmin epsilon : ℝ}
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
      ((∑ i ∈ S, sigma i*absoluteBuchstabError (up i) N Q (chi i) (old i) (p i)
          (precedingH (g i)) (precedingh (g i))) ≤
        epsilon*parentTheta N Q S (fun i => parentProduct (old i)) sigma) ∧
      (∀ i ∈ S, ∀ b : RowAtom, 0 ≤ strictRow (up i) N Q (chi i) (old i) (p i) b) ∧
      ((∑ i ∈ S, sigma i*(∑ b : RowAtom, strictRow (up i) N Q (chi i) (old i) (p i) b)) ≤
        5*parentTheta N Q S (fun i => parentProduct (old i)) sigma) := by
  obtain ⟨Te,hTe⟩ := immutable430_uniform_buchstab_absolute hmin (le_max_left Lmin 1) he
  obtain ⟨Tm,hTm⟩ := uniform_buchstab_row_mass hmin
  refine ⟨max Te Tm, ?_⟩
  intro N hN Q ι S old p chi sigma up g hw hL hC hs hg hsigma hfloor
  have hmass (i : ι) (hi : i ∈ S) := hTm N (by omega) Q (chi i) (old i) (p i) (up i)
    (hw i hi) (hL i hi) (hC i hi) (hs i hi) (hg i hi) (hfloor i hi)
  refine ⟨hTe N (by omega) Q S old p chi sigma up g hw hL hC hs hg hsigma
    (fun i hi => ⟨hfloor i hi,(physicalLevel_le_one (hw i hi)).trans (le_max_right _ _)⟩),
    fun i hi b => (hmass i hi).1 b, ?_⟩
  unfold parentTheta
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [mul_assoc,mul_comm,mul_left_comm] using
    mul_le_mul_of_nonneg_left (hmass i hi).2 (hsigma i hi)

end
end ImbalancedChen.Part5OriginalH430BuchstabLocalMass
