import ImbalancedChen.Part5OriginalH430RequestedMember
import ImbalancedChen.Part5OriginalH430RequestedBankRows
import ImbalancedChen.Part5OriginalH430SelectedFixedReadSupply
import ImbalancedChen.Part5OriginalH430LiteralAbsoluteBudget

/-!
Raw local bank suppliers instantiated for BOTH request modes, not for the
old scalar-owner bankFamily. SOURCE ONLY / UNCOMPILED.
External prime-profile limits are reused at their existing interfaces;
the new proof only assembles manuscript-local exact dictionaries and fees.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedLocalBankSupply

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalBuchstabActualRowLimits
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles Part5OriginalH430LiteralBankBudget
open Part5OriginalH430LiteralAbsoluteBudget Part5OriginalH430FixedReadRows
open Part5OriginalH430SelectedFixedReadSupply
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedBankRows
open Part5OriginalH430BankSlotTargets

/-- Pointwise equality with the generated list, including specified-cell
requests which need not lie in the old scalar-owner selected family. -/
theorem children_eq_bank {N g : ℕ} {Q : ℝ} {r : Request} {i : Fin 200} {k : Fin 106}
    (hs : Selected g r i (.bank k)) :
    children N Q g r = bankEdges N Q r (actionOfSlot k) := by
  simp only [children,hs.1,hs.2,branchEdges]

theorem requested_bank_row_eq {N g : ℕ} {Q : ℝ} {r : Request} {i : Fin 200} {k : Fin 106}
    (hr : Coherent N Q r) (hs : Selected g r i (.bank k)) (b : RowAtom) :
    edgeRow Q r (children N Q g r) b = cellReadRow N Q r.old r.node.physical (actionOfSlot k) b := by
  rw [children_eq_bank hs]
  exact bank_edgeRow_eq (coherent_window hr) (coherent_residual hr) _ b

def requestError (N : ℕ) (Q : ℝ) (r : Request) (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ b : RowAtom,
    |edgeRow Q r (children N Q g.val r) b - thetaAtom N Q (parentProduct r.old)*cellReadIdeal a b| *
      |oldAtomValue (precedingH g) (precedingh g) b|

theorem requestError_nonneg (N : ℕ) (Q : ℝ) (r : Request) (g : Fin 430) (a : Original106Action) :
    0 ≤ requestError N Q r g a :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem requestError_eq_pointError {N : ℕ} {Q : ℝ} {r : Request} {g : Fin 430}
    {i : Fin 200} {k : Fin 106} (hr : Coherent N Q r) (hs : Selected g.val r i (.bank k)) :
    requestError N Q r g (actionOfSlot k) =
      pointError N Q r.old r.node.physical g (actionOfSlot k) := by
  simp only [requestError,pointError,requested_bank_row_eq hr hs]

/-- No base or candidate bound is inferred from this feedback estimate.
Residual floor and alpha are geometric local parameters here; the next
module supplies both from the actual generated root history. -/
theorem uniform_requested_bank_local {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ r : Request,
      ∀ g : Fin 430, ∀ i : Fin 200, ∀ k : Fin 106,
      Coherent N Q r → Selected g.val r i (.bank k) →
      frozenResidualFloor ≤ physicalLevel N Q r.old →
      2 ≤ P2OriginalChildPhysicalNormalization.alpha
        (Real.log (parentProduct r.old:ℝ)/Real.log (N:ℝ)) (physicalLevel N Q r.old) →
      requestError N Q r g (actionOfSlot k) ≤ epsilon*thetaAtom N Q (parentProduct r.old) ∧
      (∀ b, 0 ≤ edgeRow Q r (children N Q g.val r) b) ∧
      (∑ b : RowAtom, edgeRow Q r (children N Q g.val r) b) ≤
        12*thetaAtom N Q (parentProduct r.old) ∧
      (thetaAtom N Q (parentProduct r.old) = 0 →
        requestError N Q r g (actionOfSlot k) = 0 ∧
        ∀ b, edgeRow Q r (children N Q g.val r) b = 0) := by
  let Lmax := max frozenResidualFloor 1
  have he2 : (0:ℝ) < epsilon/2 := by positivity
  obtain ⟨Te,hTe⟩ := immutable430_literal_absoluteCoefficientError (Lmax := Lmax)
    frozenResidualFloor_pos (le_max_left _ _) he2
  obtain ⟨Tm,hTm⟩ := all106_parentTheta_mass_le_twelve (Lmax := Lmax)
    frozenResidualFloor_pos (le_max_left _ _)
  obtain ⟨T1,hT1⟩ := Part5OriginalH430W1StrictRows.uniform_rowGap frozenResidualFloor_pos he2
  obtain ⟨T2,hT2lo,hT2⟩ := Part5OriginalH430W2DiscardedMass.uniform_W2_rowGap
    frozenResidualFloor_pos he2
  refine ⟨max 4 (max Te (max Tm (max T1 T2))),le_max_left _ _,?_⟩
  intro N hN Q r g i k hr hs hfloor halpha
  have hN4 : 4 ≤ N := by omega
  have hw := coherent_window hr
  have hres := coherent_residual hr
  have hL1 := parent_level_le_one hw
  have hLrange : physicalLevel N Q r.old ∈ Icc frozenResidualFloor Lmax :=
    ⟨hfloor,hL1.trans (le_max_right _ _)⟩
  have hdN : parentProduct r.old ≤ N := by
    exact_mod_cast hw.2.2.1.le.trans hw.2.2.2.1
  have hQ : Q = (parentProduct r.old:ℝ)*(N:ℝ)^(physicalLevel N Q r.old) := by
    simpa only [P2OriginalPositiveSameQMassLift.residualExponent,physicalLevel,residualLevel]
      using sameQ_eq_residualExponent hr.target_gt_one hw.2.1
        (zero_lt_one.trans (parentWindow_logs hw).2.1)
  have ht := thetaAtom_nonneg hN4 hw.2.1 (parentWindow_logs hw).2.1
  have hceil : physicalLevel N Q r.old / actionTarget (actionOfSlot k) ≤ r.node.physical.ceiling := by
    rw [← hres]
    exact (requested_bank_tests hr hs).2.2
  have harith :
      (∑ b : RowAtom,
        |arithmeticRow N Q (physicalLevel N Q r.old) (parentProduct r.old) (actionOfSlot k) b -
          thetaAtom N Q (parentProduct r.old)*idealRow (actionOfSlot k) b| *
          |oldAtomValue (precedingH g) (precedingh g) b|) ≤
        (epsilon/2)*thetaAtom N Q (parentProduct r.old) := by
    have h := hTe N (by omega) g Q ({()} : Finset Unit)
      (fun _ => physicalLevel N Q r.old) (fun _ => parentProduct r.old) (fun _ => (1:ℝ))
      (fun _ _ => hLrange) (fun _ _ => hw.2.1) (fun _ _ => hQ)
      (fun _ _ => zero_le_one) (fun _ _ => halpha) (actionOfSlot k)
    simpa only [absoluteCoefficientError,parentRow,parentTheta,Finset.sum_singleton,one_mul] using h
  have hm : (∑ b : RowAtom,
      arithmeticRow N Q (physicalLevel N Q r.old) (parentProduct r.old) (actionOfSlot k) b) ≤
      12*thetaAtom N Q (parentProduct r.old) := by
    rw [arithmeticRow_sum]
    have h := hTm N (by omega) Q ({()} : Finset Unit)
      (fun _ => physicalLevel N Q r.old) (fun _ => parentProduct r.old) (fun _ => (1:ℝ))
      (fun _ => actionOfSlot k) (fun _ _ => hLrange) (fun _ _ => hw.2.1)
      (fun _ _ => hQ) (fun _ _ => zero_le_one) (fun _ _ => halpha)
    simpa only [parentTheta,Finset.sum_singleton,one_mul] using h
  have htransfer :
      (∑ b : RowAtom,
        |arithmeticRow N Q (physicalLevel N Q r.old) (parentProduct r.old) (actionOfSlot k) b -
          oldProductionRow N Q r.old r.node.physical (actionOfSlot k) b| *
          |oldAtomValue (precedingH g) (precedingh g) b|) ≤
        (epsilon/2)*thetaAtom N Q (parentProduct r.old) ∧
      ∀ b, oldProductionRow N Q r.old r.node.physical (actionOfSlot k) b ≤
        arithmeticRow N Q (physicalLevel N Q r.old) (parentProduct r.old) (actionOfSlot k) b := by
    cases ha : actionOfSlot k with
    | inl ij =>
        rcases ij with ⟨u,v⟩
        have hc : physicalLevel N Q r.old/W1Target u ≤ r.node.physical.ceiling := by
          simpa only [ha,actionTarget] using hceil
        constructor
        · exact (hT1 N (by omega)).2 Q r.node.physical.ceiling r.old u v hw hfloor hc g
        · intro b
          exact (Part5OriginalH430W1StrictRows.strictRow_bounds hN4 hw
            (physicalLevel N Q r.old) u v hc b).2
    | inr j =>
        have hc : physicalLevel N Q r.old/(originalW2At j).s ≤ r.node.physical.ceiling := by
          simpa only [ha,actionTarget] using hceil
        have h := hT2 N (by omega) Q (physicalLevel N Q r.old) (parentProduct r.old)
          hfloor hL1 hw.2.1 hdN hQ j g
        have heq (b : RowAtom) := Part5OriginalH430W2ProductionRows.productionRow_eq_freshRow
          hw hres j hc b
        constructor
        · simpa only [oldProductionRow,heq,Part5OriginalH430W2DiscardedMass.rowGap] using h.1
        · intro b
          simpa only [oldProductionRow,heq] using (h.2 b).2
  have herr : requestError N Q r g (actionOfSlot k) ≤ epsilon*thetaAtom N Q (parentProduct r.old) := by
    rw [requestError_eq_pointError hr hs,pointError_exact]
    unfold oldPointError
    calc
      _ ≤ (∑ b : RowAtom,
          |arithmeticRow N Q (physicalLevel N Q r.old) (parentProduct r.old) (actionOfSlot k) b -
            oldProductionRow N Q r.old r.node.physical (actionOfSlot k) b| *
            |oldAtomValue (precedingH g) (precedingh g) b|) +
        ∑ b : RowAtom,
          |arithmeticRow N Q (physicalLevel N Q r.old) (parentProduct r.old) (actionOfSlot k) b -
            thetaAtom N Q (parentProduct r.old)*idealRow (actionOfSlot k) b| *
            |oldAtomValue (precedingH g) (precedingh g) b| := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro b _
        have h := abs_sub_le (oldProductionRow N Q r.old r.node.physical (actionOfSlot k) b)
          (arithmeticRow N Q (physicalLevel N Q r.old) (parentProduct r.old) (actionOfSlot k) b)
          (thetaAtom N Q (parentProduct r.old)*idealRow (actionOfSlot k) b)
        rw [abs_sub_comm (oldProductionRow N Q r.old r.node.physical (actionOfSlot k) b)
          (arithmeticRow N Q (physicalLevel N Q r.old) (parentProduct r.old) (actionOfSlot k) b)] at h
        simpa only [add_mul] using mul_le_mul_of_nonneg_right h (abs_nonneg
          (oldAtomValue (precedingH g) (precedingh g) b))
      _ ≤ (epsilon/2)*thetaAtom N Q (parentProduct r.old) +
          (epsilon/2)*thetaAtom N Q (parentProduct r.old) := add_le_add htransfer.1 harith
      _ = _ := by ring
  have hrow (b : RowAtom) : 0 ≤ edgeRow Q r (children N Q g.val r) b := by
    rw [requested_bank_row_eq hr hs]
    exact cellReadRow_nonneg hN4 hw _ b
  have hmass : (∑ b : RowAtom, edgeRow Q r (children N Q g.val r) b) ≤
      12*thetaAtom N Q (parentProduct r.old) := by
    simp_rw [requested_bank_row_eq hr hs]
    rw [cellReadRow_mass]
    exact (Finset.sum_le_sum (fun b _ => htransfer.2 b)).trans hm
  refine ⟨herr,hrow,hmass,?_⟩
  intro hz
  constructor
  · exact le_antisymm (by simpa only [hz,mul_zero] using herr) (requestError_nonneg _ _ _ _ _)
  · intro b
    have hb := Finset.single_le_sum (fun c _ => hrow c) (Finset.mem_univ b)
    exact le_antisymm (by simpa only [hz,mul_zero] using hb.trans hmass) (hrow b)

/-- The signed applied estimate is downstream of coefficientwise
absolute error, never used as a replacement for that stronger bound. -/
theorem request_applied_error_le (N : ℕ) (Q : ℝ) (r : Request) (g : Fin 430)
    (a : Original106Action) :
    |edgeValue Q (iterate g.val) r (children N Q g.val r) -
      thetaAtom N Q (parentProduct r.old)*idealCellProfile (precedingH g) (precedingh g) a| ≤
      requestError N Q r g a := by
  rw [← edgeRow_value,idealCellProfile,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc,← sub_mul,abs_mul]

end
end ImbalancedChen.Part5OriginalH430RequestedLocalBankSupply
