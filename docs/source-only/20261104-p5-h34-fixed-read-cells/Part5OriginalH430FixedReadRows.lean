import ImbalancedChen.Part5OriginalH430FixedReadDictionary
import ImbalancedChen.Part5OriginalH430SelectedStrictW1Supply
import ImbalancedChen.Part5OriginalH430SelectedProductionW2Supply

/-!
SOURCE ONLY / UNCOMPILED.

Separate specified-cell FIXED reads from scalar closed-atom INTEGRAL reads.
Both the arithmetic and ideal row receive the same explicit fixed-channel
change. Their discrepancy is identical, not merely bounded. This does NOT
rewrite a fixed old-cell value into the scalar adjacent minimum.
No new prime-distribution result or count-defect licence is assumed.
-/
namespace ImbalancedChen.Part5OriginalH430FixedReadRows

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430LiteralBankBudget
open P2OriginalHalfOpenProfileCarrier P2OriginalBankThetaMassLimits P2OriginalBankChildPrimeMass
open Part5OriginalH430FixedReadDictionary


/-- This is a coefficient index for a specified CLOSED cell. An inl cell
index here does not assert that the physical query lies in its OPEN atom. -/
def cellKernel (theta : ℝ) (i : Fin 200) (b : RowAtom) : ℝ :=
  if b = .inl (.inl i) then theta else 0

def scalarPoint (theta s : ℝ) : RowAtom → ℝ
  | .inl b => pointAtom theta false s b
  | .inr _ => 0

def readFixed (theta : ℝ) : Original106Action → RowAtom → ℝ
  | .inl (_,j), b => cellKernel theta (w1Cell j) b
  | .inr j, b => (4*cellKernel theta (w2Cell j true) b +
      cellKernel theta (w2Cell j false) b)/5

def scalarFixed (theta : ℝ) : Original106Action → RowAtom → ℝ
  | .inl (_,j), b => scalarPoint theta (W1Anchor j) b
  | .inr j, b => (4*scalarPoint theta (originalW2At j).s0 b +
      scalarPoint theta (originalW2At j).phi1 b)/5

theorem cellKernel_scale (theta : ℝ) (i : Fin 200) (b : RowAtom) :
    cellKernel theta i b = theta*cellKernel 1 i b := by
  by_cases hb : b = .inl (.inl i) <;> simp [cellKernel,hb]

theorem scalarPoint_scale (theta s : ℝ) (b : RowAtom) :
    scalarPoint theta s b = theta*scalarPoint 1 s b := by
  cases b <;> simp [scalarPoint,pointAtom,mul_assoc]

theorem readFixed_scale (theta : ℝ) (a : Original106Action) (b : RowAtom) :
    readFixed theta a b = theta*readFixed 1 a b := by
  rcases a with ⟨i,j⟩ | j
  · exact cellKernel_scale _ _ _
  · simp only [readFixed,cellKernel_scale theta]
    ring

theorem scalarFixed_scale (theta : ℝ) (a : Original106Action) (b : RowAtom) :
    scalarFixed theta a b = theta*scalarFixed 1 a b := by
  rcases a with ⟨i,j⟩ | j
  · exact scalarPoint_scale _ _ _
  · simp only [scalarFixed,scalarPoint_scale theta]
    ring

theorem cellKernel_mass (theta : ℝ) (i : Fin 200) :
    (∑ b : RowAtom, cellKernel theta i b) = theta := by simp [cellKernel]

theorem scalarPoint_mass (theta s : ℝ) {i : Fin 200}
    (hs : s ∈ P2Selected430CausalOccurrenceExporter.queryCell i) :
    (∑ b : RowAtom, scalarPoint theta s b) = theta := by
  have h := pointAtom_value theta false s oneNumerators
  rw [one_lookup_of_cell hs,mul_one] at h
  simpa only [Fintype.sum_sum_type,scalarPoint,Finset.sum_const_zero,
    add_zero,one_floorAtomValue,mul_one] using h

theorem readFixed_mass (theta : ℝ) (a : Original106Action) :
    (∑ b : RowAtom, readFixed theta a b) = theta := by
  rcases a with ⟨i,j⟩ | j
  · exact cellKernel_mass _ _
  · simp only [readFixed,← Finset.sum_div,Finset.sum_add_distrib,
      ← Finset.mul_sum,cellKernel_mass]
    ring

theorem scalarFixed_mass (theta : ℝ) (a : Original106Action) :
    (∑ b : RowAtom, scalarFixed theta a b) = theta := by
  rcases a with ⟨i,j⟩ | j
  · exact scalarPoint_mass theta _ (w1Cell_contains j)
  · simp only [scalarFixed,← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [scalarPoint_mass theta _ (w2Cell_contains j true),
      scalarPoint_mass theta _ (w2Cell_contains j false)]
    ring

theorem readFixed_nonneg {theta : ℝ} (ht : 0 ≤ theta)
    (a : Original106Action) (b : RowAtom) : 0 ≤ readFixed theta a b := by
  have hc (i : Fin 200) : 0 ≤ cellKernel theta i b := by
    unfold cellKernel
    split_ifs <;> first | exact ht | exact le_rfl
  rcases a with ⟨i,j⟩ | j
  · exact hc _
  · exact div_nonneg (add_nonneg (mul_nonneg (by norm_num) (hc _)) (hc _)) (by norm_num)

theorem cellKernel_value (theta : ℝ) (i : Fin 200) (H h : Fin 200 → ℤ) :
    (∑ b : RowAtom, cellKernel theta i b*oldAtomValue H h b) = theta*floorValue H i := by
  simp [cellKernel,oldAtomValue,floorAtomValue]

theorem readFixed_value (theta : ℝ) (a : Original106Action) (H h : Fin 200 → ℤ) :
    (∑ b : RowAtom, readFixed theta a b*oldAtomValue H h b) = theta*fixedValue H a := by
  rcases a with ⟨i,j⟩ | j
  · exact cellKernel_value _ _ _ _
  · simp only [readFixed,div_mul_eq_mul_div,add_mul,mul_assoc,
      ← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum,cellKernel_value,fixedValue]
    ring

def oldProductionRow (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode) :
    Original106Action → RowAtom → ℝ
  | .inl (i,j) => Part5OriginalH430W1StrictRows.strictRow N Q p.ceiling old i j
  | .inr j => Part5OriginalH430W2ProductionRows.productionRow N Q old p j

/-- Integral channels remain the ACTUAL strict prime-child sums. -/
def dynamicRow (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode) :
    Original106Action → RowAtom → ℝ
  | .inl _, .inl _ => 0
  | .inl (i,j), .inr b => Part5OriginalH430W1StrictRows.strictChildAtom N Q p.ceiling old i j b/2
  | .inr j, .inl b => (∑ k : Fin 4, Part5OriginalH430W2ProductionRows.productionPairAtom N Q old p j k b)/5
  | .inr j, .inr b => (∑ k : Fin 3, Part5OriginalH430W2ProductionRows.productionSingleAtom N Q old p j k b)/5

theorem oldProductionRow_split (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (a : Original106Action) (b : RowAtom) :
    oldProductionRow N Q old p a b =
      scalarFixed (thetaAtom N Q (parentProduct old)) a b + dynamicRow N Q old p a b := by
  rcases a with ⟨i,j⟩ | j <;> cases b <;>
    simp [oldProductionRow,Part5OriginalH430W1StrictRows.strictRow,Part5OriginalH430W2ProductionRows.productionRow,scalarFixed,scalarPoint,dynamicRow] <;> ring

def cellReadRow (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (a : Original106Action) (b : RowAtom) : ℝ :=
  readFixed (thetaAtom N Q (parentProduct old)) a b + dynamicRow N Q old p a b

/-- Explicit new ideal row. It is NOT asserted equal to the old scalar
profile; only its fixed channel has changed to literal specified-cell reads. -/
def cellReadIdeal (a : Original106Action) (b : RowAtom) : ℝ :=
  idealRow a b + readFixed 1 a b - scalarFixed 1 a b


/-- The ideal integral channels are unchanged as well. -/
def dynamicIdeal : Original106Action → RowAtom → ℝ
  | .inl _, .inl _ => 0
  | .inl (i,j), .inr b =>
      singletonIntegralAtom (1/W1Anchor j) (1/W1Target i) (W1Anchor j) b/2
  | .inr j, .inl b => (∑ k : Fin 4, pairIntegralAtom (originalW2At j) k b)/5
  | .inr j, .inr b => (∑ k : Fin 3, singletonIntegralAtom
      (P5OriginalActionMassBound.a0 (originalW2At j))
      (singletonTop (originalW2At j) k)
      (originalW2At j).s0 b)/5

theorem cellReadIdeal_split (a : Original106Action) (b : RowAtom) :
    cellReadIdeal a b = readFixed 1 a b + dynamicIdeal a b := by
  rcases a with ⟨i,j⟩ | j <;> cases b <;>
    simp [cellReadIdeal,idealRow,scalarFixed,scalarPoint,dynamicIdeal] <;> ring

theorem cellReadIdeal_mass (a : Original106Action) :
    (∑ b : RowAtom, cellReadIdeal a b) = ∑ b : RowAtom, idealRow a b := by
  simp only [cellReadIdeal,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    readFixed_mass,scalarFixed_mass,add_sub_cancel_right]

theorem cellReadIdeal_nonneg (a : Original106Action) (b : RowAtom) :
    0 ≤ cellReadIdeal a b := by
  have hs (lo hi s0 : ℝ) (c : FloorAtom) : 0 ≤ singletonIntegralAtom lo hi s0 c :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall singletonKernel_nonneg)
  have hp (p : W2Parameters) (k : Fin 4) (c : FloorAtom) : 0 ≤ pairIntegralAtom p k c :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall pairKernel_nonneg)
  rw [cellReadIdeal_split]
  apply add_nonneg (readFixed_nonneg zero_le_one a b)
  rcases a with ⟨i,j⟩ | j
  · cases b with
    | inl b => exact le_rfl
    | inr b => exact div_nonneg (hs _ _ _ _) (by norm_num)
  · cases b with
    | inl b => exact div_nonneg (Finset.sum_nonneg (fun k _ => hp _ k _)) (by norm_num)
    | inr b => exact div_nonneg (Finset.sum_nonneg (fun k _ => hs _ _ _ _)) (by norm_num)

/-- Exact coefficient identity BEFORE absolute values and before any
parent aggregation. No asymptotic error or base payment is added. -/
theorem discrepancy_exact (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (a : Original106Action) (b : RowAtom) :
    cellReadRow N Q old p a b - thetaAtom N Q (parentProduct old)*cellReadIdeal a b =
      oldProductionRow N Q old p a b - thetaAtom N Q (parentProduct old)*idealRow a b := by
  rw [oldProductionRow_split]
  unfold cellReadRow cellReadIdeal
  rw [readFixed_scale (thetaAtom N Q (parentProduct old)),
    scalarFixed_scale (thetaAtom N Q (parentProduct old))]
  ring

theorem cellReadRow_mass (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (a : Original106Action) :
    (∑ b : RowAtom, cellReadRow N Q old p a b) =
      ∑ b : RowAtom, oldProductionRow N Q old p a b := by
  simp_rw [cellReadRow,oldProductionRow_split]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,readFixed_mass,scalarFixed_mass]

theorem single_child_theta_nonneg {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {r : SingleRule} {q : Fin (N+1)} (hN : 4 ≤ N)
    (hq : q ∈ singleChildren r N Q old chi) :
    0 ≤ thetaAtom N Q (parentProduct (singleWord old q.val)) := by
  have hm := mem_singleChildren.mp hq
  have hd : 0 < parentProduct (singleWord old q.val) := by
    rw [(singleWord_history old q.val).2.2]
    exact mul_pos hm.2.1.2.1 hm.1.1.pos
  exact thetaAtom_nonneg hN hd (single_actual_residual hq).1

theorem pair_child_theta_nonneg {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {j : Fin 36} {k : Fin 4} {q : Fin (N+1) × Fin (N+1)} (hN : 4 ≤ N)
    (hq : q ∈ pairChildren j k N Q old chi) :
    0 ≤ thetaAtom N Q (parentProduct (pairWord old q.1.val q.2.val)) := by
  have hm := mem_pairChildren.mp hq
  have hd : 0 < parentProduct (pairWord old q.1.val q.2.val) := by
    rw [(pairWord_history old q.1.val q.2.val).2.2]
    exact mul_pos (mul_pos hm.2.1.2.1 hm.1.2.1.pos) hm.1.1.1.pos
  exact thetaAtom_nonneg hN hd (pair_actual_residual hq).1

theorem dynamicRow_nonneg {N : ℕ} (hN : 4 ≤ N) (Q : ℝ) (old : List ℕ)
    (p : PhysicalNode) (a : Original106Action) (b : RowAtom) :
    0 ≤ dynamicRow N Q old p a b := by
  rcases a with ⟨i,j⟩ | j
  · cases b with
    | inl b => exact le_rfl
    | inr b =>
      apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 2)
      apply Finset.sum_nonneg
      intro q hq
      unfold Part5OriginalH430W1StrictRows.atomTerm
      split_ifs
      · simpa only [(singleWord_history old q.val).2.2] using single_child_theta_nonneg hN hq
      · exact le_rfl
  · cases b with
    | inl b =>
      apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 5)
      apply Finset.sum_nonneg
      intro k _
      apply Finset.sum_nonneg
      intro q hq
      split_ifs
      · exact pair_child_theta_nonneg hN hq
      · exact le_rfl
    | inr b =>
      apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 5)
      apply Finset.sum_nonneg
      intro k _
      apply Finset.sum_nonneg
      intro q hq
      split_ifs
      · exact single_child_theta_nonneg hN hq
      · exact le_rfl

theorem cellReadRow_nonneg {N : ℕ} {Q : ℝ} {old : List ℕ} {p : PhysicalNode}
    (hN : 4 ≤ N) (hw : parentWindow N Q old p.ceiling)
    (a : Original106Action) (b : RowAtom) : 0 ≤ cellReadRow N Q old p a b :=
  add_nonneg (readFixed_nonneg (thetaAtom_nonneg hN hw.2.1
    (parentWindow_logs hw).2.1) a b) (dynamicRow_nonneg hN Q old p a b)

def cellReadProfile (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (a : Original106Action) (H h : Fin 200 → ℤ) : ℝ :=
  thetaAtom N Q (parentProduct old)*fixedValue H a +
    ∑ b : RowAtom, dynamicRow N Q old p a b*oldAtomValue H h b

theorem cellReadRow_value (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (a : Original106Action) (H h : Fin 200 → ℤ) :
    (∑ b : RowAtom, cellReadRow N Q old p a b*oldAtomValue H h b) =
      cellReadProfile N Q old p a H h := by
  simp only [cellReadRow,add_mul,Finset.sum_add_distrib,readFixed_value,cellReadProfile]

theorem fixed_physical_queries (p : PhysicalNode) (z : Point) :
    (∀ i j, (perform p (.w1Fixed i j) z).argument ∈
      P2Selected430CausalOccurrenceExporter.queryCell (w1Cell j)) ∧
    (∀ j anchor, (perform p (.w2Fixed j anchor) z).argument ∈
      P2Selected430CausalOccurrenceExporter.queryCell (w2Cell j anchor)) :=
  ⟨fun _ j => w1Cell_contains j, fun j anchor => w2Cell_contains j anchor⟩

end
end ImbalancedChen.Part5OriginalH430FixedReadRows
