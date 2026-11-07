import ImbalancedChen.Part5OriginalH430GeometricWalls
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual M common/full/root fibres are measurable.  This file supplies
the missing fibre facts without equipping arbitrary labels with a
purported arithmetic realization.  In particular, measurability is not a
smooth-box approximation theorem.
-/

namespace ImbalancedChen.Part5OriginalH430CellMeasurability

noncomputable section
open Set MeasureTheory Classical
open Part5OriginalH430AbsoluteQueries Part5OriginalH430GeometricWalls
open Part5OriginalH430FrozenRootRefinement P2PhysicalIncomingPrefixCells

theorem measurableSet_decide_fiber {X : Type*} [MeasurableSpace X]
    {S : Set X} (hS : MeasurableSet S) (b : Bool) :
    MeasurableSet {x | decide (x ∈ S) = b} := by
  cases b with
  | false =>
      convert hS.compl using 1
      ext x
      simp
  | true =>
      convert hS using 1
      ext x
      simp

theorem commonCell_measurable (p : Primitive) (n : ℕ) (c : CommonCode p n) :
    MeasurableSet (commonCell p n c) := by
  have he : commonCell p n c =
      (⋂ k : Fin (n + 1), ⋂ b : Part5OriginalUpsilon5CausalDictionary.FloorAtom,
        {x | queryApprox p b k.val x = (c.1 k b).val}) ∩
      (⋂ b : Part5OriginalUpsilon5CausalDictionary.FloorAtom,
        {x | decide (x ∈ atomSet p b) = c.2 b}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx
      refine ⟨fun k b => ?_, fun b => ?_⟩
      · exact congrArg Subtype.val
          (congrFun (congrFun (congrArg Prod.fst hx) k) b)
      · exact congrFun (congrArg Prod.snd hx) b
    · rintro ⟨hvalues, hatoms⟩
      apply Prod.ext
      · funext k b
        exact Subtype.ext (hvalues k b)
      · funext b
        exact hatoms b
  rw [he]
  exact (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun b =>
    measurableSet_eq_fun (queryApprox p b k.val).measurable measurable_const))).inter
      (MeasurableSet.iInter (fun b =>
        measurableSet_decide_fiber (atomSet_measurable p b) (c.2 b)))

theorem sign_negative_iff (v : ℝ) : sign v = .negative ↔ v < 0 := by
  unfold sign
  split_ifs <;> simp_all

theorem sign_positive_iff (v : ℝ) : sign v = .positive ↔ 0 < v := by
  unfold sign
  split_ifs <;> simp_all <;> linarith

theorem measurableSet_sign_fiber {X : Type*} [MeasurableSpace X]
    {f : X → ℝ} (hf : Measurable f) (s : Sign) :
    MeasurableSet {x | sign (f x) = s} := by
  cases s with
  | negative =>
      simpa only [sign_negative_iff] using measurableSet_lt hf measurable_const
  | zero =>
      simpa only [sign_zero_iff] using measurableSet_eq_fun hf
        (measurable_const : Measurable (fun _ : X => (0 : ℝ)))
  | positive =>
      simpa only [sign_positive_iff] using measurableSet_lt measurable_const hf

theorem fullCell_measurable (p : Primitive) (n : ℕ) (c : FullCode p n) :
    MeasurableSet (fullCell p n c) := by
  have he : fullCell p n c = commonCell p n c.1 ∩
      (⋂ j : Wall, {x | sign (wall p j x) = c.2.1 j}) ∩
      (⋂ k : Fin (n + 1), ⋂ j : Wall,
        {x | decide (x ∈ puncturedTube (wall p j) k.val) = c.2.2 k j}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx
      refine ⟨⟨congrArg Prod.fst hx, fun j => ?_⟩, fun k j => ?_⟩
      · exact congrFun (congrArg (fun z : FullCode p n => z.2.1) hx) j
      · exact congrFun (congrFun (congrArg (fun z : FullCode p n => z.2.2) hx) k) j
    · rintro ⟨⟨hcommon, hsign⟩, htube⟩
      apply Prod.ext hcommon
      apply Prod.ext
      · exact funext hsign
      · exact funext (fun k => funext (htube k))
  rw [he]
  exact ((commonCell_measurable p n c.1).inter
      (MeasurableSet.iInter (fun j => measurableSet_sign_fiber
        (wall_measurable p j) (c.2.1 j)))).inter
    (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun j =>
      measurableSet_decide_fiber
        (puncturedTube_measurable (wall_measurable p j) k.val) (c.2.2 k j))))

theorem exponentCode_fiber_some {a b : ℝ} (hab : a < b)
    (n : ℕ) (j : Fin (n + 1)) :
    {x | exponentCode a b n x = some j} = exponentCell a b n (some j) := by
  ext x
  constructor
  · intro hx
    by_cases hi : x ∈ Ico a b
    · have hm := exponentCode_membership (m := n) ⟨hi.1, hi.2.le⟩
      simpa only [hx] using hm
    · simp [exponentCode, hi] at hx
  · intro hx
    have hb := logPrimeMeshLoHi_bounds (d := 1) hab n (fun _ => j) 0
    have hbox : x ∈ Icc a b :=
      ⟨hb.1.trans hx.1, hx.2.le.trans hb.2.2⟩
    exact exponentCode_eq_of_cell hab hbox hx

theorem exponentCode_fiber_none (a b : ℝ) (n : ℕ) :
    {x | exponentCode a b n x = none} = (Ico a b)ᶜ := by
  ext x
  by_cases hx : x ∈ Ico a b <;> simp [exponentCode, hx]

theorem exponentCode_fiber_measurable {a b : ℝ} (hab : a < b)
    (n : ℕ) (c : CellCode n) : MeasurableSet {x | exponentCode a b n x = c} := by
  cases c with
  | none => rw [exponentCode_fiber_none]; exact measurableSet_Ico.compl
  | some j =>
      rw [exponentCode_fiber_some hab]
      exact measurableSet_Ico

theorem rootCell_measurable (n : ℕ) (c : RootCode n) :
    MeasurableSet (rootCell n c) := by
  have he : rootCell n c =
      ⋂ j : Fin (n + 1), {nu | exponentCode 0 1 j.val nu = c j} := by
    ext nu
    simp only [rootCell, rootCode, Set.mem_setOf_eq, Set.mem_iInter]
    exact funext_iff
  rw [he]
  exact MeasurableSet.iInter (fun j => exponentCode_fiber_measurable
    (by norm_num : (0 : ℝ) < 1) j.val (c j))

section FrozenLevel

local instance (n : ℕ) : MeasurableSpace (CellCode n) := ⊤

theorem measurable_exponentCode {a b : ℝ} (hab : a < b) (n : ℕ) :
    Measurable (exponentCode a b n) := by
  apply measurable_to_countable'
  intro c
  exact exponentCode_fiber_measurable hab n c

theorem measurable_rawLower (n : ℕ) : Measurable (rawLower n) :=
  (measurable_of_finite (lowerEndpoint n)).comp
    (measurable_exponentCode (by norm_num : (0 : ℝ) < 1) n)

theorem measurable_frozenLevel (n : ℕ) : Measurable (frozenLevel n) := by
  induction n with
  | zero => exact measurable_rawLower 0
  | succ n ih => exact ih.max (measurable_rawLower (n + 1))

end FrozenLevel
end
end ImbalancedChen.Part5OriginalH430CellMeasurability
