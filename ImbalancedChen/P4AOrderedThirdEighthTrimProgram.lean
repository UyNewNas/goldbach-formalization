import ImbalancedChen.P4AOrderedThirdStaticSixthPrograms

namespace ImbalancedChen.P4AOrderedThirdEighthTrimProgram
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P4AOriginalFourthFifthAffinePrograms
open P4AOriginalFull87SourceDictionary (Point Cell newCap comparison selected)
open P4AOriginalFull87StrictActionTrim (rowCount rowValue Margin actionSlack trim mem_trim)
open P4AOriginalFull87HistoryCore (core mem_core oldHistory thirdValue slack)
open P4AOrderedThirdStaticSixthPrograms (fullForm compForm full_eval comp_eval)
open VariableEnvelope

def rowCoeffs : (c : Cell) → Fin (rowCount c) → Fin 9 → ℚ
  | .remaining c, j => P4AOriginalRemainingEighthSources.row c j
  | .descending i,j => OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i j
  | .ascendingPair i,j => OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i j
  | .h3 i,j => (P4AOriginalFirstFailureH3Literal.sourceAffineRows i j).2

def rowForm (c : Cell) (j : Fin (rowCount c)) : Affine 8 :=
  ⟨(rowCoeffs c j 0:ℝ),fun i => (rowCoeffs c j i.succ:ℝ)⟩

theorem row_exact (c : Cell) (j : Fin (rowCount c)) (t : Point) :
    (rowForm c j).eval t=rowValue c j t := by cases c <;> rfl

def newForm : Cell → Affine 8
  | .remaining c => let a := maskAffine (P4AOriginalRemainingEighthSources.selected c)
                    (if P4AOriginalRemainingEighthSources.descendingNew c then descending a else ascending a).sub
                      (K P4AOriginalRemainingEighthSources.eta)
  | .descending _ => (descending ((X 0).add (X 7))).sub (K P2OriginalDescendingEighthLogSemantics.eta)
  | .ascendingPair _ => (ascending (((X 1).add (X 3)).add (X 7))).sub
      (K P2OriginalThirdMinorantLogDictionarySourceOnly.eta)
  | .h3 _ => (ascending (((X 1).add (X 3)).add (X 7))).sub (K P4AOriginalFirstFailureH3Literal.eta)

def cmpRemaining : P4AOriginalRemainingEighthSources.Cell → Affine 8
  | .ascending _ | .seed => descending ((X 1).add (X 2))
  | .fiftyA => ascending (((X 1).add (X 4)).add (X 5))
  | .fiftyD => descending (((X 1).add (X 4)).add (X 5))
  | _ => ascending ((X 0).add (X 3))

def cmpForm : Cell → Affine 8
  | .remaining c => cmpRemaining c
  | .descending _ => descending ((X 1).add (X 2))
  | _ => ascending ((X 0).add (X 3))

theorem new_exact (c : Cell) (t : Point) : (newForm c).eval t=newCap c t := by
  cases c with
  | remaining c =>
    by_cases h : P4AOriginalRemainingEighthSources.descendingNew c
    all_goals simp [newForm,newCap,P4AOriginalRemainingEighthSources.newCap,h,
      P4AOriginalRemainingEighthSources.selectedSum]
  | descending i => simp [newForm,newCap,P2OriginalDescendingEighthLogSemantics.newCap,
      P2OriginalDescendingEighthLogSemantics.selectedSum]
  | ascendingPair i => simp [newForm,newCap,P2OriginalThirdMinorantLogDictionarySourceOnly.newCap,
      P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum]
  | h3 i => simp [newForm,newCap,P4AOriginalFirstFailureH3Literal.M8,P4AOriginalFirstFailureH3Literal.A,A]

theorem cmp_exact (c : Cell) (t : Point) : (cmpForm c).eval t=comparison c t := by
  cases c with
  | remaining c => cases c <;> simp [cmpForm,cmpRemaining,comparison,P4AOriginalRemainingEighthSources.comparison]
  | descending i => simp [cmpForm,comparison,P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d]
  | ascendingPair i => simp [cmpForm,comparison,P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap]
  | h3 i => simp [cmpForm,comparison,P4AOriginalFirstFailureH3Literal.R6,P4AOriginalFirstFailureH3Literal.A,A]

def marginForm (c : Cell) : Margin → Affine 8
  | .positive => newForm c
  | .improvement => (newForm c).sub (cmpForm c)
  | .full j => (newForm c).sub (fullForm j)
  | .complement j => if j∈selected c then newForm c else (newForm c).sub (compForm (selected c) j)

theorem margin_exact (c : Cell) (t : Point) (j : Margin) : (marginForm c j).eval t=actionSlack c t j := by
  cases j with
  | positive => exact new_exact c t
  | improvement => simp [marginForm,actionSlack,new_exact,cmp_exact]
  | full i => simp [marginForm,actionSlack,new_exact]
  | complement i => by_cases h : i∈selected c <;> simp [marginForm,actionSlack,new_exact,h]

def vt (u : Affine 8) : Program 8 := .inf (atom (ascending u)) (atom (descending u))
theorem vt_exact (u : Affine 8) (t : Point) : (vt u).eval t=v (u.eval t) := by simp [vt,Program.eval,v_eq_min]

def ideal : Program 8 :=
  .sup (vt (X 0)) (.sup (vt ((X 0).add (X 1))) (.sup (vt (((X 0).add (X 1)).add (X 2)))
    (.sup (atom ((K cap).sub ((X 2).scale (3/8)))) (.sup (vt ((X 0).add (X 2))) (vt ((X 1).add (X 2)))))))

theorem ideal_exact (t : Point) : ideal.eval t=thirdValue t := by
  simp [ideal,thirdValue,six,B,Program.eval,vt_exact]

def histori : Fin 4 → Affine 8 :=
  ![(X 0).scale 3,((X 0).add (X 1)).add ((X 2).scale 3),
    ((((X 0).add (X 1)).add (X 2)).add (X 3)).add ((X 4).scale 3),
    ((((((X 0).add (X 1)).add (X 2)).add (X 3)).add (X 4)).add (X 5)).add ((X 6).scale 3)]

theorem histori_exact (t : Point) (i : Fin 4) : (histori i).eval t=oldHistory t i := by
  fin_cases i <;> simp [histori,oldHistory,P4AOriginalRemainingEighthSources.history]

def orderForms : Fin 3 → Affine 8 := ![(K mu).sub (X 0),(X 0).sub (X 1),(X 1).sub (X 2)]

def coreTests (delta : ℝ) : List (Gate 8) :=
  closedBox (fun _ => 0) (fun _ => mu) ++ indexed Finset.univ (fun i => LE (atom (K delta)) (atom (orderForms i))) ++
    indexed Finset.univ (fun i => LE (atom ((histori i).add (K delta))) ideal)

theorem core_exact (delta : ℝ) (t : Point) : Passed t (coreTests delta) ↔ t∈core delta := by
  simp only [coreTests,passed_append,passed_closedBox,passed_indexed,Finset.mem_univ,true_implies,
    holds_LE,Program.eval,Affine.eval_add,Affine.eval_const,histori_exact,ideal_exact,mem_core]
  constructor
  · rintro ⟨⟨⟨hl,hu⟩,hord⟩,hc⟩
    refine ⟨hl,hu,?_⟩
    intro j
    fin_cases j
    all_goals simp only [slack,Matrix.cons_val_zero,Matrix.cons_val_succ]
    all_goals first
      | simpa [orderForms] using hord (0:Fin 3)
      | simpa [orderForms] using hord (1:Fin 3)
      | simpa [orderForms] using hord (2:Fin 3)
      | exact (le_sub_iff_add_le').2 (hc 0)
      | exact (le_sub_iff_add_le').2 (hc 1)
      | exact (le_sub_iff_add_le').2 (hc 2)
      | exact (le_sub_iff_add_le').2 (hc 3)
  · rintro ⟨hl,hu,h⟩
    refine ⟨⟨⟨hl,hu⟩,?_⟩,?_⟩
    · intro i
      fin_cases i
      all_goals first
        | simpa [orderForms,slack] using h (0:Fin 7)
        | simpa [orderForms,slack] using h (1:Fin 7)
        | simpa [orderForms,slack] using h (2:Fin 7)
    · intro i
      fin_cases i
      all_goals first
        | exact (le_sub_iff_add_le').1 (show _ from h 3)
        | exact (le_sub_iff_add_le').1 (show _ from h 4)
        | exact (le_sub_iff_add_le').1 (show _ from h 5)
        | exact (le_sub_iff_add_le').1 (show _ from h 6)

def trimTests (delta : ℝ) (c : Cell) : List (Gate 8) :=
  coreTests delta ++ indexed Finset.univ (fun j => LE (atom (K delta)) (atom (rowForm c j))) ++
    indexed Finset.univ (fun j => LE (atom (K delta)) (atom (marginForm c j)))

theorem trim_exact (delta : ℝ) (c : Cell) (t : Point) : Passed t (trimTests delta c) ↔ t∈trim c delta := by
  simp only [trimTests,passed_append,core_exact,passed_indexed,Finset.mem_univ,true_implies,
    holds_LE,Program.eval,Affine.eval_const,row_exact,margin_exact,mem_trim,and_assoc]

end
end ImbalancedChen.P4AOrderedThirdEighthTrimProgram
