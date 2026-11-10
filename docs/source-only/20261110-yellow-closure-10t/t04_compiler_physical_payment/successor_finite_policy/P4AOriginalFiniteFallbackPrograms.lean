import ImbalancedChen.P4AOriginalFiniteFallbackPolicy

namespace ImbalancedChen.P4AOriginalFiniteFallbackPrograms
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackBank (Bank read read_on_cell)
open P4AOriginalFiniteFallbackPolicy (choose)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P1FiniteAffineDecisionProgram P4AOriginalFourthFifthAffinePrograms
open P4AOrderedThirdRectangleRate (Stage index)
open P4AOrderedThirdStaticRootPrograms (seed)

def memberP {i m : ℕ} (j : Fin i → Fin (m+1)) : Program i :=
  allGates (halfOpenBox (logPrimeMeshLo 0 (19/96) m j) (logPrimeMeshHi 0 (19/96) m j))
    (atom (K 1)) (atom (K 0))

theorem memberP_eval {i m : ℕ} (j : Fin i → Fin (m+1)) (t : Fin i → ℝ) :
    (memberP j).eval t=if t∈logPrimeMeshCell 0 (19/96) m j then 1 else 0 := by
  have h := passed_halfOpenBox t (logPrimeMeshLo 0 (19/96) m j) (logPrimeMeshHi 0 (19/96) m j)
  simp only [← mem_logPrimeMeshCell] at h
  rw [memberP,eval_allGates,show (∀ g∈_,g.holds t) ↔ _ from h]
  simp [Program.eval]

def readList {i k m : ℕ} (ix : Fin i → Fin k) (rows : (Fin i → Fin (m+1)) → Option ℚ)
    (fallback : Program k) : List (Fin i → Fin (m+1)) → Program k
  | [] => fallback
  | j::js => match rows j with
    | none => readList ix rows fallback js
    | some c => .le (atom (K 1)) ((memberP j).pull ix) (atom (K (c:ℝ))) (readList ix rows fallback js)

def readP {i k m : ℕ} (ix : Fin i → Fin k) (rows : (Fin i → Fin (m+1)) → Option ℚ)
    (fallback : Program k) := readList ix rows fallback Finset.univ.toList

theorem readP_eval {i k m : ℕ} (ix : Fin i → Fin k) (rows : (Fin i → Fin (m+1)) → Option ℚ)
    (fall : Program k) (t : Fin k → ℝ) :
    (readP ix rows fall).eval t=choose (read m rows (t ∘ ix)) (fall.eval t) := by
  let Hit (j : Fin i → Fin (m+1)) := (t ∘ ix)∈logPrimeMeshCell 0 (19/96) m j ∧ (rows j).isSome
  have run (xs : List (Fin i → Fin (m+1))) : (readList ix rows fall xs).eval t=
      if ∃ j∈xs,Hit j then choose (read m rows (t ∘ ix)) (fall.eval t) else fall.eval t := by
    induction xs with
    | nil => simp [readList]
    | cons j js ih =>
      cases hc : rows j with
      | none =>
        have hn : ¬Hit j := by simp [Hit,hc]
        simp [readList,hc,ih,List.mem_cons,hn]
      | some c =>
        simp only [readList,hc,Program.eval,Affine.eval_const,Program.eval_pull,memberP_eval]
        by_cases h : (t ∘ ix)∈logPrimeMeshCell 0 (19/96) m j
        · have hj : Hit j := ⟨h,by simp [hc]⟩
          rw [if_pos h,if_pos le_rfl,if_pos ⟨j,List.mem_cons_self,hj⟩,read_on_cell h,hc]
          rfl
        · have hn : ¬Hit j := fun H => h H.1
          rw [if_neg h,if_neg (by norm_num : ¬(1:ℝ)≤0),ih]
          simp [List.mem_cons,hn]
  rw [readP,run]
  split_ifs with hh
  · rfl
  · cases hc : read m rows (t ∘ ix) with
    | none => rfl
    | some c =>
      obtain ⟨j,hj,he⟩ := P4AOriginalFiniteFallbackBank.read_some_iff.mp hc
      exact (hh ⟨j,by simp,hj,by simp [he]⟩).elim

def two (B : Bank) (d : OriginalData) : Program 3 :=
  readP (fun i => i.castLE (by decide : 2≤3)) B.second (seed d)

def three (B : Bank) (d : OriginalData) : Program 3 := readP id B.third (two B d)

def switch {k : ℕ} (upper lower : Program (k+1)) : Program (k+1) :=
  allGates [LT (atom (K VariableEnvelope.mu)) (atom (X 0))] upper lower

theorem switch_eval {k : ℕ} (U L : Program (k+1)) (t : Fin (k+1) → ℝ) :
    (switch U L).eval t=if VariableEnvelope.mu<t 0 then U.eval t else L.eval t := by
  simp [switch,eval_allGates,Passed,Program.eval]

def code (B : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) : (s : Stage) → Program (index s+1)
  | .first => P4AOrderedThirdRankReads.firstP d
  | .third => switch (two B d) (P4AOrderedThirdRectangleRate.code delta n d .third)
  | .fifth => switch ((three B d).pull (fun j => j.castLE (by decide : 3≤5)))
      (P4AOrderedThirdRectangleRate.code delta n d .fifth)
  | .sixth => switch ((three B d).pull (fun j => j.castLE (by decide : 3≤6)))
      (P4AOrderedThirdRectangleRate.code delta n d .sixth)
  | .eighth => switch ((three B d).pull (fun j => j.castLE (by decide : 3≤8)))
      (P4AOrderedThirdRectangleRate.code delta n d .eighth)

end
end ImbalancedChen.P4AOriginalFiniteFallbackPrograms
