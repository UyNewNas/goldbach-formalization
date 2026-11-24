import ImbalancedChen.P4AOrderedThirdEighthTrimProgram

namespace ImbalancedChen.P4AOrderedThirdEighthSelectionProgram
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P4AOriginalFourthFifthAffinePrograms
open P4AOriginalFull87SourceDictionary (Cell Point newCap source_physical_ceiling)
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87FiniteEighthCap (finiteCap downCap)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8 source_cap_positive)
open P4AOrderedThirdEighthTrimProgram (trimTests trim_exact newForm new_exact)
open P1FiniteAffineQuantizerTable (denominator denominator_pos)

def keys (n : ℕ) : Finset (Cell × ℤ) := Finset.univ ×ˢ (Finset.Icc 0 (n:ℤ))

def bucket (n : ℕ) (i : ℤ) : ℚ := ((i-1:ℤ):ℚ)/((n:ℚ)+1)

def tests (delta : ℝ) (n : ℕ) (k : Cell × ℤ) : List (Gate 8) :=
  let value := (newForm k.1).scale (denominator n)
  trimTests delta k.1 ++ [LE (atom (K (k.2:ℝ))) (atom value),
    LT (atom value) (atom (K ((k.2:ℝ)+1)))]

theorem tests_exact (delta : ℝ) (n : ℕ) (c : Cell) (i : ℤ) (t : Point) :
    Passed t (tests delta n (c,i)) ↔ t∈trim c delta ∧ i=⌊denominator n*newCap c t⌋ := by
  simp only [tests,passed_append,trim_exact,passed_cons,passed_nil,holds_LE,holds_LT,Program.eval,
    Affine.eval_const,Affine.eval_scale,new_exact,and_true]
  constructor
  · rintro ⟨ht,hlo,hhi⟩
    exact ⟨ht,le_antisymm (Int.le_floor.mpr hlo) (by
      have hi : ⌊denominator n * newCap c t⌋<i+1 := Int.floor_lt.mpr (by exact_mod_cast hhi)
      omega)⟩
  · rintro ⟨ht,rfl⟩
    exact ⟨ht,Int.floor_le _,Int.lt_floor_add_one _⟩

def run (delta : ℝ) (n : ℕ) (fallback : Program 8) : List (Cell × ℤ) → Program 8
  | [] => fallback
  | k::ks => allGates (tests delta n k) (atom (K (bucket n k.2:ℝ))) (run delta n fallback ks)

def finish (delta : ℝ) (n : ℕ) (fallback : Program 8) : Program 8 :=
  run delta n fallback (keys n).toList

theorem finish_exact (delta : ℝ) (hd : 0<delta) (n : ℕ) (fallback : Program 8)
    (N : ℝ) (pre : List ℕ) (hl : 8≤pre.length) :
    let t := point8 N pre
    (finish delta n fallback).eval t=
      match selectedCap delta n N pre with
      | none => fallback.eval t
      | some a => (a:ℝ) := by
  let t := point8 N pre
  let Q (k : Cell × ℤ) := Passed t (tests delta n k)
  let V := (selectedCap delta n N pre).elim (fallback.eval t) (fun a => (a:ℝ))
  have hit (k : Cell × ℤ) (hk : Q k) : (bucket n k.2:ℝ)=V := by
    obtain ⟨ht,hi⟩ := (tests_exact delta n k.1 k.2 t).mp hk
    have hs := trim_subset_source k.1 hd ht
    have ho : ownerAtPrefix N pre=some k.1 := by
      rw [ownerAtPrefix,if_pos hl]
      exact (P4AOriginalFull87SourceDispatch.sourceOwner_some_iff _ _).mpr hs
    have hsel : selectedCap delta n N pre=some (finiteCap n k.1 t) := by
      simp only [selectedCap,ho,show point8 N pre∈trim k.1 delta from ht,if_true,t]
    dsimp only [V]
    rw [hsel]
    change (bucket n k.2:ℝ)=(downCap n (newCap k.1 t):ℝ)
    rw [hi]
    rfl
  have miss (hh : ¬∃ k∈keys n,Q k) : fallback.eval t=V := by
    cases ho : ownerAtPrefix N pre with
    | none => simp [V,selectedCap,ho]
    | some c =>
      by_cases ht : t∈trim c delta
      · have hs := trim_subset_source c hd ht
        let i : ℤ := ⌊denominator n*newCap c t⌋
        have hi0 : 0≤i := Int.floor_nonneg.mpr (mul_nonneg (denominator_pos n).le (source_cap_positive hs).le)
        have hi' : i<(n:ℤ)+1 := by
          apply Int.floor_lt.mpr
          have ha := mul_lt_mul_of_pos_left
            ((source_physical_ceiling hs).trans (by norm_num : (153/256:ℝ)<1)) (denominator_pos n)
          simpa [denominator] using ha
        have hek : (c,i)∈keys n := Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_Icc.mpr ⟨hi0,by omega⟩⟩
        exact (hh ⟨(c,i),hek,(tests_exact delta n c i t).mpr ⟨ht,rfl⟩⟩).elim
      · simp [V,selectedCap,ho,show point8 N pre∉trim c delta from ht]
  have eval (xs : List (Cell × ℤ)) :
      (run delta n fallback xs).eval t=if ∃ k∈xs,Q k then V else fallback.eval t := by
    induction xs with
    | nil => simp [run]
    | cons k ks ih =>
      rw [run,eval_allGates]
      by_cases hk : Q k
      · rw [if_pos hk,if_pos (show ∃ j∈k::ks,Q j from ⟨k,List.mem_cons_self,hk⟩)]
        exact hit k hk
      · rw [if_neg hk,ih]
        simp [List.mem_cons,hk]
  change (run delta n fallback (keys n).toList).eval t=_
  rw [eval]
  have hv : V=(match selectedCap delta n N pre with | none => fallback.eval t | some a => (a:ℝ)) := by
    cases h : selectedCap delta n N pre <;> simp [V,h]
  split_ifs with hh
  · exact hv
  · exact (miss (by simpa only [Finset.mem_toList] using hh)).trans hv

end
end ImbalancedChen.P4AOrderedThirdEighthSelectionProgram
