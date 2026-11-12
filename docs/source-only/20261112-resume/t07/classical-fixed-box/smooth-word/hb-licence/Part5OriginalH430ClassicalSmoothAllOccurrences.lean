import ImbalancedChen.Part5OriginalH430ClassicalSmoothNativeWordBound
import ImbalancedChen.Part5OriginalH430ClassicalSmoothPositiveSieve

/-! One original occurrence index retains the Gamma row, the index within
its original list, and its actual tail rank. Equal words in different
positions therefore continue to carry separate positive weights. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothAllOccurrences
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5Z.AdmissibleAllRankIntegerGeometricFamily (eulerOne eulerWord)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum)
open Part5OriginalH430ClassicalSmoothSharpGates (code code_bounds)
open Part5OriginalH430ClassicalSmoothRankCoordinates (rank)
open Part5OriginalH430ClassicalSmoothRankAccounting (tails)
open Part5OriginalH430ClassicalSmoothPositiveSieve (whole)
open Part5OriginalH430ClassicalSmoothEulerBounds (E)
open Part5OriginalH430ClassicalSmoothEulerConjugacy (word_smooth)
open Part5OriginalH430ClassicalSmoothRealProfile (raw raw_smooth raw_support)
open Part5OriginalH430ClassicalSmoothNativeWordBound (native_word_bound)
open scoped Classical Topology BigOperators ContDiff

def words (j : Fin 13) := secondFunctionalMotherGammaWords (9+j.val)
abbrev Mark := (j : Fin 13) × Fin (words j).length
def letters (a : Mark) : List ℕ := (words a.1)[a.2.val]
abbrev Occurrence := (a : Mark) × ↥(tails (letters a).length)
def word (o : Occurrence) := letters o.1
def length (o : Occurrence) := o.2.val
def order (o : Occurrence) : Fin 201 :=
  ⟨rank (word o).length (length o),by have h := (mem_filter.mp o.2.property).2; exact Nat.lt_succ_of_le h⟩

theorem at_least_four (o : Occurrence) : 4≤(order o).val := by
  have hmem : word o∈secondFunctionalMotherGammaWords (9+o.1.1.val) := List.getElem_mem o.1.2.isLt
  have hs := (code_bounds o.1.1 hmem).1
  change 4≤(word o).length+length o+1
  omega

theorem occurrences_eq (F : List ℕ → ℕ → ℝ) :
    (∑ o : Occurrence,F (word o) (length o))=whole F := by
  rw [Fintype.sum_sigma]
  have ht (a : Mark) : (∑ r : ↥(tails (letters a).length),F (letters a) r.val)=
      ∑ r∈tails (letters a).length,F (letters a) r := sum_coe_sort _ _
  change (∑ a : Mark,∑ r : ↥(tails (letters a).length),F (letters a) r.val)=_
  simp_rw [ht]
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro j _
  let G := fun cs : List ℕ => ∑ r∈tails cs.length,F cs r
  change (∑ i : Fin (words j).length,G ((words j)[i.val]))=((words j).map G).sum
  rw [←List.sum_ofFn,List.ofFn_getElem_eq_map]

def lane (N : ℕ) (ν δ h c : ℝ) (o : Occurrence) (k : Fin 201) : E k.val → ℝ :=
  if he : k=order o then fun v => raw (r:=length o) N (code (word o)) ν δ h c
    (fun i => v (i.cast (congrArg Fin.val he.symm))) else fun _ => 0

theorem on_rank (N : ℕ) (ν δ h c : ℝ) (o : Occurrence) :
    lane N ν δ h c o (order o)=raw (r:=length o) N (code (word o)) ν δ h c := by simp [lane]

theorem off_rank {N : ℕ} {ν δ h c : ℝ} {o : Occurrence} {k : Fin 201} (hne : k≠order o) :
    lane N ν δ h c o k=fun _ => 0 := by simp [lane,hne]

def ambient (ν δ h c : ℝ) (N : ℕ) (k : Fin 201) : E k.val → ℝ :=
  if 2≤N then fun v => ∑ o : Occurrence,lane N ν δ h c o k v else fun _ => 0

theorem lane_smooth {N : ℕ} (hN : 2≤N) (ν δ h c : ℝ) (o : Occurrence) (k : Fin 201) :
    ContDiff ℝ ∞ (lane N ν δ h c o k) := by
  by_cases he : k=order o
  · subst k; rw [on_rank]; exact raw_smooth hN _ _ _ _ _
  · rw [off_rank he]; exact contDiff_const

theorem ambient_smooth (ν δ h c : ℝ) (N : ℕ) (k : Fin 201) :
    ContDiff ℝ ∞ (ambient ν δ h c N k) := by
  by_cases hN : 2≤N
  · rw [ambient,if_pos hN]
    exact ContDiff.sum (fun o _ => lane_smooth hN ν δ h c o k)
  · rw [ambient,if_neg hN]; exact contDiff_const

theorem ambient_support {ν δ h c : ℝ} (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
    {N : ℕ} {k : Fin 201} {v : E k.val} (hw : ambient ν δ h c N k v≠0) :
    (∀i,((N:ℝ)^(1/90:ℝ))/2≤v i) ∧ (∏i,v i)≤2*(N:ℝ) := by
  by_cases hN : 2≤N
  · rw [ambient,if_pos hN] at hw
    obtain ⟨o,_,hn⟩ := exists_ne_zero_of_sum_ne_zero hw
    by_cases he : k=order o
    · subst k
      rw [on_rank] at hn
      have hs := raw_support hN hh hh' hc hc' hn
      exact ⟨fun i => (hs.1 i).le,hs.2⟩
    · rw [off_rank he] at hn
      exact (hn rfl).elim
  · rw [ambient,if_neg hN] at hw
    exact (hw rfl).elim

theorem word_zero {k : ℕ} (w : List (Fin k)) : eulerWord w (fun _ => (0:ℝ))=fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change eulerOne i (eulerWord w (fun _ => (0:ℝ)))=_
    rw [ih]
    funext x
    simp [eulerOne]

theorem word_sum {k : ℕ} {α : Type*} [Fintype α] (F : α → E k → ℝ)
    (hF : ∀a,ContDiff ℝ ∞ (F a)) (w : List (Fin k)) :
    eulerWord w (fun v => ∑ a : α,F a v)=fun v => ∑ a : α,eulerWord w (F a) v := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change eulerOne i (eulerWord w (fun v => ∑ a : α,F a v))=_
    rw [ih]
    funext v
    change fderiv ℝ (fun x => ∑ a : α,eulerWord w (F a) x) v (Pi.single i (v i))=_
    rw [fderiv_fun_sum (fun a _ => (word_smooth (hF a) w).differentiable (by simp) v),
      ContinuousLinearMap.sum_apply] <;> rfl

theorem ambient_word_bound (ν : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8)
    (hc : 0<c) (hc' : c≤1/8) (m : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,∀ k : Fin 201,∀ w : List (Fin k.val),w.length≤m →
      ∀v,|eulerWord w (ambient ν δ h c N k) v|≤C := by
  choose B hB hbound using fun o : Occurrence => native_word_bound
    (r:=length o) (code (word o)) ν hd hh hh' hc hc' m
  have ht : 0≤∑ o : Occurrence,B o := sum_nonneg (fun o _ => hB o)
  refine ⟨∑ o : Occurrence,B o,ht,?_⟩
  intro N k w hw v
  by_cases hN : 2≤N
  · rw [ambient,if_pos hN,word_sum _ (fun o => lane_smooth hN ν δ h c o k)]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro o _
    by_cases he : k=order o
    · subst k
      rw [on_rank]
      exact hbound o N hN w hw v
    · rw [off_rank he,word_zero]
      simpa only [abs_zero] using hB o
  · rw [ambient,if_neg hN,word_zero]
    simpa only [abs_zero] using ht

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothAllOccurrences

