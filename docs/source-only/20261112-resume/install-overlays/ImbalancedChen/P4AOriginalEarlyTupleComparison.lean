import ImbalancedChen.P4AOriginalEarlyTupleCarriers

namespace ImbalancedChen.P4AOriginalEarlyTupleComparison
noncomputable section
open scoped Classical BigOperators List
open Set
open P5OriginalCommonRefinedConstructor (OriginalData originalSeed)
open P5OriginalCommonRefinedSeedHull (oldFourth oldFifth)
open P5OriginalFifthArchiveFiniteIdentity (oldQ4 oldQ5)
open P4AOriginalOrderedThirdFullPolicy (current prior Root current_ancestor prior_ancestor)
open P4AOriginalEarlyFiniteStages (seed level4 level5 Q3 Q4 Q5 A4 A5 F4 F5)
open P4AOriginalEarlyHistoricalSums (oldLevel3 B4 B5 O4 O5)
open P4AOriginalEarlyTupleLevels
open P4AOriginalEarlyTupleCarriers
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (cutoff)
open P1CorrectedFifthCausalTupleDictionary (literalTupleDifference primeHistoryTuple_tupleHistory)
open P1OriginalCoarseFourthResidual (literalTupleResidualDifference)
open P4AOriginalFiniteFallbackPolicy (high)

theorem fifth_literal (L U : List ℕ→ℝ) (N cap : ℕ) (p : Fin 5→ℕ) :
    literalTupleDifference (fun h=>(N:ℝ)^L h) (fun h=>(N:ℝ)^U h) N cap p =
      actualPrimeTupleOwnCubeMinus N cap (U (hist5 p)) p -
      actualPrimeTupleOwnCubeMinus N cap (L (rosserAncestor 4 (hist5 p))) p := by
  have hlen : (hist5 p).length=5 := by rw [hist5_list]; rfl
  have hu := actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap (U (hist5 p)) (k:=4) hlen
  have hl := actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap (L (rosserAncestor 4 (hist5 p))) (k:=4) hlen
  rw [primeHistoryTuple_tupleHistory] at hu hl
  rw [hu,hl]
  simp only [literalTupleDifference,actualOwnCubeGatedMinusDensity,hist5]
  ring

theorem off_four (n : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ)
    (he : 0≤(d.e:ℝ)) (he' : (d.e:ℝ)≤1/384) (p : Fin 4→ℕ)
    (hn : ¬occurs4 d N (hist4 p)) : F4 n d w N N p=0 ∧ O4 d N N p=0 := by
  have hl : (hist4 p).length=4 := by rw [hist4_list]; rfl
  obtain ⟨hf,ho⟩ := fourth_off n d w N (hist4 p) hl (seed_nonneg d he he' w N _) hn
  have hf' : Q3 d w N (rosserAncestor 3 (hist4 p))=Q4 n d w N (hist4 p) := congrArg (fun x:ℝ=>(N:ℝ)^x) hf.symm
  have ho' : oldLevel3 d N (rosserAncestor 3 (hist4 p))=oldQ4 d N (hist4 p) := by
    rw [old_level,oldQ4,ho]
  constructor
  · simp only [F4,literalTupleResidualDifference,hf',sub_self,zero_mul,zero_div]
  · simp only [O4,literalTupleResidualDifference,ho',sub_self,zero_mul,zero_div]

theorem off_five (n : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 5→ℕ)
    (hn : ¬occurs5 d N (hist5 p)) : F5 n d w N N p=0 ∧ O5 d N N p=0 := by
  have hl : (hist5 p).length=5 := by rw [hist5_list]; rfl
  obtain ⟨hf,ho⟩ := fifth_off n d w N _ hl hn
  constructor
  · rw [F5,fifth_literal,hf,sub_self]
  · rw [O5,oldQ4,oldQ5,fifth_literal,ho,sub_self]

def PlusShift (n N : ℕ) (u : ℝ) : Prop :=
  ∀p∈box 4 N,∀ L∈Icc (0:ℝ) 1,∀ M∈Icc (0:ℝ) 1,
    (∑i,actualPrimeTupleLog N p i)+actualPrimeTupleLog N p (Fin.last 3)≤L →
    (∑i,actualPrimeTupleLog N p i)+actualPrimeTupleLog N p (Fin.last 3)≤M →
    |L-M|≤2*width n →
      |fourthTuplePlusResidualP1 N N L p-fourthTuplePlusResidualP1 N N M p|<u

def MinusShift (n N : ℕ) (u : ℝ) : Prop :=
  ∀p∈box 5 N,∀ L∈Icc (0:ℝ) 1,∀ M∈Icc (0:ℝ) 1,|L-M|≤2*width n →
    |actualPrimeTupleOwnCubeMinus N N L p-actualPrimeTupleOwnCubeMinus N N M p|<u

/-- Only the occupied part of each carrier is paired. On other words
both signed charges vanish independently of either admission decision. -/
theorem on_four {e : ℚ} {k n N : ℕ} {a w u : ℝ} (S : Alignment e k a w)
    (he' : (e:ℝ)≤1/384) (hN : 1<N) (H : PlusShift n N u) (p : Fin 4→ℕ)
    (hp : p∈A4 (bank e k a) w N N (cutoff N) ∪ B4 (bank e k a) N N (cutoff N))
    (hrow : occurs4 (bank e k a) N (hist4 p)) :
    let d := bank e k a
    p∈A4 d w N N (cutoff N) ∧ p∈B4 d N N (cutoff N) ∧ p∈box 4 N ∧ O4 d N N p≤F4 n d w N N p+u := by
  let d := bank e k a
  let h := hist4 p
  have hc : List.ofFn p <+ carrier N := by
    rcases Finset.mem_union.mp hp with hl|hr
    · exact ((mem_firstExitAdmittedTuples_iff _ _ _ _).mp hl).1
    · exact ((mem_firstExitAdmittedTuples_iff _ _ _ _).mp hr).1
  obtain ⟨hlo,hbox,ho⟩ := four_owner S hN p (primes_of_sub hc) hrow
  have hiff := carrier4_on_owner ho
  have hb : p∈B4 d N N (cutoff N) := (Finset.mem_union.mp hp).elim hiff.mp id
  have hlen : h.length=4 := by rw [hist4_list]; rfl
  obtain ⟨X,Y,sx,sy,dist⟩ := fourth_range n d (by exact_mod_cast S.nonneg) he' w N h hlen hlo ho
  have hs : seed d w N h=originalSeed d N h := congrArg Root.scalar ho
  have legal := legal_four_seed d N hN p hb
  rw [←hs] at legal
  have delta := H p hbox _ Y _ X (legal.trans sy) (legal.trans sx) dist
  have Qeq := level_three_on_owner ho
  have eq : O4 d N N p-F4 n d w N N p =
      fourthTuplePlusResidualP1 N N (level4 n d w N h) p-fourthTuplePlusResidualP1 N N (oldFourth d N h) p := by
    simp only [O4,F4,literalTupleResidualDifference,Qeq,Q4,oldQ4,fourthTuplePlusResidualP1,h,hist4]
    ring
  exact ⟨hiff.mpr hb,hb,hbox,by linarith only [eq,(abs_lt.mp delta).2]⟩

theorem on_five {e : ℚ} {k n N : ℕ} {a w u : ℝ} (S : Alignment e k a w)
    (he' : (e:ℝ)≤1/384) (hN : 1<N) (H : MinusShift n N u) (p : Fin 5→ℕ)
    (hp : p∈A5 (bank e k a) w N N (cutoff N) ∪ B5 (bank e k a) N N (cutoff N))
    (hrow : occurs5 (bank e k a) N (hist5 p)) :
    let d := bank e k a
    p∈A5 d w N N (cutoff N) ∧ p∈B5 d N N (cutoff N) ∧ p∈box 5 N ∧ O5 d N N p≤F5 n d w N N p+2*u := by
  let d := bank e k a
  let h := hist5 p
  let g := rosserAncestor 4 h
  have hc : List.ofFn p <+ carrier N := by
    rcases Finset.mem_union.mp hp with hl|hr
    · exact ((mem_firstExitFrontierTuples_iff _ _ _ _).mp hl).1
    · exact ((mem_firstExitFrontierTuples_iff _ _ _ _).mp hr).1
  obtain ⟨hlo,hbox,hmu,ho⟩ := five_owner S hN p (primes_of_sub hc) hrow
  have hiff := carrier5_on_owner ho
  have hb : p∈B5 d N N (cutoff N) := (Finset.mem_union.mp hp).elim hiff.mp id
  have hl : h.length=5 := by rw [hist5_list]; rfl
  have gl : g.length=4 := by simp [g,rosserAncestor_length,hl]
  have hgo : current d w N g=prior d N g := by
    rw [g,current_ancestor d w N h 4 (by decide),prior_ancestor d N h 4 (by decide)]
    exact ho
  have he : 0≤d.e := by exact_mod_cast S.nonneg
  obtain ⟨X,Y,dx⟩ := fifth_range n d he he' w N h hl hlo hmu ho
  obtain ⟨U,V,_,_,dv⟩ := fourth_range n d he he' w N g gl (fun hi=>hlo ((high_ancestor4 _ _).mp hi)) hgo
  have du := abs_lt.mp (H p hbox _ Y _ X dx)
  have dz := abs_lt.mp (H p hbox _ V _ U dv)
  refine ⟨hiff.mpr hb,hb,hbox,?_⟩
  rw [F5,O5,oldQ4,oldQ5,fifth_literal,fifth_literal]
  linarith only [du.1,dz.2]

end
end ImbalancedChen.P4AOriginalEarlyTupleComparison

