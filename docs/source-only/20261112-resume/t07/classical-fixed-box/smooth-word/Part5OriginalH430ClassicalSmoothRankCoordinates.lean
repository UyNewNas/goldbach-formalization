import ImbalancedChen.Part5OriginalH430ClassicalSmoothOuterWeight

/-! Read all the original marked primes from a finite native rank. Splitting
the vector into p, the prespecified q and the canonical tail is exact. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothRankCoordinates
noncomputable section
open Finset Real Wu2008DoubleSieve
open Part5OriginalH430ClassicalFixedClampMarks
open Part5OriginalH430ClassicalFixedClampGeometry (expanded prefix_data)
open Part5OriginalH430ClassicalFixedClampPrimeGeometry (tuple tuples sharp tuple_mem)
open Part5OriginalH430ClassicalRadialMarkedRanks (rankMarks slot vectors vector_spec prime_floor)
open Part5OriginalH430ClassicalSmoothSharpGates (displayed physicalProduct)
open scoped Classical BigOperators

abbrev rank (s r : ℕ) := (s+r)+1
def qi {s r : ℕ} (i : Fin s) : Fin (rank s r) := (i.castLE (Nat.le_add_right s r)).succ
def ri {s r : ℕ} (j : Fin r) : Fin (rank s r) := (j.natAdd s).succ

def first {s r : ℕ} {α : Type*} (f : Fin (rank s r) → α) := f 0
def qVec {s r : ℕ} {α : Type*} (f : Fin (rank s r) → α) (i : Fin s) := f (qi i)
def rVec {s r : ℕ} {α : Type*} (f : Fin (rank s r) → α) (i : Fin r) := f (ri i)

theorem all_slots {s r : ℕ} {α : Type*} (f : Fin (rank s r) → α) :
    List.ofFn f=first f::(List.ofFn (qVec f)++List.ofFn (rVec f)) := by
  rw [List.ofFn_succ,List.ofFn_add (n:=s) (m:=r) (f:=fun i : Fin (s+r) => f i.succ)] <;> rfl

theorem entire_product {s r N : ℕ} (t : Fin (rank s r) → Fin (2*N+1)) :
    let f := fun i => (t i).val
    Part3.labelledProduct t=physicalProduct (first f) (qVec f) (rVec f) := by
  have h := congrArg List.prod (all_slots (fun i => (t i).val))
  simpa only [List.prod_ofFn,List.prod_cons,List.prod_append,physicalProduct,
    Part3.labelledProduct,mul_assoc] using h

private theorem split_unique {s r : ℕ} {p : ℕ} {qs rs : List ℕ} {f : Fin (rank s r) → ℕ}
    (hl : qs.length=s) (he : List.ofFn f=p::(qs++rs)) :
    first f=p ∧ List.ofFn (qVec f)=qs ∧ List.ofFn (rVec f)=rs := by
  rw [all_slots f] at he
  obtain ⟨hp,hlists⟩ := List.cons.inj he
  have hq := congrArg (List.take s) hlists
  have hr := congrArg (List.drop s) hlists
  have take {l m : List ℕ} (hs : l.length=s) : (l++m).take s=l := by rw [←hs]; simp
  have drop {l m : List ℕ} (hs : l.length=s) : (l++m).drop s=m := by rw [←hs]; simp
  rw [take (l:=List.ofFn (qVec f)) List.length_ofFn,take (l:=qs) hl] at hq
  rw [drop (l:=List.ofFn (qVec f)) List.length_ofFn,drop (l:=qs) hl] at hr
  exact ⟨hp,hq,hr⟩

/-- At each full native rank the original mask=1 geometric carrier is
exactly the original prime, colour, rough tail and product program. -/
theorem original_rank_iff {N r : ℕ} {ν κ : ℝ} {cs : List ℕ}
    (t : Fin (rank cs.length r) → Fin (2*N+1))
    (j : Fin 13) (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112) :
    let f := fun i => (t i).val
    t∈vectors N ν κ cs (rank cs.length r) ↔
      sharp N ν κ cs (displayed (first f) (qVec f) (rVec f)) := by
  let f := fun i => (t i).val
  have hshape {u : Mark} (hu : u∈marks 1 N ν κ cs) :
      u.2.1.length=cs.length := by
    have h := (prefix_data hN hν hu).1
    simp only [letters,List.length_cons] at h
    omega
  constructor
  · intro ht
    obtain ⟨u,hu,he⟩ := mem_image.mp ht
    have hvec := vector_spec j hc hN hν hν' hk hu
    have hl : List.ofFn f=expanded u := by
      change List.ofFn (fun i => (t i).val)=_
      rw [←he]
      exact hvec.1
    have hh := split_unique (hshape (mem_filter.mp hu).1) (by
      simpa only [expanded,letters,List.cons_append] using hl)
    apply tuple_mem.mp
    apply mem_image.mpr
    refine ⟨u,(mem_filter.mp hu).1,?_⟩
    change (u.1,u.2.1,u.2.2.primeFactorsList)=(first f,List.ofFn (qVec f),List.ofFn (rVec f))
    rw [hh.1,hh.2.1,hh.2.2]
  · intro hsharp
    obtain ⟨u,hu,he⟩ := mem_image.mp (tuple_mem.mpr hsharp)
    have hc' : u.1=first f ∧ u.2.1=List.ofFn (qVec f) ∧
        u.2.2.primeFactorsList=List.ofFn (rVec f) := by simpa only [tuple,displayed,Prod.mk.injEq] using he
    have hl : expanded u=List.ofFn f := by
      rw [all_slots f,expanded,letters,List.cons_append,hc'.1,hc'.2.1,hc'.2.2]
    have hlen : (expanded u).length=rank cs.length r := by rw [hl,List.length_ofFn]
    have hm : u∈rankMarks N ν κ cs (rank cs.length r) := mem_filter.mpr ⟨hu,hlen⟩
    apply mem_image.mpr
    refine ⟨u,hm,?_⟩
    have hh := List.ofFn_injective ((vector_spec j hc hN hν hν' hk hm).1.trans hl)
    exact funext (fun i => Fin.ext (congrFun hh i))

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothRankCoordinates

