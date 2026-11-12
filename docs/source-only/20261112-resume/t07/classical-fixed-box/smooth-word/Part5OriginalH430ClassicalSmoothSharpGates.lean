import ImbalancedChen.Part5OriginalH430ClassicalSmoothWordPhysical

/-! Equivalence with the original sharp marked prime tuples of the positive
classical clamp. Each gamma occurrence still has its own colour word. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothSharpGates
noncomputable section
open Finset Real Wu2008DoubleSieve
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)
open Part5OriginalH430ClassicalCausalSeedScale (smallProduct)
open Part5OriginalH430ClassicalFixedClampPrimeGeometry (Tuple sharp)
open Part5OriginalH430ClassicalSmoothWordGates
open Part5OriginalH430ClassicalSmoothWordPhysical
open scoped Classical BigOperators

def code (cs : List ℕ) (i : Fin cs.length) := cs[i.val]
def displayed {s r : ℕ} (p : ℕ) (qs : Fin s → ℕ) (rs : Fin r → ℕ) : Tuple :=
  (p,List.ofFn qs,List.ofFn rs)
def physicalProduct {s r : ℕ} (p : ℕ) (qs : Fin s → ℕ) (rs : Fin r → ℕ) : ℕ :=
  p*(List.ofFn qs).prod*(List.ofFn rs).prod

theorem code_bounds {cs : List ℕ} (j : Fin 13) (hc : cs∈secondFunctionalMotherGammaWords (9+j.val)) :
    3≤cs.length ∧ ∀i,code cs i≤3 := by
  have H (j : Fin 13) : ∀ w∈secondFunctionalMotherGammaWords (9+j.val),
      3≤w.length ∧ ∀ d∈w,d≤3 := by fin_cases j <;> norm_num [secondFunctionalMotherGammaWords]
  obtain ⟨hs,hc'⟩ := H j cs hc
  exact ⟨hs,fun i => hc' _ (List.getElem_mem i.isLt)⟩

private theorem ofFn_order {d : ℕ} {α : Type*} (f : Fin d → α) (rel : α → α → Prop) :
    (List.ofFn f).Pairwise rel ↔ ∀ i j,i<j → rel (f i) (f j) := by
  constructor
  · intro h i j hij
    have hi : i.val<(List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
    have hj : j.val<(List.ofFn f).length := by simpa only [List.length_ofFn] using j.isLt
    simpa only [List.getElem_ofFn] using (List.pairwise_iff_getElem.mp h) i.val j.val hi hj hij
  · intro h
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i<d := by simpa only [List.length_ofFn] using hi
    have hj' : j<d := by simpa only [List.length_ofFn] using hj
    simpa only [List.getElem_ofFn] using h ⟨i,hi'⟩ ⟨j,hj'⟩ hij

private theorem ofFn_colours (cs : List ℕ) (f : Fin cs.length → ℕ) (F : ℕ → ℕ) :
    (List.ofFn f).map F=cs ↔ ∀i,F (f i)=code cs i := by
  have hcode : List.ofFn (code cs)=cs := List.ofFn_getElem
  rw [List.map_ofFn]
  constructor
  · intro h i
    exact congrFun (List.ofFn_injective (h.trans hcode.symm)) i
  · intro h
    have e : F ∘ f=code cs := funext h
    exact (congrArg List.ofFn e).trans hcode

/-- All prime and product inputs are the physical ones. The gate program
contains only the nonradial tests. The lower product gate is strict and
the M=N endpoint remains closed in the right hand side. -/
theorem exact_sharp {N p r : ℕ} {ν κ : ℝ} {cs : List ℕ} {qs : Fin cs.length → ℕ} {rs : Fin r → ℕ}
    (j : Fin 13) (hc : cs∈secondFunctionalMotherGammaWords (9+j.val)) (hN : 1<N)
    (hp : p.Prime) (hq : ∀i,(qs i).Prime) (hr : ∀i,(rs i).Prime) :
    sharp N ν κ cs (displayed p qs rs) ↔
      accepted (code cs) ν (logPoint N p qs rs) ∧
        smallProduct N κ<(physicalProduct p qs rs:ℝ) ∧ physicalProduct p qs rs≤N := by
  let R := (N:ℝ)^ν/(p:ℝ)
  let Qs := List.ofFn qs
  let Rs := List.ofFn rs
  have hcode := code_bounds j hc
  have hidx : cs.length-2<cs.length := by omega
  let pen : Fin cs.length := ⟨cs.length-2,hidx⟩
  have hpen : Qs.getD (Qs.length-2) 0=qs pen := by
    change (List.ofFn qs).getD ((List.ofFn qs).length-2) 0=_
    rw [List.length_ofFn,List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hidx),
      List.getElem_ofFn]
  have hphys : accepted (code cs) ν (logPoint N p qs rs) ↔
      ∀ g∈program r (code cs),raw N p R qs rs g := by
    constructor
    · intro H g hg
      exact (raw_iff_passed hN hp.pos (fun i => (hq i).pos) (fun i => (hr i).pos) ν g).mpr (H g hg)
    · intro H g hg
      exact (raw_iff_passed hN hp.pos (fun i => (hq i).pos) (fun i => (hr i).pos) ν g).mp (H g hg)
  rw [hphys,original_raw_program (code cs) hcode.2]
  change ((p.Prime ∧ _) ∧ (_ ∧ _ ∧ _ ∧ _) ∧ (_ ∧ _) ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨⟨_,hpwin⟩,⟨_,hord,hwin,hcol⟩,⟨hsort,hTail⟩,hlo,hhi⟩
    refine ⟨⟨hpwin,fun i => (hwin (qs i) (List.mem_ofFn.mpr ⟨i,rfl⟩)).2,
      (ofFn_colours _ _ _).mp hcol,(ofFn_order _ _).mp hord,(ofFn_order _ _).mp hsort,?_⟩,hlo,hhi⟩
    intro i l hi
    have he : i=pen := Fin.ext hi
    rw [he,←hpen]
    exact (hTail _ (List.mem_ofFn.mpr ⟨l,rfl⟩)).2
  · rintro ⟨⟨hpwin,hwin,hcol,hord,hsort,hTail⟩,hlo,hhi⟩
    refine ⟨⟨hp,hpwin⟩,⟨List.length_ofFn,(ofFn_order _ _).mpr hord,?_,
      (ofFn_colours _ _ _).mpr hcol⟩,⟨(ofFn_order _ _).mpr hsort,?_⟩,hlo,hhi⟩
    · intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact ⟨hq i,hwin i⟩
    · intro x hx
      obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hx
      exact ⟨hr l,by rw [hpen]; exact hTail pen l rfl⟩

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothSharpGates

