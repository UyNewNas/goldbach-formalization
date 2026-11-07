import ImbalancedChen.P2EnhancedLowerPhysicalNode

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal original 70 W1 / 36 W2 component dictionary acts on physical
nodes.  The two coordinates below are PHYSICAL appended exponents, not
new normalized coordinates chosen after refinement.  Local retention
tests are explicit inequalities and original domain membership.  They
contain neither a graph-soundness field nor the desired modulus bound.
The contraction estimate is derived from these original domains.
-/

namespace ImbalancedChen.P2EnhancedLowerPhysicalTransition

noncomputable section
open Set
open P2EnhancedLowerPhysicalNode P5OriginalActionMassBound P5OriginalFeedbackDomains

inductive StepShape where
  | retain
  | transport (cell : Fin 200)
  | buchstabUpper
  | buchstabLower
  | w1Fixed (i : Fin 7) (j : Fin 10)
  | w1Singleton (i : Fin 7) (j : Fin 10)
  | w2Fixed (bank : Fin 36) (anchor : Bool)
  | w2Singleton (bank : Fin 36) (piece : Fin 3)
  | w2Pair (bank : Fin 36) (piece : Fin 4)
  deriving DecidableEq, Fintype

def gridArgument (cell : Fin 200) : ℝ := 1+((cell.val:ℝ)+1)/50
def normalized (n : PhysicalNode) (z : Point) : Point := fun i => z i/residual n
def buchstabArgument (n : PhysicalNode) (z : Point) : ℝ := residual n/z 0-1

def perform (n : PhysicalNode) (a : StepShape) (z : Point) : PhysicalNode :=
  match a with
  | .retain => n
  | .transport cell => compareAt n (gridArgument cell)
  | .buchstabUpper => appendOne n (z 0) (buchstabArgument n z)
  | .buchstabLower => appendOne n (z 0) (buchstabArgument n z)
  | .w1Fixed _ j => compareAt n (W1Anchor j)
  | .w1Singleton _ j =>
      appendOne n (z 0) (singletonProfile (W1Anchor j) (normalized n z 0))
  | .w2Fixed bank anchor =>
      compareAt n (if anchor then (originalW2At bank).s0 else (originalW2At bank).phi1)
  | .w2Singleton bank _ =>
      appendOne n (z 0) (singletonProfile (originalW2At bank).s0 (normalized n z 0))
  | .w2Pair bank piece =>
      appendPair n (z 0) (z 1) (pairProfile (originalW2At bank) piece (normalized n z))

/-- Inner/outer cell retention evaluates these actual physical gates.
They test the NEW appended squares only; old ancestor tests are retained
by the complete old word, rather than tested at a newly optimized cap. -/
def OneGate (n : PhysicalNode) (x : ℝ) : Prop :=
  0<x ∧ x≤n.ceiling ∧ 2*x≤residual n

def PairGate (n : PhysicalNode) (x y : ℝ) : Prop :=
  0<x ∧ x<y ∧ y≤n.ceiling ∧ 2*y≤residual n ∧ y+2*x≤residual n

def LocalDomain (n : PhysicalNode) (a : StepShape) (z : Point) : Prop :=
  0<residual n ∧
  match a with
  | .retain => True
  | .transport cell => n.argument≤gridArgument cell
  | .buchstabUpper => OneGate n (z 0) ∧
      buchstabArgument n z ∈ buchstabUpperDomain n.argument
  | .buchstabLower => 2≤n.argument ∧ OneGate n (z 0) ∧
      buchstabArgument n z ∈ buchstabLowerDomain n.argument
  | .w1Fixed i j => n.argument≤W1Target i ∧ residual n/W1Anchor j≤n.ceiling
  | .w1Singleton i j => OneGate n (z 0) ∧ normalized n z 0 ∈ W1Domain i j ∧
      n.argument≤W1Target i ∧ residual n/W1Target i≤n.ceiling
  | .w2Fixed bank anchor =>
      n.argument≤(originalW2At bank).s ∧
      residual n/(if anchor then (originalW2At bank).s0 else
        (originalW2At bank).phi1)≤n.ceiling
  | .w2Singleton bank piece => OneGate n (z 0) ∧
      normalized n z 0 ∈ W2SingletonDomain (originalW2At bank) piece ∧
      n.argument≤(originalW2At bank).s ∧ residual n/(originalW2At bank).s≤n.ceiling
  | .w2Pair bank piece => PairGate n (z 0) (z 1) ∧
      normalized n z ∈ W2PairDomain (originalW2At bank) piece ∧
      n.argument≤(originalW2At bank).s ∧ residual n/(originalW2At bank).s≤n.ceiling

@[simp] theorem perform_total (n : PhysicalNode) (a : StepShape) (z : Point) :
    (perform n a z).total=n.total := by cases a <;> rfl

@[simp] theorem perform_occurrence (n : PhysicalNode) (a : StepShape) (z : Point) :
    (perform n a z).occurrence=n.occurrence := by cases a <;> rfl

theorem perform_old_slots (n : PhysicalNode) (a : StepShape) (z : Point) :
    (perform n a z).slots.take n.slots.length=n.slots := by
  cases a <;> simp [perform, compareAt, appendOne, appendPair]

theorem perform_rank (n : PhysicalNode) (a : StepShape) (z : Point) :
    (perform n a z).slots.length≤n.slots.length+2 := by
  cases a <;> simp [perform, compareAt, appendOne, appendPair]

theorem perform_selected (n : PhysicalNode) (a : StepShape) (z : Point) :
    selectedWord (perform n a z).slots=selectedWord n.slots := by
  cases a <;> simp [perform, compareAt]

theorem perform_gates {n : PhysicalNode} {a : StepShape} {z : Point}
    (hf : fullGates n) (hs : selectedGates n) (hz : LocalDomain n a z) :
    fullGates (perform n a z) ∧ selectedGates (perform n a z) := by
  cases a with
  | retain => exact ⟨hf,hs⟩
  | transport cell => exact ⟨hf,hs⟩
  | buchstabUpper => exact appendOne_gates hf hs hz.2.1.2.2
  | buchstabLower => exact appendOne_gates hf hs hz.2.2.1.2.2
  | w1Fixed i j => exact ⟨hf,hs⟩
  | w1Singleton i j => exact appendOne_gates hf hs hz.2.1.2.2
  | w2Fixed bank anchor => exact ⟨hf,hs⟩
  | w2Singleton bank piece => exact appendOne_gates hf hs hz.2.1.2.2
  | w2Pair bank piece =>
      exact appendPair_gates hf hs hz.2.1.2.2.2.1 hz.2.1.2.2.2.2

theorem perform_ceiling {n : PhysicalNode} {a : StepShape} {z : Point}
    (hz : LocalDomain n a z) : (perform n a z).ceiling≤n.ceiling := by
  cases a with
  | retain => exact le_rfl
  | transport cell => exact le_rfl
  | buchstabUpper => exact hz.2.1.2.1
  | buchstabLower => exact hz.2.2.1.2.1
  | w1Fixed i j => exact le_rfl
  | w1Singleton i j => exact hz.2.1.2.1
  | w2Fixed bank anchor => exact le_rfl
  | w2Singleton bank piece => exact hz.2.1.2.1
  | w2Pair bank piece => exact hz.2.1.2.1.le.trans hz.2.1.2.2.1

/-- The original good W2 pair domains give residual fraction at least
1/5.  The manuscript's weaker common 1/101 is consequently valid without
an assumed contraction or a saved numeric array. -/
theorem perform_residual_bound {n : PhysicalNode} {a : StepShape} {z : Point}
    (hz : LocalDomain n a z) : residual n/101≤residual (perform n a z) := by
  have hL := hz.1
  cases a with
  | retain => dsimp [perform]; linarith only [hL]
  | transport cell => change residual n/101≤residual n; linarith only [hL]
  | buchstabUpper =>
      change residual n/101≤residual (appendOne n (z 0) (buchstabArgument n z))
      rw [residual_appendOne]
      linarith only [hL,hz.2.1.2.2]
  | buchstabLower =>
      change residual n/101≤residual (appendOne n (z 0) (buchstabArgument n z))
      rw [residual_appendOne]
      linarith only [hL,hz.2.2.1.2.2]
  | w1Fixed i j => change residual n/101≤residual n; linarith only [hL]
  | w1Singleton i j =>
      dsimp only [perform]
      rw [residual_appendOne]
      linarith only [hL,hz.2.1.2.2]
  | w2Fixed bank anchor => change residual n/101≤residual n; linarith only [hL]
  | w2Singleton bank piece =>
      dsimp only [perform]
      rw [residual_appendOne]
      linarith only [hL,hz.2.1.2.2]
  | w2Pair bank piece =>
      have hg := (W2PairDomain_geometry
        (originalRepairedW2Bank_geometry _ (originalW2At_mem bank)) piece hz.2.2.1).2
      have hm := mul_le_mul_of_nonneg_left hg hL.le
      have hx : residual n*(normalized n z 0)=z 0 := by
        dsimp [normalized]; field_simp [hL.ne'] <;> ring
      have hy : residual n*(normalized n z 1)=z 1 := by
        dsimp [normalized]; field_simp [hL.ne'] <;> ring
      dsimp only [perform]
      rw [residual_appendPair]
      nlinarith only [hm,hx,hy,hL]

theorem perform_residual_pos {n : PhysicalNode} {a : StepShape} {z : Point}
    (hz : LocalDomain n a z) : 0<residual (perform n a z) :=
  (div_pos hz.1 (by norm_num : (0:ℝ)<101)).trans_le (perform_residual_bound hz)

theorem alpha_appendOne_mono {n : PhysicalNode} {x s : ℝ}
    (hL : 0<residual n) (hx : 0≤x) (hr : 0<residual n-x) (ha : 1≤alpha n) :
    alpha n≤alpha (appendOne n x s) := by
  have hA : alpha n*residual n=1-(word n).sum := by
    simp [alpha, hL.ne']
  change alpha n≤(1-(word (appendOne n x s)).sum)/residual (appendOne n x s)
  rw [word_appendOne, residual_appendOne]
  simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  apply (le_div_iff₀ hr).mpr
  have hm := mul_nonneg hx (sub_nonneg.mpr ha)
  nlinarith only [hm,hA]

theorem alpha_appendPair_mono {n : PhysicalNode} {x y s : ℝ}
    (hL : 0<residual n) (hx : 0≤x) (hy : 0≤y)
    (hr : 0<residual n-y-x) (ha : 1≤alpha n) :
    alpha n≤alpha (appendPair n x y s) := by
  have hr1 : 0<residual n-y := by linarith only [hr,hx]
  have h1 := alpha_appendOne_mono (s:=s) hL hy hr1 ha
  have h2 := alpha_appendOne_mono (n:=appendOne n y s) (s:=s)
    (by simpa only [residual_appendOne] using hr1) hx
    (by simpa only [residual_appendOne] using hr) (ha.trans h1)
  have heq : appendOne (appendOne n y s) x s=appendPair n x y s := by
    cases n
    simp [appendOne,appendPair,List.append_assoc]
  simpa only [heq] using h1.trans h2

theorem perform_alpha {n : PhysicalNode} {a : StepShape} {z : Point}
    (hz : LocalDomain n a z) (ha : 2≤alpha n) : alpha n≤alpha (perform n a z) := by
  have hr := perform_residual_pos hz
  have ha1 : 1≤alpha n := by linarith only [ha]
  cases a with
  | retain => exact le_rfl
  | transport cell => exact le_rfl
  | buchstabUpper =>
      exact alpha_appendOne_mono hz.1 hz.2.1.1.le
        (by simpa only [perform,residual_appendOne] using hr) ha1
  | buchstabLower =>
      exact alpha_appendOne_mono hz.1 hz.2.2.1.1.le
        (by simpa only [perform,residual_appendOne] using hr) ha1
  | w1Fixed i j => exact le_rfl
  | w1Singleton i j =>
      exact alpha_appendOne_mono hz.1 hz.2.1.1.le
        (by simpa only [perform,residual_appendOne] using hr) ha1
  | w2Fixed bank anchor => exact le_rfl
  | w2Singleton bank piece =>
      exact alpha_appendOne_mono hz.1 hz.2.1.1.le
        (by simpa only [perform,residual_appendOne] using hr) ha1
  | w2Pair bank piece =>
      exact alpha_appendPair_mono hz.1 hz.2.1.1.le
        (hz.2.1.1.trans hz.2.1.2.1).le
        (by simpa only [perform,residual_appendPair] using hr) ha1

end
end ImbalancedChen.P2EnhancedLowerPhysicalTransition
