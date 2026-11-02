import ImbalancedChen.P5OriginalCommonRefinedConstructor

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual ELEVEN sixth eligibility is compiled into a finite family of
literal affine gates. The seventh coordinate is the ORIGINAL actual
fifth-parent cap, not an independently chosen cap or an equality premise.
Inner endpoint tests and their quantitative disagreement bands are defined
before arithmetic tuples or N. Identically zero weak forms are retained.

This closes the sixth eligibility-gate dictionary and its endpoint-wall
localization. It does not yet compile the upstream third/fourth/fifth
piecewise-affine parent, the eighth choice, or every later Rosser test.
Properness below is in the augmented space, NOT on the parent graph.
The explicit inherited-parent substitution near the end shows why the
parent pieces must be substituted before any original wall is discarded.
-/
namespace ImbalancedChen.P2OriginalElevenAffineEndpointCompiler
noncomputable section
open Classical
open scoped BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P5OriginalCommonRefinedConstructor

abbrev Point := Physical × ℝ

structure Form where
  constant : ℝ
  coefficient : Fin 6 → ℝ
  parentCoefficient : ℝ

theorem form_ext {a b : Form} (hc : a.constant = b.constant)
    (hi : a.coefficient = b.coefficient) (hp : a.parentCoefficient = b.parentCoefficient) :
    a = b := by
  cases a
  cases b
  simp_all

def Form.eval (a : Form) (x : Point) : ℝ :=
  a.constant + ∑ i, a.coefficient i * x.1 i + a.parentCoefficient * x.2

def cn (r : ℝ) : Form := ⟨r, fun _ => 0, 0⟩
def coord (i : Fin 6) : Form := ⟨0, fun j => if j = i then 1 else 0, 0⟩
def parent : Form := ⟨0, fun _ => 0, 1⟩
def plus (a b : Form) : Form :=
  ⟨a.constant + b.constant, fun i => a.coefficient i + b.coefficient i,
    a.parentCoefficient + b.parentCoefficient⟩
def scale (r : ℝ) (a : Form) : Form :=
  ⟨r * a.constant, fun i => r * a.coefficient i, r * a.parentCoefficient⟩
def minus (a b : Form) : Form := plus a (scale (-1) b)
def sumF {ι : Type*} (s : Finset ι) (a : ι → Form) : Form :=
  ⟨∑ j ∈ s, (a j).constant, fun i => ∑ j ∈ s, (a j).coefficient i,
    ∑ j ∈ s, (a j).parentCoefficient⟩

@[simp] theorem eval_cn (r : ℝ) (x : Point) : (cn r).eval x = r := by
  simp [Form.eval, cn]
@[simp] theorem eval_coord (i : Fin 6) (x : Point) : (coord i).eval x = x.1 i := by
  simp [Form.eval, coord]
@[simp] theorem eval_parent (x : Point) : parent.eval x = x.2 := by
  simp [Form.eval, parent]
@[simp] theorem eval_plus (a b : Form) (x : Point) :
    (plus a b).eval x = a.eval x + b.eval x := by
  simp only [Form.eval, plus, add_mul, Finset.sum_add_distrib]
  ring
@[simp] theorem eval_scale (r : ℝ) (a : Form) (x : Point) :
    (scale r a).eval x = r * a.eval x := by
  simp only [Form.eval, scale, mul_assoc, ← Finset.mul_sum]
  ring
@[simp] theorem eval_minus (a b : Form) (x : Point) :
    (minus a b).eval x = a.eval x - b.eval x := by simp [minus]; ring
@[simp] theorem eval_sumF {ι : Type*} (s : Finset ι) (a : ι → Form) (x : Point) :
    (sumF s a).eval x = ∑ j ∈ s, (a j).eval x := by
  simp only [Form.eval, sumF, Finset.sum_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

def Form.slope (a : Form) : ℝ := (∑ i, |a.coefficient i|) + |a.parentCoefficient|
def Form.lower (a : Form) (lo : Point) (tau : ℝ) : ℝ := a.eval lo - a.slope * tau

def InBox (lo : Point) (tau : ℝ) (x : Point) : Prop :=
  (∀ i, lo.1 i ≤ x.1 i ∧ x.1 i ≤ lo.1 i + tau) ∧
    lo.2 ≤ x.2 ∧ x.2 ≤ lo.2 + tau

theorem slope_nonneg (a : Form) : 0 ≤ a.slope :=
  add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (abs_nonneg _)

/-- One explicit, N-independent coefficient norm controls the WHOLE box. -/
theorem eval_variation (a : Form) (lo x : Point) (tau : ℝ)
    (hx : InBox lo tau x) : |a.eval x - a.eval lo| ≤ a.slope * tau := by
  have hcoord (i : Fin 6) : |x.1 i - lo.1 i| ≤ tau := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hx.1 i).1)]
    linarith [(hx.1 i).2]
  have hparent : |x.2 - lo.2| ≤ tau := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.2.1)]
    linarith [hx.2.2]
  have heq : a.eval x - a.eval lo =
      (∑ i, a.coefficient i * (x.1 i - lo.1 i)) +
        a.parentCoefficient * (x.2 - lo.2) := by
    simp only [Form.eval, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |∑ i, a.coefficient i * (x.1 i - lo.1 i)| +
        |a.parentCoefficient * (x.2 - lo.2)| := abs_add _ _
    _ ≤ (∑ i, |a.coefficient i * (x.1 i - lo.1 i)|) +
        |a.parentCoefficient * (x.2 - lo.2)| :=
      add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ (∑ i, |a.coefficient i| * tau) + |a.parentCoefficient| * tau := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hparent (abs_nonneg _)
    _ = a.slope * tau := by rw [Form.slope, Finset.sum_mul]; ring

structure Test where
  strict : Bool
  margin : Form

def ltF (a b : Form) : Test := ⟨true, minus b a⟩
def leF (a b : Form) : Test := ⟨false, minus b a⟩
def yesTest : Test := ltF (cn 0) (cn 1)
def Pass (g : Test) (x : Point) : Prop :=
  if g.strict then 0 < g.margin.eval x else 0 ≤ g.margin.eval x
def Inner (g : Test) (lo : Point) (tau : ℝ) : Prop :=
  if g.strict then 0 < g.margin.lower lo tau else 0 ≤ g.margin.lower lo tau

@[simp] theorem pass_lt (a b : Form) (x : Point) :
    Pass (ltF a b) x ↔ a.eval x < b.eval x := by
  simp [Pass, ltF, sub_pos]
@[simp] theorem pass_le (a b : Form) (x : Point) :
    Pass (leF a b) x ↔ a.eval x ≤ b.eval x := by
  simp [Pass, leF, sub_nonneg]
@[simp] theorem pass_yes (x : Point) : Pass yesTest x := by simp [yesTest]

theorem inner_sound (g : Test) (lo x : Point) (tau : ℝ)
    (hx : InBox lo tau x) (hg : Inner g lo tau) : Pass g x := by
  have hb := (abs_sub_le_iff.mp (eval_variation g.margin lo x tau hx)).2
  cases hs : g.strict <;> simp only [Inner, Pass, hs, Bool.false_eq_true,
    if_false, if_true, Form.lower] at hg ⊢ <;> linarith

/-- A missed actual gate lies within an explicit mesh band of a proper
affine wall in the AUGMENTED space. A nonzero augmented slope can restrict
to zero on the parent graph; this is not yet an original-wall payment. -/
theorem missed_inner_near_proper_wall (g : Test) (lo x : Point) (tau : ℝ)
    (hx : InBox lo tau x) (hpass : Pass g x) (hmiss : ¬Inner g lo tau) :
    0 < g.margin.slope ∧ |g.margin.eval x| ≤ 2 * g.margin.slope * tau := by
  have hv := abs_sub_le_iff.mp (eval_variation g.margin lo x tau hx)
  have hslope := slope_nonneg g.margin
  have hpos : 0 < g.margin.slope := by
    by_contra hn
    have hz : g.margin.slope = 0 := le_antisymm (le_of_not_gt hn) hslope
    cases hs : g.strict <;>
      simp only [Inner, Pass, hs, Bool.false_eq_true, if_false, if_true,
        Form.lower, hz, zero_mul, sub_zero] at hpass hmiss <;> linarith
  refine ⟨hpos, ?_⟩
  cases hs : g.strict <;>
    simp only [Inner, Pass, hs, Bool.false_eq_true, if_false, if_true,
      Form.lower] at hpass hmiss
  · rw [abs_of_nonneg hpass]
    push_neg at hmiss
    linarith [hv.1]
  · rw [abs_of_nonneg hpass.le]
    push_neg at hmiss
    linarith [hv.1]

/-- The literal original affine forms. -/
def r0 : Form := scale (1/2) (plus (cn 1) (coord 0))
def s5 : Form := sumF Finset.univ (fun i : Fin 5 => coord i.castSucc)
def s6 : Form := plus s5 (coord 5)
def h3 : Form := plus (plus (coord 0) (coord 1)) (scale 3 (coord 2))
def h5 : Form := plus (sumF Finset.univ (fun i : Fin 4 => coord (i.castLE (by omega))))
  (scale 3 (coord 4))
def wForm : Form := minus (cn (153/256)) (scale (3/8) (coord 2))
def old (c : Cell) : Form := match c.family with
  | .singleton | .tent33 => r0
  | .pair17 => minus (cn (57/64)) (scale (3/2) (plus (coord 0) (coord 4)))
  | .pair12 => scale (1/2) (plus (plus (cn 1) (coord 2)) (coord 3))
def clipped : Form := minus (plus s5 (scale 4 (coord 5))) (cn eta)
def asc33 : Form := scale (1/2) (plus (plus (cn 1) (coord 0)) (coord 5))
def desc33 : Form := minus (cn (57/64)) (scale (3/2) (plus (coord 0) (coord 5)))
def asc34 : Form := scale (1/2) (plus (plus (cn 1) (coord 1)) (coord 5))
def fresh (c : Cell) : Form := if c.family = .tent33 then minus asc33 (cn eta) else clipped
def subset (mask : ℕ) : Form := sumF Finset.univ (fun i : Fin 5 =>
  if bit mask i.val then coord i.castSucc else cn 0)
def selected (mask : ℕ) : Form := sumF Finset.univ (fun i : Fin 6 =>
  if bit mask i.val then coord i else cn 0)
def square (j : Fin 6) : Form := plus
  (sumF Finset.univ (fun i : Fin 6 => if i < j then coord i else cn 0))
  (scale 2 (coord j))
def remaining (mask : ℕ) (j : Fin 6) : Form := plus
  (plus (selected mask) (sumF Finset.univ (fun i : Fin 6 =>
    if i < j ∧ bit mask i.val = false then coord i else cn 0))) (scale 2 (coord j))

@[simp] theorem r0_eval (x : Point) : r0.eval x = R0 x.1 := by simp [r0, R0]; ring
@[simp] theorem s5_eval (x : Point) : s5.eval x = S5 x.1 := by
  simp [s5, S5, Fin.sum_univ_succ]; ring
@[simp] theorem s6_eval (x : Point) : s6.eval x = S6 x.1 := by simp [s6, S6]
@[simp] theorem h3_eval (x : Point) : h3.eval x = H3 x.1 := by simp [h3, H3]
@[simp] theorem h5_eval (x : Point) : h5.eval x = H5 x.1 := by
  simp [h5, H5, Fin.sum_univ_succ]; ring
@[simp] theorem wForm_eval (x : Point) : wForm.eval x = W x.1 := by simp [wForm, W]; ring
@[simp] theorem old_eval (c : Cell) (x : Point) : (old c).eval x = oldCap c x.1 := by
  cases hf : c.family <;> simp [old, oldCap, hf] <;> ring
@[simp] theorem clipped_eval (x : Point) : clipped.eval x = clippedCap x.1 := by
  simp [clipped, clippedCap]
@[simp] theorem asc33_eval (x : Point) : asc33.eval x = ascending33 x.1 := by
  simp [asc33, ascending33]; ring
@[simp] theorem desc33_eval (x : Point) : desc33.eval x = descending33 x.1 := by
  simp [desc33, descending33]; ring
@[simp] theorem asc34_eval (x : Point) : asc34.eval x = ascending34 x.1 := by
  simp [asc34, ascending34]; ring
@[simp] theorem fresh_eval (c : Cell) (x : Point) : (fresh c).eval x = newCap c x.1 := by
  by_cases hc : c.family = .tent33 <;> simp [fresh, newCap, hc]
@[simp] theorem subset_eval (mask : ℕ) (x : Point) :
    (subset mask).eval x = subsetSum mask x.1 := by
  simp only [subset, eval_sumF, subsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  cases bit mask i.val <;> simp
@[simp] theorem selected_eval (mask : ℕ) (x : Point) :
    (selected mask).eval x = selectedSum mask x.1 := by
  simp only [selected, eval_sumF, selectedSum]
  apply Finset.sum_congr rfl
  intro i hi
  cases bit mask i.val <;> simp
@[simp] theorem square_eval (j : Fin 6) (x : Point) :
    (square j).eval x = fullSquare j x.1 := by
  simp only [square, eval_plus, eval_sumF, eval_scale, eval_coord, fullSquare]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  split <;> simp_all
@[simp] theorem remaining_eval (mask : ℕ) (j : Fin 6) (x : Point) :
    (remaining mask j).eval x = remainingSquare mask j x.1 := by
  simp only [remaining, eval_plus, eval_sumF, eval_scale, eval_coord,
    selected_eval, remainingSquare]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  split <;> simp_all

def branch (c : Cell) (mask : ℕ) (capForm : Form) : Test :=
  if c.descending mask then
    leF (minus (cn (57/64)) (scale (3/2) (subset mask))) capForm
  else leF (subset mask) (minus (scale 2 capForm) (cn 1))

@[simp] theorem branch_pass (c : Cell) (mask : ℕ) (a : Form) (x : Point) :
    Pass (branch c mask a) x ↔ branchLicense (c.descending mask) (a.eval x) (subsetSum mask x.1) := by
  cases h : c.descending mask <;> simp [branch, branchLicense, h] <;> ring_nf

inductive Key where
  | rpos | order (i : Fin 5) | largest | oldCutoff | compactCutoff
  | history3 | history5 | oldW | oldBranch (i : Fin 31) | first3Branch (i : Fin 7)
  | comparison | pairAbove | winner | positiveGap | selectedAscending | selectedDescending
  | fullSquare (j : Fin 6) | remainingSquare (j : Fin 6)
  | oldArgument | newArgument | priority1 | priority2 | parentLower | parentUpper
  deriving DecidableEq, Fintype

/-- This is the actual original gate bank, including all 31 old branches,
all 7 third branches, all full and complement squares, priority, and BOTH
comparisons with the actual inherited parent. -/
def gate (c : Cell) : Key → Test
  | .rpos => ltF (cn 0) (coord 5)
  | .order i => ltF (coord i.succ) (coord i.castSucc)
  | .largest => ltF (coord 0) (cn mu)
  | .oldCutoff => ltF (coord 5) (cn (1/50))
  | .compactCutoff => ltF (cn (53/4608)) (coord 5)
  | .history3 => ltF h3 r0
  | .history5 => ltF h5 r0
  | .oldW => leF wForm r0
  | .oldBranch i => branch c (i.val + 1) (old c)
  | .first3Branch i => branch c (i.val + 1) r0
  | .comparison => leF r0 (old c)
  | .pairAbove => if c.family = .pair17 ∨ c.family = .pair12 then ltF r0 (old c) else yesTest
  | .winner => match c.family with
      | .pair17 => ltF (cn mu) (plus (coord 0) (coord 4))
      | .pair12 => ltF (plus (coord 2) (coord 3)) (cn mu)
      | _ => yesTest
  | .positiveGap => ltF (old c) (fresh c)
  | .selectedAscending => ltF (fresh c) (scale (1/2) (plus (cn 1) (selected c.selectedMask)))
  | .selectedDescending => ltF (fresh c) (minus (cn (57/64)) (scale (3/2) (selected c.selectedMask)))
  | .fullSquare j => ltF (square j) (fresh c)
  | .remainingSquare j => if bit c.selectedMask j.val = false then
      ltF (remaining c.selectedMask j) (fresh c) else yesTest
  | .oldArgument => ltF (coord 5) (minus r0 s6)
  | .newArgument => ltF (minus (fresh c) s6) (scale 3 (coord 5))
  | .priority1 => match c with
      | .singleton34_1371 | .singleton50_1353 | .singleton50_1355 => ltF desc33 (fresh c)
      | .tent33_1371 | .tent33_1867 => ltF asc33 clipped
      | _ => yesTest
  | .priority2 => match c with
      | .singleton50_1353 | .singleton50_1355 => ltF asc34 (fresh c)
      | _ => yesTest
  | .parentLower => ltF h5 parent
  | .parentUpper => leF parent (old c)

def GeometricEligible (c : Cell) (x : Point) : Prop :=
  PhysicalCell c x.1 ∧ H5 x.1 < x.2 ∧ x.2 ≤ oldCap c x.1

theorem eligible_all_pass (c : Cell) (x : Point) (hx : GeometricEligible c x) :
    ∀ k : Key, Pass (gate c k) x := by
  obtain ⟨h, hlow, hupp⟩ := hx
  intro k
  cases k with
  | rpos => simpa [gate] using h.rpos
  | order i =>
      obtain ⟨h54, h43, h32, h21, h10⟩ := h.order
      fin_cases i
      · simpa [gate] using h10
      · simpa [gate] using h21
      · simpa [gate] using h32
      · simpa [gate] using h43
      · simpa [gate] using h54
  | largest => simpa [gate] using h.largest
  | oldCutoff => simpa [gate] using h.oldCutoff
  | compactCutoff => simpa [gate] using h.compactCutoff
  | history3 => simpa [gate] using h.history3
  | history5 => simpa [gate] using h.history5
  | oldW => simpa [gate] using h.oldW
  | oldBranch i =>
      simpa [gate] using h.oldBranches (i.val + 1) (Finset.mem_Icc.mpr (by omega))
  | first3Branch i =>
      simpa [gate] using h.first3Branches (i.val + 1) (Finset.mem_Icc.mpr (by omega))
  | comparison => simpa [gate] using h.comparison
  | pairAbove =>
      by_cases hp : c.family = .pair17 ∨ c.family = .pair12
      · simpa [gate, hp] using h.pairAbove hp
      · simp [gate, hp]
  | winner =>
      cases hf : c.family <;> simpa [gate, winnerPlane, hf] using h.winner
  | positiveGap => simpa [gate] using h.positiveGap
  | selectedAscending => simpa [gate, div_eq_mul_inv, mul_comm] using h.selectedAscending
  | selectedDescending => simpa [gate, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      using h.selectedDescending
  | fullSquare j => simpa [gate] using h.fullSquares j
  | remainingSquare j =>
      by_cases hj : bit c.selectedMask j.val = false
      · simpa [gate, hj] using h.remainingSquares j hj
      · simp [gate, hj]
  | oldArgument => simpa [gate] using h.oldArgument
  | newArgument => simpa [gate, newResidual] using h.newArgument
  | priority1 =>
      have hp := h.priority
      cases c <;> simp_all [gate, priority]
  | priority2 =>
      have hp := h.priority
      cases c <;> simp_all [gate, priority]
  | parentLower => simpa [gate] using hlow
  | parentUpper => simpa [gate] using hupp

theorem all_pass_eligible (c : Cell) (x : Point)
    (h : ∀ k : Key, Pass (gate c k) x) : GeometricEligible c x := by
  have hb : ∀ mask ∈ Finset.Icc 1 31,
      branchLicense (c.descending mask) (oldCap c x.1) (subsetSum mask x.1) := by
    intro mask hm
    obtain ⟨hm1, hm31⟩ := Finset.mem_Icc.mp hm
    have heq : mask - 1 + 1 = mask := Nat.sub_add_cancel hm1
    simpa [gate, heq] using h (.oldBranch ⟨mask - 1, by omega⟩)
  have hb3 : ∀ mask ∈ Finset.Icc 1 7,
      branchLicense (c.descending mask) (R0 x.1) (subsetSum mask x.1) := by
    intro mask hm
    obtain ⟨hm1, hm7⟩ := Finset.mem_Icc.mp hm
    have heq : mask - 1 + 1 = mask := Nat.sub_add_cancel hm1
    simpa [gate, heq] using h (.first3Branch ⟨mask - 1, by omega⟩)
  refine ⟨{
    rpos := by simpa [gate] using h .rpos
    order := ?_
    largest := by simpa [gate] using h .largest
    oldCutoff := by simpa [gate] using h .oldCutoff
    compactCutoff := by simpa [gate] using h .compactCutoff
    history3 := by simpa [gate] using h .history3
    history5 := by simpa [gate] using h .history5
    oldW := by simpa [gate] using h .oldW
    oldBranches := hb
    first3Branches := hb3
    comparison := by simpa [gate] using h .comparison
    pairAbove := ?_
    winner := ?_
    positiveGap := by simpa [gate] using h .positiveGap
    selectedAscending := by simpa [gate, div_eq_mul_inv, mul_comm] using h .selectedAscending
    selectedDescending := by
      simpa [gate, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h .selectedDescending
    fullSquares := fun j => by simpa [gate] using h (.fullSquare j)
    remainingSquares := ?_
    oldArgument := by simpa [gate] using h .oldArgument
    newArgument := by simpa [gate, newResidual] using h .newArgument
    priority := ?_ }, by simpa [gate] using h .parentLower,
    by simpa [gate] using h .parentUpper⟩
  · exact ⟨by simpa [gate] using h (.order 4),
      by simpa [gate] using h (.order 3), by simpa [gate] using h (.order 2),
      by simpa [gate] using h (.order 1), by simpa [gate] using h (.order 0)⟩
  · intro hp
    simpa [gate, hp] using h .pairAbove
  · cases hf : c.family <;> simpa [gate, winnerPlane, hf] using h .winner
  · intro j hj
    simpa [gate, hj] using h (.remainingSquare j)
  · have h1 := h .priority1
    have h2 := h .priority2
    cases c <;> simp_all [gate, priority]

def EndpointEligible (c : Cell) (lo : Point) (tau : ℝ) : Prop :=
  ∀ k : Key, Inner (gate c k) lo tau

def WallBand (c : Cell) (k : Key) (tau : ℝ) (x : Point) : Prop :=
  0 < (gate c k).margin.slope ∧
    |(gate c k).margin.eval x| ≤ 2 * (gate c k).margin.slope * tau

theorem endpoint_eligible_sound (c : Cell) (lo x : Point) (tau : ℝ)
    (hx : InBox lo tau x) (hc : EndpointEligible c lo tau) : GeometricEligible c x :=
  all_pass_eligible c x (fun k => inner_sound (gate c k) lo x tau hx (hc k))

/-- Actual branch disagreement is on this fixed literal augmented bank,
with mesh width 2*||coefficients||_1*tau; no arithmetic-tuple test defines
the endpoints and no generic support/equality premise is supplied. -/
theorem eligibility_difference_wall (c : Cell) (lo x : Point) (tau : ℝ)
    (hx : InBox lo tau x) (hc : GeometricEligible c x)
    (hmiss : ¬EndpointEligible c lo tau) : ∃ k : Key, WallBand c k tau x := by
  change ¬∀ k : Key, Inner (gate c k) lo tau at hmiss
  push_neg at hmiss
  obtain ⟨k, hk⟩ := hmiss
  exact ⟨k, missed_inner_near_proper_wall (gate c k) lo x tau hx
    (eligible_all_pass c x hc k) hk⟩

def actualPoint (d : OriginalData) (N : ℝ) (pre : List ℕ) : Point :=
  (primeHistoryLogCoordinates N 6 pre, actualParent5 d N pre)

theorem actual_eligibility_dictionary (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (c : Cell) : eligibleSixth d N c pre ↔
      pre.length = 6 ∧ ∀ k : Key, Pass (gate c k) (actualPoint d N pre) := by
  constructor
  · intro h
    exact ⟨h.1, eligible_all_pass c (actualPoint d N pre) h.2⟩
  · rintro ⟨hlen, h⟩
    exact ⟨hlen, all_pass_eligible c (actualPoint d N pre) h⟩

/-- Original source instantiation with the inherited parent read from the
actual constructor. The only hypotheses are literal box membership and
the actual unrounded row's eligibility; the wall is proved, not assumed. -/
theorem actual_sixth_disagreement_wall (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (c : Cell) (lo : Point) (tau : ℝ)
    (hx : InBox lo tau (actualPoint d N pre)) (hc : eligibleSixth d N c pre)
    (hmiss : ¬EndpointEligible c lo tau) :
    ∃ k : Key, WallBand c k tau (actualPoint d N pre) :=
  eligibility_difference_wall c lo (actualPoint d N pre) tau hx hc.2 hmiss

def meshLower (tau v : ℝ) : ℝ := ((⌊v / tau⌋ : ℤ) : ℝ) * tau
def meshPoint (tau : ℝ) (x : Point) : Point :=
  (fun i => meshLower tau (x.1 i), meshLower tau x.2)

theorem meshLower_bounds (tau v : ℝ) (htau : 0 < tau) :
    meshLower tau v ≤ v ∧ v ≤ meshLower tau v + tau := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (v / tau)) htau.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (v / tau)) htau
  rw [div_mul_cancel₀ v htau.ne'] at hlo hhi
  constructor
  · exact hlo
  · dsimp [meshLower]
    nlinarith only [hhi]

theorem actual_mem_mesh (tau : ℝ) (htau : 0 < tau) (x : Point) :
    InBox (meshPoint tau x) tau x :=
  ⟨fun i => meshLower_bounds tau (x.1 i) htau, meshLower_bounds tau x.2 htau⟩

open P1OriginalVariableFourthContinuation

/-- Real endpoint choice for the actual eleven candidates. The actual
parent is kept as the seed; all admitted row candidates use fixed lower
affine endpoints. No arithmetic tuple is inspected to decide a box gate. -/
def endpointLambda6 (d : OriginalData) (N : ℝ) (tau : ℝ) (pre : List ℕ) : ℝ :=
  let lo := meshPoint tau (actualPoint d N pre)
  finiteMax allCells.toFinset
    (fun c => pre.length = 6 ∧ EndpointEligible c lo tau)
    (fun c => (fresh c).lower lo tau) (actualParent5 d N pre)

def candidateSlope : ℝ := ∑ c ∈ allCells.toFinset, (fresh c).slope

theorem candidateSlope_nonneg : 0 ≤ candidateSlope :=
  Finset.sum_nonneg (fun c hc => slope_nonneg (fresh c))

theorem candidate_slope_le (c : Cell) : (fresh c).slope ≤ candidateSlope := by
  exact Finset.single_le_sum (fun d hd => slope_nonneg (fresh d))
    (List.mem_toFinset.mpr (allCells_complete c))

theorem endpointLambda6_le_actual (d : OriginalData) (N : ℝ) (tau : ℝ)
    (htau : 0 < tau) (pre : List ℕ) :
    endpointLambda6 d N tau pre ≤ lambda6 d N pre := by
  unfold endpointLambda6
  dsimp only
  apply finiteMax_le
  · exact actualParent5_le_lambda6 d N pre
  · intro c hc he
    have hx := actual_mem_mesh tau htau (actualPoint d N pre)
    have hc' : eligibleSixth d N c pre :=
      ⟨he.1, endpoint_eligible_sound c _ _ tau hx he.2⟩
    have hv := (abs_sub_le_iff.mp (eval_variation (fresh c) _ _ tau hx)).2
    have heval := fresh_eval c (actualPoint d N pre)
    have hrow := eligibleSixth_newCap_le_lambda6 d N c pre hc'
    dsimp [Form.lower]
    linarith

def OnAugmentedGateBand (tau : ℝ) (x : Point) : Prop :=
  ∃ c : Cell, ∃ k : Key, WallBand c k tau x

/-- Off the proved original decision bands, the actual finite maximum
changes by at most one explicit mesh constant, uniformly in N, histories,
actual parent values, and all eleven contenders (ties included). -/
theorem actualLambda6_le_endpoint_add_mesh (d : OriginalData) (N : ℝ)
    (tau : ℝ) (htau : 0 < tau) (pre : List ℕ)
    (hoff : ¬OnAugmentedGateBand tau (actualPoint d N pre)) :
    lambda6 d N pre ≤ endpointLambda6 d N tau pre + 2 * candidateSlope * tau := by
  have hx := actual_mem_mesh tau htau (actualPoint d N pre)
  have herr : 0 ≤ 2 * candidateSlope * tau := by
    exact mul_nonneg (mul_nonneg (by norm_num) candidateSlope_nonneg) htau.le
  unfold lambda6
  apply finiteMax_le
  · have hs : actualParent5 d N pre ≤ endpointLambda6 d N tau pre :=
      finiteMax_seed_le _ _ _ _
    exact hs.trans (le_add_of_nonneg_right herr)
  · intro c hc he
    have hend : EndpointEligible c (meshPoint tau (actualPoint d N pre)) tau := by
      by_contra hn
      obtain ⟨k, hk⟩ := actual_sixth_disagreement_wall d N pre c _ tau hx he hn
      exact hoff ⟨c, k, hk⟩
    have hrow : (fresh c).lower (meshPoint tau (actualPoint d N pre)) tau ≤
        endpointLambda6 d N tau pre := finiteMax_row_le _ _ _ _ c hc ⟨he.1, hend⟩
    have hv := (abs_sub_le_iff.mp (eval_variation (fresh c) _ _ tau hx)).1
    have hslope := mul_le_mul_of_nonneg_right (candidate_slope_le c) htau.le
    have heval := fresh_eval c (actualPoint d N pre)
    dsimp [Form.lower] at hrow
    linarith

/-- Substitute a genuine affine parent piece BEFORE forming endpoint
errors. The resulting form has no independent parent coordinate. -/
def substituteParent (f a : Form) : Form :=
  ⟨f.constant + f.parentCoefficient * a.constant,
    fun i => f.coefficient i + f.parentCoefficient * a.coefficient i, 0⟩

theorem substituteParent_eval (f a : Form) (t : Physical) (r : ℝ) :
    (substituteParent f a).eval (t, r) = f.eval (t, a.eval (t, 0)) := by
  simp only [substituteParent, Form.eval, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, mul_zero, zero_mul, add_zero]
  ring

theorem substitute_self_minus_parent (a : Form) (ha : a.parentCoefficient = 0) :
    substituteParent (minus a parent) a = cn 0 := by
  apply form_ext
  · simp [substituteParent, minus, plus, scale, parent, cn, ha]
  · funext i
    simp [substituteParent, minus, plus, scale, parent, cn, ha]
  · rfl

theorem old_no_parent (c : Cell) : (old c).parentCoefficient = 0 := by
  cases hf : c.family <;>
    simp [old, hf, r0, scale, plus, minus, coord, cn]

def inheritedTest (c : Cell) (k : Key) : Test :=
  ⟨(gate c k).strict, substituteParent (gate c k).margin (old c)⟩

/-- The actual equality/inherit branch parent=oldCap is an OPEN branch
possibility, not a proper wall to discard. Its weak upper gate compiles to
zero<=zero and is retained for EVERY mesh width and EVERY endpoint. -/
theorem inherited_parent_upper_retained (c : Cell) (lo : Point) (tau : ℝ) :
    Inner (inheritedTest c .parentUpper) lo tau := by
  change 0 ≤ (substituteParent (minus (old c) parent) (old c)).lower lo tau
  rw [substitute_self_minus_parent (old c) (old_no_parent c)]
  simp [Form.lower, Form.slope, cn]

/-- Source-level inherited-branch dictionary. The displayed equality is
the original branch condition; it does not assume any compiler estimate
or any source equality. No assertion is made that all parents inherit. -/
theorem actual_inherited_gate_dictionary (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (c : Cell)
    (hbranch : actualParent5 d N pre = oldCap c (primeHistoryLogCoordinates N 6 pre))
    (k : Key) :
    Pass (inheritedTest c k) (primeHistoryLogCoordinates N 6 pre, 0) ↔
      Pass (gate c k) (actualPoint d N pre) := by
  have hev : (substituteParent (gate c k).margin (old c)).eval
      (primeHistoryLogCoordinates N 6 pre, 0) =
      (gate c k).margin.eval (actualPoint d N pre) := by
    rw [substituteParent_eval, old_eval]
    simp only [actualPoint, hbranch]
  cases hs : (gate c k).strict <;> simp [Pass, inheritedTest, hs, hev]

end
end ImbalancedChen.P2OriginalElevenAffineEndpointCompiler
