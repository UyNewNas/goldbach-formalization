import ImbalancedChen.P1OriginalVariableFourthContinuation
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

A finite affine comparison program, with distinct strict and nonstrict
branches. The program contains no arbitrary point-dependent predicate.
Its finite signature cells retain equality faces. A closed-box certificate
checks BOTH endpoint signs, not a midpoint or a sampled execution.
-/
namespace ImbalancedChen.P1FiniteAffineDecisionProgram
noncomputable section
open scoped Classical BigOperators
open P1OriginalVariableFourthContinuation

structure Affine (k : ℕ) where
  constant : ℝ
  coefficient : Fin k → ℝ

def Affine.eval {k : ℕ} (a : Affine k) (t : Fin k → ℝ) : ℝ :=
  a.constant + ∑ i, a.coefficient i * t i

def Affine.const {k : ℕ} (x : ℝ) : Affine k := ⟨x, fun _ => 0⟩
def Affine.coord {k : ℕ} (i : Fin k) : Affine k :=
  ⟨0, fun j => if j = i then 1 else 0⟩
def Affine.add {k : ℕ} (a b : Affine k) : Affine k :=
  ⟨a.constant + b.constant, fun i => a.coefficient i + b.coefficient i⟩
def Affine.sub {k : ℕ} (a b : Affine k) : Affine k :=
  ⟨a.constant - b.constant, fun i => a.coefficient i - b.coefficient i⟩
def Affine.scale {k : ℕ} (s : ℝ) (a : Affine k) : Affine k :=
  ⟨s * a.constant, fun i => s * a.coefficient i⟩
def Affine.sum {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Affine k) : Affine k :=
  ⟨∑ i ∈ s, (f i).constant, fun j => ∑ i ∈ s, (f i).coefficient j⟩

@[simp] theorem Affine.eval_const {k : ℕ} (x : ℝ) (t : Fin k → ℝ) :
    (Affine.const x).eval t = x := by simp [Affine.eval, Affine.const]
@[simp] theorem Affine.eval_coord {k : ℕ} (i : Fin k) (t : Fin k → ℝ) :
    (Affine.coord i).eval t = t i := by simp [Affine.eval, Affine.coord, ite_mul]
@[simp] theorem Affine.eval_add {k : ℕ} (a b : Affine k) (t : Fin k → ℝ) :
    (a.add b).eval t = a.eval t + b.eval t := by
  simp only [Affine.eval, Affine.add, add_mul, Finset.sum_add_distrib]
  ring
@[simp] theorem Affine.eval_sub {k : ℕ} (a b : Affine k) (t : Fin k → ℝ) :
    (a.sub b).eval t = a.eval t - b.eval t := by
  simp only [Affine.eval, Affine.sub, sub_mul, Finset.sum_sub_distrib]
  ring
@[simp] theorem Affine.eval_scale {k : ℕ} (s : ℝ) (a : Affine k) (t : Fin k → ℝ) :
    (a.scale s).eval t = s * a.eval t := by
  simp only [Affine.eval, Affine.scale, mul_add, mul_assoc, Finset.mul_sum]
@[simp] theorem Affine.eval_sum {k : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Affine k) (t : Fin k → ℝ) :
    (Affine.sum s f).eval t = ∑ i ∈ s, (f i).eval t := by
  simp only [Affine.eval, Affine.sum, Finset.sum_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

inductive Program (k : ℕ) where
  | leaf : Affine k → Program k
  | sup : Program k → Program k → Program k
  | inf : Program k → Program k → Program k
  | lt : Program k → Program k → Program k → Program k → Program k
  | le : Program k → Program k → Program k → Program k → Program k

def Program.eval {k : ℕ} (t : Fin k → ℝ) : Program k → ℝ
  | .leaf a => a.eval t
  | .sup a b => max (a.eval t) (b.eval t)
  | .inf a b => min (a.eval t) (b.eval t)
  | .lt a b yes no => if a.eval t < b.eval t then yes.eval t else no.eval t
  | .le a b yes no => if a.eval t ≤ b.eval t then yes.eval t else no.eval t

def Program.leaves {k : ℕ} : Program k → Finset (Affine k)
  | .leaf a => {a}
  | .sup a b | .inf a b => a.leaves ∪ b.leaves
  | .lt a b yes no | .le a b yes no =>
      (a.leaves ∪ b.leaves) ∪ (yes.leaves ∪ no.leaves)

/-- Only the two finite comparison bits are read. Equality has lt=false,
le=true and is not confused with either strict side. -/
def Program.select {k : ℕ} (cmp : Affine k → Affine k → Bool × Bool) :
    Program k → Affine k
  | .leaf a => a
  | .sup a b => if (cmp (a.select cmp) (b.select cmp)).2 then b.select cmp else a.select cmp
  | .inf a b => if (cmp (a.select cmp) (b.select cmp)).2 then a.select cmp else b.select cmp
  | .lt a b yes no =>
      if (cmp (a.select cmp) (b.select cmp)).1 then yes.select cmp else no.select cmp
  | .le a b yes no =>
      if (cmp (a.select cmp) (b.select cmp)).2 then yes.select cmp else no.select cmp

theorem Program.select_mem {k : ℕ} (p : Program k)
    (cmp : Affine k → Affine k → Bool × Bool) : p.select cmp ∈ p.leaves := by
  induction p with
  | leaf a => simp [Program.select, Program.leaves]
  | sup a b ha hb => simp only [Program.select]; split_ifs <;> simp [Program.leaves, ha, hb]
  | inf a b ha hb => simp only [Program.select]; split_ifs <;> simp [Program.leaves, ha, hb]
  | lt a b yes no ha hb hy hn =>
      simp only [Program.select]; split_ifs <;> simp [Program.leaves, hy, hn]
  | le a b yes no ha hb hy hn =>
      simp only [Program.select]; split_ifs <;> simp [Program.leaves, hy, hn]

/-- The theorem is used with the actual finite affine comparisons below.
It is not a premise of the concrete producer correctness theorems. -/
theorem Program.select_correct {k : ℕ} (p : Program k) (t : Fin k → ℝ)
    (cmp : Affine k → Affine k → Bool × Bool)
    (hcmp : ∀ a ∈ p.leaves, ∀ b ∈ p.leaves,
      cmp a b = (decide (a.eval t < b.eval t), decide (a.eval t ≤ b.eval t))) :
    (p.select cmp).eval t = p.eval t := by
  revert hcmp
  induction p with
  | leaf a => intro _; rfl
  | sup a b ha hb =>
      intro hcmp
      have hca := ha (fun x hx y hy => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy]))
      have hcb := hb (fun x hx y hy => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy]))
      have h := hcmp (a.select cmp) (by simp [Program.leaves, a.select_mem cmp])
        (b.select cmp) (by simp [Program.leaves, b.select_mem cmp])
      simp only [Program.select, h, hca, hcb, decide_eq_true_eq, Program.eval]
      by_cases hab : a.eval t ≤ b.eval t
      · simp [hab, max_eq_right hab, hcb]
      · simp [hab, max_eq_left (le_of_not_ge hab), hca]
  | inf a b ha hb =>
      intro hcmp
      have hca := ha (fun x hx y hy => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy]))
      have hcb := hb (fun x hx y hy => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy]))
      have h := hcmp (a.select cmp) (by simp [Program.leaves, a.select_mem cmp])
        (b.select cmp) (by simp [Program.leaves, b.select_mem cmp])
      simp only [Program.select, h, hca, hcb, decide_eq_true_eq, Program.eval]
      by_cases hab : a.eval t ≤ b.eval t
      · simp [hab, min_eq_left hab, hca]
      · simp [hab, min_eq_right (le_of_not_ge hab), hcb]
  | lt a b yes no ha hb hy hn =>
      intro hcmp
      have hca := ha (fun x hx y hy' => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy']))
      have hcb := hb (fun x hx y hy' => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy']))
      have hcy := hy (fun x hx y hy' => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy']))
      have hcn := hn (fun x hx y hy' => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy']))
      have h := hcmp (a.select cmp) (by simp [Program.leaves, a.select_mem cmp])
        (b.select cmp) (by simp [Program.leaves, b.select_mem cmp])
      simp only [Program.select, h, hca, hcb, decide_eq_true_eq, Program.eval]
      split_ifs <;> assumption
  | le a b yes no ha hb hy hn =>
      intro hcmp
      have hca := ha (fun x hx y hy' => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy']))
      have hcb := hb (fun x hx y hy' => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy']))
      have hcy := hy (fun x hx y hy' => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy']))
      have hcn := hn (fun x hx y hy' => hcmp x (by simp [Program.leaves, hx]) y (by simp [Program.leaves, hy']))
      have h := hcmp (a.select cmp) (by simp [Program.leaves, a.select_mem cmp])
        (b.select cmp) (by simp [Program.leaves, b.select_mem cmp])
      simp only [Program.select, h, hca, hcb, decide_eq_true_eq, Program.eval]
      split_ifs <;> assumption

abbrev Program.Label {k : ℕ} (p : Program k) := {a : Affine k // a ∈ p.leaves}
abbrev Program.Signature {k : ℕ} (p : Program k) :=
  (p.Label × p.Label) → Bool × Bool

/-- This is a genuinely finite index set. No affine cell feasibility
oracle is required; inconsistent signatures have empty geometric cells. -/
def Program.allSignatures {k : ℕ} (p : Program k) : Finset p.Signature := Finset.univ

def Program.signature {k : ℕ} (p : Program k) (t : Fin k → ℝ) : p.Signature :=
  fun ab => (decide (ab.1.val.eval t < ab.2.val.eval t),
    decide (ab.1.val.eval t ≤ ab.2.val.eval t))

def Program.lookup {k : ℕ} (p : Program k) (s : p.Signature)
    (a b : Affine k) : Bool × Bool :=
  if ha : a ∈ p.leaves then if hb : b ∈ p.leaves then s (⟨a, ha⟩, ⟨b, hb⟩)
    else (false, false) else (false, false)

def Program.table {k : ℕ} (p : Program k) (s : p.Signature) : Affine k :=
  p.select (p.lookup s)

def Program.region {k : ℕ} (p : Program k) (s : p.Signature) : Set (Fin k → ℝ) :=
  {t | p.signature t = s}

theorem Program.table_exact {k : ℕ} (p : Program k) (t : Fin k → ℝ) :
    (p.table (p.signature t)).eval t = p.eval t := by
  apply p.select_correct t (p.lookup (p.signature t))
  intro a ha b hb
  simp only [Program.lookup, dif_pos ha, dif_pos hb, Program.signature]

theorem Program.table_on_region {k : ℕ} (p : Program k) (s : p.Signature)
    (t : Fin k → ℝ) (ht : t ∈ p.region s) : (p.table s).eval t = p.eval t := by
  change p.signature t = s at ht
  rw [← ht]
  exact p.table_exact t

/-- The full finite partition includes all equality cells; impossible bit
assignments simply define empty regions. No wall deletion is performed. -/
theorem Program.regions_cover {k : ℕ} (p : Program k) :
    (⋃ s : p.Signature, p.region s) = Set.univ := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨p.signature t, rfl⟩

theorem Program.region_unique {k : ℕ} (p : Program k) (s r : p.Signature)
    (t : Fin k → ℝ) (hs : t ∈ p.region s) (hr : t ∈ p.region r) : s = r := by
  change p.signature t = s at hs
  change p.signature t = r at hr
  exact hs.symm.trans hr

/-- Exact coefficient-sign extrema on a closed rectangular box. -/
def Affine.lower {k : ℕ} (a : Affine k) (lo hi : Fin k → ℝ) : ℝ :=
  a.constant + ∑ i, if 0 ≤ a.coefficient i then a.coefficient i * lo i
    else a.coefficient i * hi i

def Affine.upper {k : ℕ} (a : Affine k) (lo hi : Fin k → ℝ) : ℝ :=
  a.constant + ∑ i, if 0 ≤ a.coefficient i then a.coefficient i * hi i
    else a.coefficient i * lo i

theorem Affine.box_bounds {k : ℕ} (a : Affine k) (lo hi t : Fin k → ℝ)
    (hl : ∀ i, lo i ≤ t i) (hu : ∀ i, t i ≤ hi i) :
    a.lower lo hi ≤ a.eval t ∧ a.eval t ≤ a.upper lo hi := by
  constructor
  · apply add_le_add_left
    apply Finset.sum_le_sum
    intro i _
    by_cases h : 0 ≤ a.coefficient i
    · simp only [if_pos h]; exact mul_le_mul_of_nonneg_left (hl i) h
    · simp only [if_neg h]; exact mul_le_mul_of_nonpos_left (hu i) (le_of_not_ge h)
  · apply add_le_add_left
    apply Finset.sum_le_sum
    intro i _
    by_cases h : 0 ≤ a.coefficient i
    · simp only [if_pos h]; exact mul_le_mul_of_nonneg_left (hu i) h
    · simp only [if_neg h]; exact mul_le_mul_of_nonpos_left (hl i) (le_of_not_ge h)

def Program.BoxCertificate {k : ℕ} (p : Program k) (s : p.Signature)
    (lo hi : Fin k → ℝ) : Prop :=
  ∀ ab : p.Label × p.Label,
    let d := ab.1.val.sub ab.2.val
    (if (s ab).1 then d.upper lo hi < 0 else 0 ≤ d.lower lo hi) ∧
    (if (s ab).2 then d.upper lo hi ≤ 0 else 0 < d.lower lo hi)

/-- A certificate is a sufficient whole-box test, not an assumed sample
identity. This does not say every original rectangle passes the test. -/
theorem Program.boxCertificate_sound {k : ℕ} (p : Program k) (s : p.Signature)
    (lo hi : Fin k → ℝ) (hc : p.BoxCertificate s lo hi)
    (t : Fin k → ℝ) (hl : ∀ i, lo i ≤ t i) (hu : ∀ i, t i ≤ hi i) :
    t ∈ p.region s ∧ (p.table s).eval t = p.eval t := by
  have hsig : p.signature t = s := by
    funext ab
    have hb := (ab.1.val.sub ab.2.val).box_bounds lo hi t hl hu
    rw [Affine.eval_sub] at hb
    have h := hc ab
    rcases hab : s ab with ⟨ltBit, leBit⟩
    simp only [hab] at h
    apply Prod.ext
    · change decide (ab.1.val.eval t < ab.2.val.eval t) = ltBit
      cases ltBit with
      | false =>
          have hx : ab.2.val.eval t ≤ ab.1.val.eval t := by
            have hl' : 0 ≤ (ab.1.val.sub ab.2.val).lower lo hi := h.1
            linarith [hb.1]
          simp [not_lt_of_ge hx]
      | true =>
          have hx : ab.1.val.eval t < ab.2.val.eval t := by
            have hu' : (ab.1.val.sub ab.2.val).upper lo hi < 0 := h.1
            linarith [hb.2]
          simp [hx]
    · change decide (ab.1.val.eval t ≤ ab.2.val.eval t) = leBit
      cases leBit with
      | false =>
          have hx : ab.2.val.eval t < ab.1.val.eval t := by
            have hl' : 0 < (ab.1.val.sub ab.2.val).lower lo hi := h.2
            linarith [hb.1]
          simp [not_le_of_gt hx]
      | true =>
          have hx : ab.1.val.eval t ≤ ab.2.val.eval t := by
            have hu' : (ab.1.val.sub ab.2.val).upper lo hi ≤ 0 := h.2
            linarith [hb.2]
          simp [hx]
  exact ⟨hsig, p.table_on_region s t hsig⟩

/-- Lift an own-rank program into a larger coordinate space. The theorem
states exactly which coordinates are read; there is no child-dependent
choice of a predecessor label. -/
def Affine.pull {k l : ℕ} (f : Fin k → Fin l) (a : Affine k) : Affine l :=
  ⟨a.constant, fun j => ∑ i, if f i = j then a.coefficient i else 0⟩

@[simp] theorem Affine.eval_pull {k l : ℕ} (f : Fin k → Fin l)
    (a : Affine k) (t : Fin l → ℝ) :
    (a.pull f).eval t = a.eval (fun i => t (f i)) := by
  simp only [Affine.eval, Affine.pull, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

def Program.pull {k l : ℕ} (f : Fin k → Fin l) : Program k → Program l
  | .leaf a => .leaf (a.pull f)
  | .sup a b => .sup (a.pull f) (b.pull f)
  | .inf a b => .inf (a.pull f) (b.pull f)
  | .lt a b yes no => .lt (a.pull f) (b.pull f) (yes.pull f) (no.pull f)
  | .le a b yes no => .le (a.pull f) (b.pull f) (yes.pull f) (no.pull f)

@[simp] theorem Program.eval_pull {k l : ℕ} (f : Fin k → Fin l)
    (p : Program k) (t : Fin l → ℝ) :
    (p.pull f).eval t = p.eval (fun i => t (f i)) := by
  induction p <;> simp_all [Program.pull, Program.eval]

structure Gate (k : ℕ) where
  strict : Bool
  lhs : Program k
  rhs : Program k

def Gate.holds {k : ℕ} (t : Fin k → ℝ) (g : Gate k) : Prop :=
  if g.strict then g.lhs.eval t < g.rhs.eval t else g.lhs.eval t ≤ g.rhs.eval t

def Gate.branch {k : ℕ} (g : Gate k) (yes no : Program k) : Program k :=
  if g.strict then .lt g.lhs g.rhs yes no else .le g.lhs g.rhs yes no

def allGates {k : ℕ} : List (Gate k) → Program k → Program k → Program k
  | [], yes, _ => yes
  | g :: gs, yes, no => g.branch (allGates gs yes no) no

@[simp] theorem eval_allGates {k : ℕ} (gs : List (Gate k))
    (yes no : Program k) (t : Fin k → ℝ) :
    (allGates gs yes no).eval t =
      if ∀ g ∈ gs, g.holds t then yes.eval t else no.eval t := by
  induction gs with
  | nil => simp [allGates]
  | cons g gs ih =>
      cases hg : g.strict <;>
        simp [allGates, Gate.branch, Gate.holds, hg, Program.eval, ih]
      all_goals split_ifs <;> simp_all

private theorem finiteMax_insert {ι : Type*} (s : Finset ι) (i : ι)
    (eligible : ι → Prop) (profile : ι → ℝ) (seed : ℝ) :
    finiteMax (insert i s) eligible profile seed =
      if eligible i then max (profile i) (finiteMax s eligible profile seed)
      else finiteMax s eligible profile seed := by
  by_cases hi : eligible i
  · rw [if_pos hi]
    apply le_antisymm
    · apply finiteMax_le
      · exact (finiteMax_seed_le _ _ _ _).trans (le_max_right _ _)
      · intro j hj he
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact le_max_left _ _
        · exact (finiteMax_row_le _ _ _ _ j hj he).trans (le_max_right _ _)
    · apply max_le
      · exact finiteMax_row_le _ _ _ _ i (Finset.mem_insert_self _ _) hi
      · apply finiteMax_le
        · exact finiteMax_seed_le _ _ _ _
        · intro j hj he
          exact finiteMax_row_le _ _ _ _ j (Finset.mem_insert_of_mem hj) he
  · rw [if_neg hi]
    apply le_antisymm
    · apply finiteMax_le
      · exact finiteMax_seed_le _ _ _ _
      · intro j hj he
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact (hi he).elim
        · exact finiteMax_row_le _ _ _ _ j hj he
    · apply finiteMax_le
      · exact finiteMax_seed_le _ _ _ _
      · intro j hj he
        exact finiteMax_row_le _ _ _ _ j (Finset.mem_insert_of_mem hj) he

/-- Parallel maximum: tests read the original named parent program.
The recursively accumulated maximum is not substituted into those tests. -/
def maxRows {k : ℕ} {ι : Type*} (tests : ι → List (Gate k))
    (candidate : ι → Program k) (seed : Program k) : List ι → Program k
  | [] => seed
  | i :: is =>
      let rest := maxRows tests candidate seed is
      allGates (tests i) (.sup (candidate i) rest) rest

theorem eval_maxRows {k : ℕ} {ι : Type*} (tests : ι → List (Gate k))
    (candidate : ι → Program k) (seed : Program k) (xs : List ι) (t : Fin k → ℝ) :
    (maxRows tests candidate seed xs).eval t =
      finiteMax xs.toFinset (fun i => ∀ g ∈ tests i, g.holds t)
        (fun i => (candidate i).eval t) (seed.eval t) := by
  induction xs with
  | nil =>
      simp only [maxRows, List.toFinset_nil]
      symm
      exact finiteMax_eq_seed_of_outside _ _ _ _ (by simp)
  | cons i xs ih =>
      simp only [maxRows, eval_allGates, Program.eval, ih, List.toFinset_cons]
      exact (finiteMax_insert _ _ _ _ _).symm

end
end ImbalancedChen.P1FiniteAffineDecisionProgram
