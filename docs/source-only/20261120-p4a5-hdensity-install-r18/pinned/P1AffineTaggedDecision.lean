import ImbalancedChen.P1AffineCertifiedLookup
import Mathlib.Data.Fintype.EquivFin

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Finite affine tests select an actual label, not just a scalar value.
Labels are encoded injectively by fixed natural constants. The existing
closed-box certificate therefore fixes the LABEL throughout the box,
including equality decisions. No uniqueness of a maximizer is assumed.
-/
namespace ImbalancedChen.P1AffineTaggedDecision
noncomputable section
open scoped Classical BigOperators
open Set
open P1FiniteAffineDecisionProgram P1AffineCertifiedMesh P1AffineCertifiedLookup

inductive Trace (k : ℕ) (α : Type*) where
  | leaf : α → Trace k α
  | branch : Gate k → Trace k α → Trace k α → Trace k α

def Trace.eval {k : ℕ} {α : Type*} (t : Fin k → ℝ) : Trace k α → α
  | .leaf a => a
  | .branch g yes no => if g.holds t then yes.eval t else no.eval t

/-- Only comparison programs and fixed constant tags enter this code. -/
def Trace.compile {k : ℕ} {α : Type*} (key : α → ℝ) : Trace k α → Program k
  | .leaf a => .leaf (Affine.const (key a))
  | .branch g yes no => g.branch (yes.compile key) (no.compile key)

theorem Trace.compile_eval {k : ℕ} {α : Type*} (d : Trace k α)
    (key : α → ℝ) (t : Fin k → ℝ) :
    (d.compile key).eval t = key (d.eval t) := by
  induction d with
  | leaf a => simp [Trace.compile, Trace.eval, Program.eval]
  | branch g yes no hy hn =>
      cases hg : g.strict <;>
        simp [Trace.compile, Gate.branch, Program.eval, Trace.eval,
          Gate.holds, hg, hy, hn, apply_ite]

/-- Evaluation using a finite comparison signature. The resulting label
exists even for unrealizable signatures; those have no geometric points. -/
def Trace.selectTag {k : ℕ} {α : Type*}
    (cmp : Affine k → Affine k → Bool × Bool) : Trace k α → α
  | .leaf a => a
  | .branch g yes no =>
      let bits := cmp (g.lhs.select cmp) (g.rhs.select cmp)
      if (if g.strict then bits.1 else bits.2) then
        yes.selectTag cmp else no.selectTag cmp

theorem Trace.select_compile {k : ℕ} {α : Type*} (d : Trace k α)
    (key : α → ℝ) (cmp : Affine k → Affine k → Bool × Bool) :
    (d.compile key).select cmp = Affine.const (key (d.selectTag cmp)) := by
  induction d with
  | leaf a => rfl
  | branch g yes no hy hn =>
      cases hg : g.strict <;>
        simp [Trace.compile, Gate.branch, Program.select, Trace.selectTag,
          hg, hy, hn, apply_ite]

/-- A fixed injective coding; no arithmetic target or sample point occurs. -/
def tagKey {α : Type*} [Fintype α] (a : α) : ℝ :=
  ((Fintype.equivFin α a).val : ℝ)

theorem tagKey_injective {α : Type*} [Fintype α] :
    Function.Injective (@tagKey α _) := by
  intro a b h
  apply (Fintype.equivFin α).injective
  apply Fin.ext
  exact_mod_cast h

def Trace.code {k : ℕ} {α : Type*} [Fintype α] (d : Trace k α) : Program k :=
  d.compile tagKey

def Trace.tableTag {k : ℕ} {α : Type*} [Fintype α] (d : Trace k α)
    (s : d.code.Signature) : α := d.selectTag (d.code.lookup s)

theorem Trace.tag_on_region {k : ℕ} {α : Type*} [Fintype α]
    (d : Trace k α) (s : d.code.Signature) (t : Fin k → ℝ)
    (ht : t ∈ d.code.region s) : d.eval t = d.tableTag s := by
  have h := d.code.table_on_region s t ht
  change ((d.compile tagKey).select (d.code.lookup s)).eval t =
    (d.compile tagKey).eval t at h
  rw [Trace.select_compile, Affine.eval_const, Trace.compile_eval] at h
  exact tagKey_injective h.symm

theorem Trace.tableTag_exact {k : ℕ} {α : Type*} [Fintype α]
    (d : Trace k α) (t : Fin k → ℝ) :
    d.tableTag (d.code.signature t) = d.eval t :=
  (d.tag_on_region _ t rfl).symm

/-- One fixed tag on the ENTIRE certified closed rectangle, not just a
mask attached to a single sampled point or a constant cap. -/
theorem Trace.tag_on_closed_box {k : ℕ} {α : Type*} [Fintype α]
    (d : Trace k α) (s : d.code.Signature) (lo hi : Fin k → ℝ)
    (hc : d.code.BoxCertificate s lo hi) (t : Fin k → ℝ)
    (hl : ∀ i, lo i ≤ t i) (hu : ∀ i, t i ≤ hi i) :
    d.eval t = d.tableTag s :=
  d.tag_on_region s t (d.code.boxCertificate_sound s lo hi hc t hl hu).1

def Trace.lookup {k : ℕ} {α : Type*} [Fintype α]
    (d : Trace k α) (m : ℕ) (t : Fin k → ℝ) : α :=
  if t ∈ cube k ∧ gridLabel m t ∈ approved d.code m then
    d.tableTag (d.code.signature (center m (gridLabel m t)))
  else d.tableTag (d.code.signature t)

/-- Rejected cells and proper equality walls retain exact decisions.
This lookup does not change a policy or erase an arithmetic occurrence. -/
theorem Trace.lookup_exact {k : ℕ} {α : Type*} [Fintype α]
    (d : Trace k α) (m : ℕ) (t : Fin k → ℝ) : d.lookup m t = d.eval t := by
  unfold Trace.lookup
  split_ifs with h
  · have hb := mem_logPrimeMeshCell.mp (gridLabel_mem m t h.1)
    exact (d.tag_on_closed_box _ _ _ ((mem_approved _ _ _).mp h.2)
      t (fun i => (hb i).1) (fun i => (hb i).2.le)).symm
  · exact d.tableTag_exact t

/-- Conjunctions are interpreted with their ORIGINAL strict/nonstrict bits. -/
def guarded {k : ℕ} {α : Type*} :
    List (Gate k) → Trace k α → Trace k α → Trace k α
  | [], yes, _ => yes
  | g :: gs, yes, no => .branch g (guarded gs yes no) no

theorem guarded_eval {k : ℕ} {α : Type*} (gs : List (Gate k))
    (yes no : Trace k α) (t : Fin k → ℝ) :
    (guarded gs yes no).eval t =
      if ∀ g ∈ gs, g.holds t then yes.eval t else no.eval t := by
  induction gs with
  | nil => simp [guarded]
  | cons g gs ih =>
      by_cases hg : g.holds t <;>
        by_cases hgs : ∀ h ∈ gs, h.holds t <;>
        simp [guarded, Trace.eval, ih, hg, hgs]

/-- First witness in one fixed pre-N enumeration. This selects provenance
among ties; it does not impose a new tie rule on an existing finite maximum. -/
def firstWitness {k : ℕ} {α : Type*} (tests : α → List (Gate k)) :
    List α → Trace k (Option α)
  | [] => .leaf none
  | a :: as => guarded (tests a) (.leaf (some a)) (firstWitness tests as)

theorem firstWitness_sound {k : ℕ} {α : Type*} (tests : α → List (Gate k))
    (xs : List α) (t : Fin k → ℝ) (a : α)
    (h : (firstWitness tests xs).eval t = some a) :
    a ∈ xs ∧ ∀ g ∈ tests a, g.holds t := by
  revert h
  induction xs with
  | nil => intro h; simp [firstWitness, Trace.eval] at h
  | cons b bs ih =>
      intro h
      rw [firstWitness, guarded_eval] at h
      by_cases hb : ∀ g ∈ tests b, g.holds t
      · rw [if_pos hb] at h
        have hba : b = a := Option.some.inj h
        subst b
        exact ⟨by simp, hb⟩
      · rw [if_neg hb] at h
        obtain ⟨ha,ht⟩ := ih h
        exact ⟨List.mem_cons_of_mem b ha,ht⟩

theorem firstWitness_none_iff {k : ℕ} {α : Type*} (tests : α → List (Gate k))
    (xs : List α) (t : Fin k → ℝ) :
    (firstWitness tests xs).eval t = none ↔
      ∀ a ∈ xs, ¬(∀ g ∈ tests a, g.holds t) := by
  induction xs with
  | nil => simp [firstWitness, Trace.eval]
  | cons a as ih =>
      rw [firstWitness, guarded_eval]
      by_cases ha : ∀ g ∈ tests a, g.holds t <;> simp [ha, Trace.eval, ih]

theorem firstWitness_exists {k : ℕ} {α : Type*} (tests : α → List (Gate k))
    (xs : List α) (t : Fin k → ℝ)
    (h : ∃ a ∈ xs, ∀ g ∈ tests a, g.holds t) :
    ∃ a, (firstWitness tests xs).eval t = some a := by
  cases he : (firstWitness tests xs).eval t with
  | none =>
      obtain ⟨a,ha,hg⟩ := h
      exact ((firstWitness_none_iff tests xs t).mp he a ha hg).elim
  | some a => exact ⟨a,he⟩

end
end ImbalancedChen.P1AffineTaggedDecision
