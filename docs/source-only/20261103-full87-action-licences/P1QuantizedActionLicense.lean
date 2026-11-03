import ImbalancedChen.P1GuardFrozenFiniteCapAlgebra
import ImbalancedChen.SelectedPrefixBoxCap

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The finite-parent construction does not by itself license a selected mask.
This module transports the ORIGINAL half/full/complementary lower gates
through the EXISTING biased quantizer. A winning row is extracted from the
SAME raw eligible finite maximum; inactive and losing rows are not assigned
an inherited mask. No signed monotonicity or integral estimate is used.
-/
namespace ImbalancedChen.P1QuantizedActionLicense
noncomputable section
open scoped Classical BigOperators Topology
open Filter VariableEnvelope P1OriginalVariableFourthContinuation
open P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)

/-- Selected indices have no complementary test. They repeat the harmless
half gate rather than creating a spurious complementary-square obligation. -/
abbrev Gate (k : ℕ) := Option (Bool × Fin k)

def gate {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ) : Gate k → ℝ
  | none => 1 / 2
  | some (false, j) => prefixSquareExpr t j
  | some (true, j) => if j ∈ I then 1 / 2 else selectedSquareExpr I t j

def LowerLicense {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ) (M : ℝ) : Prop :=
  ∀ g : Gate k, gate I t g < M

theorem lowerLicense_iff {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ) (M : ℝ) :
    LowerLicense I t M ↔ (1 / 2 : ℝ) < M ∧
      (∀ j, prefixSquareExpr t j < M) ∧
      (∀ j ∉ I, selectedSquareExpr I t j < M) := by
  constructor
  · intro h
    exact ⟨h none, fun j => h (some (false,j)),
      fun j hj => by simpa only [gate, if_neg hj] using h (some (true,j))⟩
  · rintro ⟨hh,hf,hc⟩ g
    cases g with
    | none => exact hh
    | some x =>
      rcases x with ⟨b,j⟩
      cases b with
      | false => exact hf j
      | true =>
        by_cases hj : j ∈ I
        · simpa only [gate, if_pos hj] using hh
        · simpa only [gate, if_neg hj] using hc j hj

/-- A real positive floor for a finite set of actual strictly positive
values. The sentinel makes empty banks safe, without a nonempty hypothesis. -/
theorem exists_positive_floor {ι : Type*} (s : Finset ι) (P : ι → Prop)
    (f : ι → ℝ) (hf : ∀ i ∈ s, P i → 0 < f i) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ i ∈ s, P i → delta ≤ f i := by
  let S := insert (1 : ℝ) ((s.filter P).image f)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have hm := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with he | hi
    · rw [he]; norm_num
    · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hi
      rw [← he]
      exact hf i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  · intro i hi hp
    exact Finset.min'_le S (f i)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hp⟩,rfl⟩))

/-- The margin is computed from the gates, not a new input licence. -/
def margin {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ) (M : ℝ) : ℝ :=
  (insert 1 (Finset.univ.image (fun g : Gate k => M - gate I t g))).min'
    ⟨1, Finset.mem_insert_self _ _⟩

theorem margin_le {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ) (M : ℝ)
    (g : Gate k) : margin I t M ≤ M - gate I t g := by
  exact Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g,Finset.mem_univ _,rfl⟩))

theorem margin_pos {k : ℕ} {I : Finset (Fin k)} {t : Fin k → ℝ} {M : ℝ}
    (h : LowerLicense I t M) : 0 < margin I t M := by
  have hm := Finset.min'_mem
    (insert 1 (Finset.univ.image (fun g : Gate k => M - gate I t g)))
    (show (insert 1 (Finset.univ.image (fun g : Gate k => M - gate I t g))).Nonempty
      from ⟨1, Finset.mem_insert_self _ _⟩)
  rcases Finset.mem_insert.mp hm with he | hi
  · change 0 < margin I t M
    change margin I t M = 1 at he
    rw [he]; norm_num
  · obtain ⟨g,_,he⟩ := Finset.mem_image.mp hi
    change M - gate I t g = margin I t M at he
    rw [← he]
    exact sub_pos.mpr (h g)

theorem exists_resolution (delta : ℝ) (hd : 0 < delta) :
    ∃ n0 : ℕ, ∀ n ≥ n0, 8 * width n < delta := by
  obtain ⟨n0,hn0⟩ := Filter.eventually_atTop.mp
    (width_tendsto.eventually (gt_mem_nhds (show (0 : ℝ) < delta / 8 by positivity)))
  exact ⟨n0,fun n hn => by have h := hn0 n hn; linarith⟩

/-- A positive rounded value retains the extra full downward grid step.
Clipping to zero is NOT permitted to erase that debit in this statement. -/
theorem rounded_step (n : ℕ) (M : ℝ) (hM : 0 ≤ M) (hc : M ≤ cap)
    (hpos : 0 < (rounded n M : ℝ)) :
    (rounded n M : ℝ) + width n ≤ M := by
  have hq : (0 : ℚ) < max 0 (P4AOriginalFull87FiniteEighthCap.downCap n M) := by
    have hh := hpos
    rw [rounded, clamp_eq hM hc] at hh
    exact_mod_cast hh
  have hd : (0 : ℚ) < P4AOriginalFull87FiniteEighthCap.downCap n M := by
    simpa only [lt_max_iff, lt_self_iff_false, false_or] using hq
  rw [rounded, clamp_eq hM hc, max_eq_right hd.le]
  have he := (P4AOriginalFull87FiniteEighthCap.downCap_error n M).2
  linarith

/-- Transport every actual lower gate, with an explicit half-margin.
Only the range and original gate margins are generic hypotheses here;
the concrete archive suppliers prove them from their original row tests. -/
theorem rounded_licensed {k : ℕ} (n : ℕ) (I : Finset (Fin k))
    (t : Fin k → ℝ) (M delta : ℝ) (hd : 0 < delta) (hc : M ≤ cap)
    (hg : ∀ g : Gate k, gate I t g + delta ≤ M)
    (hn : 4 * width n < delta) :
    (∀ g : Gate k, gate I t g + delta / 2 < (rounded n M : ℝ)) ∧
      (rounded n M : ℝ) + width n ≤ M := by
  have hh := hg none
  have hM : 0 ≤ M := by change (1 / 2 : ℝ) + delta ≤ M at hh; linarith
  have herr := (rounded_error n M hM hc).1
  have hlow : ∀ g : Gate k, gate I t g + delta / 2 < (rounded n M : ℝ) := by
    intro g
    have h := hg g
    linarith
  refine ⟨hlow, rounded_step n M hM hc ?_⟩
  have h := hlow none
  change (1 / 2 : ℝ) + delta / 2 < (rounded n M : ℝ) at h
  linarith

/-- Same eligible subset; a STRICT increase has a genuine winning row.
The selected row equals its own rounded endpoint, not an unrelated seed.
The raw eligibility is not re-evaluated at any rounded current. -/
theorem winning_row {ι : Type*} (n : ℕ) (base parent : ℝ)
    (rows : Finset ι) (eligible : ι → Prop) (raw : ι → ℝ)
    (hbase : base ≤ parent)
    (hwin : parent < finiteMax rows eligible (fun i => protect n base (raw i)) parent) :
    ∃ i ∈ rows, eligible i ∧
      finiteMax rows eligible (fun i => protect n base (raw i)) parent =
        (rounded n (raw i) : ℝ) := by
  rcases finiteMax_attained rows eligible (fun i => protect n base (raw i)) parent with
    he | ⟨i,hi,hg,he⟩
  · exact (lt_irrefl parent (he ▸ hwin)).elim
  · refine ⟨i,hi,hg,?_⟩
    have hr : base < protect n base (raw i) := hbase.trans_lt (he ▸ hwin)
    have hq : base < (rounded n (raw i) : ℝ) := by
      simpa only [protect, lt_max_iff, lt_self_iff_false, false_or] using hr
    rw [he, protect, max_eq_right hq.le]

/-- Once the value is licensed, the original integer gates are obtained
with the unchanged selected mask and exact power dictionary. -/
theorem integer_squares {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ)
    (M : ℝ) (h : LowerLicense I t M) (N : ℝ) (hN : 1 < N)
    (p : Fin k → ℕ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i) :
    (∀ j, ((∏ i ∈ Finset.univ.filter (fun i : Fin k => i < j), p i : ℕ) : ℝ) *
      (p j : ℝ)^2 < N ^ M) ∧
    (∀ j ∉ I, ((∏ i ∈ I, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i : Fin k => i < j ∧ i ∉ I), p i : ℕ) : ℝ) *
      (p j : ℝ)^2 < N ^ M) := by
  obtain ⟨_,hf,hs⟩ := (lowerLicense_iff I t M).mp h
  exact ⟨fun j => prefixSquareExpr_actual_gate N hN p t hp j (hf j),
    fun j hj => selectedSquareExpr_actual_gate I N hN p t hp j (hs j hj)⟩

end
end ImbalancedChen.P1QuantizedActionLicense
