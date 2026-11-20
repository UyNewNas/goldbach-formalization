import ImbalancedChen.P4AOriginalFull87FiniteEighthCap
import ImbalancedChen.P1OriginalVariableFourthContinuation

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

A bounded finite rational quantizer, using the preceding packet's actual
one-step-biased floor. Monotone maps commute with a finite maximum ONLY
with the SAME eligible set. The eligibility predicate is never recomputed
at the rounded current value. Keeping an exact finite seed avoids losing
an already proved odd-history margin. No signed monotonicity is asserted.
-/
namespace ImbalancedChen.P1GuardFrozenFiniteCapAlgebra
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P1OriginalVariableFourthContinuation
open P4AOriginalFull87FiniteEighthCap (downCap downCap_cast downCap_error)
open P4AOriginalFull87HistoryCore (width width_pos)

/-- Clamp inputs, not an original source predicate. On the proved physical
range this operation is the identity. Outside it no approximation is claimed. -/
def clamp (x : ℝ) : ℝ := max 0 (min cap x)

theorem clamp_bounds (x : ℝ) : 0 ≤ clamp x ∧ clamp x ≤ cap := by
  exact ⟨le_max_left _ _, max_le (by norm_num [cap]) (min_le_left _ _)⟩

theorem clamp_eq {x : ℝ} (hx : 0 ≤ x) (hc : x ≤ cap) : clamp x = x := by
  simp only [clamp, min_eq_right hc, max_eq_right hx]

theorem clamp_mono : Monotone clamp := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

theorem downCap_mono (n : ℕ) : Monotone (downCap n) := by
  intro x y hxy
  have hd : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hf := Int.floor_mono (mul_le_mul_of_nonneg_left hxy hd)
  unfold downCap
  exact div_le_div_of_nonneg_right (by exact_mod_cast sub_le_sub_right hf 1)
    (by positivity)

/-- Finite, rational, nonnegative, and defined even for nonphysical inputs. -/
def rounded (n : ℕ) (x : ℝ) : ℚ := max 0 (downCap n (clamp x))

def roundedAlphabet (n : ℕ) : Finset ℚ :=
  insert 0 (P4AOriginalFull87FiniteEighthCap.alphabet n)

theorem rounded_mem (n : ℕ) (x : ℝ) : rounded n x ∈ roundedAlphabet n := by
  have hc := clamp_bounds x
  have hm := P4AOriginalFull87FiniteEighthCap.downCap_mem_alphabet n
    (clamp x) hc.1 (hc.2.trans_lt (by norm_num [cap]))
  unfold rounded roundedAlphabet
  by_cases h : 0 ≤ downCap n (clamp x)
  · rw [max_eq_right h]
    exact Finset.mem_insert_of_mem hm
  · rw [max_eq_left (le_of_not_ge h)]
    exact Finset.mem_insert_self _ _

theorem rounded_mono (n : ℕ) : Monotone (fun x : ℝ => (rounded n x : ℝ)) := by
  intro x y hxy
  exact_mod_cast max_le_max (le_refl (0 : ℚ)) (downCap_mono n (clamp_mono hxy))

theorem rounded_error (n : ℕ) (x : ℝ) (hx : 0 ≤ x) (hc : x ≤ cap) :
    x - 2 * width n < (rounded n x : ℝ) ∧
      0 ≤ (rounded n x : ℝ) ∧ (rounded n x : ℝ) ≤ x := by
  have he := downCap_error n x
  rw [rounded, clamp_eq hx hc, Rat.cast_max, Rat.cast_zero]
  exact ⟨he.1.trans_le (le_max_right _ _), le_max_left _ _,
    max_le hx (by linarith [width_pos n])⟩

/-- Preserve the actual original third seed instead of debiting it anew. -/
def protect (n : ℕ) (seed x : ℝ) : ℝ := max seed (rounded n x : ℝ)

theorem seed_le_protect (n : ℕ) (seed x : ℝ) : seed ≤ protect n seed x :=
  le_max_left _ _

theorem protect_mono (n : ℕ) (seed : ℝ) : Monotone (protect n seed) := by
  intro x y h
  exact max_le_max le_rfl (rounded_mono n h)

theorem protect_error (n : ℕ) (seed x : ℝ)
    (hs : 0 ≤ seed) (hsx : seed ≤ x) (hc : x ≤ cap) :
    seed ≤ protect n seed x ∧ x - 2 * width n < protect n seed x ∧
      protect n seed x ≤ x := by
  have he := rounded_error n x (hs.trans hsx) hc
  exact ⟨le_max_left _ _, he.1.trans_le (le_max_right _ _), max_le hsx he.2.2⟩

/-- A proved original lower gate with a margin delta survives with half
that margin. This elementary transport does NOT supply the original row's
margin or any integrated omitted-mass estimate by itself. -/
theorem protect_lower_gate (n : ℕ) (seed x gate delta : ℝ)
    (hs : 0 ≤ seed) (hsx : seed ≤ x) (hc : x ≤ cap)
    (hgate : gate + delta ≤ x) (hn : 4 * width n < delta) :
    gate + delta / 2 < protect n seed x := by
  have he := (protect_error n seed x hs hsx hc).2.1
  linarith

/-- No accumulating rounding debt: a later monotone raw cap dominates
all earlier rounded caps on the SAME grid. -/
theorem protect_nested (n : ℕ) (seed x y : ℝ) (hxy : x ≤ y) :
    max (protect n seed x) (rounded n y : ℝ) = protect n seed y := by
  unfold protect
  rw [max_assoc, max_eq_right (rounded_mono n hxy)]

/-- The original finite maximum is an attained value, not a supremum
requiring any extra continuity or strict monotonicity hypothesis. -/
theorem finiteMax_attained {ι : Type*} (rows : Finset ι)
    (eligible : ι → Prop) (profile : ι → ℝ) (seed : ℝ) :
    finiteMax rows eligible profile seed = seed ∨
      ∃ r ∈ rows, eligible r ∧ finiteMax rows eligible profile seed = profile r := by
  have hm : finiteMax rows eligible profile seed ∈ finiteValues rows eligible profile seed :=
    Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hm with h | h
  · exact Or.inl h
  · obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨r, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2, heq.symm⟩

/-- IMPORTANT: eligible is literally the same predicate on both sides.
This does not justify substituting a rounded parent INTO eligible. -/
theorem map_finiteMax {ι : Type*} (f : ℝ → ℝ) (hf : Monotone f)
    (rows : Finset ι) (eligible : ι → Prop) (profile : ι → ℝ) (seed : ℝ) :
    f (finiteMax rows eligible profile seed) =
      finiteMax rows eligible (fun r => f (profile r)) (f seed) := by
  apply le_antisymm
  · rcases finiteMax_attained rows eligible profile seed with h | ⟨r, hr, he, h⟩
    · rw [h]
      exact finiteMax_seed_le _ _ _ _
    · rw [h]
      exact finiteMax_row_le _ _ _ _ r hr he
  · apply finiteMax_le
    · exact hf (finiteMax_seed_le rows eligible profile seed)
    · intro r hr he
      exact hf (finiteMax_row_le rows eligible profile seed r hr he)

theorem protect_finiteMax {ι : Type*} (n : ℕ) (base : ℝ)
    (rows : Finset ι) (eligible : ι → Prop) (profile : ι → ℝ) (seed : ℝ) :
    protect n base (finiteMax rows eligible profile seed) =
      finiteMax rows eligible (fun r => protect n base (profile r)) (protect n base seed) :=
  map_finiteMax _ (protect_mono n base) rows eligible profile seed

/-- A real cap in a finite rational alphabet stays rational after max. -/
theorem protect_mem_union (n : ℕ) (A : Finset ℚ) (seed x : ℝ)
    (hs : seed ∈ A.image (fun a => (a : ℝ))) :
    protect n seed x ∈ (A ∪ roundedAlphabet n).image (fun a => (a : ℝ)) := by
  by_cases h : (rounded n x : ℝ) ≤ seed
  · rw [protect, max_eq_left h]
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨a, Finset.mem_union_left _ ha, rfl⟩
  · rw [protect, max_eq_right (le_of_not_ge h)]
    exact Finset.mem_image.mpr
      ⟨rounded n x, Finset.mem_union_right _ (rounded_mem n x), rfl⟩

end
end ImbalancedChen.P1GuardFrozenFiniteCapAlgebra
