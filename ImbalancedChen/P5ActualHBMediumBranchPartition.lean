import ImbalancedChen.P5ActualHBDyadicProductWindow

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- Original PP section 4 selects an INDIVIDUAL occurrence in the original
-- medium window. A maximal occurrence does not license that selection.
-- Here the first medium position is fixed from the entire block word,
-- before any factor tuple. The complementary Type I branch is retained.
namespace ImbalancedChen.P5Z.ActualHBMediumBranchPartition
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow

def Medium (A B : ℝ) (b : Block) : Prop := A ≤ (lower b : ℝ) ∧ (lower b : ℝ) ≤ B

def firstMedium (A B : ℝ) (bs : List Block) : Option ℕ :=
  bs.findIdx? (fun b => decide (Medium A B b))

def longBlocks (B : ℝ) (bs : List Block) : List Block :=
  bs.filter (fun b => decide (B < (lower b : ℝ)))

def rawProduct (bs : List Block) : ℝ := ((bs.map lower).prod : ℕ)

theorem rawProduct_nil : rawProduct [] = 1 := by simp [rawProduct]
theorem rawProduct_cons (b : Block) (bs : List Block) :
    rawProduct (b::bs) = (lower b : ℝ) * rawProduct bs := by
  simp [rawProduct]

theorem rawProduct_nonneg (bs : List Block) : 0 ≤ rawProduct bs := by
  exact Nat.cast_nonneg _

theorem lower_one_le (b : Block) : (1 : ℝ) ≤ lower b := by
  have h : 1 ≤ lower b := Nat.succ_le_of_lt (lower_pos b)
  exact_mod_cast h

-- The selected position retains occurrence order and its original role.
theorem firstMedium_some {A B : ℝ} {bs : List Block} {i : ℕ}
    (h : firstMedium A B bs = some i) :
    ∃ hi : i < bs.length, Medium A B bs[i] ∧
      ∀ k (hk : k < i), ¬Medium A B (bs[k]'(hk.trans hi)) := by
  obtain ⟨hi,hm,hbefore⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hi,by simpa using hm,fun k hk => by simpa using hbefore k hk⟩

theorem firstMedium_none {A B : ℝ} {bs : List Block} :
    firstMedium A B bs = none ↔ ∀ b ∈ bs, ¬Medium A B b := by
  simp only [firstMedium,List.findIdx?_eq_none_iff,decide_eq_false_iff_not]

theorem noMedium_short_or_long {A B : ℝ} {bs : List Block}
    (hn : firstMedium A B bs = none) {b : Block} (hb : b ∈ bs) :
    (lower b : ℝ) < A ∨ B < (lower b : ℝ) := by
  have h := firstMedium_none.mp hn b hb
  unfold Medium at h
  by_cases ha : A ≤ (lower b : ℝ)
  · exact Or.inr (lt_of_not_ge (fun hh => h ⟨ha,hh⟩))
  · exact Or.inl (lt_of_not_ge ha)

private theorem rawProduct_le_pow {A : ℝ} (hA : 0 ≤ A) :
    ∀ bs : List Block, (∀ b ∈ bs, (lower b : ℝ) ≤ A) →
      rawProduct bs ≤ A^bs.length := by
  intro bs
  induction bs with
  | nil => intro h; simp [rawProduct]
  | cons b bs ih =>
    intro h
    have hb := h b (by simp)
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem b hc))
    rw [rawProduct_cons,List.length_cons,pow_succ]
    exact (mul_le_mul hb ht (rawProduct_nonneg bs) hA).trans_eq (mul_comm _ _)

-- This bound counts literal long OCCURRENCES, including repeated blocks.
theorem long_power_le_rawProduct {B : ℝ} (hB : 1 ≤ B) :
    ∀ bs : List Block, B^(longBlocks B bs).length ≤ rawProduct bs := by
  intro bs
  induction bs with
  | nil => simp [longBlocks,rawProduct]
  | cons b bs ih =>
    have hb := lower_one_le b
    have hp := rawProduct_nonneg bs
    by_cases hl : B < (lower b : ℝ)
    · have hh := mul_le_mul hl.le ih (by positivity : 0 ≤ B^(longBlocks B bs).length)
        (by linarith : 0 ≤ (lower b : ℝ))
      simpa [longBlocks,hl,rawProduct_cons,pow_succ,mul_comm] using hh
    · have hh : B^(longBlocks B bs).length ≤ (lower b : ℝ)*rawProduct bs := by
        have hg := mul_le_mul_of_nonneg_right hb hp
        nlinarith
      simpa [longBlocks,hl,rawProduct_cons] using hh

-- An actual nonzero six-slot coefficient has a genuine long occurrence
-- if its lower product cannot be made entirely from short occurrences.
theorem actual_noMedium_has_long {z y A B : ℝ} (hz : 0 ≤ z) (hA : 1 ≤ A)
    {j n : ℕ} {bs : List Block} (hj : j ∈ Finset.range 3)
    (hn : blockCoefficient z y j n bs ≠ 0)
    (hbranch : firstMedium A B bs = none)
    (hscale : 64*A^6 < (n : ℝ)) :
    ∃ b ∈ bs, B < (lower b : ℝ) := by
  obtain ⟨hlen,hlo,hhi⟩ := actual_block_six_slot_window hz hj hn
  by_contra h
  have hcap : ∀ b ∈ bs, (lower b : ℝ) ≤ A := by
    intro b hb
    rcases noMedium_short_or_long hbranch hb with hs | hl
    · exact hs.le
    · exact False.elim (h ⟨b,hb,hl⟩)
  have hp := rawProduct_le_pow (by linarith : 0 ≤ A) bs hcap
  have hexp : A^bs.length ≤ A^6 := pow_le_pow_right₀ hA hlen
  have hn' : (n : ℝ) ≤ 64*rawProduct bs := by exact_mod_cast hhi
  nlinarith

-- This is also valid for concatenated original group words once their
-- physical complete-product bound supplies rawProduct < B^3.
theorem atMostTwoLong {B : ℝ} (hB : 1 ≤ B) {bs : List Block}
    (hphysical : rawProduct bs < B^3) : (longBlocks B bs).length ≤ 2 := by
  by_contra h
  have hc : 3 ≤ (longBlocks B bs).length := by omega
  have hp := pow_le_pow_right₀ hB hc
  have hprod := long_power_le_rawProduct hB bs
  linarith

theorem actual_noMedium_one_or_two_long {z y A B : ℝ}
    (hz : 0 ≤ z) (hA : 1 ≤ A) (hB : 1 ≤ B)
    {j n : ℕ} {bs : List Block} (hj : j ∈ Finset.range 3)
    (hn : blockCoefficient z y j n bs ≠ 0)
    (hbranch : firstMedium A B bs = none)
    (hshort : 64*A^6 < (n : ℝ)) (hcomplete : (n : ℝ) < B^3) :
    (longBlocks B bs).length = 1 ∨ (longBlocks B bs).length = 2 := by
  obtain ⟨b,hb,hbl⟩ := actual_noMedium_has_long hz hA hj hn hbranch hshort
  have hmem : b ∈ longBlocks B bs := by simp [longBlocks,hb,hbl]
  have hpos : 0 < (longBlocks B bs).length := List.length_pos.mpr (by
    intro he; simpa [he] using hmem)
  have hlo := (actual_block_product_window hz hn).2.1
  have hr : rawProduct bs ≤ (n : ℝ) := by exact_mod_cast hlo
  have htwo := atMostTwoLong hB (hr.trans_lt hcomplete)
  omega

-- Exact arithmetic branch partition. Neither branch is discarded and
-- the original signed weights and the one logarithm are left untouched.
def mediumPart (A B z y : ℝ) (j n : ℕ) (bs : List Block) : ℂ :=
  if firstMedium A B bs = none then 0 else blockCoefficient z y j n bs

def typeIPart (A B z y : ℝ) (j n : ℕ) (bs : List Block) : ℂ :=
  if firstMedium A B bs = none then blockCoefficient z y j n bs else 0

theorem exact_block_partition (A B z y : ℝ) (j n : ℕ) (bs : List Block) :
    blockCoefficient z y j n bs = mediumPart A B z y j n bs +
      typeIPart A B z y j n bs := by
  by_cases h : firstMedium A B bs = none <;> simp [mediumPart,typeIPart,h]

theorem actual_original_identity_partition {z y : ℝ} (hz : 0 ≤ z) (hy : 0 ≤ y)
    (A B : ℝ) {n : ℕ} (hn : (n : ℝ) ≤ y^3) :
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)*ImbalancedChen.Part3.roughOneSlot z n =
      ∑ j ∈ Finset.range 3, (((-1 : ℝ)^j*(Nat.choose 3 (j+1) : ℝ) : ℝ) : ℂ)*
        (∑ bs ∈ blockWords n (2*(j+1)),
          (mediumPart A B z y j n bs + typeIPart A B z y j n bs)) := by
  rw [actual_dyadic_rough_HB_identity hz hy hn]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Finset.sum_congr rfl
  intro bs hbs
  exact exact_block_partition A B z y j n bs

def originalLower (X zeta : ℝ) : ℝ := X^(3*zeta)
def originalUpper (X zeta : ℝ) : ℝ := X^(1/3+zeta/4)

-- No claim is made that a largest slot is medium. The two primitive
-- numerical chart reserves are explicit; local scale transfer, auxiliary
-- SW, one/two-long Brun estimates and all final PP bounds remain OPEN.
end
end ImbalancedChen.P5Z.ActualHBMediumBranchPartition
