import ImbalancedChen.P5ActualHBDyadicProductWindow
import ImbalancedChen.RestrictedResidueScale

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The scale below is the COMPLETE outer HB product.  It is not the residual
modulus and it is not the product of the three W endpoint lengths.  Each
original HB group keeps its own 1/log(n) normalization.  A dyadic block of
one selected occurrence and a dyadic block of its whole complement have
product between one quarter of the complete integer and that integer.
These assertions follow from the actual ordered positive factor tuples.
-/

namespace ImbalancedChen.P5Z.OriginalHBCompleteProductScale
noncomputable section
open Classical Filter
open scoped BigOperators
open ImbalancedChen.Part3
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow

/-- The denominator is the logarithm of THIS ORIGINAL group product.
It is never the logarithm of a chosen individual HB occurrence. -/
def normalizedBlock (z y : ℝ) (j n : ℕ) (bs : List Block) : ℂ :=
  blockCoefficient z y j n bs / (Real.log (n : ℝ) : ℂ)

theorem normalized_original_group_identity {z y : ℝ} (hz : 0 ≤ z) (hy : 0 ≤ y)
    {n : ℕ} (hn : (n : ℝ) ≤ y ^ 3) :
    (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * roughOneSlot z n) /
        (Real.log (n : ℝ) : ℂ) =
      ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ)) : ℝ) : ℂ) *
          ∑ bs ∈ blockWords n (2 * (j + 1)), normalizedBlock z y j n bs := by
  rw [actual_dyadic_rough_HB_identity hz hy hn]
  simp only [Finset.sum_div, normalizedBlock, mul_div_assoc]

/-- Every original group retains its own log and its own signed HB row.
This product equality does not identify different original groups. -/
theorem all_original_group_logs {ι : Type*} (s : Finset ι)
    (z y : ι → ℝ) (n : ι → ℕ) (hz : ∀ i ∈ s, 0 ≤ z i)
    (hy : ∀ i ∈ s, 0 ≤ y i) (hn : ∀ i ∈ s, (n i : ℝ) ≤ y i ^ 3) :
    (∏ i ∈ s, (((ArithmeticFunction.vonMangoldt (n i) : ℝ) : ℂ) *
      roughOneSlot (z i) (n i)) / (Real.log (n i : ℝ) : ℂ)) =
    ∏ i ∈ s, ∑ j ∈ Finset.range 3,
      ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ)) : ℝ) : ℂ) *
        ∑ bs ∈ blockWords (n i) (2 * (j + 1)), normalizedBlock (z i) (y i) j (n i) bs := by
  apply Finset.prod_congr rfl
  intro i hi
  exact normalized_original_group_identity (hz i hi) (hy i hi) (hn i hi)

/-- Dividing by the original group log cannot manufacture an active block.
Units, for which the logarithmic numerator vanishes, cause no exception. -/
theorem normalized_active_window {z y : ℝ} (hz : 0 ≤ z) {j n : ℕ}
    {bs : List Block} (hj : j ∈ Finset.range 3)
    (h : normalizedBlock z y j n bs ≠ 0) :
    bs.length ≤ 6 ∧ (bs.map lower).prod ≤ n ∧ n ≤ 64 * (bs.map lower).prod := by
  have hb : blockCoefficient z y j n bs ≠ 0 := by
    intro he
    exact h (by simp [normalizedBlock, he])
  exact actual_block_six_slot_window hz hj hb

/-- An original HB row contains actual ordered occurrences. Equal values
do not merge their positions, or remove any original group log. -/
structure OriginalGroupTuple where
  integer : ℕ
  row : ℕ
  factors : List ℕ
  mem : factors ∈ factorTuples (2 * (row + 1)) integer

def joined (gs : List OriginalGroupTuple) : List ℕ := (gs.map (·.factors)).flatten
def completeInteger (gs : List OriginalGroupTuple) : ℕ := (gs.map (·.integer)).prod

theorem joined_prod (gs : List OriginalGroupTuple) : (joined gs).prod = completeInteger gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      have hg := (factorTuples_spec _ _ g.factors g.mem).2.1
      simpa only [joined, completeInteger, List.map_cons, List.flatten_cons,
        List.prod_append, List.prod_cons, hg] using congrArg (g.integer * ·) ih

theorem joined_pos (gs : List OriginalGroupTuple) : ∀ p ∈ joined gs, 0 < p := by
  induction gs with
  | nil => simp [joined]
  | cons g gs ih =>
      intro p hp
      have hp' : p ∈ g.factors ++ joined gs := by simpa [joined] using hp
      rcases List.mem_append.mp hp' with hp | hp
      · exact (factorTuples_spec _ _ g.factors g.mem).2.2 p hp
      · exact ih p hp

/-- Literal dyadic complete scale after selecting one HB occurrence and
dyadically regrouping ALL its complementary occurrences. b and c are fixed
block labels, before any source tuple is summed. -/
def localScale (b c : Block) : ℝ := (lower b : ℝ) * (lower c : ℝ)

/-- The source scale parameter is log_x N, unrelated to a sieve-state
ratio. In particular the original spectral N^(7/32) is not replaced by
x^(7/32). The upper moving-residue range bounds qscale uniformly. -/
def qscale (N : ℕ) (x : ℝ) : ℝ := Real.log (N : ℝ) / Real.log x

theorem qscale_relation {N : ℕ} (hN : 1 < N) {x kappa : ℝ}
    (hx : 1 < x) (hres : (N : ℝ) ≤ x ^ (1 + kappa)) :
    x ^ qscale N x = N ∧ 0 < qscale N x ∧ qscale N x ≤ 1 + kappa := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hxp : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hmul : Real.log x * qscale N x = Real.log (N : ℝ) := by
    dsimp only [qscale]
    field_simp [hL.ne']
  refine ⟨?_, div_pos (Real.log_pos hNr) hL, ?_⟩
  · rw [Real.rpow_def_of_pos hxp, hmul, Real.exp_log hNp]
  · apply (div_le_iff₀ hL).mpr
    have hh := (Real.log_le_log_iff hNp (Real.rpow_pos_of_pos hxp _)).mpr hres
    rw [Real.log_rpow hxp] at hh
    exact hh

theorem actual_occurrence_complete_window (gs : List OriginalGroupTuple)
    {p : ℕ} (hp : p ∈ joined gs) {b c : Block}
    (hb : Owns b p) (hc : Owns c (completeInteger gs / p)) :
    1 ≤ (lower b : ℝ) ∧ 1 ≤ (lower c : ℝ) ∧
      localScale b c ≤ (completeInteger gs : ℝ) ∧
      (completeInteger gs : ℝ) ≤ 4 * localScale b c := by
  have hd : p ∣ completeInteger gs := by rw [← joined_prod]; exact List.dvd_prod hp
  have hprod : p * (completeInteger gs / p) = completeInteger gs := Nat.mul_div_cancel' hd
  have hblo := (owns_bounds hb).1
  have hbhi := (owns_bounds hb).2
  have hclo := (owns_bounds hc).1
  have hchi := (owns_bounds hc).2
  have hlo := Nat.mul_le_mul hblo hclo
  have hhi := Nat.mul_le_mul hbhi hchi
  rw [hprod] at hlo hhi
  refine ⟨by exact_mod_cast (Nat.succ_le_iff.mpr (lower_pos b)),
    by exact_mod_cast (Nat.succ_le_iff.mpr (lower_pos c)), ?_, ?_⟩
  · dsimp only [localScale]
    exact_mod_cast hlo
  · have hh : completeInteger gs ≤ 4 * (lower b * lower c) := by nlinarith
    dsimp only [localScale]
    exact_mod_cast hh

/-- The original smooth complete-product trim and upper support transfer
to x with explicit constants. No bound on a residual quotient is used. -/
theorem actual_trimmed_complete_scale {N : ℕ} {C κ₀ : ℝ}
    (gs : List OriginalGroupTuple) {p : ℕ} (hp : p ∈ joined gs) {b c : Block}
    (hb : Owns b p) (hc : Owns c (completeInteger gs / p))
    (htrim : (N : ℝ) ^ (1 - κ₀) ≤ (completeInteger gs : ℝ))
    (hsupport : (completeInteger gs : ℝ) ≤ C * N) :
    (1 / 4 : ℝ) * (N : ℝ) ^ (1 - κ₀) ≤ localScale b c ∧
      localScale b c ≤ C * N := by
  have hw := actual_occurrence_complete_window gs hp hb hc
  exact ⟨by linarith [hw.2.2.2], hw.2.2.1.trans hsupport⟩

/-- The threshold precedes every actual group, factor tuple and block.
The physical residue is the original target N. -/
theorem exists_actual_HB_residue_threshold {C κ κ₀ : ℝ}
    (hC : 0 < C) (hκ : 0 < κ) (htrim : κ₀ < κ / (4 * (1 + κ))) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (gs : List OriginalGroupTuple) (p : ℕ) (b c : Block),
      p ∈ joined gs → Owns b p → Owns c (completeInteger gs / p) →
      (N : ℝ) ^ (1 - κ₀) ≤ (completeInteger gs : ℝ) →
      (completeInteger gs : ℝ) ≤ C * N →
      1 < localScale b c ∧ C⁻¹ * localScale b c ≤ N ∧
        (N : ℝ) ≤ localScale b c ^ (1 + κ) := by
  obtain ⟨_, N₀, hN₀, hscale⟩ :=
    ImbalancedChen.exists_manuscript_restrictedResidueScale_threshold
      (by norm_num : (0 : ℝ) < 1 / 4) hC hκ htrim
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN gs p b c hp hb hc ht hs
  have hw := actual_trimmed_complete_scale gs hp hb hc ht hs
  exact hscale N hN (localScale b c) hw.1 hw.2

end
end ImbalancedChen.P5Z.OriginalHBCompleteProductScale
