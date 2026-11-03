import ImbalancedChen.P4AOriginalFull87StrictActionTrim
import Mathlib.Algebra.Order.Floor.Ring

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Finite rational rank-eight caps, one alphabet fixed before every N.
The original affine cap is rounded DOWN with one extra grid step.  The
rounding debit is less than two steps.  On the exact compact action trims,
all lower gates keep delta/2 and the original selected-tent upper licence
keeps a positive grid step.  This is not a finiteization of ranks 4/5/6,
not a signed-saving monotonicity theorem, and not a compiler reserve.
-/
namespace ImbalancedChen.P4AOriginalFull87FiniteEighthCap
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)

/-- One guard-independent, rational, downward-biased rounding rule. -/
def downCap (n : ℕ) (x : ℝ) : ℚ :=
  ((⌊((n : ℝ) + 1) * x⌋ - 1 : ℤ) : ℚ) / ((n : ℚ) + 1)

theorem downCap_cast (n : ℕ) (x : ℝ) :
    (downCap n x : ℝ) =
      ((⌊((n : ℝ) + 1) * x⌋ : ℝ) - 1) / ((n : ℝ) + 1) := by
  simp [downCap]

/-- Valid for every real x, including integer grid walls. The extra step
is never lost when x lies exactly on a rounding boundary. -/
theorem downCap_error (n : ℕ) (x : ℝ) :
    x - 2 * width n < (downCap n x : ℝ) ∧
      (downCap n x : ℝ) ≤ x - width n := by
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlo := Int.floor_le (((n : ℝ) + 1) * x)
  have hhi := Int.lt_floor_add_one (((n : ℝ) + 1) * x)
  rw [downCap_cast]
  constructor
  · apply (lt_div_iff₀ hd).mpr
    have heq : (x - 2 * width n) * ((n : ℝ) + 1) =
        ((n : ℝ) + 1) * x - 2 := by
      unfold width
      field_simp [ne_of_gt hd]
      <;> ring
    rw [heq]
    linarith
  · apply (div_le_iff₀ hd).mpr
    have heq : (x - width n) * ((n : ℝ) + 1) =
        ((n : ℝ) + 1) * x - 1 := by
      unfold width
      field_simp [ne_of_gt hd]
      <;> ring
    rw [heq]
    linarith

/-- A literal finite rational alphabet, independent of c,t,e,q,omega,N. -/
def alphabet (n : ℕ) : Finset ℚ :=
  (Finset.Icc (-1 : ℤ) (n : ℤ)).image fun k => (k : ℚ) / ((n : ℚ) + 1)

theorem downCap_mem_alphabet (n : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    downCap n x ∈ alphabet n := by
  let k : ℤ := ⌊((n : ℝ) + 1) * x⌋
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlo := Int.floor_le (((n : ℝ) + 1) * x)
  have hhi := Int.lt_floor_add_one (((n : ℝ) + 1) * x)
  have hprod : 0 ≤ ((n : ℝ) + 1) * x := mul_nonneg hd.le hx
  have hkloR : (-1 : ℝ) < (k : ℝ) := by dsimp [k]; linarith
  have hklo : (-1 : ℤ) < k := by exact_mod_cast hkloR
  have hprodup : ((n : ℝ) + 1) * x < (n : ℝ) + 1 := by nlinarith
  have hkupR : (k : ℝ) < (n : ℝ) + 1 := by dsimp [k]; linarith
  have hkup : k < (n : ℤ) + 1 := by exact_mod_cast hkupR
  apply Finset.mem_image.mpr
  exact ⟨k - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩

def finiteCap (n : ℕ) (c : Cell) (t : Point) : ℚ := downCap n (newCap c t)

theorem finiteCap_mem_alphabet (n : ℕ) {c : Cell} {t : Point} (hs : Source c t) :
    finiteCap n c t ∈ alphabet n :=
  downCap_mem_alphabet n _
    (P4AOriginalFull87SourceDispatch.source_cap_positive hs).le
    ((source_physical_ceiling hs).trans (by norm_num))

/-- Every square licence is transported in its correct direction.
The comparison bound will be replaced by the ACTUAL parent below. -/
theorem finiteCap_licensed (n : ℕ) {delta : ℝ} (hd : 0 < delta)
    (hn : 4 * width n < delta) {c : Cell} {t : Point} (ht : t ∈ trim c delta) :
    delta / 2 < (finiteCap n c t : ℝ) ∧
    comparison c t + delta / 2 < (finiteCap n c t : ℝ) ∧
    (∀ j, prefixSquareExpr t j + delta / 2 < (finiteCap n c t : ℝ)) ∧
    (∀ j ∉ selected c,
      selectedSquareExpr (selected c) t j + delta / 2 < (finiteCap n c t : ℝ)) ∧
    (finiteCap n c t : ℝ) + width n ≤ newCap c t ∧
    (finiteCap n c t : ℝ) + width n < v (∑ j ∈ selected c, t j) := by
  have hs : Source c t := trim_subset_source c hd ht
  have ha := ((mem_trim c delta t).mp ht).2.2
  have herr := downCap_error n (newCap c t)
  change newCap c t - 2 * width n < (finiteCap n c t : ℝ) ∧
      (finiteCap n c t : ℝ) ≤ newCap c t - width n at herr
  have hpos := ha Margin.positive
  have hgain := ha Margin.improvement
  dsimp only [actionSlack] at hpos hgain
  refine ⟨by linarith, by linarith, ?_, ?_, by linarith, ?_⟩
  · intro j
    have h := ha (Margin.full j)
    dsimp only [actionSlack] at h
    linarith
  · intro j hj
    have h := ha (Margin.complement j)
    simp only [actionSlack, if_neg hj] at h
    linarith
  · have h := source_selected_license hs
    linarith

theorem exists_uniform_cap_resolution (delta : ℝ) (hd : 0 < delta) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → 4 * width n < delta := by
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp
    (width_tendsto.eventually (gt_mem_nhds (show (0 : ℝ) < delta / 4 by positivity)))
  exact ⟨n0, fun n hn => by have h := hn0 n hn; linarith⟩

/-- The rounded cap is strictly below the ORIGINAL physical ceiling and
terminal cube as well, not only below a newly introduced surrogate cap. -/
theorem finiteCap_upper (n : ℕ) {c : Cell} {t : Point} (hs : Source c t) :
    (finiteCap n c t : ℝ) < (153 / 256 : ℝ) ∧
      (finiteCap n c t : ℝ) < (∑ j, t j) + 3 * t 7 := by
  have herr := (downCap_error n (newCap c t)).2
  have hp := width_pos n
  have hlo : (finiteCap n c t : ℝ) < newCap c t := by
    change (finiteCap n c t : ℝ) ≤ newCap c t - width n at herr
    linarith
  exact ⟨hlo.trans (source_physical_ceiling hs),
    hlo.trans (source_improvement_terminal hs).2⟩

end
end ImbalancedChen.P4AOriginalFull87FiniteEighthCap
