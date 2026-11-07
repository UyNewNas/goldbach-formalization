import ImbalancedChen.P2U8DirectedBoxEnclosure
import Mathlib.Algebra.Order.Floor.Semiring

/-!
SOURCE ONLY / UNCOMPILED. Explicit complete uniform rational covers of
the original U8 domain, with no coverage hypothesis in the final bound.

The carrier meshes the entire closed rectangle
[417/5000,1/3] × [1/3,1/2]. Its decidable rational filter only removes
cells whose lower corner already lies strictly beyond x+2y=1.
Cells on that wall and every cell crossing it are retained. Each selected
cell pays its complete closed-box enclosure, including its exterior part.

No adopted fine-cell table, selected numerical endpoint, or assertion
about convergence to that endpoint is supplied by this module.
-/

namespace ImbalancedChen.P2U8UniformRationalCover

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open Classical
open P2NegativeDomainCover P2U8DirectedBoxEnclosure

def step (a b : ℚ) (M : ℕ) : ℚ := (b - a) / (M : ℚ)
def node (a b : ℚ) (M k : ℕ) : ℚ := a + step a b M * (k : ℚ)

theorem step_pos {a b : ℚ} (hab : a < b) {M : ℕ} (hM : 0 < M) :
    0 < step a b M := by
  exact div_pos (sub_pos.mpr hab) (by exact_mod_cast hM)

theorem step_mul_count (a b : ℚ) {M : ℕ} (hM : 0 < M) :
    step a b M * (M : ℚ) = b - a := by
  unfold step
  exact div_mul_cancel₀ _ (by exact_mod_cast hM.ne')

theorem node_last (a b : ℚ) {M : ℕ} (hM : 0 < M) : node a b M M = b := by
  rw [node, step_mul_count a b hM]
  ring

theorem node_mono {a b : ℚ} (hab : a < b) {M : ℕ} (hM : 0 < M)
    {j k : ℕ} (hjk : j ≤ k) : node a b M j ≤ node a b M k := by
  exact add_le_add_left (mul_le_mul_of_nonneg_left (by exact_mod_cast hjk)
    (step_pos hab hM).le) a

theorem start_le_node {a b : ℚ} (hab : a < b) {M : ℕ} (hM : 0 < M) (k : ℕ) :
    a ≤ node a b M k := by
  exact le_add_of_nonneg_right (mul_nonneg (step_pos hab hM).le (Nat.cast_nonneg k))

theorem node_le_end {a b : ℚ} (hab : a < b) {M : ℕ} (hM : 0 < M)
    {k : ℕ} (hk : k ≤ M) : node a b M k ≤ b := by
  exact (node_mono hab hM hk).trans_eq (node_last a b hM)

/-- Floor-indexed coverage of every half-open side, including rational
mesh edges. The cell itself is closed, so no point is lost at an edge. -/
theorem uniform_interval_halfopen {a b : ℚ} (hab : a < b) {M : ℕ}
    (hM : 0 < M) {x : ℝ} (hx : x ∈ Ico (a : ℝ) (b : ℝ)) :
    ∃ i : Fin M,
      ((node a b M i.val : ℚ) : ℝ) ≤ x ∧
        x ≤ ((node a b M (i.val + 1) : ℚ) : ℝ) := by
  let δ : ℝ := (step a b M : ℝ)
  let k := Nat.floor ((x - (a : ℝ)) / δ)
  have hδ : 0 < δ := by exact_mod_cast step_pos hab hM
  have hcancel : δ * (M : ℝ) = (b : ℝ) - a := by
    exact_mod_cast step_mul_count a b hM
  have hnorm : 0 ≤ (x - (a : ℝ)) / δ := div_nonneg (sub_nonneg.mpr hx.1) hδ.le
  have hk : k < M := by
    apply (Nat.floor_lt hnorm).mpr
    apply (div_lt_iff₀ hδ).mpr
    nlinarith only [hx.2, hcancel]
  have hlo := (le_div_iff₀ hδ).mp (Nat.floor_le hnorm)
  have hhi := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((x - (a : ℝ)) / δ))
  refine ⟨⟨k, hk⟩, ?_, ?_⟩
  · simp only [node, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
    change (a : ℝ) + δ * (k : ℝ) ≤ x
    nlinarith only [hlo]
  · simp only [node, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
    change x ≤ (a : ℝ) + δ * ((k : ℝ) + 1)
    nlinarith only [hhi]

/-- The final closed endpoint is assigned to the last cell explicitly;
there is no additional cell extending beyond the original rectangle. -/
theorem uniform_interval_closed {a b : ℚ} (hab : a < b) {M : ℕ}
    (hM : 0 < M) {x : ℝ} (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    ∃ i : Fin M,
      ((node a b M i.val : ℚ) : ℝ) ≤ x ∧
        x ≤ ((node a b M (i.val + 1) : ℚ) : ℝ) := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · exact uniform_interval_halfopen hab hM ⟨hx.1, hlt⟩
  · have hlast : M - 1 + 1 = M := by omega
    refine ⟨⟨M - 1, by omega⟩, ?_, ?_⟩
    · change ((node a b M (M - 1) : ℚ) : ℝ) ≤ x
      rw [heq]
      exact_mod_cast node_le_end hab hM (Nat.sub_le M 1)
    · change x ≤ ((node a b M (M - 1 + 1) : ℚ) : ℝ)
      rw [heq, hlast, node_last a b hM]

def alpha : ℚ := 417 / 5000
def cubeWall : ℚ := 1 / 3
def top : ℚ := 1 / 2

theorem alpha_lt_cubeWall : alpha < cubeWall := by norm_num [alpha, cubeWall]
theorem cubeWall_lt_top : cubeWall < top := by norm_num [cubeWall, top]

def meshBox (M : ℕ) (ij : Fin M × Fin M) : Box :=
  ⟨node alpha cubeWall M ij.1.val, node alpha cubeWall M (ij.1.val + 1),
    node cubeWall top M ij.2.val, node cubeWall top M (ij.2.val + 1)⟩

/-- A finite decidable filter. Equality is deliberately retained. -/
def selected (M : ℕ) : Finset (Fin M × Fin M) :=
  Finset.univ.filter fun ij => (meshBox M ij).xl + 2 * (meshBox M ij).yl ≤ 1

theorem meshBox_valid {M : ℕ} (hM : 0 < M) (ij : Fin M × Fin M) :
    (meshBox M ij).Valid := by
  have hxlo := start_le_node alpha_lt_cubeWall hM ij.1.val
  have hylo := start_le_node cubeWall_lt_top hM ij.2.val
  have hxorder := node_mono alpha_lt_cubeWall hM (Nat.le_succ ij.1.val)
  have hyorder := node_mono cubeWall_lt_top hM (Nat.le_succ ij.2.val)
  have hxhi := node_le_end alpha_lt_cubeWall hM (Nat.succ_le_of_lt ij.1.isLt)
  have hyhi := node_le_end cubeWall_lt_top hM (Nat.succ_le_of_lt ij.2.isLt)
  change 0 < node alpha cubeWall M ij.1.val ∧
    node alpha cubeWall M ij.1.val ≤ node alpha cubeWall M (ij.1.val + 1) ∧
    0 < node cubeWall top M ij.2.val ∧
    node cubeWall top M ij.2.val ≤ node cubeWall top M (ij.2.val + 1) ∧
    node alpha cubeWall M (ij.1.val + 1) + node cubeWall top M (ij.2.val + 1) < 1
  refine ⟨?_, hxorder, ?_, hyorder, ?_⟩
  · exact (by norm_num [alpha] : (0 : ℚ) < alpha).trans_le hxlo
  · exact (by norm_num [cubeWall] : (0 : ℚ) < cubeWall).trans_le hylo
  · have hfixed : cubeWall + top < 1 := by norm_num [cubeWall, top]
    linarith only [hxhi, hyhi, hfixed]

/-- The full closed original rectangle is genuinely meshed. -/
theorem mesh_rectangle_cover {M : ℕ} (hM : 0 < M) {x : Point}
    (hx : x ∈ Icc (fun i : Fin 2 => if i = 0 then (alpha : ℝ) else (cubeWall : ℝ))
      (fun i : Fin 2 => if i = 0 then (cubeWall : ℝ) else (top : ℝ))) :
    ∃ ij : Fin M × Fin M, x ∈ (meshBox M ij).region := by
  have hx0 : x 0 ∈ Icc (alpha : ℝ) (cubeWall : ℝ) := by
    simpa using (show (if (0 : Fin 2) = 0 then (alpha : ℝ) else cubeWall) ≤ x 0 ∧
      x 0 ≤ (if (0 : Fin 2) = 0 then (cubeWall : ℝ) else top) from ⟨hx.1 0, hx.2 0⟩)
  have hx1 : x 1 ∈ Icc (cubeWall : ℝ) (top : ℝ) := by
    simpa using (show (if (1 : Fin 2) = 0 then (alpha : ℝ) else cubeWall) ≤ x 1 ∧
      x 1 ≤ (if (1 : Fin 2) = 0 then (cubeWall : ℝ) else top) from ⟨hx.1 1, hx.2 1⟩)
  obtain ⟨i, hi⟩ := uniform_interval_closed alpha_lt_cubeWall hM hx0
  obtain ⟨j, hj⟩ := uniform_interval_closed cubeWall_lt_top hM hx1
  exact ⟨(i, j), Box.mem_region.mpr ⟨hi.1, hi.2, hj.1, hj.2⟩⟩

/-- Every box reaching the closed affine gate survives the rational
filter. This includes all boxes touching the wall x+2y=1. -/
theorem mem_selected_of_reaches_gate {M : ℕ} {ij : Fin M × Fin M} {x : Point}
    (hx : x ∈ (meshBox M ij).region) (hgate : x 0 + 2 * x 1 ≤ 1) :
    ij ∈ selected M := by
  obtain ⟨hxl, _, hyl, _⟩ := Box.mem_region.mp hx
  have hreal : ((meshBox M ij).xl : ℝ) + 2 * (meshBox M ij).yl ≤ 1 := by
    linarith only [hxl, hyl, hgate]
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by exact_mod_cast hreal⟩

/-- Actual U8 coverage with neither an assumed cell table nor an assumed
cover theorem. Its strict walls are retained by the closed cell carrier. -/
theorem selected_covers_eighthDomain {M : ℕ} (hM : 0 < M) :
    ∀ x ∈ eighthDomain, ∃ ij ∈ selected M, x ∈ (meshBox M ij).region := by
  intro x hx
  have hx0 := mem_logPrimeBox.mp hx.1 (0 : Fin 2)
  have hx1 := mem_logPrimeBox.mp hx.1 (1 : Fin 2)
  have hr := hx.2
  change x 0 < 1 / 3 ∧ 1 / 3 ≤ x 1 ∧ x 0 + 2 * x 1 < 1 at hr
  have hrect : x ∈ Icc
      (fun i : Fin 2 => if i = 0 then (alpha : ℝ) else (cubeWall : ℝ))
      (fun i : Fin 2 => if i = 0 then (cubeWall : ℝ) else (top : ℝ)) := by
    constructor <;> intro i <;> fin_cases i
    · simpa [alpha] using hx0.1
    · simpa [cubeWall] using hr.2.1
    · simpa [cubeWall] using hr.1.le
    · simpa [top] using hx1.2.le
  obtain ⟨ij, hij⟩ := mesh_rectangle_cover hM hrect
  exact ⟨ij, mem_selected_of_reaches_gate hij hr.2.2.le, hij⟩

/-- Finite rational data only: no integral is stored in the upper sum. -/
def uniformUpper (M : ℕ) : ℚ :=
  ∑ ij ∈ selected M, (meshBox M ij).upper * (meshBox M ij).area

/-- For every positive mesh count, a proved complete rational upper sum
for the actual original negative eighth harmonic term. -/
theorem eighthIntegral_le_uniformUpper (M : ℕ) (hM : 0 < M) :
    currentChenUpsilon8HarmonicIntegral ≤ (uniformUpper M : ℝ) := by
  exact eighthIntegral_le_box_cover (selected M) (meshBox M)
    (fun ij _ => meshBox_valid hM ij) (selected_covers_eighthDomain hM)

/-- A checkable rational endpoint comparison, ready for a future adopted
data instance. No original selected endpoint is asserted here. -/
def endpointCheck (M : ℕ) (q : ℚ) : Bool := decide (uniformUpper M ≤ q)

theorem endpointCheck_sound (M : ℕ) (hM : 0 < M) (q : ℚ)
    (hcheck : endpointCheck M q = true) :
    currentChenUpsilon8HarmonicIntegral ≤ (q : ℝ) := by
  have hq : uniformUpper M ≤ q := of_decide_eq_true hcheck
  exact (eighthIntegral_le_uniformUpper M hM).trans (by exact_mod_cast hq)

end

end ImbalancedChen.P2U8UniformRationalCover
