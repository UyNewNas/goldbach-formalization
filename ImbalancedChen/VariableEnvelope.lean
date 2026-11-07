import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The literal eight-branch variable envelope

At residue exponent `alpha = 1` and spectral exponent `7/32`, this file
retains all eight branches and every gate in the manuscript's definition.
It proves the six-branch identity on `0 ≤ z ≤ y ≤ x ≤ 25/128`, including
the boundary `z = 0`. This is an algebraic result, not a distribution or
sieve estimate, and makes no claim for perturbed residue exponents.

Reference: manuscript section "A continuous six-branch expression on the
ordered domain", `variable-envelope-simplification.tex`; the starting
functions specialize Lichtman, arXiv:2309.08522v1, (6.2) and (6.4).
-/

namespace ImbalancedChen.VariableEnvelope

noncomputable section

/-- The crossing point of the two active affine branches. -/
def mu : ℝ := 25 / 128

/-- The global upper bound for the simplified level. -/
def cap : ℝ := 153 / 256

def A (t : ℝ) : ℝ := (1 + t) / 2
def C (t : ℝ) : ℝ := 57 / 64 - 3 / 2 * t
def B (t : ℝ) : ℝ := cap - 3 / 8 * t

/-- The original three-way minimum, before removing its middle branch. -/
def v (t : ℝ) : ℝ := min (A t) (min ((32 - 34 * t) / 39) (C t))

/-- The original gate: retain the value at equality, and return zero on failure. -/
def psi (a b : ℝ) : ℝ := if b ≤ a then a else 0

/-- The inner minimum in the original `w` branch. -/
def wInner (_a b c : ℝ) : ℝ :=
  min ((66 - 34 * c) / 107) (min (B c) (1 - 2 * b))

/-- The original gated `w` branch. -/
def w (a b c : ℝ) : ℝ := psi (wInner a b c) (A a)

/-- All eight original branches, with both `w` and both pair gates intact. -/
def original (x y z : ℝ) : ℝ :=
  max (v x) (max (v y) (max (v (x + y)) (max (v (x + y + z))
    (max (w x y z) (max (w x z y)
      (max (psi (v (x + z)) (x + 2 * y + z))
        (psi (v (y + z)) (2 * x + y + z))))))))

/-- The six continuous branches, asserted equal to `original` only on the ordered domain. -/
def six (x y z : ℝ) : ℝ :=
  max (v x) (max (v (x + y)) (max (v (x + y + z))
    (max (B z) (max (v (x + z)) (v (y + z))))))

/-- The closed ordered domain; the manuscript additionally assumes `0 < z`. -/
def Ordered (x y z : ℝ) : Prop := 0 ≤ z ∧ z ≤ y ∧ y ≤ x ∧ x ≤ mu

/-- The middle affine branch is redundant (even for negative inputs). -/
theorem v_eq_min (t : ℝ) : v t = min (A t) (C t) := by
  have h : min (A t) (C t) ≤ (32 - 34 * t) / 39 := by
    by_cases ht : t ≤ mu
    · exact (min_le_left _ _).trans (by dsimp [A, mu] at *; linarith)
    · exact (min_le_right _ _).trans (by dsimp [C, mu] at *; linarith)
  apply le_antisymm
  · exact le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_right _ _))
  · exact le_min (min_le_left _ _) (le_min h (min_le_right _ _))

theorem v_eq_A {t : ℝ} (ht : t ≤ mu) : v t = A t := by
  rw [v_eq_min, min_eq_left]
  dsimp [A, C, mu] at *
  linarith

theorem v_eq_C {t : ℝ} (ht : mu ≤ t) : v t = C t := by
  rw [v_eq_min, min_eq_right]
  dsimp [A, C, mu] at *
  linarith

theorem v_le_cap (t : ℝ) : v t ≤ cap := by
  by_cases ht : t ≤ mu
  · rw [v_eq_A ht]
    dsimp [A, mu, cap] at *
    linarith
  · rw [v_eq_C (le_of_not_ge ht)]
    dsimp [C, mu, cap] at *
    linarith

/-- Both original inner minima reduce to `B` on the required coordinate ranges. -/
theorem wInner_eq_B (a : ℝ) {b c : ℝ} (hb : b ≤ mu) (hc : 0 ≤ c) :
    wInner a b c = B c := by
  have h₁ : B c ≤ (66 - 34 * c) / 107 := by
    dsimp [B, cap]; linarith
  have h₂ : B c ≤ 1 - 2 * b := by
    dsimp [B, cap, mu] at *; linarith
  simp only [wInner, min_eq_left h₂, min_eq_right h₁]

/-- A nonnegative baseline absorbs a failed gate. -/
theorem max_psi_eq {b a t : ℝ} (hb : 0 ≤ b) (hgate : b ≤ a → t ≤ a) :
    max b (psi a t) = max b a := by
  by_cases ht : t ≤ a
  · simp [psi, ht]
  · have hab : a ≤ b := le_of_not_ge (fun h => ht (hgate h))
    simp [psi, ht, max_eq_left hb, max_eq_left hab]

/-- A winning pair branch has a strictly positive uniform gate surplus.
The generalized statement makes both original pair gates immediate instances. -/
theorem pair_gate_margin {x s r : ℝ} (hx : x ≤ mu) (hr : r ≤ x)
    (hwin : v x ≤ v s) : 3 / 256 ≤ v s - (s + 2 * r) := by
  rw [v_eq_A hx] at hwin
  have hs : A x ≤ C s := hwin.trans (by rw [v_eq_min]; exact min_le_right _ _)
  rw [v_eq_min]
  have hA : s + 2 * r + 3 / 256 ≤ A s := by
    dsimp [A, C, mu] at *; linarith
  have hC : s + 2 * r + 3 / 256 ≤ C s := by
    dsimp [A, C, mu] at *; linarith
  linarith [le_min hA hC]

theorem xz_gate_margin {x y z : ℝ} (h : Ordered x y z)
    (hwin : v x ≤ v (x + z)) :
    3 / 256 ≤ v (x + z) - (x + 2 * y + z) := by
  have hm := pair_gate_margin h.2.2.2 h.2.2.1 hwin
  linarith

theorem yz_gate_margin {x y z : ℝ} (h : Ordered x y z)
    (hwin : v x ≤ v (y + z)) :
    3 / 256 ≤ v (y + z) - (2 * x + y + z) := by
  have hm := pair_gate_margin h.2.2.2 (le_refl x) hwin
  linarith

private theorem max_base_max (b a c : ℝ) :
    max b (max a c) = max (max b a) (max b c) := by
  apply le_antisymm <;> simp only [max_le_iff] <;> simp

/-- The original eight branches equal the six ungated branches on the ordered domain.
No branch equality, continuity, or analytic estimate is assumed. -/
theorem original_eq_six {x y z : ℝ} (h : Ordered x y z) :
    original x y z = six x y z := by
  rcases h with ⟨hz, hzy, hyx, hx⟩
  have hy : y ≤ mu := hyx.trans hx
  have hzmu : z ≤ mu := hzy.trans hy
  have hy0 : 0 ≤ y := hz.trans hzy
  have hx0 : 0 ≤ x := hy0.trans hyx
  have hb : 0 ≤ v x := by rw [v_eq_A hx]; dsimp [A]; linarith
  have hvy : v y ≤ v x := by rw [v_eq_A hy, v_eq_A hx]; dsimp [A]; linarith
  have hBy : B y ≤ B z := by dsimp [B]; linarith
  have hw₁ : max (v x) (w x y z) = max (v x) (B z) := by
    rw [w, wInner_eq_B x hy hz]
    exact max_psi_eq hb (by intro hh; simpa only [v_eq_A hx] using hh)
  have hw₂ : max (v x) (w x z y) = max (v x) (B y) := by
    rw [w, wInner_eq_B x hzmu hy0]
    exact max_psi_eq hb (by intro hh; simpa only [v_eq_A hx] using hh)
  have hp₁ : max (v x) (psi (v (x + z)) (x + 2 * y + z)) =
      max (v x) (v (x + z)) := by
    apply max_psi_eq hb
    intro hh
    have hm := xz_gate_margin ⟨hz, hzy, hyx, hx⟩ hh
    linarith
  have hp₂ : max (v x) (psi (v (y + z)) (2 * x + y + z)) =
      max (v x) (v (y + z)) := by
    apply max_psi_eq hb
    intro hh
    have hm := yz_gate_margin ⟨hz, hzy, hyx, hx⟩ hh
    linarith
  have hsplit (a b c d e f g : ℝ) :
      max (v x) (max a (max b (max c (max d (max e (max f g)))))) =
      max (max (v x) a) (max (max (v x) b) (max (max (v x) c)
        (max (max (v x) d) (max (max (v x) e)
          (max (max (v x) f) (max (v x) g)))))) := by
    repeat rw [max_base_max (v x)]
  unfold original
  rw [hsplit, max_eq_left hvy, hw₁, hw₂, hp₁, hp₂]
  unfold six
  have habs : max (B z) (B y) = B z := max_eq_left hBy
  calc
    _ = max (v x) (max (v (x + y)) (max (v (x + y + z))
        (max (max (B z) (B y)) (max (v (x + z)) (v (y + z)))))) := by
          apply le_antisymm <;> simp only [max_le_iff] <;> simp
    _ = _ := by rw [habs]

end

end ImbalancedChen.VariableEnvelope
