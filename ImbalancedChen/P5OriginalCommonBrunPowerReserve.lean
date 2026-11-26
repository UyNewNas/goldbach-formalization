import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- Original distribution-prime-product-completion-20261010, lines 43-44,
-- 329-338 and 389-398. This is the raw POWER-error connection, before
-- any local logarithmic theorem is requested. No PP bound is a premise.
namespace ImbalancedChen.P5Z.OriginalCommonBrunPowerReserve
noncomputable section

def reserve (zeta theta nu : ℝ) : ℝ :=
  min ((1 - 20*zeta - theta)/4)
    (min ((1 - 40*zeta - 3*theta/2)/4) (nu/4))

theorem reserve_pos {zeta theta nu : ℝ}
    (hone : 20*zeta + theta < 1)
    (htwo : 40*zeta + 3*theta/2 < 1) (hnu : 0 < nu) :
    0 < reserve zeta theta nu := by
  unfold reserve
  exact lt_min (by linarith) (lt_min (by linarith) (by linarith))

-- This one choice pays y and y squared in their actual different errors.
-- The factor 4 leaves a strict reserve after support constants are absorbed.
theorem exponent_reserves {zeta theta nu eta : ℝ}
    (htheta : 0 ≤ theta)
    (hone : 20*zeta + theta < 1)
    (htwo : 40*zeta + 3*theta/2 < 1) (hnu : 0 < nu)
    (heta : eta ≤ reserve zeta theta nu) :
    20*zeta + eta + theta ≤ 1 - reserve zeta theta nu ∧
    20*zeta + eta ≤ 1 - reserve zeta theta nu ∧
    40*zeta + 2*eta + 3*theta/2 ≤ 1 - reserve zeta theta nu ∧
    40*zeta + 2*eta ≤ 1 - reserve zeta theta nu ∧
    1 - nu + eta ≤ 1 - reserve zeta theta nu := by
  have hp := reserve_pos hone htwo hnu
  have h1 : reserve zeta theta nu ≤ (1-20*zeta-theta)/4 := min_le_left _ _
  have h2 : reserve zeta theta nu ≤ (1-40*zeta-3*theta/2)/4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h3 : reserve zeta theta nu ≤ nu/4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem mul_power {x A B a b : ℝ} (hx : 0 < x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ x^A) (hB : b ≤ x^B) :
    a*b ≤ x^(A+B) := by
  calc
    a*b ≤ x^A*x^B := mul_le_mul hA hB hb (Real.rpow_nonneg hx.le _)
    _ = x^(A+B) := by rw [Real.rpow_add hx]

private theorem triple_power {x A B C a b c : ℝ} (hx : 0 < x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ x^A) (hB : b ≤ x^B) (hC : c ≤ x^C) :
    a*b*c ≤ x^(A+B+C) := by
  exact mul_power hx (mul_nonneg ha hb) hc (mul_power hx ha hb hA hB) hC

-- In a two-long chart this uses the OTHER long variable's lower bound.
-- It does not bound U+V by the complete scale and lose the power reserve.
private theorem complementary_power {x a b c nu : ℝ} (hx : 0 < x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hscale : a*b*c=x)
    (hc : x^nu ≤ c) : a*b ≤ x^(1-nu) := by
  have heq : x^(1-nu)*x^nu = x := by
    rw [← Real.rpow_add hx]
    have he : (1-nu)+nu = 1 := by ring
    rw [he,Real.rpow_one]
  have hmul : a*b*x^nu ≤ x^(1-nu)*x^nu := by
    rw [heq]
    calc
      a*b*x^nu ≤ a*b*c := mul_le_mul_of_nonneg_left hc (mul_nonneg ha hb)
      _ = x := hscale
  exact le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hx nu)

-- Actual one-long raw E5. The epsilon term is kept separate: its
-- superlogarithmic density gap must never be multiplied by x^o(1).
theorem one_long_raw {x M U y D epsilon zeta theta nu eta : ℝ}
    (hx : 1 ≤ x) (hM0 : 0 ≤ M) (hy0 : 0 ≤ y) (hD0 : 0 ≤ D)
    (hscale : M*U=x) (hM : M ≤ x^(20*zeta))
    (hy : y ≤ x^eta) (hD : D ≤ x^theta) (htheta : 0 ≤ theta)
    (hone : 20*zeta+theta < 1) (htwo : 40*zeta+3*theta/2 < 1)
    (hnu : 0 < nu) (heta : eta ≤ reserve zeta theta nu) :
    M*U*epsilon + M*y + M*y*D ≤
      x*epsilon + 2*x^(1-reserve zeta theta nu) := by
  have hxp : 0 < x := by linarith
  obtain ⟨he1,he2,he3,he4,he5⟩ := exponent_reserves htheta hone htwo hnu heta
  have hmy : M*y ≤ x^(1-reserve zeta theta nu) := by
    exact (mul_power hxp hM0 hy0 hM hy).trans
      (Real.rpow_le_rpow_of_exponent_le hx he2)
  have hmyd : M*y*D ≤ x^(1-reserve zeta theta nu) := by
    exact (triple_power hxp hM0 hy0 hD0 hM hy hD).trans
      (Real.rpow_le_rpow_of_exponent_le hx he1)
  rw [hscale]
  linarith

-- Actual two-long E4, with no intermediate product=a exception and no
-- growing divisor moment. All y factors occur in the power terms below.
theorem two_long_raw {x M U V y D epsilon zeta theta nu eta : ℝ}
    (hx : 1 ≤ x) (hM0 : 0 ≤ M) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hy0 : 0 ≤ y) (hD0 : 0 ≤ D) (hscale : M*U*V=x)
    (hM : M ≤ x^(40*zeta)) (hU : x^nu ≤ U) (hV : x^nu ≤ V)
    (hy : y ≤ x^eta) (hD : D ≤ x^theta) (htheta : 0 ≤ theta)
    (hone : 20*zeta+theta < 1) (htwo : 40*zeta+3*theta/2 < 1)
    (hnu : 0 < nu) (heta : eta ≤ reserve zeta theta nu) :
    M*U*V*epsilon + M*(U+V)*y + M*y^2 + M*y^2*D^(3/2 : ℝ) ≤
      x*epsilon + 4*x^(1-reserve zeta theta nu) := by
  have hxp : 0 < x := by linarith
  obtain ⟨he1,he2,he3,he4,he5⟩ := exponent_reserves htheta hone htwo hnu heta
  have hy2 : y^2 ≤ x^(2*eta) := by
    have hh := mul_power hxp hy0 hy0 hy hy
    have he : eta+eta = 2*eta := by ring
    simpa only [pow_two,he] using hh
  have hD32 : D^(3/2 : ℝ) ≤ x^(3*theta/2) := by
    have hh := Real.rpow_le_rpow hD0 hD (by norm_num : (0 : ℝ) ≤ 3/2)
    have he : theta*(3/2 : ℝ) = 3*theta/2 := by ring
    simpa only [← Real.rpow_mul hxp.le,he] using hh
  have hmy2 : M*y^2 ≤ x^(1-reserve zeta theta nu) := by
    exact (mul_power hxp hM0 (sq_nonneg y) hM hy2).trans
      (Real.rpow_le_rpow_of_exponent_le hx he4)
  have hlead : M*y^2*D^(3/2 : ℝ) ≤ x^(1-reserve zeta theta nu) := by
    exact (triple_power hxp hM0 (sq_nonneg y) (Real.rpow_nonneg hD0 _)
      hM hy2 hD32).trans (Real.rpow_le_rpow_of_exponent_le hx he3)
  have hMU : M*U ≤ x^(1-nu) := complementary_power hxp hM0 hU0 hscale hV
  have hscale' : M*V*U=x := by nlinarith [hscale]
  have hMV : M*V ≤ x^(1-nu) := complementary_power hxp hM0 hV0 hscale' hU
  have hMUy : M*U*y ≤ x^(1-reserve zeta theta nu) := by
    exact (mul_power hxp (mul_nonneg hM0 hU0) hy0 hMU hy).trans
      (Real.rpow_le_rpow_of_exponent_le hx he5)
  have hMVy : M*V*y ≤ x^(1-reserve zeta theta nu) := by
    exact (mul_power hxp (mul_nonneg hM0 hV0) hy0 hMV hy).trans
      (Real.rpow_le_rpow_of_exponent_le hx he5)
  have hcross : M*(U+V)*y ≤ 2*x^(1-reserve zeta theta nu) := by
    nlinarith [hMUy,hMVy]
  rw [hscale]
  linarith

-- A finite family of genuine strict gates has one common positive
-- reserve. This is chosen BEFORE asking for the various local exponents.
-- No family member's discrepancy is a hypothesis of this theorem.
theorem finite_common_reserve {ι : Type*} (s : Finset ι)
    (zeta theta nu : ι → ℝ)
    (hone : ∀ i ∈ s, 20*zeta i+theta i < 1)
    (htwo : ∀ i ∈ s, 40*zeta i+3*theta i/2 < 1)
    (hnu : ∀ i ∈ s, 0 < nu i) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ i ∈ s, delta ≤ reserve (zeta i) (theta i) (nu i) := by
  classical
  revert hone htwo hnu
  induction s using Finset.induction_on with
  | empty =>
    intro hone htwo hnu
    exact ⟨1,by norm_num,by simp⟩
  | @insert i s his ih =>
    intro hone htwo hnu
    obtain ⟨d,hd,hds⟩ := ih
      (fun j hj => hone j (Finset.mem_insert_of_mem hj))
      (fun j hj => htwo j (Finset.mem_insert_of_mem hj))
      (fun j hj => hnu j (Finset.mem_insert_of_mem hj))
    let r := reserve (zeta i) (theta i) (nu i)
    have hr : 0 < r := reserve_pos (hone i (by simp)) (htwo i (by simp)) (hnu i (by simp))
    refine ⟨min d r,lt_min hd hr,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hds j hjs)

end
end ImbalancedChen.P5Z.OriginalCommonBrunPowerReserve
