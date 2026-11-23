import ImbalancedChen.P4BSmoothGateUpperStep
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
Positive smooth outer approximation to the ordered convolution-prefix rectangle.
The lower edge of each original window is closed and the upper edge is open.
The two exterior collars have the same multiplicative ratio, including when
the original endpoints or the integer labels coincide in different slots.
-/
namespace ImbalancedChen.P2WuJointWindowProfile

noncomputable section
open Finset P4B
open scoped BigOperators Classical

def lowerBase (L w : ℝ) := L / (1 + w)

theorem lowerBase_pos {L w : ℝ} (hL : 0 < L) (hw : 0 < w) :
    0 < lowerBase L w :=
  div_pos hL (by linarith)

theorem lowerBase_mul {L w : ℝ} (hw : 0 < w) :
    lowerBase L w * (1 + w) = L :=
  div_mul_cancel₀ L (by linarith : (1 : ℝ) + w ≠ 0)

def windowFactor (L V w x : ℝ) : ℝ :=
  smoothGateUpperStep (lowerBase L w * w) (x - L) *
    smoothGateUpperStep (V * w) (V - x)

def windowCollar (L V w x : ℝ) : Prop :=
  (lowerBase L w < x ∧ x < L) ∨ (V ≤ x ∧ x < V * (1 + w))

theorem windowFactor_bounds (L V w x : ℝ) :
    0 ≤ windowFactor L V w x ∧ windowFactor L V w x ≤ 1 := by
  have hlo := smoothGateUpperStep_bounds (lowerBase L w * w) (x - L)
  have hhi := smoothGateUpperStep_bounds (V * w) (V - x)
  exact ⟨mul_nonneg hlo.1 hhi.1, (mul_le_mul_of_nonneg_right hlo.2 hhi.1).trans
    (by simpa only [one_mul] using hhi.2)⟩

theorem windowFactor_one {L V w x : ℝ} (hL : 0 < L) (hV : 0 < V) (hw : 0 < w)
    (hlo : L ≤ x) (hhi : x ≤ V) : windowFactor L V w x = 1 := by
  rw [windowFactor, smoothGateUpperStep_eq_one (mul_pos (lowerBase_pos hL hw) hw)
    (sub_nonneg.mpr hlo), smoothGateUpperStep_eq_one (mul_pos hV hw) (sub_nonneg.mpr hhi),
    one_mul]

theorem windowFactor_nonzero_iff {L V w x : ℝ} (hL : 0 < L) (hV : 0 < V) (hw : 0 < w) :
    windowFactor L V w x ≠ 0 ↔ lowerBase L w < x ∧ x < V * (1 + w) := by
  have hbase := lowerBase_mul (L := L) hw
  rw [windowFactor, mul_ne_zero_iff]
  constructor
  · rintro ⟨hl, hu⟩
    have h₁ := smoothGateUpperStep_nonzero_support (mul_pos (lowerBase_pos hL hw) hw) hl
    have h₂ := smoothGateUpperStep_nonzero_support (mul_pos hV hw) hu
    constructor <;> nlinarith only [hbase, h₁, h₂]
  · rintro ⟨hl, hu⟩
    constructor
    · intro hz
      have h := (smoothGateUpperStep_eq_zero_iff (mul_pos (lowerBase_pos hL hw) hw)).mp hz
      nlinarith only [hbase, hl, h]
    · intro hz
      have h := (smoothGateUpperStep_eq_zero_iff (mul_pos hV hw)).mp hz
      nlinarith only [hu, h]

/-- All prefix windows are sampled on one physical word; the slot map is
the original prefix inclusion when used on the Wu family. -/
def profile {i r : ℕ} (L V : Fin i → ℝ) (w : ℝ) (slot : Fin i → Fin r)
    (x : Fin r → ℝ) : ℝ :=
  ∏ j, windowFactor (L j) (V j) w (x (slot j))

theorem profile_smooth {i r : ℕ} (L V : Fin i → ℝ) (w : ℝ)
    (slot : Fin i → Fin r) {n : ℕ∞} : ContDiff ℝ n (profile L V w slot) := by
  unfold profile
  apply contDiff_prod
  intro j _
  have hx : ContDiff ℝ n (fun x : Fin r → ℝ => x (slot j)) := contDiff_apply ℝ ℝ (slot j)
  exact ((contDiff_smoothGateUpperStep (lowerBase (L j) w * w)).comp
    (hx.sub contDiff_const)).mul
    ((contDiff_smoothGateUpperStep (V j * w)).comp (contDiff_const.sub hx))

theorem profile_bounds {i r : ℕ} (L V : Fin i → ℝ) (w : ℝ) (slot : Fin i → Fin r)
    (x : Fin r → ℝ) : 0 ≤ profile L V w slot x ∧ profile L V w slot x ≤ 1 := by
  unfold profile
  exact ⟨prod_nonneg (fun j _ => (windowFactor_bounds _ _ _ _).1),
    prod_le_one (fun j _ => (windowFactor_bounds _ _ _ _).1)
      (fun j _ => (windowFactor_bounds _ _ _ _).2)⟩

theorem profile_one {i r : ℕ} {L V : Fin i → ℝ} {w : ℝ} {slot : Fin i → Fin r}
    {x : Fin r → ℝ} (hL : ∀ j, 0 < L j) (hV : ∀ j, 0 < V j) (hw : 0 < w)
    (hin : ∀ j, L j ≤ x (slot j) ∧ x (slot j) ≤ V j) : profile L V w slot x = 1 :=
  prod_eq_one (fun j _ => windowFactor_one (hL j) (hV j) hw (hin j).1 (hin j).2)

theorem profile_nonzero_iff {i r : ℕ} {L V : Fin i → ℝ} {w : ℝ} {slot : Fin i → Fin r}
    {x : Fin r → ℝ} (hL : ∀ j, 0 < L j) (hV : ∀ j, 0 < V j) (hw : 0 < w) :
    profile L V w slot x ≠ 0 ↔
      ∀ j, lowerBase (L j) w < x (slot j) ∧ x (slot j) < V j * (1 + w) := by
  constructor
  · intro hn j
    exact (windowFactor_nonzero_iff (hL j) (hV j) hw).mp
      ((prod_ne_zero_iff.mp hn) j (mem_univ j))
  · intro h
    exact prod_ne_zero_iff.mpr (fun j _ => (windowFactor_nonzero_iff (hL j) (hV j) hw).mpr (h j))

theorem outside_nonzero_collar {i r : ℕ} {L V : Fin i → ℝ} {w : ℝ}
    {slot : Fin i → Fin r} {x : Fin r → ℝ}
    (hL : ∀ j, 0 < L j) (hV : ∀ j, 0 < V j) (hw : 0 < w)
    (hout : ¬ ∀ j, L j ≤ x (slot j) ∧ x (slot j) < V j)
    (hn : profile L V w slot x ≠ 0) : ∃ j, windowCollar (L j) (V j) w (x (slot j)) := by
  classical
  have hwide := (profile_nonzero_iff hL hV hw).mp hn
  by_contra h
  apply hout
  intro j
  have hj : ¬ windowCollar (L j) (V j) w (x (slot j)) := fun hc => h ⟨j, hc⟩
  exact ⟨le_of_not_gt (fun hlow => hj (Or.inl ⟨(hwide j).1, hlow⟩)),
    lt_of_not_ge (fun hupp => hj (Or.inr ⟨hupp, (hwide j).2⟩))⟩

/-- Outside the union of the `2*i` actual exterior collars, the common smooth
profile is exactly the sharp half-open rectangle, including the empty prefix. -/
theorem profile_eq_indicator_off_collar {i r : ℕ} {L V : Fin i → ℝ} {w : ℝ}
    {slot : Fin i → Fin r} {x : Fin r → ℝ}
    (hL : ∀ j, 0 < L j) (hV : ∀ j, 0 < V j) (hw : 0 < w)
    (hoff : ∀ j, ¬ windowCollar (L j) (V j) w (x (slot j))) :
    profile L V w slot x =
      (if ∀ j, L j ≤ x (slot j) ∧ x (slot j) < V j then 1 else 0) := by
  classical
  split_ifs with hin
  · exact profile_one hL hV hw (fun j => ⟨(hin j).1, (hin j).2.le⟩)
  · by_contra hn
    obtain ⟨j, hj⟩ := outside_nonzero_collar hL hV hw hin hn
    exact hoff j hj

end
end ImbalancedChen.P2WuJointWindowProfile
