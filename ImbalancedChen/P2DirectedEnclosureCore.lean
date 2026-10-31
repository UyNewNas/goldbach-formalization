import ImbalancedChen.Certificates.RationalLogCertificate
import ImbalancedChen.Certificates.PairedFibreIntegral
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Cast.Order

/-! Exact rational enclosure/rounding prefix of P2DirectedLogRounding.
Only the independent Expr convenience syntax remains in the legacy facade.
All moved declaration names, types, bodies and proofs are unchanged. -/
namespace ImbalancedChen.Certificates.P2DirectedLogRounding

open scoped BigOperators

structure Enclosure where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

def Enclosure.Contains (a : Enclosure) (x : ℝ) : Prop :=
  (a.lower : ℝ) ≤ x ∧ x ≤ (a.upper : ℝ)

def Enclosure.point (q : ℚ) : Enclosure := ⟨q, q⟩

def Enclosure.log (c : RationalLogCertificate) : Enclosure :=
  ⟨c.lower, c.upper⟩

def Enclosure.add (a b : Enclosure) : Enclosure :=
  ⟨a.lower + b.lower, a.upper + b.upper⟩

def Enclosure.neg (a : Enclosure) : Enclosure := ⟨-a.upper, -a.lower⟩

def Enclosure.sub (a b : Enclosure) : Enclosure := a.add b.neg

def Enclosure.mul (a b : Enclosure) : Enclosure :=
  ⟨min (min (a.lower * b.lower) (a.lower * b.upper))
      (min (a.upper * b.lower) (a.upper * b.upper)),
    max (max (a.lower * b.lower) (a.lower * b.upper))
      (max (a.upper * b.lower) (a.upper * b.upper))⟩

theorem Enclosure.point_contains (q : ℚ) : (Enclosure.point q).Contains q := by
  exact ⟨le_rfl, le_rfl⟩

theorem Enclosure.log_contains (c : RationalLogCertificate) (hc : c.check = true) :
    (Enclosure.log c).Contains (Real.log (c.argument : ℝ)) := by
  exact c.check_sound hc

theorem Enclosure.add_contains {a b : Enclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x + y) := by
  rcases hx with ⟨hxl, hxu⟩
  rcases hy with ⟨hyl, hyu⟩
  constructor <;> simp only [Enclosure.add, Enclosure.Contains, Rat.cast_add]
  · exact add_le_add hxl hyl
  · exact add_le_add hxu hyu

theorem Enclosure.neg_contains {a : Enclosure} {x : ℝ} (hx : a.Contains x) :
    a.neg.Contains (-x) := by
  rcases hx with ⟨hxl, hxu⟩
  constructor <;> simp only [Enclosure.neg, Enclosure.Contains, Rat.cast_neg]
  · exact neg_le_neg hxu
  · exact neg_le_neg hxl

theorem Enclosure.sub_contains {a b : Enclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (a.sub b).Contains (x - y) := by
  simpa only [Enclosure.sub, sub_eq_add_neg] using
    Enclosure.add_contains hx (Enclosure.neg_contains hy)

private theorem scalar_bounds {l u y : ℝ} (hy : l ≤ y ∧ y ≤ u) (c : ℝ) :
    min (c * l) (c * u) ≤ c * y ∧ c * y ≤ max (c * l) (c * u) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 hc),
      (mul_le_mul_of_nonneg_left hy.2 hc).trans (le_max_right _ _)⟩
  · have hc' : c ≤ 0 := le_of_not_ge hc
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 hc'),
      (mul_le_mul_of_nonpos_left hy.1 hc').trans (le_max_left _ _)⟩

private theorem four_corner_bounds {l u a b x y : ℝ}
    (hx : l ≤ x ∧ x ≤ u) (hy : a ≤ y ∧ y ≤ b) :
    min (min (l * a) (l * b)) (min (u * a) (u * b)) ≤ x * y ∧
      x * y ≤ max (max (l * a) (l * b)) (max (u * a) (u * b)) := by
  have hl := scalar_bounds hy l
  have hu := scalar_bounds hy u
  by_cases hy0 : 0 ≤ y
  · exact ⟨((min_le_left _ _).trans hl.1).trans
        (mul_le_mul_of_nonneg_right hx.1 hy0),
      (mul_le_mul_of_nonneg_right hx.2 hy0).trans
        (hu.2.trans (le_max_right _ _))⟩
  · have hy0' : y ≤ 0 := le_of_not_ge hy0
    exact ⟨((min_le_right _ _).trans hu.1).trans
        (mul_le_mul_of_nonpos_right hx.2 hy0'),
      (mul_le_mul_of_nonpos_right hx.1 hy0').trans
        (hl.2.trans (le_max_left _ _))⟩

/-- Four-corner propagation, valid even when either interval crosses zero. -/
theorem Enclosure.mul_contains {a b : Enclosure} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x * y) := by
  simpa only [Enclosure.Contains, Enclosure.mul, Rat.cast_min, Rat.cast_max,
    Rat.cast_mul] using four_corner_bounds hx hy

/-- The scale is rational; the integer floor is applied to exact rationals. -/
def dyadicScale (bits : ℕ) : ℚ := (2 : ℚ) ^ bits

def roundDown (bits : ℕ) (q : ℚ) : ℚ :=
  (⌊q * dyadicScale bits⌋ : ℚ) / dyadicScale bits

def roundUp (bits : ℕ) (q : ℚ) : ℚ :=
  (⌈q * dyadicScale bits⌉ : ℚ) / dyadicScale bits

theorem dyadicScale_pos (bits : ℕ) : 0 < dyadicScale bits := by
  unfold dyadicScale
  positivity

theorem roundDown_le (bits : ℕ) (q : ℚ) : roundDown bits q ≤ q := by
  apply (div_le_iff₀ (dyadicScale_pos bits)).mpr
  exact Int.floor_le (q * dyadicScale bits)

theorem le_roundUp (bits : ℕ) (q : ℚ) : q ≤ roundUp bits q := by
  apply (le_div_iff₀ (dyadicScale_pos bits)).mpr
  exact Int.le_ceil (q * dyadicScale bits)

/-- A directed rounding step loses strictly less than one ulp, including
for negative rational inputs. -/
theorem roundDown_error (bits : ℕ) (q : ℚ) :
    0 ≤ q - roundDown bits q ∧
      q - roundDown bits q < 1 / dyadicScale bits := by
  constructor
  · exact sub_nonneg.mpr (roundDown_le bits q)
  · have hf := Int.lt_floor_add_one (q * dyadicScale bits)
    have hs := dyadicScale_pos bits
    apply (mul_lt_mul_iff_left₀ hs).mp
    rw [sub_mul]
    dsimp only [roundDown]
    rw [div_mul_cancel₀ _ (ne_of_gt hs), div_mul_cancel₀ _ (ne_of_gt hs)]
    linarith

theorem roundUp_error (bits : ℕ) (q : ℚ) :
    0 ≤ roundUp bits q - q ∧
      roundUp bits q - q < 1 / dyadicScale bits := by
  constructor
  · exact sub_nonneg.mpr (le_roundUp bits q)
  · have hf := Int.ceil_lt_add_one (q * dyadicScale bits)
    have hs := dyadicScale_pos bits
    apply (mul_lt_mul_iff_left₀ hs).mp
    rw [sub_mul]
    dsimp only [roundUp]
    rw [div_mul_cancel₀ _ (ne_of_gt hs), div_mul_cancel₀ _ (ne_of_gt hs)]
    linarith

def Enclosure.round (a : Enclosure) (bits : ℕ) : Enclosure :=
  ⟨roundDown bits a.lower, roundUp bits a.upper⟩

theorem Enclosure.round_contains {a : Enclosure} {x : ℝ}
    (hx : a.Contains x) (bits : ℕ) : (a.round bits).Contains x := by
  have hl : (roundDown bits a.lower : ℝ) ≤ (a.lower : ℝ) := by
    exact_mod_cast roundDown_le bits a.lower
  have hu : (a.upper : ℝ) ≤ (roundUp bits a.upper : ℝ) := by
    exact_mod_cast le_roundUp bits a.upper
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

/-- The extra enclosure width is bounded locally, independently of signs. -/
theorem Enclosure.round_width (a : Enclosure) (bits : ℕ) :
    (a.round bits).upper - (a.round bits).lower <
      a.upper - a.lower + 2 / dyadicScale bits := by
  have hl := (roundDown_error bits a.lower).2
  have hu := (roundUp_error bits a.upper).2
  change roundUp bits a.upper - roundDown bits a.lower < _
  have htwo : (2 : ℚ) / dyadicScale bits =
      1 / dyadicScale bits + 1 / dyadicScale bits := by ring
  rw [htwo]
  linarith

end ImbalancedChen.Certificates.P2DirectedLogRounding
