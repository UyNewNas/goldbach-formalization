import ImbalancedChen.Part3PrimitiveRealEisensteinLaplacian
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

The explicit mixed derivative of the real Eisenstein seed, its locally
summable majorant, and both mixed derivative exchanges for the literal
primitive infinite series. This proves equality of the two actual mixed
coordinate derivatives. It does not identify coordinatewise differentiability
with two-variable Frechet differentiability or assert ContDiff from it.
-/

namespace ImbalancedChen.Part3.PrimitiveRealEisensteinMixedDerivatives

noncomputable section

open Set Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedLaplacian
open ImbalancedChen.Part3.RealEisensteinDerivativeMajorant
open ImbalancedChen.Part3.PrimitiveRealEisensteinFirstDerivatives

private theorem primitive_nonzero (v : PrimitivePair) :
    (v.1 0 : ℝ) ≠ 0 ∨ (v.1 1 : ℝ) ≠ 0 := by
  by_contra h
  push_neg at h
  have hv : v.1 = 0 := by
    ext i
    fin_cases i
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have hg : (v.1 0).gcd (v.1 1) = 1 := v.2.2
  simp [hv] at hg

private theorem lattice_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun v : PrimitivePair => ‖v.1‖ ^ (-(2 * s))) :=
  (EisensteinSeries.summable_one_div_norm_rpow
    (by linarith : (2 : ℝ) < 2 * s)).subtype _

/-- The common mixed derivative in the two coordinate orders. -/
def mixedXY (s c d x y : ℝ) : ℝ :=
  -s ^ 2 * y ^ (s - 1) * Q c d x y ^ (-s - 1) * Qx c d x +
    s * (s + 1) * y ^ s * Q c d x y ^ (-s - 2) * Qx c d x * Qy c y

private theorem q_hasDerivAt_x (c d x y : ℝ) :
    HasDerivAt (fun t : ℝ => Q c d t y) (Qx c d x) x := by
  have h : HasDerivAt (fun t : ℝ => c * t + d) c x := by
    convert ((hasDerivAt_id x).const_mul c).add_const d using 1 <;> ring
  convert (h.pow 2).add_const ((c * y) ^ 2) using 1 <;>
    simp [Q, Qx] <;> ring

private theorem q_hasDerivAt_y (c d x y : ℝ) :
    HasDerivAt (fun t : ℝ => Q c d x t) (Qy c y) y := by
  have h : HasDerivAt (fun t : ℝ => c * t) c y := by
    convert (hasDerivAt_id y).const_mul c using 1 <;> ring
  convert (hasDerivAt_const y ((c * x + d) ^ 2)).add (h.pow 2)
    using 1 <;> simp [Q, Qy] <;> ring

private theorem qpow_hasDerivAt_x (p c d x y : ℝ) (hq : 0 < Q c d x y) :
    HasDerivAt (fun t : ℝ => Q c d t y ^ p)
      (p * Q c d x y ^ (p - 1) * Qx c d x) x := by
  convert (Real.hasDerivAt_rpow_const (x := Q c d x y) (p := p)
    (Or.inl hq.ne')).comp x (q_hasDerivAt_x c d x y) using 1 <;> ring

private theorem qpow_hasDerivAt_y (p c d x y : ℝ) (hq : 0 < Q c d x y) :
    HasDerivAt (fun t : ℝ => Q c d x t ^ p)
      (p * Q c d x y ^ (p - 1) * Qy c y) y := by
  convert (Real.hasDerivAt_rpow_const (x := Q c d x y) (p := p)
    (Or.inl hq.ne')).comp y (q_hasDerivAt_y c d x y) using 1 <;> ring

/-- Vertical derivative of the actual horizontal seed derivative. -/
theorem firstX_hasDerivAt_y (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => firstX s c d x t) (mixedXY s c d x y) y := by
  have hq := Q_pos hcd hy (x := x)
  have hp : HasDerivAt (fun t : ℝ => t ^ s) (s * y ^ (s - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  have hqp : HasDerivAt (fun t : ℝ => Q c d x t ^ (-s - 1))
      ((-s - 1) * Q c d x y ^ (-s - 2) * Qy c y) y := by
    convert qpow_hasDerivAt_y (-s - 1) c d x y hq using 1 <;> ring
  convert (hp.mul hqp).const_mul (-s * Qx c d x) using 1 <;>
    simp [firstX, mixedXY] <;> ring

/-- Horizontal derivative of the actual vertical seed derivative. -/
theorem firstY_hasDerivAt_x (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => firstY s c d t y) (mixedXY s c d x y) x := by
  have hq := Q_pos hcd hy (x := x)
  have hq0 : HasDerivAt (fun t : ℝ => Q c d t y ^ (-s))
      ((-s) * Q c d x y ^ (-s - 1) * Qx c d x) x :=
    qpow_hasDerivAt_x (-s) c d x y hq
  have hq1 : HasDerivAt (fun t : ℝ => Q c d t y ^ (-s - 1))
      ((-s - 1) * Q c d x y ^ (-s - 2) * Qx c d x) x := by
    convert qpow_hasDerivAt_x (-s - 1) c d x y hq using 1 <;> ring
  convert (hq0.const_mul (s * y ^ (s - 1))).sub
    (hq1.const_mul (s * y ^ s * Qy c y)) using 1 <;>
      simp [firstY, mixedXY] <;> ring

private theorem mixedXY_factor (s c d x y : ℝ)
    (hy : 0 < y) (hq : 0 < Q c d x y) :
    mixedXY s c d x y =
      -s ^ 2 * coordinateSeed s c d x y * (Qx c d x / Q c d x y) / y +
        s * (s + 1) * coordinateSeed s c d x y *
          (Qx c d x / Q c d x y) * (Qy c y / Q c d x y) := by
  unfold mixedXY coordinateSeed
  rw [Real.rpow_sub hy s 1, Real.rpow_sub hq (-s) 1,
    Real.rpow_sub hq (-s) 2]
  simp only [Real.rpow_one, Real.rpow_natCast]
  field_simp [hy.ne', hq.ne'] <;> ring

/-- A mixed derivative costs only y^(-2), uniformly in the nonzero pair. -/
theorem abs_mixedXY_le (s c d x y : ℝ) (hs : 1 < s)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    |mixedXY s c d x y| ≤
      (3 * s ^ 2 + 2 * s) * coordinateSeed s c d x y / y ^ 2 := by
  have hq := Q_pos hcd hy (x := x)
  have hf : 0 ≤ coordinateSeed s c d x y := by unfold coordinateSeed; positivity
  have ha : |Qx c d x / Q c d x y| ≤ 1 / y := by
    simpa [abs_div, abs_of_pos hq] using Qx_ratio_le c d x y hy hq
  have hb : |Qy c y / Q c d x y| ≤ 2 / y := by
    simpa [abs_div, abs_of_pos hq] using Qy_ratio_le c d x y hy hq
  have hfirst :
      |-s ^ 2 * coordinateSeed s c d x y * (Qx c d x / Q c d x y) / y| ≤
        s ^ 2 * coordinateSeed s c d x y / y ^ 2 := by
    simp only [abs_div, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg s),
      abs_of_nonneg hf, abs_of_pos hy]
    calc
      _ ≤ s ^ 2 * coordinateSeed s c d x y * (1 / y) / y := by gcongr
      _ = _ := by ring
  have hc : 0 ≤ s * (s + 1) * coordinateSeed s c d x y := by positivity
  have hsecond :
      |s * (s + 1) * coordinateSeed s c d x y *
        (Qx c d x / Q c d x y) * (Qy c y / Q c d x y)| ≤
        2 * s * (s + 1) * coordinateSeed s c d x y / y ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc]
    calc
      _ ≤ s * (s + 1) * coordinateSeed s c d x y * (1 / y) * (2 / y) := by
        gcongr
      _ = _ := by ring
  rw [mixedXY_factor s c d x y hy hq]
  calc
    _ ≤ |-s ^ 2 * coordinateSeed s c d x y * (Qx c d x / Q c d x y) / y| +
        |s * (s + 1) * coordinateSeed s c d x y *
          (Qx c d x / Q c d x y) * (Qy c y / Q c d x y)| := abs_add _ _
    _ ≤ s ^ 2 * coordinateSeed s c d x y / y ^ 2 +
        2 * s * (s + 1) * coordinateSeed s c d x y / y ^ 2 :=
      add_le_add hfirst hsecond
    _ = _ := by ring

/-- Absolute convergence of the literal mixed derivative series. -/
theorem mixedXY_summable (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    Summable (fun v : PrimitivePair => mixedXY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
  apply Summable.of_norm_bounded
    ((primitive_coordinateSeed_summable s hs x y hy).mul_left
      ((3 * s ^ 2 + 2 * s) / y ^ 2))
  intro v
  calc
    ‖mixedXY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y‖ =
        |mixedXY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| := Real.norm_eq_abs _
    _ ≤ (3 * s ^ 2 + 2 * s) * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y /
        y ^ 2 := abs_mixedXY_le s _ _ x y hs (primitive_nonzero v) hy
    _ = ((3 * s ^ 2 + 2 * s) / y ^ 2) *
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by ring

/-- Explicit summable lattice majorant for the mixed derivative on a strip. -/
theorem mixedXY_boundedStrip (s : ℝ) (hs : 1 < s)
    (A B Y x y : ℝ) (hB : 0 < B) (hx : |x| ≤ A)
    (hy : B ≤ y) (hY : y ≤ Y) (v : PrimitivePair) :
    |mixedXY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| ≤
      ((3 * s ^ 2 + 2 * s) / B ^ 2 *
        (Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)))) *
        ‖v.1‖ ^ (-(2 * s)) := by
  have hypos : 0 < y := hB.trans_le hy
  have hseed := coordinateSeed_boundedStrip s hs A B Y x y hB hx hy hY v.1
  calc
    _ ≤ (3 * s ^ 2 + 2 * s) *
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y ^ 2 :=
      abs_mixedXY_le s _ _ x y hs (primitive_nonzero v) hypos
    _ ≤ (3 * s ^ 2 + 2 * s) *
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / B ^ 2 := by gcongr
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hseed
        (show 0 ≤ (3 * s ^ 2 + 2 * s) / B ^ 2 by positivity)
      nlinarith

/-- Vertical differentiation of the actual horizontal first-derivative sum. -/
theorem primitive_firstX_tsum_hasDerivAt_y (s x y : ℝ)
    (hs : 1 < s) (hy : 0 < y) :
    HasDerivAt
      (fun t : ℝ => ∑' v : PrimitivePair, firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x t)
      (∑' v : PrimitivePair, mixedXY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) y := by
  have hB : 0 < y / 2 := by linarith
  let C : ℝ := (3 * y / 2) ^ s *
    EisensteinSeries.r ⟨⟨|x|, y / 2⟩, hB⟩ ^ (-(2 * s))
  let u : PrimitivePair → ℝ := fun v =>
    ((3 * s ^ 2 + 2 * s) / (y / 2) ^ 2 * C) * ‖v.1‖ ^ (-(2 * s))
  have hu : Summable u :=
    (lattice_summable s hs).mul_left ((3 * s ^ 2 + 2 * s) / (y / 2) ^ 2 * C)
  have hyI : y ∈ Ioo (y / 2) (3 * y / 2) := by constructor <;> linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := u)
    (t := Ioo (y / 2) (3 * y / 2)) hu isOpen_Ioo isPreconnected_Ioo
    (fun v t ht => firstX_hasDerivAt_y s _ _ x t (primitive_nonzero v)
      (hB.trans ht.1))
    ?_ hyI (firstX_summable s x y hs hy) hyI
  intro v t ht
  have hb := mixedXY_boundedStrip s hs |x| (y / 2) (3 * y / 2)
    x t hB le_rfl ht.1.le ht.2.le v
  simpa only [Real.norm_eq_abs, u, C] using hb

/-- Horizontal differentiation of the actual vertical first-derivative sum. -/
theorem primitive_firstY_tsum_hasDerivAt_x (s x y : ℝ)
    (hs : 1 < s) (hy : 0 < y) :
    HasDerivAt
      (fun t : ℝ => ∑' v : PrimitivePair, firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) t y)
      (∑' v : PrimitivePair, mixedXY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) x := by
  let A : ℝ := |x| + 1
  let C : ℝ := y ^ s * EisensteinSeries.r ⟨⟨A, y⟩, hy⟩ ^ (-(2 * s))
  let u : PrimitivePair → ℝ := fun v =>
    ((3 * s ^ 2 + 2 * s) / y ^ 2 * C) * ‖v.1‖ ^ (-(2 * s))
  have hu : Summable u :=
    (lattice_summable s hs).mul_left ((3 * s ^ 2 + 2 * s) / y ^ 2 * C)
  have hx : x ∈ Ioo (x - 1) (x + 1) := by constructor <;> linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := u)
    (t := Ioo (x - 1) (x + 1)) hu isOpen_Ioo isPreconnected_Ioo
    (fun v t ht => firstY_hasDerivAt_x s _ _ t y (primitive_nonzero v) hy)
    ?_ hx (firstY_summable s x y hs hy) hx
  intro v t ht
  have htA : |t| ≤ A := by
    apply abs_le.mpr
    constructor <;> dsimp [A] <;>
      linarith [neg_abs_le x, le_abs_self x, ht.1, ht.2]
  have hb := mixedXY_boundedStrip s hs A y y t y hy htA le_rfl le_rfl v
  simpa only [Real.norm_eq_abs, u, C] using hb

/-- The actual mixed coordinate derivative in the order horizontal, vertical. -/
theorem coordinateEisenstein_mixed_xy (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun r : ℝ => coordinateEisenstein s r t) x) y =
      (1 / 2 : ℝ) * ∑' v : PrimitivePair,
        mixedXY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by
  have hevent : (fun t : ℝ => deriv (fun r : ℝ => coordinateEisenstein s r t) x)
      =ᶠ[𝓝 y] (fun t => (1 / 2 : ℝ) * ∑' v : PrimitivePair,
        firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (coordinateEisenstein_hasDerivAt_x s x t hs ht).deriv
  have hsum := (primitive_firstX_tsum_hasDerivAt_y s x y hs hy).const_mul (1 / 2 : ℝ)
  exact (hsum.congr_of_eventuallyEq hevent.symm).deriv

/-- The actual mixed coordinate derivative in the order vertical, horizontal. -/
theorem coordinateEisenstein_mixed_yx (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun r : ℝ => coordinateEisenstein s t r) y) x =
      (1 / 2 : ℝ) * ∑' v : PrimitivePair,
        mixedXY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by
  have hfirst : (fun t : ℝ => deriv (fun r : ℝ => coordinateEisenstein s t r) y) =
      (fun t => (1 / 2 : ℝ) * ∑' v : PrimitivePair,
        firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) t y) :=
    funext fun t => (coordinateEisenstein_hasDerivAt_y s t y hs hy).deriv
  rw [hfirst]
  exact ((primitive_firstY_tsum_hasDerivAt_x s x y hs hy).const_mul (1 / 2 : ℝ)).deriv

/-- Equality of the two genuine mixed coordinate derivatives of the literal
primitive infinite Eisenstein series. This uses the proved exchanges above. -/
theorem coordinateEisenstein_mixed_comm (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun r : ℝ => coordinateEisenstein s r t) x) y =
      deriv (fun t : ℝ => deriv (fun r : ℝ => coordinateEisenstein s t r) y) x := by
  rw [coordinateEisenstein_mixed_xy s x y hs hy,
    coordinateEisenstein_mixed_yx s x y hs hy]

end

end ImbalancedChen.Part3.PrimitiveRealEisensteinMixedDerivatives
