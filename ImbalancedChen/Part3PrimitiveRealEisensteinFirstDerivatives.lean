import ImbalancedChen.Part3RealEisensteinDerivativeMajorant
import ImbalancedChen.Part3PrimitiveRealEisensteinAutomorphy
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

Actual differentiation under the primitive-pair Eisenstein sum, for real s > 1.
The horizontal and vertical derivatives are the literal sums of firstX and
firstY. Their summable local bounds come from the preceding explicit seed
calculation, and the exchange uses the pinned Mathlib theorem
hasDerivAt_tsum_of_isPreconnected. No derivative or eigenrelation for the
infinite series is supplied as an assumption. Second derivatives and the full
series Laplace equation remain separate work.
-/

namespace ImbalancedChen.Part3.PrimitiveRealEisensteinFirstDerivatives

noncomputable section

open Set Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.RealEisensteinSeedLaplacian
open ImbalancedChen.Part3.RealEisensteinDerivativeMajorant
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy

abbrev PrimitivePair := EisensteinSeries.gammaSet 1 1 0

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

/-- A real chart extension of the classical primitive series, with its
usual factor one half. On positive heights it is the actual series. -/
def coordinateEisenstein (s x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' v : PrimitivePair,
    coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y

/-- The chart extension agrees exactly with the previously constructed
automorphic primitive Eisenstein series. -/
theorem coordinateEisenstein_eq_actual (s : ℝ) (z : UpperHalfPlane) :
    coordinateEisenstein s z.re z.im = primitiveEisenstein s z := by
  unfold coordinateEisenstein primitiveEisenstein
  congr 1
  apply tsum_congr
  intro v
  exact coordinateSeed_eq_seed s z v.1

/-- Absolute convergence of the horizontal derivative series at every
positive height. -/
theorem firstX_summable (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    Summable (fun v : PrimitivePair =>
      firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
  apply Summable.of_norm_bounded
    ((primitive_coordinateSeed_summable s hs x y hy).mul_left (s / y))
  intro v
  calc
    ‖firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y‖ =
        |firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| := Real.norm_eq_abs _
    _ ≤ s * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y :=
      abs_firstX_le s _ _ x y hs (primitive_nonzero v) hy
    _ = (s / y) * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by ring

/-- Absolute convergence of the vertical derivative series at every
positive height. -/
theorem firstY_summable (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    Summable (fun v : PrimitivePair =>
      firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
  apply Summable.of_norm_bounded
    ((primitive_coordinateSeed_summable s hs x y hy).mul_left (3 * s / y))
  intro v
  calc
    ‖firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y‖ =
        |firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| := Real.norm_eq_abs _
    _ ≤ 3 * s * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y :=
      abs_firstY_le s _ _ x y hs (primitive_nonzero v) hy
    _ = (3 * s / y) * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by ring

/-- The first horizontal derivative of the literal primitive seed sum.
The convergence and derivative bounds are proved, rather than assumed. -/
theorem primitive_tsum_hasDerivAt_x (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    HasDerivAt
      (fun t : ℝ => ∑' v : PrimitivePair,
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) t y)
      (∑' v : PrimitivePair, firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) x := by
  let A : ℝ := |x| + 1
  let C : ℝ := y ^ s * EisensteinSeries.r ⟨⟨A, y⟩, hy⟩ ^ (-(2 * s))
  let u : PrimitivePair → ℝ := fun v =>
    (s / y * C) * ‖v.1‖ ^ (-(2 * s))
  have hu : Summable u := (lattice_summable s hs).mul_left (s / y * C)
  have hx : x ∈ Ioo (x - 1) (x + 1) := by constructor <;> linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := u)
    (t := Ioo (x - 1) (x + 1)) hu isOpen_Ioo isPreconnected_Ioo
    (fun v t ht => coordinateSeed_hasDerivAt_x s _ _ t y (primitive_nonzero v) hy)
    ?_ hx (primitive_coordinateSeed_summable s hs x y hy) hx
  intro v t ht
  have htA : |t| ≤ A := by
    apply abs_le.mpr
    constructor <;> dsimp [A] <;>
      linarith [neg_abs_le x, le_abs_self x, ht.1, ht.2]
  have hb := (coordinateDerivatives_boundedStrip s hs A y y t y hy
    htA le_rfl le_rfl v).1
  simpa only [Real.norm_eq_abs, u, C] using hb

/-- The first vertical derivative of the literal primitive seed sum.
The local interval has lower height y/2 and upper height 3y/2. -/
theorem primitive_tsum_hasDerivAt_y (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    HasDerivAt
      (fun t : ℝ => ∑' v : PrimitivePair,
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x t)
      (∑' v : PrimitivePair, firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) y := by
  have hB : 0 < y / 2 := by linarith
  let C : ℝ := (3 * y / 2) ^ s *
    EisensteinSeries.r ⟨⟨|x|, y / 2⟩, hB⟩ ^ (-(2 * s))
  let u : PrimitivePair → ℝ := fun v =>
    (3 * s / (y / 2) * C) * ‖v.1‖ ^ (-(2 * s))
  have hu : Summable u :=
    (lattice_summable s hs).mul_left (3 * s / (y / 2) * C)
  have hyI : y ∈ Ioo (y / 2) (3 * y / 2) := by constructor <;> linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := u)
    (t := Ioo (y / 2) (3 * y / 2)) hu isOpen_Ioo isPreconnected_Ioo
    (fun v t ht => coordinateSeed_hasDerivAt_y s _ _ x t (primitive_nonzero v)
      (hB.trans ht.1))
    ?_ hyI (primitive_coordinateSeed_summable s hs x y hy) hyI
  intro v t ht
  have hb := (coordinateDerivatives_boundedStrip s hs |x| (y / 2)
    (3 * y / 2) x t hB le_rfl ht.1.le ht.2.le v).2.1
  simpa only [Real.norm_eq_abs, u, C] using hb

/-- Actual first horizontal derivative, including the classical normalization. -/
theorem coordinateEisenstein_hasDerivAt_x (s x y : ℝ)
    (hs : 1 < s) (hy : 0 < y) :
    HasDerivAt (fun t => coordinateEisenstein s t y)
      ((1 / 2 : ℝ) *
        ∑' v : PrimitivePair, firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) x := by
  exact (primitive_tsum_hasDerivAt_x s x y hs hy).const_mul (1 / 2 : ℝ)

/-- Actual first vertical derivative, including the classical normalization. -/
theorem coordinateEisenstein_hasDerivAt_y (s x y : ℝ)
    (hs : 1 < s) (hy : 0 < y) :
    HasDerivAt (fun t => coordinateEisenstein s x t)
      ((1 / 2 : ℝ) *
        ∑' v : PrimitivePair, firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) y := by
  exact (primitive_tsum_hasDerivAt_y s x y hs hy).const_mul (1 / 2 : ℝ)

/-- A derivative theorem directly on the actual upper-half-plane series
along its complete horizontal line. -/
theorem actualEisenstein_horizontal_hasDerivAt (s x y : ℝ)
    (hs : 1 < s) (hy : 0 < y) :
    HasDerivAt (fun t => primitiveEisenstein s (point t y hy))
      ((1 / 2 : ℝ) *
        ∑' v : PrimitivePair, firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) x := by
  have heq : (fun t => primitiveEisenstein s (point t y hy)) =
      (fun t => coordinateEisenstein s t y) := by
    funext t
    simpa using (coordinateEisenstein_eq_actual s (point t y hy)).symm
  rw [heq]
  exact coordinateEisenstein_hasDerivAt_x s x y hs hy

end

end ImbalancedChen.Part3.PrimitiveRealEisensteinFirstDerivatives
