import ImbalancedChen.Part3PrimitiveRealEisensteinMixedDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

A genuine two-variable Frechet derivative of the literal real primitive
Eisenstein series for s > 1, obtained by differentiating the infinite sum
with the pinned hasFDerivAt_tsum_of_isPreconnected theorem. The seed derivative
is an explicit continuous linear map, whose operator norm is controlled by
the two already computed coordinate derivatives. No coordinatewise-to-Frechet
shortcut is used. Full C2/ContDiff regularity is not asserted in this file.
-/

namespace ImbalancedChen.Part3.PrimitiveRealEisensteinFrechetDerivative

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

/-- The actual real-pair derivative of a single lattice summand. -/
def seedGradient (s c d x y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  firstX s c d x y • ContinuousLinearMap.fst ℝ ℝ ℝ +
    firstY s c d x y • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem seedGradient_apply (s c d x y : ℝ) (h : ℝ × ℝ) :
    seedGradient s c d x y h = firstX s c d x y * h.1 + firstY s c d x y * h.2 := by
  simp [seedGradient]

/-- Operator-norm control, not just coordinatewise derivative control. -/
theorem norm_seedGradient_le (s c d x y : ℝ) :
    ‖seedGradient s c d x y‖ ≤ |firstX s c d x y| + |firstY s c d x y| := by
  simpa [seedGradient, norm_smul, Real.norm_eq_abs] using
    (norm_add_le
      (firstX s c d x y • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (firstY s c d x y • ContinuousLinearMap.snd ℝ ℝ ℝ))

/-- Direct two-variable differentiation of the explicit quadratic seed. -/
theorem coordinateSeed_hasFDerivAt (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => coordinateSeed s c d p.1 p.2)
      (seedGradient s c d x y) (x, y) := by
  have hx : HasFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (x, y) := hasFDerivAt_fst
  have hyv : HasFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) := hasFDerivAt_snd
  have hcx : HasFDerivAt (fun p : ℝ × ℝ => c * p.1 + d)
      (c • ContinuousLinearMap.fst ℝ ℝ ℝ) (x, y) :=
    (hx.const_mul c).add_const d
  have hcy : HasFDerivAt (fun p : ℝ × ℝ => c * p.2)
      (c • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) := hyv.const_mul c
  have hQ : HasFDerivAt (fun p : ℝ × ℝ => Q c d p.1 p.2)
      (Qx c d x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        Qy c y • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) := by
    convert (hcx.pow 2).add (hcy.pow 2) using 1 <;>
      ext h <;> simp [Q, Qx, Qy] <;> ring
  have hq : 0 < Q c d x y := Q_pos hcd hy
  have hp : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ s)
      ((s * y ^ (s - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) :=
    (Real.hasDerivAt_rpow_const (x := y) (p := s) (Or.inl hy.ne'))
      .comp_hasFDerivAt (x, y) hyv
  have hqp : HasFDerivAt (fun p : ℝ × ℝ => Q c d p.1 p.2 ^ (-s))
      (((-s) * Q c d x y ^ (-s - 1)) •
        (Qx c d x • ContinuousLinearMap.fst ℝ ℝ ℝ +
          Qy c y • ContinuousLinearMap.snd ℝ ℝ ℝ)) (x, y) :=
    (Real.hasDerivAt_rpow_const (x := Q c d x y) (p := -s) (Or.inl hq.ne'))
      .comp_hasFDerivAt (x, y) hQ
  convert hp.mul hqp using 1 <;>
    ext h <;> simp [coordinateSeed, seedGradient, firstX, firstY] <;> ring

/-- At positive height the derivative operator has the same lattice decay
as the seed, with only one inverse height factor. -/
theorem norm_seedGradient_le_seed (s c d x y : ℝ) (hs : 1 < s)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    ‖seedGradient s c d x y‖ ≤ 4 * s * coordinateSeed s c d x y / y := by
  calc
    _ ≤ |firstX s c d x y| + |firstY s c d x y| := norm_seedGradient_le s c d x y
    _ ≤ s * coordinateSeed s c d x y / y +
        3 * s * coordinateSeed s c d x y / y :=
      add_le_add (abs_firstX_le s c d x y hs hcd hy)
        (abs_firstY_le s c d x y hs hcd hy)
    _ = _ := by ring

/-- Absolute convergence of the actual continuous-linear-map derivative series. -/
theorem seedGradient_summable (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    Summable (fun v : PrimitivePair => seedGradient s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
  apply Summable.of_norm_bounded
    ((primitive_coordinateSeed_summable s hs x y hy).mul_left (4 * s / y))
  intro v
  calc
    _ ≤ 4 * s * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y :=
      norm_seedGradient_le_seed s _ _ x y hs (primitive_nonzero v) hy
    _ = (4 * s / y) * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by ring

/-- Local uniform operator-norm majorant for the true Frechet derivative. -/
theorem seedGradient_boundedStrip (s : ℝ) (hs : 1 < s)
    (A B Y x y : ℝ) (hB : 0 < B) (hx : |x| ≤ A)
    (hy : B ≤ y) (hY : y ≤ Y) (v : PrimitivePair) :
    ‖seedGradient s (v.1 0 : ℝ) (v.1 1 : ℝ) x y‖ ≤
      (4 * s / B * (Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)))) *
        ‖v.1‖ ^ (-(2 * s)) := by
  have hb := coordinateDerivatives_boundedStrip s hs A B Y x y hB hx hy hY v
  calc
    _ ≤ |firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| +
        |firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| := norm_seedGradient_le s _ _ x y
    _ ≤ (s / B * (Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)))) *
          ‖v.1‖ ^ (-(2 * s)) +
        (3 * s / B * (Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)))) *
          ‖v.1‖ ^ (-(2 * s)) := add_le_add hb.1 hb.2.1
    _ = _ := by ring

/-- Genuine two-variable differentiation under the primitive infinite sum,
using a uniform operator-norm bound on an explicit open rectangle. -/
theorem primitive_tsum_hasFDerivAt (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    HasFDerivAt
      (fun p : ℝ × ℝ => ∑' v : PrimitivePair,
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) p.1 p.2)
      (∑' v : PrimitivePair, seedGradient s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) (x, y) := by
  have hB : 0 < y / 2 := by linarith
  let A : ℝ := |x| + 1
  let C : ℝ := (3 * y / 2) ^ s *
    EisensteinSeries.r ⟨⟨A, y / 2⟩, hB⟩ ^ (-(2 * s))
  let u : PrimitivePair → ℝ := fun v =>
    (4 * s / (y / 2) * C) * ‖v.1‖ ^ (-(2 * s))
  have hu : Summable u := (lattice_summable s hs).mul_left (4 * s / (y / 2) * C)
  have hp : (x, y) ∈ Ioo (x - 1) (x + 1) ×ˢ Ioo (y / 2) (3 * y / 2) := by
    constructor <;> constructor <;> linarith
  refine hasFDerivAt_tsum_of_isPreconnected
    (f := fun (v : PrimitivePair) (p : ℝ × ℝ) =>
      coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) p.1 p.2)
    (f' := fun (v : PrimitivePair) (p : ℝ × ℝ) =>
      seedGradient s (v.1 0 : ℝ) (v.1 1 : ℝ) p.1 p.2)
    (u := u) (s := Ioo (x - 1) (x + 1) ×ˢ Ioo (y / 2) (3 * y / 2))
    hu (isOpen_Ioo.prod isOpen_Ioo) (isPreconnected_Ioo.prod isPreconnected_Ioo)
    (fun v p ht => coordinateSeed_hasFDerivAt s _ _ p.1 p.2 (primitive_nonzero v)
      (hB.trans ht.2.1))
    ?_ hp (primitive_coordinateSeed_summable s hs x y hy) hp
  intro v p ht
  have htA : |p.1| ≤ A := by
    apply abs_le.mpr
    constructor <;> dsimp [A] <;>
      linarith [neg_abs_le x, le_abs_self x, ht.1.1, ht.1.2]
  have hb := seedGradient_boundedStrip s hs A (y / 2) (3 * y / 2)
    p.1 p.2 hB htA ht.2.1.le ht.2.2.le v
  simpa only [u, C] using hb

/-- The normalized actual primitive Eisenstein series has this genuine
two-variable Frechet derivative throughout its positive-height chart. -/
theorem coordinateEisenstein_hasFDerivAt (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => coordinateEisenstein s p.1 p.2)
      ((1 / 2 : ℝ) • ∑' v : PrimitivePair,
        seedGradient s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) (x, y) := by
  exact (primitive_tsum_hasFDerivAt s x y hs hy).const_mul (1 / 2 : ℝ)

/-- Two-variable differentiability on the full positive-height chart. -/
theorem coordinateEisenstein_differentiableOn (s : ℝ) (hs : 1 < s) :
    DifferentiableOn ℝ (fun p : ℝ × ℝ => coordinateEisenstein s p.1 p.2)
      {p : ℝ × ℝ | 0 < p.2} := by
  intro p hp
  have hd := (coordinateEisenstein_hasFDerivAt s p.1 p.2 hs hp).differentiableAt
  exact hd.differentiableWithinAt

end

end ImbalancedChen.Part3.PrimitiveRealEisensteinFrechetDerivative
