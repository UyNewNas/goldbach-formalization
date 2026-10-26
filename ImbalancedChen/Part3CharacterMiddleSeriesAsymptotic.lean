import ImbalancedChen.Part3CharacterEisensteinGrowingHeight
import Mathlib.Analysis.Asymptotics.Lemmas

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
For the ORIGINAL q=p character series, the actual native middle chart
sigma10=p has incoming coefficient p^s*chi(-sigma00). The infinite
reindexing is accompanied by genuine absolute convergence on both sides.
This initial analytic statement is for each fixed REAL s>1. The remainder
is proved o(y^s), not postulated, and no continuation or basis assertion
is made. The same proof works for every positive p, hence in particular
at prime-square level including p=2. -/

noncomputable section
open Complex UpperHalfPlane EisensteinSeries Filter Topology Set Matrix
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.CharacterEisensteinRowAction
open ImbalancedChen.Part3.CharacterEisensteinSeries
open ImbalancedChen.Part3.CharacterMiddleCuspGeometry20261026b
open ImbalancedChen.Part3.CharacterMiddlePrimitiveRows20261026b
open ImbalancedChen.Part3.CharacterMiddleZeroFirstPairs20261026b
open ImbalancedChen.Part3.CharacterEisensteinGrowingHeight20261026b

namespace ImbalancedChen.Part3.CharacterMiddleSeriesAsymptotic20261026b

theorem middleTransportWeight_norm_le {p : ℕ} (chi : DirichletCharacter ℂ p)
    (a : ℤ) (v : PrimitivePair) : ‖middleTransportWeight chi a v‖ ≤ 1 :=
  characterWeight_norm_le_one chi (-(v.1 1)) (v.1 0+a*v.1 1)

/-- Absolute summability of the actual transported seed, independent of
any infinite-sum reindexing or cancellation of character weights. -/
theorem middleTransportSeed_norm_summable {p : ℕ}
    (chi : DirichletCharacter ℂ p) (a : ℤ) (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : PrimitivePair =>
      ‖middleTransportWeight chi a v*complexSeed z v s‖) := by
  apply (primitiveSeed_summable s.re hs z).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro v
  rw [norm_mul]
  calc
    _ ≤ ‖complexSeed z v s‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (middleTransportWeight_norm_le chi a v) (norm_nonneg (complexSeed z v s))
    _ = seed s.re z v.1 := by rw [norm_complexSeed, positiveBase_rpow_eq_seed]

/-- The genuine absolutely convergent ORIGINAL series is reindexed by
the actual determinant-one primitive row bijection. -/
theorem original_middle_absolute_reindex (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : PrimitivePair => ‖characterSeed hp chi (sigma • z) v s‖) ∧
    Summable (fun v : PrimitivePair =>
      ‖middleTransportWeight chi (sigma 0 0) v*
        complexSeed (middleAffinePoint p hp sigma z) v s‖) ∧
    characterEisenstein hp chi s (sigma • z) =
      (1/2 : ℂ)*∑' v : PrimitivePair,
        middleTransportWeight chi (sigma 0 0) v*
          complexSeed (middleAffinePoint p hp sigma z) v s := by
  refine ⟨characterSeed_norm_summable hp chi (sigma • z) s hs,
    middleTransportSeed_norm_summable chi (sigma 0 0) _ s hs, ?_⟩
  unfold characterEisenstein
  congr 1
  calc
    _ = ∑' v : PrimitivePair,
        middleTransportWeight chi (sigma 0 0) (middleRowEquiv (sigma 0 0) v)*
          complexSeed (middleAffinePoint p hp sigma z) (middleRowEquiv (sigma 0 0) v) s :=
      tsum_congr (fun v => characterSeed_middle_transport p hp chi sigma hc z v s)
    _ = _ := (middleRowEquiv (sigma 0 0)).tsum_eq _

private theorem weightedKernel_summable (w : PrimitivePair → ℂ)
    (hw : ∀ v, ‖w v‖ ≤ 1) (s : ℝ) (hs : 1 < s) (z : ℍ) :
    Summable (fun v : PrimitivePair => w v*(rowKernel s z v : ℂ)) := by
  apply Summable.of_norm_bounded (rowKernel_summable s hs z)
  intro v
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (rowKernel_nonneg s z v)]
  exact (mul_le_mul_of_nonneg_right (hw v) (rowKernel_nonneg s z v)).trans_eq (one_mul _)

/-- Exact numerator factorization is justified termwise on the actual
real seed and commuted with the topological sum by continuous scalar multiplication. -/
theorem weighted_complexSeed_factor (w : PrimitivePair → ℂ) (s : ℝ) (z : ℍ) :
    (∑' v : PrimitivePair, w v*complexSeed z v (s : ℂ)) =
      (z.im^s : ℂ)*(∑' v : PrimitivePair, w v*(rowKernel s z v : ℂ)) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro v
  rw [complexSeed_ofReal]
  simp only [seed, rowKernel, Complex.ofReal_mul]
  ring

private theorem zeroFirstPlus_ne_minus : zeroFirstPlus ≠ zeroFirstMinus := by
  intro h
  have he := congrArg (fun v : PrimitivePair => v.1 1) h
  norm_num [zeroFirstPlus, zeroFirstMinus] at he

/-- Both primitive zero-first rows are removed explicitly. Everything
else remains in the actual, absolutely convergent, signed remainder. -/
theorem weighted_kernel_sum_split (w : PrimitivePair → ℂ)
    (hw : ∀ v, ‖w v‖ ≤ 1) (s : ℝ) (hs : 1 < s) (z : ℍ) :
    (∑' v : PrimitivePair, w v*(rowKernel s z v : ℂ)) =
      w zeroFirstPlus + w zeroFirstMinus + weightedRemainder w s z := by
  classical
  let f0 : PrimitivePair → ℂ := fun v =>
    if v.1 0 = 0 then w v*(rowKernel s z v : ℂ) else 0
  have h0 : Summable f0 := by
    apply Summable.of_norm_bounded (rowKernel_summable s hs z)
    intro v
    dsimp only [f0]
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (rowKernel_nonneg s z v)]
      exact (mul_le_mul_of_nonneg_right (hw v)
        (rowKernel_nonneg s z v)).trans_eq (one_mul _)
    · simpa using rowKernel_nonneg s z v
  have hfinite : (∑' v : PrimitivePair, f0 v) =
      w zeroFirstPlus + w zeroFirstMinus := by
    rw [tsum_eq_sum (s := {zeroFirstPlus, zeroFirstMinus})]
    · simp [f0, rowKernel, zeroFirstPlus, zeroFirstMinus, zeroFirstPlus_ne_minus]
    · intro v hv
      have hn : v.1 0 ≠ 0 := by
        intro hc
        rcases (primitive_zero_first_iff v).mp hc with rfl | rfl <;> simp at hv
      simp [f0, hn]
  calc
    _ = ∑' v : PrimitivePair,
        (f0 v + if v.1 0 = 0 then 0 else w v*(rowKernel s z v : ℂ)) := by
      apply tsum_congr
      intro v
      dsimp only [f0]
      split_ifs <;> simp
    _ = (∑' v : PrimitivePair, f0 v) + weightedRemainder w s z :=
      h0.tsum_add (weightedRemainder_summable w hw s hs z)
    _ = _ := by rw [hfinite]

/-- Specialization retains the actual chi(-a) in both zero rows. -/
theorem middle_kernel_sum_split {p : ℕ} (chi : DirichletCharacter ℂ p)
    (a : ℤ) (s : ℝ) (hs : 1 < s) (z : ℍ) :
    (∑' v : PrimitivePair, middleTransportWeight chi a v*(rowKernel s z v : ℂ)) =
      2*chi (-a : ZMod p) + weightedRemainder (middleTransportWeight chi a) s z := by
  rw [weighted_kernel_sum_split _ (middleTransportWeight_norm_le chi a) s hs z,
    middleTransportWeight_zeroFirstPlus, middleTransportWeight_zeroFirstMinus]
  ring

/-- A real-positive representative of the requested canonical p^s factor. -/
def middleIncoming {p : ℕ} (chi : DirichletCharacter ℂ p) (a : ℤ) (s : ℝ) : ℂ :=
  ((p : ℝ)^s : ℂ)*chi (-a : ZMod p)

theorem middleIncoming_eq_cpow {p : ℕ} (chi : DirichletCharacter ℂ p)
    (a : ℤ) (s : ℝ) :
    middleIncoming chi a s = (p : ℂ)^(s : ℂ)*chi (-a : ZMod p) := by
  simpa only [middleIncoming, Complex.ofReal_natCast] using
    congrArg (fun t : ℂ => t*chi (-a : ZMod p))
      (Complex.ofReal_cpow (Nat.cast_nonneg p) s)

/-- Exact normalized ORIGINAL series, prior to taking any limit. -/
theorem original_middle_normalized_exact (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (z : ℍ) (s : ℝ) (hs : 1 < s) :
    characterEisenstein hp chi (s : ℂ) (sigma • z)/(z.im^s : ℂ) =
      middleIncoming chi (sigma 0 0) s +
        ((p : ℝ)^s : ℂ)*(1/2 : ℂ)*
          weightedRemainder (middleTransportWeight chi (sigma 0 0)) s
            (middleAffinePoint p hp sigma z) := by
  have hsC : 1 < (s : ℂ).re := hs
  rw [(original_middle_absolute_reindex p hp chi sigma hc z (s : ℂ) hsC).2.2,
    weighted_complexSeed_factor, middle_kernel_sum_split chi _ s hs,
    middleAffinePoint_im, Real.mul_rpow (Nat.cast_nonneg p) z.im_pos.le]
  have hpow : (z.im^s : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos z.im_pos s).ne'
  push_cast
  unfold middleIncoming
  field_simp [hpow]
  ring

/-- True normalized leading limit at the actual width-one middle cusp.
For y≥1, cuspPoint is literally x+i*y; the max only makes it total. -/
theorem original_middle_normalized_tendsto (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (s : ℝ) (hs : 1 < s) (x : ℝ) :
    Tendsto (fun y : ℝ =>
      characterEisenstein hp chi (s : ℂ) (sigma • cuspPoint x y)/(y^s : ℂ))
      atTop (nhds (middleIncoming chi (sigma 0 0) s)) := by
  let z : ℝ → ℍ := fun y => middleAffinePoint p hp sigma (cuspPoint x y)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hx : ∀ y, (z y).re = (p : ℝ)*x+(sigma 1 1 : ℝ) := by
    intro y
    have he := congrArg Complex.re (middleAffinePoint_coe p hp sigma (cuspPoint x y))
    simpa [z, Complex.mul_re] using he
  have hy : ∀ y, 1 ≤ (z y).im := by
    intro y
    rw [show (z y).im = (p : ℝ)*max 1 y by simp [z, middleAffinePoint_im]]
    nlinarith [le_max_left (1 : ℝ) y]
  have hz : Tendsto (fun y => (z y).im) atTop atTop := by
    simpa only [z, middleAffinePoint_im] using
      (cuspPoint_im_tendsto x).const_mul_atTop hpR
  have htail := weightedRemainder_tendsto_zero
    (middleTransportWeight chi (sigma 0 0))
    (middleTransportWeight_norm_le chi (sigma 0 0)) s hs _ z hx hy hz
  have hmain := (htail.const_mul (((p : ℝ)^s : ℂ)*(1/2 : ℂ))).const_add
    (middleIncoming chi (sigma 0 0) s)
  have hnorm : Tendsto (fun y : ℝ =>
      characterEisenstein hp chi (s : ℂ) (sigma • cuspPoint x y)/
        ((cuspPoint x y).im^s : ℂ)) atTop
      (nhds (middleIncoming chi (sigma 0 0) s)) := by
    simpa only [z, original_middle_normalized_exact p hp chi sigma hc _ s hs,
      mul_zero, add_zero] using hmain
  apply hnorm.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  simp only [cuspPoint_im, max_eq_right hy]

/-- Actual error term is o(y^s). In particular its modulus is
little-o of y^Re(s) in this initial REAL s>1 range. -/
theorem original_middle_remainder_isLittleO (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (s : ℝ) (hs : 1 < s) (x : ℝ) :
    (fun y : ℝ => characterEisenstein hp chi (s : ℂ) (sigma • cuspPoint x y) -
      middleIncoming chi (sigma 0 0) s*(y^s : ℂ)) =o[atTop]
        (fun y : ℝ => (y^s : ℂ)) := by
  have hgf : ∀ᶠ y : ℝ in atTop, (y^s : ℂ) = 0 →
      characterEisenstein hp chi (s : ℂ) (sigma • cuspPoint x y) -
        middleIncoming chi (sigma 0 0) s*(y^s : ℂ) = 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hpow : (y^s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (by linarith : 0 < y) s).ne'
    exact fun h => (hpow h).elim
  apply (Asymptotics.isLittleO_iff_tendsto' hgf).mpr
  have ht : Tendsto (fun y : ℝ =>
      characterEisenstein hp chi (s : ℂ) (sigma • cuspPoint x y)/(y^s : ℂ) -
        middleIncoming chi (sigma 0 0) s) atTop (nhds 0) := by
    simpa using (original_middle_normalized_tendsto p hp chi sigma hc s hs x).sub_const
      (middleIncoming chi (sigma 0 0) s)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hpow : (y^s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (by linarith : 0 < y) s).ne'
  simp [sub_div, hpow]

end ImbalancedChen.Part3.CharacterMiddleSeriesAsymptotic20261026b

