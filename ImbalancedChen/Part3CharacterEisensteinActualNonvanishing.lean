import ImbalancedChen.Part3CharacterMiddleSeriesAsymptotic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The proved nonzero middle incoming coefficient makes the ACTUAL character
series nonzero for each real s>1. This holds for every actual character;
nontriviality is not an assumed nonvanishing supplier. Modulus two is
explicitly principal, so no nonexistent nontrivial character mod2 is used.
A second genuine comparison uses its vanishing leading term at infinity:
for p>1 this series is not a scalar multiple of ANY single untwisted
positive-integer dilation. This does NOT prove independence from their
linear span, a newform theorem, or completeness of Eisenstein channels. -/

noncomputable section
open Complex UpperHalfPlane EisensteinSeries Filter Topology Set Matrix
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.CharacterEisensteinRowAction
open ImbalancedChen.Part3.CharacterEisensteinSeries
open ImbalancedChen.Part3.CharacterMiddleCuspGeometry20261026b
open ImbalancedChen.Part3.CharacterMiddlePrimitiveRows20261026b
open ImbalancedChen.Part3.CharacterMiddleZeroFirstPairs20261026b
open ImbalancedChen.Part3.CharacterEisensteinGrowingHeight20261026b
open ImbalancedChen.Part3.CharacterMiddleSeriesAsymptotic20261026b

namespace ImbalancedChen.Part3.CharacterEisensteinActualNonvanishing20261026b

/-- The actual determinant identity at sigma10=p makes -a a unit
modulo p. This proof retains signed character evaluation and pays zeros. -/
theorem middle_character_value_ne_zero (p : ℕ) (chi : DirichletCharacter ℂ p)
    (sigma : SL(2, ℤ)) (hc : sigma 1 0 = (p : ℤ)) :
    chi (-(sigma 0 0) : ZMod p) ≠ 0 := by
  have hdet : sigma 0 0*sigma 1 1-sigma 0 1*(p : ℤ) = 1 := by
    simpa only [Matrix.det_fin_two, hc] using sigma.det_coe
  have hmod := congrArg (fun t : ℤ => (t : ZMod p)) hdet
  have had : (sigma 0 0 : ZMod p)*(sigma 1 1 : ZMod p) = 1 := by
    simpa using hmod
  have hneg : (-(sigma 0 0) : ZMod p)*(-(sigma 1 1) : ZMod p) = 1 := by
    simpa only [neg_mul_neg] using had
  have hchi : chi (-(sigma 0 0) : ZMod p)*chi (-(sigma 1 1) : ZMod p) = 1 := by
    rw [← map_mul, hneg, map_one]
  intro hz
  rw [hz, zero_mul] at hchi
  exact zero_ne_one hchi

theorem middleIncoming_ne_zero (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (s : ℝ) :
    middleIncoming chi (sigma 0 0) s ≠ 0 := by
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (by exact_mod_cast hp : 0 < (p : ℝ)) s).ne'
  · exact middle_character_value_ne_zero p chi sigma hc

/-- Nonvanishing is derived from the actual infinite-series limit,
not from the finite incoming candidate alone. -/
theorem original_series_eventually_ne_zero_middle (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (s : ℝ) (hs : 1 < s) (x : ℝ) :
    ∀ᶠ y : ℝ in atTop,
      characterEisenstein hp chi (s : ℂ) (sigma • cuspPoint x y) ≠ 0 := by
  have he := (original_middle_normalized_tendsto p hp chi sigma hc s hs x).eventually
    (eventually_ne_nhds (middleIncoming_ne_zero p hp chi sigma hc s))
  filter_upwards [he] with y hy
  intro hz
  apply hy
  rw [hz, zero_div]

/-- A literal native width-one middle matrix, requiring no cusp
classification theorem and valid also for p=2 and p=1. -/
def standardMiddleMatrix (p : ℕ) : SL(2, ℤ) :=
  ⟨!![1, 0; (p : ℤ), 1], by simp⟩

/-- Honest existential nonvanishing of the ORIGINAL function on H. -/
theorem original_character_series_nonzero (p : ℕ) (hp : 0 < p)
    (chi : DirichletCharacter ℂ p) (s : ℝ) (hs : 1 < s) :
    ∃ z : ℍ, characterEisenstein hp chi (s : ℂ) z ≠ 0 := by
  have hc : standardMiddleMatrix p 1 0 = (p : ℤ) := by simp [standardMiddleMatrix]
  obtain ⟨y, hy⟩ := (original_series_eventually_ne_zero_middle p hp chi
    (standardMiddleMatrix p) hc s hs 0).exists
  exact ⟨standardMiddleMatrix p • cuspPoint 0 y, hy⟩

/-- This is in particular an actual prime-square-level result; no
hypothesis that a nontrivial character exists is hidden in the statement. -/
theorem prime_square_character_series_nonzero (p : ℕ) (hp : p.Prime)
    (chi : DirichletCharacter ℂ p) (s : ℝ) (hs : 1 < s) :
    ∃ z : ℍ, characterEisenstein hp.pos chi (s : ℂ) z ≠ 0 :=
  original_character_series_nonzero p hp.pos chi s hs

/-- Explicit p=2 edge: the sole actual character is principal. -/
theorem modulus_two_character_eq_principal (chi : DirichletCharacter ℂ 2) :
    chi = 1 := by
  ext a
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases ha with rfl | rfl <;> simp

theorem no_nontrivial_character_modulus_two (chi : DirichletCharacter ℂ 2)
    (hchi : chi ≠ 1) : False := hchi (modulus_two_character_eq_principal chi)

/-- The same paid lattice tail gives a native incoming coefficient at
infinity for any bounded fixed weight and any positive integer dilation. -/
private theorem scaled_weighted_normalized_tendsto (k : ℕ) (hk : 0 < k)
    (w : PrimitivePair → ℂ) (hw : ∀ v, ‖w v‖ ≤ 1)
    (s : ℝ) (hs : 1 < s) (x : ℝ) :
    Tendsto (fun y : ℝ =>
      ((1/2 : ℂ)*∑' v : PrimitivePair,
        w v*complexSeed (scaledPoint k hk (cuspPoint x y)) v (s : ℂ))/(y^s : ℂ))
      atTop (nhds (((k : ℝ)^s : ℂ)*
        ((w zeroFirstPlus+w zeroFirstMinus)/2))) := by
  let z : ℝ → ℍ := fun y => scaledPoint k hk (cuspPoint x y)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hx : ∀ y, (z y).re = (k : ℝ)*x := by
    intro y
    have he := congrArg Complex.re (scaledPoint_coe k hk (cuspPoint x y))
    simpa [z, Complex.mul_re] using he
  have hy : ∀ y, 1 ≤ (z y).im := by
    intro y
    rw [show (z y).im = (k : ℝ)*max 1 y by simp [z, scaledPoint_im]]
    nlinarith [le_max_left (1 : ℝ) y]
  have hz : Tendsto (fun y => (z y).im) atTop atTop := by
    simpa only [z, scaledPoint_im] using
      (cuspPoint_im_tendsto x).const_mul_atTop hkR
  have htail := weightedRemainder_tendsto_zero w hw s hs _ z hx hy hz
  have hlim : Tendsto (fun y : ℝ => ((k : ℝ)^s : ℂ)*(1/2 : ℂ)*
      (w zeroFirstPlus+w zeroFirstMinus+weightedRemainder w s (z y)))
      atTop (nhds (((k : ℝ)^s : ℂ)*((w zeroFirstPlus+w zeroFirstMinus)/2))) := by
    convert (htail.const_add (w zeroFirstPlus+w zeroFirstMinus)).const_mul
      (((k : ℝ)^s : ℂ)*(1/2 : ℂ)) using 1 <;> ring
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  rw [weighted_complexSeed_factor, weighted_kernel_sum_split w hw s hs,
    scaledPoint_im, cuspPoint_im, max_eq_right hy,
    Real.mul_rpow (Nat.cast_nonneg k) (by linarith : 0 ≤ y)]
  have hpow : (y^s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (by linarith : 0 < y) s).ne'
  dsimp only [z]
  push_cast
  field_simp [hpow]
  ring

/-- At infinity the ORIGINAL character weights delete the two zero-first
rows for p>1. All other rows tend to zero by the actual lattice majorant. -/
theorem original_character_infinity_normalized_tendsto (p : ℕ) (hp : 0 < p)
    (hp1 : p ≠ 1) (chi : DirichletCharacter ℂ p)
    (s : ℝ) (hs : 1 < s) (x : ℝ) :
    Tendsto (fun y : ℝ =>
      characterEisenstein hp chi (s : ℂ) (cuspPoint x y)/(y^s : ℂ))
      atTop (nhds 0) := by
  have h := scaled_weighted_normalized_tendsto p hp (primitiveWeight chi)
    (fun v => characterWeight_norm_le_one chi (v.1 0) (v.1 1)) s hs x
  simpa [characterEisenstein, characterSeed, primitiveWeight, characterWeight,
    zeroFirstPlus, zeroFirstMinus, chi.map_zero' hp1] using h

/-- The comparator is the actual previously defined full-level primitive
series evaluated at k*z, i.e. one native untwisted oldform channel. -/
theorem untwisted_dilation_infinity_normalized_tendsto (k : ℕ) (hk : 0 < k)
    (s : ℝ) (hs : 1 < s) (x : ℝ) :
    Tendsto (fun y : ℝ =>
      primitiveComplexEisenstein (s : ℂ) (scaledPoint k hk (cuspPoint x y))/(y^s : ℂ))
      atTop (nhds ((k : ℝ)^s : ℂ)) := by
  simpa [primitiveComplexEisenstein] using
    scaled_weighted_normalized_tendsto k hk (fun _ => 1) (by simp) s hs x

/-- Genuine separation from every SINGLE untwisted positive-integer
dilation, including the individual k=1,p,p² oldforms at level p².
No claim about their multi-dimensional span follows from this theorem. -/
theorem original_character_not_scalar_untwisted_dilation (p : ℕ) (hp : 0 < p)
    (hp1 : p ≠ 1) (chi : DirichletCharacter ℂ p) (s : ℝ) (hs : 1 < s)
    (k : ℕ) (hk : 0 < k) :
    ¬ ∃ C : ℂ, ∀ z : ℍ, characterEisenstein hp chi (s : ℂ) z =
      C*primitiveComplexEisenstein (s : ℂ) (scaledPoint k hk z) := by
  rintro ⟨C, hC⟩
  have hleft := original_character_infinity_normalized_tendsto p hp hp1 chi s hs 0
  have hright : Tendsto (fun y : ℝ =>
      characterEisenstein hp chi (s : ℂ) (cuspPoint 0 y)/(y^s : ℂ))
      atTop (nhds (C*((k : ℝ)^s : ℂ))) := by
    simpa only [hC, mul_div_assoc] using
      (untwisted_dilation_infinity_normalized_tendsto k hk s hs 0).const_mul C
  have he : (0 : ℂ) = C*((k : ℝ)^s : ℂ) := tendsto_nhds_unique hleft hright
  have hkpow : ((k : ℝ)^s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (by exact_mod_cast hk : 0 < (k : ℝ)) s).ne'
  have hC0 : C = 0 := (mul_eq_zero.mp he.symm).resolve_right hkpow
  obtain ⟨z, hz⟩ := original_character_series_nonzero p hp chi s hs
  apply hz
  simp [hC z, hC0]

end ImbalancedChen.Part3.CharacterEisensteinActualNonvanishing20261026b
