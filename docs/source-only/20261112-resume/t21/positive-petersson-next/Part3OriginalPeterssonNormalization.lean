import ImbalancedChen.Part3OriginalPeterssonPretrace

namespace ImbalancedChen.Part3.OriginalPeterssonNormalization20261112

noncomputable section
open Complex Matrix
open scoped MatrixGroups UpperHalfPlane ComplexConjugate
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalPeterssonPretrace20261112 NativeHolomorphicFourierNormalization20261102s

def coefficientScale (j m : ℕ) : ℝ :=
  (4*Real.pi)^(j+1)*(Real.sqrt m)^(2*j+1)

theorem raw_eq_scaled_R (N : ℕ) (hN : 0<N) (j : ℕ) (f : Forms N (j+1))
    (g : SL(2,ℤ)) {m : ℕ} (hm : 0<m) :
    raw N hN (j+1) g m f = (coefficientScale j m : ℂ)*frameR N hN (j+1) f g m := by
  let u : ℝ := Real.sqrt m
  have hu : 0<u := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have hu2 : u^2=(m:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hscale : holomorphicScale (j+1) m = ((coefficientScale j m * u : ℝ) : ℂ) := by
    unfold holomorphicScale coefficientScale
    rw [← Complex.ofReal_pow]
    apply congrArg Complex.ofReal
    conv_lhs => rw [← hu2, mul_pow, ← pow_mul]
    change (4*Real.pi)^(j+1)*u^(2*(j+1)) = (4*Real.pi)^(j+1)*u^(2*j+1)*u
    rw [show 2*(j+1)=(2*j+1)+1 by omega, pow_succ]
    ring
  have hC : (coefficientScale j m : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (mul_pos (pow_pos (by positivity) _) (pow_pos hu _)).ne'
  have huC : (u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [frameR, holomorphicR_eq_qExpansion, hscale, Complex.ofReal_mul]
  change _ = _ * ((u : ℂ) * _ / _)
  field_simp [huC,hC,raw]

theorem normalization_factor {j m n : ℕ} (hm : 0<m) (hn : 0<n) :
    (Real.sqrt m / Real.sqrt n)^(2*j+1) * mass (j+1) m *
      (coefficientScale j m * coefficientScale j n) = 4*Real.pi*Real.Gamma (2*(j:ℝ)+1) := by
  let u := Real.sqrt (m:ℝ)
  let v := Real.sqrt (n:ℝ)
  let t := 4*Real.pi
  let d := 2*j+1
  have hu : u≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne'
  have hv : v≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have ht : t≠0 := (by positivity : 0<4*Real.pi).ne'
  have h : t^(j+1)*t^(j+1)=t^d*t := by
    rw [← pow_add, ← pow_succ]; congr 1 <;> dsimp [d] <;> omega
  have h' : (u^2)^d = u^d*u^d := by rw [← pow_mul, ← pow_add, two_mul]
  have hm' : u^2 = (m:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  unfold mass coefficientScale
  rw [show 2*(j+1)-1 = d by dsimp [d]; omega]
  push_cast
  rw [show 2*((j:ℝ)+1)-1=2*(j:ℝ)+1 by ring]
  change (u/v)^d*((1/(t*(m:ℝ)))^d*_) * (t^(j+1)*u^d*(t^(j+1)*v^d)) = t*_
  rw [← hm', div_pow, div_pow, one_pow, mul_pow, h']
  rw [show t^(j+1)*u^d*(t^(j+1)*v^d)=(t^(j+1)*t^(j+1))*(u^d*v^d) by ring, h]
  field_simp [ht,hu,hv]
  <;> ring

/-- The factor 4π follows from the literal vertical integral and (4.7). -/
theorem normalized_P_coefficient (N : ℕ) [NeZero N] (j : ℕ) (g h : SL(2,ℤ))
    {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    (((Real.sqrt m / Real.sqrt n)^(2*j+1) : ℝ) : ℂ) *
      raw N (NeZero.pos N) (j+1) h n (Pvector N (j+1) g m) =
      ((4*Real.pi*Real.Gamma (2*(j:ℝ)+1) : ℝ) : ℂ) *
        ∑ i, conj (frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) g m) *
          frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) h n := by
  rw [coefficient_of_Pvector, ← normalization_factor hm hn]
  simp only [Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [raw_eq_scaled_R N _ j _ g hm, raw_eq_scaled_R N _ j _ h hn, map_mul,
    Complex.conj_ofReal]
  ring

end
end ImbalancedChen.Part3.OriginalPeterssonNormalization20261112
