import ImbalancedChen.Part3ActualYoungFormalClass

/-! Both directions of the true physical dilation change on the critical
line, and the inverse-Gram projected kernel for the physical original
functions with first factor conjugated. -/
namespace ImbalancedChen.Part3.ActualYoungCriticalProjection20261110

noncomputable section
attribute [local instance] Classical.propDecidable
open Complex Matrix UpperHalfPlane Set
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualYoungFormalClass20261110 ActualYoungCriticalCusps20261110
open ActualYoungCriticalD20261110 ActualCriticalCuspEvaluation20261110
open ActualYoungDilationInverse20261110 ActualYoungCuspCoefficients20261110
open ActualCuspDenominatorClasses20261110 Gamma0DegeneracyMapSourceOnly

local instance bandNe (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩

def dilationCoefficient {q L : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (j b : Div L) : ℂ :=
  (kernelMatrix χ s L).adjugate j b / ((kernelMatrix χ s L).det*levelFactor (q^2*L) (q*j.1) s)

def dilationFunction {q L : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hL : 0 < L)
    (b : Div L) (s : ℂ) (z : ℍ) : ℂ :=
  ordinary χ s (degeneracyDiagonal (dilation hL b) (dilation hL b).pos • z)

theorem D_as_dilations {q L : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hL : 0 < L)
    (j : Div L) (s : ℂ) (z : ℍ) :
    criticalD χ hL j s z = ∑ b : Div L,dilationCoefficient χ s j b*dilationFunction χ hL b s z := by
  classical
  rw [criticalD,Matrix.cramer_eq_adjugate_mulVec]
  change (∑ b : Div L, (kernelMatrix χ s L).adjugate j b*dilationFunction χ hL b s z)/_ = _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  unfold dilationCoefficient
  ring

/-- This forward relation is a direct inversion on the critical
functions themselves, including all dilations and the central parameter. -/
theorem dilations_as_D {q L : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hL : 0 < L)
    (b : Div L) (s : ℂ) (hs : 0 < s.re) (z : ℍ) :
    dilationFunction χ hL b s z = ∑ j : Div L,
      kernelMatrix χ s L b j*(levelFactor (q^2*L) (q*j.1) s*criticalD χ hL j s z) := by
  classical
  let K := kernelMatrix χ s L
  let V := fun B : Div L => dilationFunction χ hL B s z
  have hK : K.det ≠ 0 := kernel_det_ne_zero χ hs L hL
  have he : (fun j : Div L => levelFactor (q^2*L) (q*j.1) s*criticalD χ hL j s z) =
      K.det⁻¹ • (K.adjugate *ᵥ V) := by
    funext j
    have hj : levelFactor (q^2*L) (q*j.1) s ≠ 0 := Complex.exp_ne_zero _
    rw [criticalD,Matrix.cramer_eq_adjugate_mulVec]
    change levelFactor _ _ s*((K.adjugate *ᵥ V) j/(K.det*levelFactor _ _ s)) =
      K.det⁻¹*(K.adjugate *ᵥ V) j
    field_simp [hK,hj] <;> ring
  change V b = (K *ᵥ (fun j : Div L => levelFactor (q^2*L) (q*j.1) s*criticalD χ hL j s z)) b
  rw [he,Matrix.mulVec_smul,Matrix.mulVec_mulVec,Matrix.mul_adjugate K,
    Matrix.smul_mulVec,Matrix.one_mulVec,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul]
  field_simp [hK]

/-- Each occupied physical character channel carries its actual conductor,
level, original denominator and one fixed coefficient per admissible
dilation. These coefficients are independent of the observing cusp, z,
Fourier sign and Fourier index. -/
theorem channel_slot {N : ℕ} [NeZero N] (f : Div N) (ξ : DirichletCharacter ℂ (band N f.1)) :
    letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
    ∃ (L : ℕ) (hL : 0 < L) (j : Div L), ξ.conductor^2*L = N ∧ ξ.conductor*j.1 = f.1 ∧
      ∀ s z, channelFunction f ξ s z = criticalD ξ.primitiveCharacter hL j s z := by
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  let q := ξ.conductor
  let j := f.1/q
  let k := (N/f.1)/q
  have hf := (Nat.mem_divisors.mp f.2).1
  have hfpos := Nat.pos_of_dvd_of_pos hf (NeZero.pos N)
  have hM := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hf) hfpos
  have hqf : q ∣ f.1 := ξ.conductor_dvd_level.trans (Nat.gcd_dvd_left _ _)
  have hqM : q ∣ N/f.1 := ξ.conductor_dvd_level.trans (Nat.gcd_dvd_right _ _)
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd hfpos hqf) (NeZero.pos q)
  have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd hM hqM) (NeZero.pos q)
  have h₁ : q*j = f.1 := Nat.mul_div_cancel' hqf
  have h₂ : q*k = N/f.1 := Nat.mul_div_cancel' hqM
  refine ⟨j*k,Nat.mul_pos hj hk,⟨j,Nat.mem_divisors.mpr ⟨dvd_mul_right j k,(Nat.mul_pos hj hk).ne'⟩⟩,?_,h₁,?_⟩
  · calc
      q^2*(j*k) = (q*j)*(q*k) := by ring
      _ = N := by rw [h₁,h₂,Nat.mul_div_cancel' hf]
  · intro s z
    rfl

private theorem character_delta {H : ℕ} [NeZero H] (u v : (ZMod H)ˣ) :
    (∑ ξ : DirichletCharacter ℂ H, star (ξ (-(u : ZMod H)))*ξ (-(v : ZMod H))) =
      if u = v then (H.totient : ℂ) else 0 := by
  have invValue (ξ : DirichletCharacter ℂ H) : star (ξ (-(u : ZMod H))) = ξ ((-(u : ZMod H))⁻¹) := by
    rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']
    have hu : IsUnit (-(u : ZMod H)) := u.isUnit.neg
    have hn := (hu.map ξ).ne_zero
    have hh : ξ ((-(u : ZMod H))⁻¹)*ξ (-(u : ZMod H)) = 1 := by
      rw [← map_mul,ZMod.inv_mul_of_unit _ hu,map_one]
    field_simp [hn]
    simpa only [eq_comm] using hh
  simp_rw [invValue]
  simpa only [neg_inj,Units.val_inj] using
    DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit.neg (-(v : ZMod H))

theorem local_projection {H : ℕ} [NeZero H] (A B : (ZMod H)ˣ → ℂ) :
    (∑ ξ : DirichletCharacter ℂ H,
      star (∑ u : (ZMod H)ˣ,ξ (-(u : ZMod H))*A u)*(∑ v : (ZMod H)ˣ,ξ (-(v : ZMod H))*B v)) =
      (H.totient : ℂ)*∑ u : (ZMod H)ˣ,star (A u)*B u := by
  classical
  let V := fun (ξ : DirichletCharacter ℂ H) (u : (ZMod H)ˣ) => ξ (-(u : ZMod H))
  have term (ξ : DirichletCharacter ℂ H) :
      star (∑ u : (ZMod H)ˣ,V ξ u*A u)*(∑ v : (ZMod H)ˣ,V ξ v*B v) =
        ∑ u : (ZMod H)ˣ,∑ v : (ZMod H)ˣ,(star (V ξ u)*V ξ v)*(star (A u)*B v) := by
    rw [star_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [star_mul]
    ring
  change (∑ ξ : DirichletCharacter ℂ H,star (∑ u : (ZMod H)ˣ,V ξ u*A u)*(∑ v : (ZMod H)ˣ,V ξ v*B v)) = _
  simp_rw [term]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,show ∀ v : (ZMod H)ˣ, (∑ ξ : DirichletCharacter ℂ H,star (V ξ u)*V ξ v) =
    if u = v then (H.totient : ℂ) else 0 from character_delta u,ite_mul,zero_mul]
  simp

/-- Young's inverse-Gram weights for two evaluations of the original
functions. The star is on the first factor, and 4π enters once. -/
theorem actual_inverse_gram_kernel (N : ℕ) [NeZero N] (t : ℝ) (z w : ℍ) :
    (∑ f : Div N, ∑ ξ : DirichletCharacter ℂ (band N f.1),
      star (channelFunction f ξ (criticalPoint t) z)*channelFunction f ξ (criticalPoint t) w /
        (4*(Real.pi : ℂ)*((band N f.1).totient : ℂ))) =
    ∑ a : Parameters N, star (physicalFamily N t a z)*physicalFamily N t a w/(4*(Real.pi : ℂ)) := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro f _
  let A := fun u : (ZMod (band N f.1))ˣ => physicalFamily N t ⟨f,u⟩ z
  let B := fun u : (ZMod (band N f.1))ˣ => physicalFamily N t ⟨f,u⟩ w
  have hφ : ((band N f.1).totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (band N f.1)))).ne'
  have H := local_projection A B
  simp only [A,B,physicalFamily,direct_channel] at H
  rw [← Finset.sum_div,← Finset.sum_div,H]
  field_simp [hφ,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end
end ImbalancedChen.Part3.ActualYoungCriticalProjection20261110

