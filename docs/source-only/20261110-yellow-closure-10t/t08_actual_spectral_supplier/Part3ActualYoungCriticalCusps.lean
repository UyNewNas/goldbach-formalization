import ImbalancedChen.Part3ActualYoungCriticalD
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! Finite Fourier inversion on every actual denominator's unit group.
This continues each individual genuine normalized parabolic cusp function
through s=1/2+it, including the conductor-one contribution and t=0. -/
namespace ImbalancedChen.Part3.ActualYoungCriticalCusps20261110

noncomputable section
open Complex Matrix UpperHalfPlane Set
open scoped BigOperators MatrixGroups UpperHalfPlane
open ActualYoungCuspCoefficients20261110 ActualYoungDilationInverse20261110
open ActualCuspDenominatorClasses20261110 ActualCharacterCuspExpansion20261110
open ActualYoungCriticalD20261110 NativeAllCuspEisenstein20261026b
open NativeAllCuspFrameCovariance20261026b

private theorem band_pos {N : ℕ} [NeZero N] (f : Div N) : 0 < band N f.1 :=
  Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))

private structure Slot (N f q : ℕ) where
  L : ℕ
  pos : 0 < L
  j : Div L
  level : q^2*L = N
  denominator : q*j.1 = f

private def slot {q N : ℕ} [NeZero N] (hq : 0 < q) (f : Div N) (hd : q ∣ band N f.1) :
    Slot N f.1 q := by
  let M := N/f.1
  let j := f.1/q
  let k := M/q
  have hqf := hd.trans (Nat.gcd_dvd_left f.1 M)
  have hqM := hd.trans (Nat.gcd_dvd_right f.1 M)
  have hf := (Nat.mem_divisors.mp f.2).1
  have hfpos := Nat.pos_of_dvd_of_pos hf (NeZero.pos N)
  have hM : 0 < M := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hf) hfpos
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd hfpos hqf) hq
  have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd hM hqM) hq
  have h₁ : q*j = f.1 := Nat.mul_div_cancel' hqf
  have h₂ : q*k = M := Nat.mul_div_cancel' hqM
  refine ⟨j*k,Nat.mul_pos hj hk,⟨j,Nat.mem_divisors.mpr ⟨dvd_mul_right j k,(Nat.mul_pos hj hk).ne'⟩⟩,?_,h₁⟩
  calc
    q^2*(j*k) = (q*j)*(q*k) := by ring
    _ = N := by rw [h₁,h₂,Nat.mul_div_cancel' hf]

def continuedDAt {N q : ℕ} [NeZero q] [NeZero N] (χ : DirichletCharacter ℂ q)
    (f : Div N) (hd : q ∣ band N f.1) (s : ℂ) (z : ℍ) : ℂ :=
  let S := slot (NeZero.pos q) f hd
  criticalD χ S.pos S.j s z

private theorem relevel {q L N : ℕ} [NeZero q] [NeZero N] (hq : 0 < q) (hL : 0 < L)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (j : Div L) (f : Div N)
    (hN : q^2*L = N) (hf : q*j.1 = f.1) (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    criticalD χ hL j s z = D χ f s z := by
  subst N
  have he : lifted hq hL j = f := Subtype.ext hf
  simpa only [he] using criticalD_initial hq hL χ hχ s hs j z

theorem continuedDAt_initial {N q : ℕ} [NeZero q] [NeZero N] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (f : Div N) (hd : q ∣ band N f.1) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    continuedDAt χ f hd s z = D χ f s z :=
  relevel (NeZero.pos q) _ χ hχ _ _ (slot _ f hd).level (slot _ f hd).denominator z s hs

private def fromBand {N : ℕ} [NeZero N] (f : Div N) (ξ : DirichletCharacter ℂ (band N f.1))
    (s : ℂ) (z : ℍ) : ℂ := by
  letI : NeZero (band N f.1) := ⟨(band_pos f).ne'⟩
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  exact continuedDAt ξ.primitiveCharacter f ξ.conductor_dvd_level s z

theorem band_D_initial {N : ℕ} [NeZero N] (f : Div N) (ξ : DirichletCharacter ℂ (band N f.1))
    (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    fromBand f ξ s z = ∑' u : (ZMod (band N f.1))ˣ,
      ξ (-(u : ZMod (band N f.1)))*cuspEisenstein N (parameterFrame ⟨f,u⟩) s z := by
  classical
  letI : NeZero (band N f.1) := ⟨(band_pos f).ne'⟩
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  rw [fromBand,continuedDAt_initial _ ξ.primitiveCharacter_isPrimitive _ _ s hs,D]
  apply tsum_congr
  intro u
  let hd := (Nat.mem_divisors.mp f.2).1
  let U := unitInteger hd u
  have hH : (band N f.1 : ℤ) ∣ (N : ℤ) := by exact_mod_cast (Nat.gcd_dvd_left f.1 (N/f.1)).trans hd
  have hu : IsCoprime (-U) (band N f.1 : ℤ) := by
    simpa [U] using (unitInteger_coprime hd u).of_isCoprime_of_dvd_right hH
  have H := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ.primitiveCharacter ξ.conductor_dvd_level hu
  rw [ξ.changeLevel_primitiveCharacter] at H
  have hcast : ((-U : ℤ) : ZMod (band N f.1)) = -(u : ZMod (band N f.1)) := by
    rw [Int.cast_neg,unitInteger_cast]
  rw [hcast] at H
  simpa only [U,Int.cast_neg] using congrArg (fun c : ℂ => c*cuspEisenstein N (parameterFrame ⟨f,u⟩) s z) H.symm

def parameterFamily {N : ℕ} [NeZero N] (a : Parameters N) (s : ℂ) (z : ℍ) : ℂ := by
  letI : NeZero (band N a.1.1) := ⟨(band_pos a.1).ne'⟩
  exact ((band N a.1.1).totient : ℂ)⁻¹ * ∑ ξ : DirichletCharacter ℂ (band N a.1.1),
    ξ ((-(a.2 : ZMod (band N a.1.1)))⁻¹)*fromBand a.1 ξ s z

/-- Character orthogonality selects the actual single cusp function.
The scalar is precisely the inverse cardinality of the true unit group. -/
theorem parameterFamily_initial {N : ℕ} [NeZero N] (a : Parameters N) (s : ℂ)
    (hs : 1 < s.re) (z : ℍ) :
    parameterFamily a s z = cuspEisenstein N (parameterFrame a) s z := by
  classical
  obtain ⟨f,u⟩ := a
  let H := band N f.1
  letI : NeZero H := ⟨(band_pos f).ne'⟩
  let F := fun v : (ZMod H)ˣ => cuspEisenstein N (parameterFrame ⟨f,v⟩) s z
  have hu : IsUnit (-(u : ZMod H)) := u.isUnit.neg
  have hsum (v : (ZMod H)ˣ) :
      (∑ ξ : DirichletCharacter ℂ H, ξ ((-(u : ZMod H))⁻¹)*ξ (-(v : ZMod H))) =
      if u = v then (H.totient : ℂ) else 0 := by
    simpa only [neg_inj,Units.val_inj] using
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (-(v : ZMod H))
  have hΦ : (H.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (band_pos f)).ne'
  change (H.totient : ℂ)⁻¹ * (∑ ξ : DirichletCharacter ℂ H, ξ ((-(u : ZMod H))⁻¹)*fromBand f ξ s z) = F u
  simp_rw [band_D_initial f _ s hs z,tsum_fintype,Finset.mul_sum,← mul_assoc]
  rw [Finset.sum_comm]
  change (H.totient : ℂ)⁻¹*(∑ v : (ZMod H)ˣ, ∑ ξ : DirichletCharacter ℂ H,
    (ξ ((-(u : ZMod H))⁻¹)*ξ (-(v : ZMod H)))*F v) = F u
  simp_rw [← Finset.sum_mul,hsum,ite_mul,zero_mul]
  simp [hΦ]

theorem parameterFamily_differentiable {N : ℕ} [NeZero N] (a : Parameters N)
    (z : ℍ) (s : ℂ) (hs : 1/2 ≤ s.re) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun w => parameterFamily a w z) s := by
  classical
  letI : NeZero (band N a.1.1) := ⟨(band_pos a.1).ne'⟩
  unfold parameterFamily
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro ξ _
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  exact (criticalD_differentiable ξ.primitiveCharacter _ _ z s hs h1).const_mul _

def cuspFamily (N : ℕ) [NeZero N] (a : NativeCusps N) (s : ℂ) (z : ℍ) : ℂ :=
  parameterFamily ((youngCuspEquiv N).symm a) s z

/-- Every original normalized single parabolic function has the actual
continuation indexed by its native projective cusp, independently of
which integral frame represented it on the initial half-plane. -/
theorem cuspFamily_initial (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    cuspFamily N (nativeFrameOrbit N g) s z = cuspEisenstein N g s z := by
  let a := (youngCuspEquiv N).symm (nativeFrameOrbit N g)
  have he : nativeFrameOrbit N (parameterFrame a) = nativeFrameOrbit N g :=
    (youngCuspEquiv N).apply_symm_apply _
  obtain ⟨γ,k,hg⟩ := (frames_same_class_iff N _ _).mp ((nativeFrameOrbit_eq_iff N _ _).mp he)
  change parameterFamily a s z = _
  rw [parameterFamily_initial a s hs,hg,cuspEisenstein_frame_right_translation N (NeZero.pos N) _ _ s hs,
    cuspEisenstein_frame_left_Gamma0 N (NeZero.pos N) γ (parameterFrame a) s hs]

theorem all_cusps_critical (N : ℕ) [NeZero N] (a : NativeCusps N) (t : ℝ) (z : ℍ) :
    DifferentiableAt ℂ (fun s => cuspFamily N a s z) (1/2+Complex.I*t) := by
  apply parameterFamily_differentiable
  · simp [Complex.mul_re]
  · intro h
    have H := congrArg Complex.re h
    norm_num [Complex.mul_re] at H

end
end ImbalancedChen.Part3.ActualYoungCriticalCusps20261110
