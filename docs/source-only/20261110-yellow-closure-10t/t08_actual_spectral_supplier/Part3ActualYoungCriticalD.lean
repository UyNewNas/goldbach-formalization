import ImbalancedChen.Part3ActualYoungDilationInverse
import ImbalancedChen.Part3CompletedActualEisensteinIdentity

/-! Reverse the finite divisor block on the physical original functions.
Cramer's numerator uses the continued genuine oldforms at each B, with
the two full-level constant terms retained at conductor one. -/
namespace ImbalancedChen.Part3.ActualYoungCriticalD20261110

noncomputable section
open Complex Matrix UpperHalfPlane Set
open scoped BigOperators MatrixGroups UpperHalfPlane
open ActualYoungDilationInverse20261110 ActualYoungCuspCoefficients20261110
open ActualCuspDenominatorClasses20261110 ActualCharacterCriticalFamily20261110
open OriginalCharacterPairDilation20261102s CharacterEisensteinSeries
open CharacterEisensteinRowAction PrimitiveEisensteinParameterAnalytic
open Gamma0DegeneracyMapSourceOnly CompletedActualEisensteinIdentity20261025a

def principalOrdinary (s : ℂ) (z : ℍ) : ℂ :=
  (Real.pi : ℂ)^s/Complex.Gamma s*reciprocalL (1 : DirichletCharacter ℂ 1) (2*s)*
    completedActualEisenstein s z

private theorem principal_initial (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    principalOrdinary s z = primitiveComplexEisenstein s z := by
  have h₂ : 1 < (2*s).re := by simp [Complex.mul_re]; linarith
  have hn : 2*s ≠ 1 := by intro he; simp [he] at h₂
  have hz : riemannZeta (2*s) ≠ 0 := by simpa only [DirichletCharacter.LFunction_modOne_eq] using
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ 1) (.inr hn) h₂.le
  have hΓ := Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re)
  have hπ : (Real.pi : ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [principalOrdinary,completedActualEisenstein_eq_initial s hs,completionFactor,Complex.cpow_neg,
    reciprocalL,if_pos rfl,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hn]
  change _*((2*s-1)/((2*s-1)*(1 : DirichletCharacter ℂ 1).LFunction (2*s)))*_ = _
  rw [DirichletCharacter.LFunction_modOne_eq]
  field_simp [hπ,hΓ,hz,sub_ne_zero.mpr hn] <;> ring

def ordinary {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (z : ℍ) : ℂ :=
  if q = 1 then principalOrdinary s z else primitiveFamily χ s z

theorem ordinary_initial {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    ordinary χ s z = characterEisenstein hq χ s z := by
  by_cases h : q = 1
  · subst q
    have hc (t : ZMod 1) : χ t = 1 := by rw [Subsingleton.elim t 1,map_one]
    have hz : scaledPoint 1 hq z = z := by
      apply UpperHalfPlane.ext
      simp [scaledPoint_coe]
    simp [ordinary,principal_initial s hs,characterEisenstein,primitiveComplexEisenstein,
      characterSeed,primitiveWeight,characterWeight,hc,hz]
  · simp only [ordinary,if_neg h,primitiveFamily_initial hq h χ hχ s hs z]

theorem ordinary_differentiable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (z : ℍ) (s : ℂ) (hs : 1/2 ≤ s.re) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun w => ordinary χ w z) s := by
  by_cases hq : q = 1
  · simp only [ordinary,if_pos hq,principalOrdinary]
    have hp : (0 : ℝ) < s.re := by linarith
    have h0 : s ≠ 0 := by intro he; simp [he] at hp
    have hG : DifferentiableAt ℂ Complex.Gamma s := by
      apply Complex.differentiableAt_Gamma
      intro n he
      have hr := congrArg Complex.re he
      simp only [Complex.neg_re,Complex.natCast_re] at hr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have h₂ : 1 ≤ (2*s).re := by simp [Complex.mul_re]; linarith
    have hE := (completedActualEisenstein_analyticOnNhd z s (by simpa using And.intro h0 h1)).differentiableAt
    exact (((differentiableAt_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).div
      hG (Complex.Gamma_ne_zero_of_re_pos hp)).mul
        ((reciprocalL_differentiableAt _ _ h₂).comp s (differentiableAt_id.const_mul 2))).mul hE
  · simpa only [ordinary,if_neg hq] using primitiveFamily_differentiableAt χ z s hs

def dilation {L : ℕ} (hL : 0 < L) (b : Div L) : ℕ+ :=
  ⟨b.1,Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp b.2).1 hL⟩

theorem level_at_dilation {q L : ℕ} (b : Div L) : q^2*b.1 ∣ q^2*L :=
  Nat.mul_dvd_mul_left _ (Nat.mem_divisors.mp b.2).1

def lifted {q L : ℕ} (hq : 0 < q) (hL : 0 < L) (j : Div L) : Div (q^2*L) := by
  refine ⟨q*j.1,Nat.mem_divisors.mpr ⟨?_,mul_ne_zero (pow_ne_zero _ hq.ne') hL.ne'⟩⟩
  obtain ⟨k,hk⟩ := (Nat.mem_divisors.mp j.2).1
  refine ⟨q*k,?_⟩
  rw [hk]
  ring

@[simp] theorem lifted_val {q L : ℕ} (hq : 0 < q) (hL : 0 < L) (j : Div L) :
    (lifted hq hL j).1 = q*j.1 := rfl

private theorem lifted_supported {q L : ℕ} (hq : 0 < q) (hL : 0 < L) (j : Div L) :
    q ∣ band (q^2*L) (lifted hq hL j).1 := by
  obtain ⟨k,hk⟩ := (Nat.mem_divisors.mp j.2).1
  have hj := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp j.2).1 hL
  have H : q^2*L = (q*j.1)*(q*k) := by rw [hk]; ring
  rw [band,lifted_val,H,Nat.mul_div_cancel_left _ (Nat.mul_pos hq hj)]
  exact Nat.dvd_gcd (dvd_mul_right _ _) (dvd_mul_right _ _)

private def bandEquiv {q L : ℕ} (hq : 0 < q) (hL : 0 < L) :
    Div L ≃ {f : Div (q^2*L) // q ∣ band (q^2*L) f.1} := by
  apply Equiv.ofBijective (fun j => ⟨lifted hq hL j,lifted_supported hq hL j⟩)
  constructor
  · intro a b he
    apply Subtype.ext
    have H := congrArg (fun f : {f : Div (q^2*L) // q ∣ band (q^2*L) f.1} => f.1.1) he
    exact Nat.eq_of_mul_eq_mul_left hq (by simpa only [lifted_val] using H)
  · rintro ⟨f,hf⟩
    obtain ⟨j,hj⟩ := hf.trans (Nat.gcd_dvd_left _ _)
    obtain ⟨k,hk⟩ := hf.trans (Nat.gcd_dvd_right _ _)
    have H := Nat.mul_div_cancel' (Nat.mem_divisors.mp f.2).1
    have H' : q^2*L = q^2*(j*k) := by
      calc
        _ = f.1*((q^2*L)/f.1) := H.symm
        _ = _ := by rw [hk,hj]; ring
    have hjL := Nat.eq_of_mul_eq_mul_left (pow_pos hq 2) H'
    refine ⟨⟨j,Nat.mem_divisors.mpr ⟨⟨k,hjL⟩,hL.ne'⟩⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa only [lifted_val] using hj.symm

private theorem cancel_conductor {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (a b : ℕ) : divisorKernel χ s (q*a) (q*b) = divisorKernel χ s a b := by
  simp only [divisorKernel,Nat.gcd_mul_left,Nat.mul_div_mul_left _ _ hq]

private theorem kernel_symm {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (a b : ℕ) :
    divisorKernel χ s a b = divisorKernel χ s b a := by
  simp only [divisorKernel,Nat.gcd_comm b a,mul_comm]

/-- The SAME finite matrix acts on the actual D-functions at the occupied
level q²L. Its Bth left side is the genuine oldform evaluated at Bz. -/
theorem actual_matrix_system {q L : ℕ} [NeZero q] (hq : 0 < q) (hL : 0 < L)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    letI : NeZero (q^2*L) := ⟨mul_ne_zero (pow_ne_zero _ hq.ne') hL.ne'⟩
    (fun b : Div L => ordinary χ s (degeneracyDiagonal (dilation hL b) (dilation hL b).pos • z)) =
      kernelMatrix χ s L *ᵥ (fun j : Div L => levelFactor (q^2*L) (q*j.1) s *
        D χ (lifted hq hL j) s z) := by
  classical
  letI : NeZero (q^2*L) := ⟨mul_ne_zero (pow_ne_zero _ hq.ne') hL.ne'⟩
  funext b
  let N := q^2*L
  let S : Set (Div N) := {f | q ∣ band N f.1}
  let F : Div N → ℂ := fun f => levelFactor N f.1 s*divisorKernel χ s f.1 (q*b.1)*D χ f s z
  have hsup : Function.support F ⊆ S := by
    intro f hf
    apply kernel_conductor_support hq χ (dilation hL b) (level_at_dilation b)
      (Nat.mem_divisors.mp f.2).1 s
    intro he
    exact hf (by simp only [F,he,mul_zero,zero_mul])
  have hpart : (∑' f : Div N,F f) = ∑ j : Div L,F (lifted hq hL j) := by
    calc
      _ = ∑' f : S,F f.1 := (tsum_subtype_eq_of_support_subset hsup).symm
      _ = ∑' j : Div L,F (lifted hq hL j) :=
        ((bandEquiv hq hL).tsum_eq (fun f => F f.1)).symm
      _ = _ := tsum_fintype _
  rw [ordinary_initial hq χ hχ s hs]
  change characterLatticeOldform hq χ (dilation hL b) s z = _
  rw [original_oldform_eq_D_sum hq χ (dilation hL b) (level_at_dilation b) s hs z]
  change (∑' f : Div N,F f) = _
  rw [hpart]
  apply Finset.sum_congr rfl
  intro j _
  change levelFactor N (lifted hq hL j).1 s * divisorKernel χ s (lifted hq hL j).1 (q*b.1) * _ =
    divisorKernel χ s b.1 j.1 * _
  rw [lifted_val,cancel_conductor hq,kernel_symm χ s j.1 b.1]
  ring

def criticalD {q L : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hL : 0 < L)
    (j : Div L) (s : ℂ) (z : ℍ) : ℂ :=
  let K := kernelMatrix χ s L
  K.cramer (fun b : Div L => ordinary χ s (degeneracyDiagonal (dilation hL b) (dilation hL b).pos • z)) j /
    (K.det*levelFactor (q^2*L) (q*j.1) s)

/-- Actual reverse change, requiring no unknown nonsingularity or native
cusp-continuation premise. -/
theorem criticalD_initial {q L : ℕ} [NeZero q] (hq : 0 < q) (hL : 0 < L)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 < s.re) (j : Div L) (z : ℍ) :
    letI : NeZero (q^2*L) := ⟨mul_ne_zero (pow_ne_zero _ hq.ne') hL.ne'⟩
    criticalD χ hL j s z = D χ (lifted hq hL j) s z := by
  letI : NeZero (q^2*L) := ⟨mul_ne_zero (pow_ne_zero _ hq.ne') hL.ne'⟩
  have hK := kernel_det_ne_zero χ (by linarith : 0 < s.re) L hL
  have hC := Complex.exp_ne_zero (s*(Real.log (((q^2*L : ℕ) : ℝ)/(band (q^2*L) (q*j.1) : ℝ)) : ℂ))
  rw [criticalD,actual_matrix_system hq hL χ hχ s hs z,Matrix.cramer_eq_adjugate_mulVec,
    Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul]
  apply (div_eq_iff (mul_ne_zero hK hC)).mpr
  ring

private theorem det_diff {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℂ → Matrix ι ι ℂ)
    (s : ℂ) (ha : ∀ i j, DifferentiableAt ℂ (fun w => A w i j) s) :
    DifferentiableAt ℂ (fun w => (A w).det) s := by
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  exact (DifferentiableAt.fun_finsetProd (fun i _ => ha (σ i) i)).const_mul _

private theorem kernel_diff {q L : ℕ} (χ : DirichletCharacter ℂ q) (i j : Div L) (s : ℂ) :
    DifferentiableAt ℂ (fun w => kernelMatrix χ w L i j) s := by
  have h (a : ℕ) : DifferentiableAt ℂ (fun w => twist χ w a) s :=
    (((differentiableAt_id.neg).mul_const (Real.log (a : ℝ) : ℂ)).cexp).const_mul _
  exact (h _).mul (h _)

/-- Each original Young D-function now has an actual parameter continuation
to every 1/2+it, using Cramer's finite determinant, including q=1 and t=0.
The distinct possible pole at s=1 is excluded. -/
theorem criticalD_differentiable {q L : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hL : 0 < L) (j : Div L) (z : ℍ) (s : ℂ) (hs : 1/2 ≤ s.re) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun w => criticalD χ hL j w z) s := by
  classical
  have hK := kernel_det_ne_zero χ (by linarith : 0 < s.re) L hL
  let V := fun w (b : Div L) => ordinary χ w (degeneracyDiagonal (dilation hL b) (dilation hL b).pos • z)
  have hnum : DifferentiableAt ℂ (fun w => ((kernelMatrix χ w L).updateCol j (V w)).det) s := by
    apply det_diff
    intro i k
    by_cases he : k = j
    · subst k
      simpa only [Matrix.updateCol_self,V] using ordinary_differentiable χ _ s hs h1
    · simpa only [Matrix.updateCol_ne he] using kernel_diff χ i k s
  have hden := det_diff (fun w => kernelMatrix χ w L) s (fun i k => kernel_diff χ i k s)
  have hC : DifferentiableAt ℂ (levelFactor (q^2*L) (q*j.1)) s :=
    (differentiableAt_id.mul_const _).cexp
  have hC0 : levelFactor (q^2*L) (q*j.1) s ≠ 0 := Complex.exp_ne_zero _
  simpa only [criticalD,Matrix.cramer_apply,V] using hnum.div (hden.mul hC) (mul_ne_zero hK hC0)

end
end ImbalancedChen.Part3.ActualYoungCriticalD20261110
