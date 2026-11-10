import ImbalancedChen.Part3ActualCuspDenominatorClasses

/-! The actual matrix entries in Young (7.1) and the finite sum of his
character combinations D. All rows outside the character conductor
band vanish by the two genuine signed zero-extended characters. -/
namespace ImbalancedChen.Part3.ActualYoungCuspCoefficients20261110

noncomputable section
open Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualCharacterCuspExpansion20261110 ActualCuspDenominatorClasses20261110
open CharacterEisensteinRowAction ActualCharacterCuspRowReduction20261110
open Gamma0GeneralCuspWidth20261025a Gamma0CuspLeftWidthCovariance20261026b
open NativeAllCuspFrameCovariance20261026b NativeAllCuspEisenstein20261026b
open PrimitiveRealEisensteinAutomorphy OriginalCharacterPairDilation20261102s

def posPower (x : ℝ) (s : ℂ) := Complex.exp (s*(Real.log x : ℂ))

theorem posPower_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    posPower (x*y) s = posPower x s*posPower y s := by
  rw [posPower,Real.log_mul hx.ne' hy.ne',Complex.ofReal_add,mul_add,Complex.exp_add]
  rfl

def twist {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : ℂ :=
  χ (n : ZMod q)*posPower n (-s)

def divisorKernel {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (a b : ℕ) : ℂ :=
  twist χ s (a/a.gcd b)*twist χ s (b/a.gcd b)

def levelFactor (N f : ℕ) (s : ℂ) : ℂ := posPower ((N : ℝ)/(band N f : ℝ)) s

theorem youngFrame_width {N f : ℕ} (hf : 0 < f) (hd : f ∣ N) (u : ℤ)
    (hu : IsCoprime u (N : ℤ)) :
    cuspWidth N (youngFrame f u) = (N/f)/(band N f) := by
  let M := N/f
  have hN : N = f*M := (Nat.mul_div_cancel' hd).symm
  have H : N.gcd ((u*(f : ℤ)).natAbs^2) = f*(band N f) := by
    calc
      _ = ((u*u)*((f : ℤ)*f)).gcd (N : ℤ) := by
        simp [Int.gcd_eq_natAbs,Int.natAbs_mul,pow_two,Nat.gcd_comm,mul_mul_mul_comm]
      _ = ((f : ℤ)*f).gcd (N : ℤ) := gcd_mul_unit _ _ _ (hu.mul_left hu)
      _ = (f*f).gcd (f*M) := by rw [← Nat.cast_mul,Int.gcd_natCast_natCast,hN]
      _ = _ := by simp [Nat.gcd_mul_left,band,M]
  change N/N.gcd ((u*(f : ℤ)).natAbs^2) = _
  rw [H]
  change N/(f*band N f) = M/(band N f)
  conv_lhs => lhs; rw [hN]
  exact Nat.mul_div_mul_left M (band N f) hf

theorem coefficient_at_youngFrame {N q f : ℕ} [NeZero N] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (hl : q^2*(B : ℕ) ∣ N) (hf : 0 < f) (hd : f ∣ N)
    (u : ℤ) (hu : IsCoprime u (N : ℤ)) (s : ℂ) :
    cuspCoefficient hq χ B N (youngFrame f u) s =
      χ (-u : ZMod q)*levelFactor N f s*divisorKernel χ s f (q*(B : ℕ)) := by
  let p := q*(B : ℕ)
  let h := f.gcd p
  let H := band N f
  let M := N/f
  let w := M/H
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hp : 0 < p := Nat.mul_pos hq B.pos
  have hg : 0 < h := Nat.gcd_pos_of_pos_left _ hf
  have hM : 0 < M := Nat.div_pos (Nat.le_of_dvd hN hd) hf
  have hH : 0 < H := Nat.gcd_pos_of_pos_left _ hf
  have hpN : p ∣ N := dvd_trans (show p ∣ q^2*(B : ℕ) by
    refine ⟨q,?_⟩; simp [p,pow_two,mul_assoc,mul_comm,mul_left_comm]) hl
  have hu' : IsCoprime u (p : ℤ) := hu.of_isCoprime_of_dvd_right (by exact_mod_cast hpN)
  have hgc : (u*(f : ℤ)).gcd (p : ℤ) = h := by rw [gcd_mul_unit _ _ _ hu',Int.gcd_natCast_natCast]
  have h₁ : (h : ℤ) ∣ (f : ℤ) := by exact_mod_cast Nat.gcd_dvd_left f p
  have hA : 0 < f/h := Nat.div_pos (Nat.le_of_dvd hf (Nat.gcd_dvd_left f p)) hg
  have hB : 0 < p/h := Nat.div_pos (Nat.le_of_dvd hp (Nat.gcd_dvd_right f p)) hg
  have hwidth := youngFrame_width hf hd u hu
  have hw : 0 < w := hwidth ▸ cuspWidth_pos N hN (youngFrame f u)
  have hfd : (h : ℝ)*(f/h : ℕ) = f := by exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left f p)
  have hpd : (h : ℝ)*(p/h : ℕ) = p := by exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right f p)
  have hwd : (H : ℝ)*w = M := by exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right f M)
  have hNd : (f : ℝ)*M = N := by exact_mod_cast Nat.mul_div_cancel' hd
  have hAE : 0 < ((f/h : ℕ) : ℝ) := by exact_mod_cast hA
  have hBE : 0 < ((p/h : ℕ) : ℝ) := by exact_mod_cast hB
  have hHE : 0 < (H : ℝ) := by exact_mod_cast hH
  have hpE : 0 < (p : ℝ) := by exact_mod_cast hp
  have hNE : 0 < (N : ℝ) := by exact_mod_cast hN
  have hr : ((h : ℝ)^2/p)*(w : ℝ) =
      ((N : ℝ)/H)/(((f/h : ℕ) : ℝ)*((p/h : ℕ) : ℝ)) := by
    field_simp [hHE.ne',hpE.ne',hAE.ne',hBE.ne']
    linear_combination (norm := ring_nf)
      (H : ℝ)*(w : ℝ)*(h : ℝ)*((p/h : ℕ) : ℝ)*hfd +
      (H : ℝ)*(w : ℝ)*(f : ℝ)*hpd + (f : ℝ)*(p : ℝ)*hwd + (p : ℝ)*hNd
  have hneg : -(u*(f : ℤ))/(h : ℤ) = (-u)*((f/h : ℕ) : ℤ) := by
    rw [Int.natCast_ediv,← neg_mul,Int.mul_ediv_assoc _ h₁]
  have ht : posPower (((h : ℝ)^2/p)*w) s =
      levelFactor N f s*posPower ((f/h : ℕ) : ℝ) (-s)*posPower ((p/h : ℕ) : ℝ) (-s) := by
    rw [hr]
    simp only [levelFactor,posPower,Real.log_div (div_pos hNE hHE).ne' (mul_pos hAE hBE).ne',
      Real.log_mul hAE.ne' hBE.ne',Complex.ofReal_sub,Complex.ofReal_add,← Complex.exp_add]
    congr 1
    ring
  rw [cuspCoefficient_explicit hq χ B N hN]
  change characterWeight χ (-(u*(f : ℤ))/((u*(f : ℤ)).gcd (p : ℤ) : ℤ))
    ((p : ℤ)*1/((u*(f : ℤ)).gcd (p : ℤ) : ℤ))*
    posPower (((((u*(f : ℤ)).gcd (p : ℤ) : ℕ) : ℝ)^2/p)*(cuspWidth N (youngFrame f u) : ℝ)) s = _
  rw [hgc,hwidth,hneg,mul_one,← Int.natCast_ediv,ht,characterWeight,Int.cast_mul,Int.cast_neg,
    Int.cast_natCast,Int.cast_natCast,map_mul,divisorKernel,twist,twist]
  ring

/-- When the two actual zero-extended characters survive, both f and N/f
are multiples of the primitive conductor. This includes all common-prime
ramification when B and N/(q²B) share factors. -/
theorem kernel_conductor_support {q N f : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (hl : q^2*(B : ℕ) ∣ N) (hf : f ∣ N) (s : ℂ)
    (hn : divisorKernel χ s f (q*(B : ℕ)) ≠ 0) :
    q ∣ band N f := by
  let p := q*(B : ℕ)
  let h := f.gcd p
  have hA : χ ((f/h : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    apply hn
    change (χ ((f/h : ℕ) : ZMod q)*_)*_ = _
    rw [hz,zero_mul,zero_mul]
  have hB : χ ((p/h : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    apply hn
    change _*(χ ((p/h : ℕ) : ZMod q)*_) = _
    rw [hz,zero_mul,mul_zero]
  have hcop (n : ℕ) (hn' : χ (n : ZMod q) ≠ 0) : q.Coprime n := by
    apply Nat.coprime_comm.mp
    rw [Nat.coprime_iff_gcd_eq_one,← Int.gcd_natCast_natCast,← Int.isCoprime_iff_gcd_eq_one]
    exact (χ.apply_ne_zero_iff (n : ℤ)).mp (by simpa using hn')
  have hqP : q ∣ p := dvd_mul_right q _
  have hD : q ∣ h := (hcop _ hB).dvd_of_dvd_mul_right (by simpa only
    [Nat.mul_div_cancel' (Nat.gcd_dvd_right f p)] using hqP : q ∣ h*(p/h))
  have hqf := hD.trans (Nat.gcd_dvd_left f p)
  have hgN : q*h ∣ N := (Nat.mul_dvd_mul_left q (Nat.gcd_dvd_right f p)).trans
    (by simpa [p,pow_two,mul_assoc] using hl)
  have hgpos : 0 < h := Nat.gcd_pos_of_pos_right _ (Nat.mul_pos hq B.pos)
  have hQ : q ∣ (f/h)*(N/f) := by
    obtain ⟨k,hk⟩ := hgN
    refine ⟨k,Nat.eq_of_mul_eq_mul_left hgpos ?_⟩
    calc
      h*((f/h)*(N/f)) = f*(N/f) := by rw [← mul_assoc,Nat.mul_div_cancel' (Nat.gcd_dvd_left f p)]
      _ = N := Nat.mul_div_cancel' hf
      _ = h*(q*k) := by rw [hk]; ring
  exact Nat.dvd_gcd hqf ((hcop _ hA).dvd_of_dvd_mul_left hQ)

def D {N q : ℕ} [NeZero N] (χ : DirichletCharacter ℂ q)
    (f : {f : ℕ // f ∈ N.divisors}) (s : ℂ) (z : ℍ) : ℂ :=
  ∑' u : (ZMod (band N f.1))ˣ,
    χ (-(unitInteger (Nat.mem_divisors.mp f.2).1 u) : ZMod q)*
      cuspEisenstein N (parameterFrame ⟨f,u⟩) s z

private theorem same_frame_pair {q N : ℕ} [NeZero N] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (hl : q^2*(B : ℕ) ∣ N) (g h : SL(2,ℤ)) (he : nativeFrameOrbit N g = nativeFrameOrbit N h)
    (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    cuspCoefficient hq χ B N g s*cuspEisenstein N g s z =
    cuspCoefficient hq χ B N h s*cuspEisenstein N h s z := by
  have hN := Nat.pos_of_ne_zero (NeZero.ne N)
  have H := (nativeFrameOrbit_eq_iff N g h).mp he
  obtain ⟨γ,k,hframe⟩ := (frames_same_class_iff N _ _).mp H
  have hE : cuspEisenstein N h s z = cuspEisenstein N g s z := by
    rw [hframe,cuspEisenstein_frame_right_translation N hN _ _ s hs,
      cuspEisenstein_frame_left_Gamma0 N hN γ g s hs]
  have hw : cuspWidth N h = cuspWidth N g := by
    rw [hframe,cuspWidth_right_translation,cuspWidth_left_mul N _ _ γ.property]
  obtain ⟨δ,hδ⟩ := Quotient.exact H
  simp only [cuspCoefficient,← hδ,hw,hE,rowWeight_invariant hq χ B N hl]

/-- Actual finite Young expansion grouped into his D-functions. The
underlying parabolic E series are individually the original cusp series;
absolute convergence on the initial half-plane is inherited throughout. -/
theorem original_oldform_eq_D_sum {N q : ℕ} [NeZero N] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (B : ℕ+) (hl : q^2*(B : ℕ) ∣ N) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    characterLatticeOldform hq χ B s z = ∑' f : {f : ℕ // f ∈ N.divisors},
      levelFactor N f.1 s*divisorKernel χ s f.1 (q*(B : ℕ))*D χ f s z := by
  classical
  letI : Finite (Parameters N) := Finite.of_equiv (NativeCusps N) (youngCuspEquiv N).symm
  let E : Parameters N ≃ CuspRowClass N := (youngCuspEquiv N).trans (nativeCuspEquiv N).symm
  let F : Parameters N → ℂ := fun a => cuspCoefficient hq χ B N (parameterFrame a) s*
    cuspEisenstein N (parameterFrame a) s z
  have he (a : Parameters N) : nativeFrameOrbit N (classFrame (E a)) = nativeFrameOrbit N (parameterFrame a) :=
    (nativeCuspEquiv N).apply_symm_apply ((youngCuspEquiv N) a)
  have hsum : characterLatticeOldform hq χ B s z = ∑' a : Parameters N,F a := by
    rw [actual_oldform_eq_finite_cusp_sum hq χ B N hl s hs z,← tsum_fintype,
      ← E.tsum_eq (fun x => cuspCoefficient hq χ B N (classFrame x) s*cuspEisenstein N (classFrame x) s z)]
    exact tsum_congr (fun a => same_frame_pair hq χ B hl _ _ (he a) s hs z)
  rw [hsum,((summable_of_finite F).tsum_sigma)]
  apply tsum_congr
  intro f
  rw [D,← tsum_mul_left]
  apply tsum_congr
  intro u
  let hd := (Nat.mem_divisors.mp f.2).1
  let hp := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero (NeZero.ne N))
  change cuspCoefficient hq χ B N (youngFrame f.1 (unitInteger hd u)) s* _ = _
  rw [coefficient_at_youngFrame hq χ B hl hp hd _ (unitInteger_coprime hd u) s]
  ring

end
end ImbalancedChen.Part3.ActualYoungCuspCoefficients20261110
