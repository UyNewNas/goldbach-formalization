import ImbalancedChen.Part3OriginalHolomorphicBesselOffDiagonal

/-! Absolute convergence for exchanging the full h and c sums. This
fixed-parameter domination is used only for Fubini; the uniform bound
comes from the previously estimated, summed native Bessel window. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicHeightModulusFubini20261113
open Finset Real
open ActualGeneralJBesselSourceOnly (generalJ generalJTerm generalJ_hasSum)
open GeneralComplexISeriesSourceOnly (generalICoeff)
open OriginalSmoothPoissonTail (kloosterman)
open OriginalHolomorphicPhysicalCosine20261113 (form argument scale)
open OriginalHolomorphicOddWindow20261113 (weight weight_one weight_nonnegative)
open OriginalHolomorphicBesselOffDiagonal20261113 (nativeTerm nativeWindow geometricTerm)

private theorem integer_J_domination (h : ℕ) {v x : ℝ} (hv : 0≤v) (hx : 0≤x)
    (le : x/2≤v) : ‖generalJ (h:ℂ) x‖≤(x/2)^h/(h.factorial:ℝ)*exp (v^2) := by
  have H : HasSum (fun j : ℕ => (v^2)^j/(j.factorial:ℝ)) (exp (v^2)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (v^2)
  apply (generalJ_hasSum (by simp : -1<(h:ℂ).re) x).norm_le_of_bounded
    (H.mul_left ((x/2)^h/(h.factorial:ℝ)))
  intro j
  have hΓ : Complex.Gamma ((j:ℂ)+(h:ℂ)+1)=((h+j).factorial:ℂ) := by
    simpa only [Nat.cast_add,add_comm (h:ℂ) j] using Complex.Gamma_nat_eq_factorial (h+j)
  have x0 : 0≤x/2 := by positivity
  have jf : 0<(j.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hf : 0<(h.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos h
  have big : (h.factorial:ℝ)≤(h+j).factorial := by
    exact_mod_cast Nat.factorial_le (show h≤h+j by omega)
  have degree : (x/2)^(2*j)≤(v^2)^j := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ x0 le 2) _
  have cap := div_le_div₀ (pow_nonneg (sq_nonneg v) j) degree
    (mul_pos jf hf) (mul_le_mul_of_nonneg_left big jf.le)
  rw [generalJTerm,Complex.cpow_natCast,generalICoeff,hΓ]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg x0,norm_neg,
    norm_one,one_pow,norm_inv,Complex.norm_natCast,one_mul]
  convert mul_le_mul_of_nonneg_left cap (pow_nonneg x0 h) using 1 <;> ring

private theorem bessel_envelope {A : ℝ} (ha : 0≤A) {c : ℕ} (hc : 0<c)
    {h : ℕ} (hh : 3≤h) :
    ‖generalJ (h:ℂ) (A/c)‖≤exp ((A/2)^2+A/2)/(c:ℝ)^3 := by
  have cp : 0<(c:ℝ) := by exact_mod_cast hc
  have c1 : 1≤(c:ℝ) := by exact_mod_cast hc
  have a0 : 0≤A/2 := by positivity
  have le : (A/(c:ℝ))/2≤A/2 := by
    have v := div_le_self ha c1
    exact div_le_div_of_nonneg_right v (by norm_num)
  have p := integer_J_domination h a0 (div_nonneg ha cp.le) le
  have E : HasSum (fun n : ℕ => (A/2)^n/(n.factorial:ℝ)) (exp (A/2)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (A/2)
  have coef : (A/2)^h/(h.factorial:ℝ)≤exp (A/2) := by
    rw [←E.tsum_eq]
    exact E.summable.le_tsum h (fun n _ => div_nonneg (pow_nonneg a0 _) (Nat.cast_nonneg _))
  have cpower := pow_le_pow_right₀ c1 hh
  have cost := div_le_div₀ (exp_pos (A/2)).le coef (pow_pos cp 3) cpower
  apply p.trans
  have F := mul_le_mul_of_nonneg_left cost (exp_pos ((A/2)^2)).le
  rw [exp_add]
  rw [show A/(c:ℝ)/2=(A/2)/c by ring,div_pow]
  convert F using 1 <;> ring

private theorem size_S (c m n : ℕ) [NeZero c] : ‖kloosterman c (m:ℤ) (n:ℤ)‖≤c := by
  rw [OriginalSmoothPoissonTail.Physical.kloosterman_eq_zmod]
  calc
    _≤_ := norm_sum_le _ _
    _≤∑ _ : ZMod c,(1:ℝ) := by
      apply sum_le_sum
      intro i _
      split_ifs <;> simp [ZMod.stdAddChar_apply,Circle.norm_coe]
    _=_ := by simp [ZMod.card]

private def pairTerm (m n z : ℕ) (t : ℝ) (p : ℕ×ℕ) : ℂ :=
  let c := z*(p.2+1)
  (kloosterman c (m:ℤ) (n:ℤ)/(c:ℂ))*nativeTerm t (argument c m n) p.1

private theorem pair_summable (m n : ℕ) {z : ℕ} (hz : 0<z) {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    Summable (fun p : ℕ×ℕ => ‖pairTerm m n z t p‖) := by
  let A := 4*π*sqrt m*sqrt n
  let r := exp (-t)
  let H := fun h : ℕ => (h:ℝ)*r^h
  let V := fun j : ℕ => 1/((j:ℝ)+1)^2
  have rp : 0<r := exp_pos _
  have r1 : ‖r‖<1 := by rw [Real.norm_eq_abs,abs_of_pos rp]; exact exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have sh : Summable H := (hasSum_coe_mul_geometric_of_norm_lt_one r1).summable
  have sv : Summable V := by
    have N : Summable (fun j : ℕ => 1/(j:ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa only [V,Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr N
  have h0 (h : ℕ) : 0≤H h := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg rp.le _)
  have v0 (j : ℕ) : 0≤V j := div_nonneg zero_le_one (sq_nonneg _)
  have major := ((sh.mul_of_nonneg sv h0 v0).const_mul (exp ((A/2)^2+A/2)))
  apply major.of_nonneg_of_le (fun p => norm_nonneg (pairTerm m n z t p))
  intro p
  let c := z*(p.2+1)
  have cn : 0<c := Nat.mul_pos hz (by omega)
  letI : NeZero c := ⟨cn.ne'⟩
  have cp : 0<(c:ℝ) := by exact_mod_cast cn
  have cg : (p.2:ℝ)+1≤(c:ℝ) := by
    have N : p.2+1≤c := by simpa only [one_mul] using Nat.mul_le_mul_right (p.2+1) hz
    exact_mod_cast N
  have c1 : 1≤(c:ℝ) := by exact_mod_cast cn
  have dj : 0<(p.2:ℝ)+1 := by positivity
  have den : ((p.2:ℝ)+1)^2≤(c:ℝ)^3 :=
    (pow_le_pow_left₀ dj.le cg 2).trans (pow_le_pow_right₀ c1 (by norm_num))
  have b0 : 0≤exp ((A/2)^2+A/2) := (exp_pos _).le
  have dom0 := div_le_div_of_nonneg_left b0 (sq_pos_of_pos dj) den
  have eq : argument c m n=A/c := by dsimp only [argument,A,scale]; ring
  have ks : ‖kloosterman c (m:ℤ) (n:ℤ)/(c:ℂ)‖≤1 := by
    rw [norm_div,Complex.norm_natCast]
    exact (div_le_one cp).mpr (size_S c m n)
  change ‖(kloosterman c (m:ℤ) (n:ℤ)/(c:ℂ))*nativeTerm t (argument c m n) p.1‖≤_
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) ks).trans
  by_cases hh : Odd p.1
  · rw [nativeTerm,if_pos hh]
    by_cases one : p.1=1
    · rw [one,weight_one,mul_zero,Complex.ofReal_zero,zero_mul,norm_zero]
      exact mul_nonneg b0 (mul_nonneg (h0 _) (v0 _))
    · have k3 : 3≤p.1 := by obtain ⟨j,hj⟩ := hh; omega
      have hpos := weight_nonnegative ht1 (show 1≤p.1 by omega)
      have ep : exp (-t)^p.1=exp (-(p.1:ℝ)*t) := by rw [←exp_nat_mul]; congr 1 <;> ring
      have bill : (p.1:ℝ)*weight t p.1≤H p.1 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        dsimp only [r,weight]
        rw [ep]
        exact sub_le_self _ (mul_nonneg (exp_pos _).le (exp_pos _).le)
      have B := (bessel_envelope (show 0≤A by dsimp only [A]; positivity) cn k3).trans dom0
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos),
        norm_mul,norm_pow,Complex.norm_I,one_pow,one_mul,eq]
      have h := mul_le_mul bill B (norm_nonneg _) (h0 _)
      convert h using 1 <;> dsimp only [V] <;> ring
  · rw [nativeTerm,if_neg hh,norm_zero]
    exact mul_nonneg b0 (mul_nonneg (h0 _) (v0 _))

def matrixEntry (M z : ℕ) (t : ℝ) (a b : ℕ → ℂ) (h j : ℕ) : ℂ :=
  let c := z*(j+1)
  (2:ℂ)*form M c a b (fun m n => nativeTerm t (argument c m n) h)/(c:ℂ)

private theorem expanded (M z : ℕ) (t : ℝ) (a b : ℕ → ℂ) (h j : ℕ) :
    matrixEntry M z t a b h j =
      ∑ i∈range (M+1),∑ k∈range (M+1),
        (2*a (M+i)*b (M+k))*pairTerm (M+i) (M+k) z t (h,j) := by
  simp only [matrixEntry,form,pairTerm,mul_sum,sum_div]
  exact sum_congr rfl (fun i _ => sum_congr rfl (fun k _ => by ring))

private theorem matrix_summable {M z : ℕ} (hz : 0<z) {t : ℝ} (ht : 0<t)
    (ht1 : t≤1) (a b : ℕ → ℂ) :
    Summable (fun p : ℕ×ℕ => ‖matrixEntry M z t a b p.1 p.2‖) := by
  let F := fun p : ℕ×ℕ => ∑ i∈range (M+1),∑ k∈range (M+1),
    ‖2*a (M+i)*b (M+k)‖*‖pairTerm (M+i) (M+k) z t p‖
  have S : Summable F := by
    apply summable_sum
    intro i _
    apply summable_sum
    intro k _
    exact (pair_summable (M+i) (M+k) hz ht ht1).const_mul _
  apply S.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  rw [expanded]
  apply (norm_sum_le _ _).trans
  exact sum_le_sum (fun i _ => (norm_sum_le _ _).trans_eq (by simp only [norm_mul]))

/-- An unconditional h/c exchange on the original geometric progression.
The endpoint trace can sum the actual h-rows first. -/
theorem original_height_modulus_fubini {M z : ℕ} (hM : 0<M) (hz : 0<z)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) (a b : ℕ → ℂ) :
    Summable (fun p : ℕ×ℕ => ‖matrixEntry M z t a b p.1 p.2‖) ∧
    (∑' h,∑' j, matrixEntry M z t a b h j) = ∑' j,geometricTerm M z t a b j := by
  have S := matrix_summable (M:=M) hz ht ht1 a b
  refine ⟨S,?_⟩
  have reorder : (∑' h,∑' j,matrixEntry M z t a b h j)=∑' j,∑' h,matrixEntry M z t a b h j :=
    (Summable.tsum_comm (f:=matrixEntry M z t a b) S.of_norm).symm
  rw [reorder]
  apply tsum_congr
  intro j
  let c := z*(j+1)
  have cp : 0<(c:ℝ) := by exact_mod_cast Nat.mul_pos hz (by omega : 0<j+1)
  have pos (i k : ℕ) : 0<argument c (M+i) (M+k) := by
    dsimp only [argument,scale]
    exact mul_pos (mul_pos (div_pos (mul_pos (by norm_num) pi_pos) cp)
      (sqrt_pos.mpr (by exact_mod_cast (show 0<M+i by omega))))
      (sqrt_pos.mpr (by exact_mod_cast (show 0<M+k by omega)))
  have H := hasSum_sum (s:=range (M+1)) fun i _ => hasSum_sum (s:=range (M+1)) fun k _ =>
    ((OriginalHolomorphicBesselOffDiagonal20261113.native_window_eq ht (pos i k)).1.hasSum).mul_left
      ((2*a (M+i)*b (M+k))*(kloosterman c (M+i:ℕ) (M+k:ℕ)/(c:ℂ)))
  have J : HasSum (fun h => matrixEntry M z t a b h j) (geometricTerm M z t a b j) := by
    convert H using 1
    · funext h
      rw [expanded]
      exact sum_congr rfl (fun i _ => sum_congr rfl (fun k _ => by dsimp only [pairTerm,c]; ring))
    · dsimp only [geometricTerm,form,nativeWindow,c]
      rw [sum_div]
      apply sum_congr rfl
      intro i _
      rw [sum_div]
      exact sum_congr rfl (fun k _ => by ring)
  exact J.tsum_eq

end ImbalancedChen.Part3.OriginalHolomorphicHeightModulusFubini20261113
end
