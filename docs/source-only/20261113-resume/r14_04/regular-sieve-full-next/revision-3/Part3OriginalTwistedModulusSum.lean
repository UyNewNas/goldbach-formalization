import ImbalancedChen.Part3OriginalTwistedKloosterman

/-! The finite small-modulus contribution on the original progression c=zd.
The cutoff is H² zD ≤ M. The oscillatory parameter and damping may vary
with d, independently of the common coefficient vectors. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalTwistedModulusSum20261113
open Complex Finset
open OriginalTwistedKloosterman20261113 (twistedForm twisted_form_bound)
open OriginalTwistedSqrtAnalysis20261113 (budget)

private theorem root_recip_count (D : ℕ) :
    (∑ j∈range D,(Real.sqrt (j+1:ℕ))⁻¹)≤2*Real.sqrt D := by
  induction D with
  | zero => simp
  | succ n ih =>
    let x := Real.sqrt (n:ℝ)
    let y := Real.sqrt (n+1:ℕ)
    have xp : 0≤x := Real.sqrt_nonneg _
    have yp : 0<y := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n+1 by omega))
    have xy : x≤y := Real.sqrt_le_sqrt (by exact_mod_cast (show n≤n+1 by omega))
    have sqx : x^2=n := Real.sq_sqrt (by positivity)
    have sqy : y^2=(n:ℝ)+1 := by
      simpa only [Nat.cast_add,Nat.cast_one] using Real.sq_sqrt (show 0≤((n+1:ℕ):ℝ) by positivity)
    have E : (y-x)*(y+x)=1 := by nlinarith only [sqx,sqy]
    have A : y⁻¹≤2*(y-x) := by
      rw [←one_div,div_le_iff₀ yp]
      have := mul_le_mul_of_nonneg_left (show y+x≤2*y by linarith only [xy]) (sub_nonneg.mpr xy)
      nlinarith only [this,E]
    rw [sum_range_succ]
    change _+y⁻¹≤2*y
    change _≤2*x at ih
    linarith only [ih,A]

def packetEnergy (M : ℕ) (a : ℕ → ℂ) : ℝ :=
  Real.sqrt (∑ i∈range (M+1),‖a (M+i)‖^2)

/-- No height power is paid in this whole progression of physical
Kloosterman sums. The oscillatory parameter remains bounded below by τ
and the coefficient of each transformed sum may have size H. -/
theorem short_modulus_sum {M z D : ℕ} (hz : 0<z) (hM : 0<M) {H τ : ℝ}
    (hH : 1≤H) (hτ : 0<τ) (cut : H^2*z*D≤M) (lam θ : ℕ → ℝ) (w : ℕ → ℂ)
    (hlam : ∀ j<D,0≤lam j) (hθ : ∀ j<D,τ≤θ j ∧ θ j≤2)
    (hw : ∀ j<D,‖w j‖≤H) (a b : ℕ → ℂ) :
    ‖∑ j∈range D,w j / ((z*(j+1):ℕ):ℂ)*
      twistedForm M (z*(j+1)) (lam j) (θ j) a b‖ ≤
      2*Real.exp (4*Real.pi)*Real.sqrt (244*(1+Real.log M)/τ)*
        ((M:ℝ)/z)*packetEnergy M a*packetEnergy M b := by
  let Q := Real.sqrt (244*(1+Real.log M)/τ)
  let A := packetEnergy M a
  let B := packetEnergy M b
  have zp : 0<(z:ℝ) := by exact_mod_cast hz
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have M1 : 1≤(M:ℝ) := by exact_mod_cast (show 1≤M by omega)
  have lp := Real.log_nonneg M1
  have hp := zero_lt_one.trans_le hH
  have h2 : 1≤H^2 := by nlinarith only [hH,sq_nonneg (H-1)]
  have zD : (z:ℝ)*D≤M := by
    have h := mul_le_mul_of_nonneg_right h2 (show 0≤(z:ℝ)*D by positivity)
    linarith only [h,cut]
  have zDn : z*D≤M := by exact_mod_cast zD
  have Bmono {t : ℝ} (ht : τ≤t) : budget M t≤(M:ℝ)*Q^2 := by
    have R := div_le_div_of_nonneg_left (show 0≤244*(M:ℝ)*(1+Real.log M) by positivity) hτ ht
    dsimp only [budget,Q]
    rw [Real.sq_sqrt (by positivity)]
    convert R using 1 <;> ring
  let F := H*Real.exp (4*Real.pi)*Q*Real.sqrt M*(Real.sqrt z)⁻¹*A*B
  have A0 : 0≤A := Real.sqrt_nonneg _
  have B0 : 0≤B := Real.sqrt_nonneg _
  have Q0 : 0≤Q := Real.sqrt_nonneg _
  have F0 : 0≤F := by dsimp only [F]; positivity
  have one (j : ℕ) (hj : j<D) :
      ‖w j/((z*(j+1):ℕ):ℂ)*twistedForm M (z*(j+1)) (lam j) (θ j) a b‖≤
        F*(Real.sqrt (j+1:ℕ))⁻¹ := by
    let c := z*(j+1)
    have cn : 0<c := Nat.mul_pos hz (by omega)
    letI : NeZero c := ⟨cn.ne'⟩
    have cp : 0<(c:ℝ) := by exact_mod_cast cn
    have cM : c≤M := (Nat.mul_le_mul_left z (show j+1≤D by omega)).trans zDn
    have ht := hθ j hj
    have T := twisted_form_bound (c:=c) cM (hlam j hj) (hτ.trans_le ht.1) ht.2 a b
    have BS := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Bmono ht.1) cp.le)
    have fact : Real.sqrt ((c:ℝ)*((M:ℝ)*Q^2))=Real.sqrt c*(Real.sqrt M*Q) := by
      rw [Real.sqrt_mul cp.le,Real.sqrt_mul mp.le,Real.sqrt_sq Q0]
    rw [fact] at BS
    have vc := div_le_div_of_nonneg_right (hw j hj) cp.le
    change ‖w j/(c:ℂ)*twistedForm M c (lam j) (θ j) a b‖≤_
    rw [norm_mul,norm_div,Complex.norm_natCast]
    have U := mul_le_mul vc T (norm_nonneg _) (div_nonneg hp.le cp.le)
    apply U.trans
    have V := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right BS A0) B0)
      (show 0≤H/(c:ℝ)*Real.exp (4*Real.pi) by positivity)
    change H/(c:ℝ)*(Real.exp (4*Real.pi)*(Real.sqrt ((c:ℝ)*budget M (θ j))*A*B))≤_
    calc
      _≤(H/(c:ℝ)*Real.exp (4*Real.pi))*(Real.sqrt c*(Real.sqrt M*Q)*A*B) := by
        convert V using 1 <;> ring
      _=_ := by
        have ccast : (c:ℝ)=(z:ℝ)*(j+1:ℕ) := by dsimp only [c];push_cast;ring
        have zj := Real.sqrt_pos.mpr zp
        have ij : 0<Real.sqrt (j+1:ℕ) := Real.sqrt_pos.mpr (by positivity)
        have Es : Real.sqrt c=Real.sqrt z*Real.sqrt (j+1:ℕ) := by
          rw [ccast,Real.sqrt_mul zp.le]
        have Ec : (c:ℝ)=(Real.sqrt z)^2*(Real.sqrt (j+1:ℕ))^2 := by
          rw [ccast,Real.sq_sqrt zp.le,Real.sq_sqrt (by positivity)]
        dsimp only [F]
        rw [Es,Ec]
        field_simp [zj.ne',ij.ne'] <;>ring
  have cutroot : H*Real.sqrt z*Real.sqrt D≤Real.sqrt M := by
    have U := Real.sqrt_le_sqrt cut
    rwa [Real.sqrt_mul (mul_nonneg (sq_nonneg H) zp.le),Real.sqrt_mul (sq_nonneg H),
      Real.sqrt_sq hp.le] at U
  have U := mul_le_mul_of_nonneg_left (root_recip_count D) F0
  have L := (norm_sum_le (range D) (fun j => w j / ((z*(j+1):ℕ):ℂ)*
    twistedForm M (z*(j+1)) (lam j) (θ j) a b)).trans
    (sum_le_sum (fun j hj => one j (mem_range.mp hj)))
  rw [←mul_sum] at L
  apply (L.trans U).trans
  have R := mul_le_mul_of_nonneg_right cutroot
    (show 0≤2*Real.exp (4*Real.pi)*Q*Real.sqrt M*A*B by positivity)
  apply (mul_le_mul_iff_left₀ zp).mp
  let T := 2*Real.exp (4*Real.pi)*Q*Real.sqrt M*A*B
  have zz := Real.sq_sqrt zp.le
  have zm := Real.sq_sqrt mp.le
  have zn := (Real.sqrt_pos.mpr zp).ne'
  have leftE : F*(2*Real.sqrt D)*(z:ℝ)=(H*Real.sqrt z*Real.sqrt D)*T := by
    dsimp only [F,T]
    conv_lhs => arg 2; rw [←zz]
    field_simp [zn] <;>ring
  have rightE : (2*Real.exp (4*Real.pi)*Q*((M:ℝ)/z)*A*B)*z=Real.sqrt M*T := by
    dsimp only [T]
    have E : (2*Real.exp (4*Real.pi)*Q*((M:ℝ)/z)*A*B)*z=
        2*Real.exp (4*Real.pi)*Q*(M:ℝ)*A*B := by field_simp [zp.ne'] <;>ring
    rw [E]
    conv_lhs => rw [←zm]
    ring
  change F*(2*Real.sqrt D)*(z:ℝ)≤(2*Real.exp (4*Real.pi)*Q*((M:ℝ)/z)*A*B)*z
  rw [leftE,rightE]
  exact R

end ImbalancedChen.Part3.OriginalTwistedModulusSum20261113
end
