import ImbalancedChen.Part3OriginalIntervalFoldedKloosterman
import ImbalancedChen.Part3OriginalTwistedSqrtTaylor

/-! A rectangle in the physical double sum for the unrestricted-θ
Kloosterman bound. Both anchors depend on the rectangle. Only its
quadratic cross variation is constrained. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalTwistedRectangle20261113
open Complex Finset
open OAI.Problem337.ExponentialSum (phase phase_norm)
open OriginalSmoothPoissonTail (kloosterman)
open OriginalIntervalFoldedKloosterman20261113 (intervalEnergy rectangular_bound)
open OriginalTwistedSqrtTaylor20261113 (fullFactor weightBill weightBill_sum weightBill_nonneg)

private theorem root_width {M A m H : ℝ} (hM : 0<M) (hA : M≤A)
    (hm : A≤m) (hi : m-A≤H) :
    Real.sqrt m-Real.sqrt A≤H/(2*Real.sqrt M) := by
  have xp := Real.sqrt_pos.mpr hM
  have r := Real.sqrt_le_sqrt hA
  have s := Real.sqrt_le_sqrt hm
  have d : 2*Real.sqrt M≤Real.sqrt m+Real.sqrt A := by linarith only [r,s]
  have p := mul_le_mul_of_nonneg_left d (sub_nonneg.mpr s)
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [p,Real.sq_sqrt (hM.trans_le hA).le,Real.sq_sqrt ((hM.trans_le hA).trans_le hm).le,hi]

private def slope (lam θ c d y v : ℝ) : ℂ :=
  (-(lam*d*(y-v)):ℝ)+(4*Real.pi*θ/c*d*(y-v):ℝ)*I
private def lhs (lam θ c d y v w : ℝ) (j : ℕ) : ℂ :=
  fullFactor lam θ c y w*(slope lam θ c d y v)^j/(j.factorial:ℂ)
private def rhs (lam θ c d n v w : ℝ) (j : ℕ) : ℂ :=
  fullFactor lam θ c v (n-w)*(((n-w)/d:ℝ):ℂ)^j

private theorem expansion (lam θ c d y n v w : ℝ) (hd : 0<d) :
    HasSum (fun j : ℕ => lhs lam θ c d y v w j*rhs lam θ c d n v w j)
      (fullFactor lam θ c y n) := by
  let p := fullFactor lam θ c y w
  let q := fullFactor lam θ c v (n-w)
  let z := slope lam θ c d y v
  let t : ℂ := ((n-w)/d:ℝ)
  have H : HasSum (fun j : ℕ => (z*t)^j/j.factorial) (exp (z*t)) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z*t)
  have E : p*q*exp (z*t)=fullFactor lam θ c y n := by
    dsimp only [p,q,z,t,slope,fullFactor,phase]
    simp only [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    push_cast
    have dc : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
    field_simp [dc] <;> ring
  rw [←E]
  apply (H.mul_left (p*q)).congr_fun
  intro j
  simp only [p,q,z,t,lhs,rhs,mul_pow];ring

private theorem lhs_norm {M : ℕ} {lam θ c d y v w : ℝ} (hlam : 0≤lam)
    (hd : 0≤d) (hdy : 0≤y-v) (h1 : d*(y-v)≤M) (h2 : |4*Real.pi*θ/c*d*(y-v)|≤4*Real.pi)
    (hy : (M:ℝ)≤y*w) (j : ℕ) : ‖lhs lam θ c d y v w j‖≤weightBill M lam j := by
  have z : ‖slope lam θ c d y v‖≤lam*M+4*Real.pi := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_neg,
      abs_of_nonneg (mul_nonneg (mul_nonneg hlam hd) hdy)]
    have u := mul_le_mul_of_nonneg_left h1 hlam
    exact add_le_add (by linarith only [u]) h2
  have p : Real.exp (-lam*y*w)≤Real.exp (-lam*M) := Real.exp_le_exp.mpr (by
    have := mul_le_mul_of_nonneg_left hy hlam; linarith only [this])
  simp only [lhs,fullFactor,weightBill,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),phase_norm,mul_one,norm_pow,Complex.norm_natCast]
  rw [←mul_div_assoc]
  exact div_le_div_of_nonneg_right
    (mul_le_mul p (pow_le_pow_left₀ (norm_nonneg _) z _) (by positivity) (Real.exp_pos _).le)
    (by positivity)

private theorem rhs_norm {lam θ c d n v w : ℝ} (hlam : 0≤lam) (hd : 0<d)
    (hn : 0≤n-w) (h1 : n-w≤d) (hv : 0≤v) (j : ℕ) : ‖rhs lam θ c d n v w j‖≤1 := by
  have t0 := div_nonneg hn hd.le
  have t1 : (n-w)/d≤1 := (div_le_one hd).mpr h1
  have e1 : Real.exp (-lam*v*(n-w))≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) hv) hn)
  simp only [rhs,fullFactor,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    phase_norm,mul_one,norm_pow,abs_of_nonneg t0]
  exact mul_le_one₀ e1 (pow_nonneg t0 _) (pow_le_one₀ t0 t1)

def rect (c A B D E : ℕ) (lam θ : ℝ) (a b : ℕ → ℂ) : ℂ :=
  ∑ m∈Ico A B,∑ n∈Ico D E,
    (a m*b n*kloosterman c (m:ℤ) (n:ℤ))*fullFactor lam θ c (Real.sqrt m) (Real.sqrt n)

theorem rectangular_twisted_bound {M c H A B D E : ℕ} [NeZero c] (hM : 0<M)
    (hH : 0<H) (hHM : H≤M) (hAB : A≤B) (hDE : D≤E)
    (hMA : M≤A) (hMD : M≤D) (h1 : B-A≤H) (h2 : E-D≤H)
    {lam θ : ℝ} (hlam : 0≤lam) (hθ : 0≤θ) (cross : θ*(H:ℝ)^2≤c*(M:ℝ))
    (a b : ℕ → ℂ) :
    ‖rect c A B D E lam θ a b‖ ≤ Real.exp (4*Real.pi)*
      (((c:ℝ)+H)*Real.sqrt (intervalEnergy A B a)*Real.sqrt (intervalEnergy D E b)) := by
  let x := Real.sqrt (M:ℝ)
  let d : ℝ := H/(2*x)
  let v := Real.sqrt (A:ℝ)
  let w := Real.sqrt (D:ℝ)
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have hp : 0<(H:ℝ) := by exact_mod_cast hH
  have cp : 0<(c:ℝ) := by exact_mod_cast NeZero.pos c
  have xp : 0<x := Real.sqrt_pos.mpr mp
  have dp : 0<d := div_pos hp (mul_pos (by norm_num) xp)
  have xp2 : x^2=M := Real.sq_sqrt mp.le
  have d2 : d^2=(H:ℝ)^2/(4*M) := by
    dsimp only [d]
    rw [div_pow,mul_pow,xp2]
    norm_num
  have dx : d^2≤M := by
    rw [d2,div_le_iff₀ (by positivity)]
    have t : (H:ℝ)≤M := by exact_mod_cast hHM
    nlinarith only [mul_self_le_mul_self hp.le t,sq_nonneg (M:ℝ)]
  have dt : θ*d^2≤c := by
    rw [d2,←mul_div_assoc,div_le_iff₀ (by positivity)]
    nlinarith only [cross,mul_nonneg cp.le mp.le]
  have inL (m : ℕ) (hm : m∈Ico A B) : Real.sqrt m-v∈Set.Icc 0 d := by
    obtain ⟨ham,hmb⟩ := mem_Ico.mp hm
    refine ⟨sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast ham)),?_⟩
    apply root_width mp (by exact_mod_cast hMA) (by exact_mod_cast ham)
    have hi : m≤H+A := by omega
    have hi' : (m:ℝ)≤H+(A:ℝ) := by exact_mod_cast hi
    linarith only [hi']
  have inR (n : ℕ) (hn : n∈Ico D E) : Real.sqrt n-w∈Set.Icc 0 d := by
    obtain ⟨hdn,hne⟩ := mem_Ico.mp hn
    refine ⟨sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast hdn)),?_⟩
    apply root_width mp (by exact_mod_cast hMD) (by exact_mod_cast hdn)
    have hi : n≤H+D := by omega
    have hi' : (n:ℝ)≤H+(D:ℝ) := by exact_mod_cast hi
    linarith only [hi']
  let L := fun j m => a m*lhs lam θ c d (Real.sqrt m) v w j
  let R := fun j n => b n*rhs lam θ c d (Real.sqrt n) v w j
  let F := fun j => ∑ m∈Ico A B,∑ n∈Ico D E,L j m*R j n*kloosterman c (m:ℤ) (n:ℤ)
  have series : HasSum F (rect c A B D E lam θ a b) := by
    have S := hasSum_sum (s:=Ico A B) fun m _ => hasSum_sum (s:=Ico D E) fun n _ =>
      (expansion lam θ c d (Real.sqrt m) (Real.sqrt n) v w dp).mul_left (a m*b n*kloosterman c (m:ℤ) (n:ℤ))
    apply S.congr_fun
    intro j
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    dsimp [F,L,R]
    ring
  have terms (j : ℕ) : ‖F j‖≤weightBill M lam j*
      (((c:ℝ)+H)*Real.sqrt (intervalEnergy A B a)*Real.sqrt (intervalEnergy D E b)) := by
    have w0 := weightBill_nonneg M hlam j
    have EA : intervalEnergy A B (L j)≤(weightBill M lam j)^2*intervalEnergy A B a := by
      unfold intervalEnergy
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      have g := inL m hm
      have e : d*(Real.sqrt m-v)≤d^2 := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_left g.2 dp.le
      have theta : θ*(d*(Real.sqrt m-v))≤c := (mul_le_mul_of_nonneg_left e hθ).trans dt
      have phasebd : |4*Real.pi*θ/c*d*(Real.sqrt m-v)|≤4*Real.pi := by
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) dp.le) g.1)]
        have tt := mul_le_mul_of_nonneg_left theta (show 0≤4*Real.pi by positivity)
        apply (mul_le_mul_iff_left₀ cp).mp
        convert tt using 1 <;> field_simp [cp.ne'] <;> ring
      have lo := (mem_Ico.mp hm).1
      have leftM : x≤Real.sqrt m := Real.sqrt_le_sqrt (by exact_mod_cast hMA.trans lo)
      have rightM : x≤w := Real.sqrt_le_sqrt (by exact_mod_cast hMD)
      have mass : (M:ℝ)≤Real.sqrt m*w := by
        have := mul_le_mul leftM rightM xp.le (Real.sqrt_nonneg _)
        nlinarith only [this,xp2]
      have T := lhs_norm hlam dp.le g.1 (e.trans dx) phasebd mass j
      dsimp only [L]
      rw [norm_mul,mul_pow,mul_comm ((weightBill M lam j)^2)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) T 2) (sq_nonneg _)
    have EB : intervalEnergy D E (R j)≤intervalEnergy D E b := by
      apply sum_le_sum
      intro n hn
      have g := inR n hn
      have T := rhs_norm (θ:=θ) (c:=c) hlam dp g.1 g.2 (Real.sqrt_nonneg _) j
      dsimp only [R]
      rw [norm_mul,mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) T)
    have U := Real.sqrt_le_sqrt EA
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (weightBill_nonneg M hlam j)] at U
    have V := Real.sqrt_le_sqrt EB
    apply (rectangular_bound hAB hDE h1 h2 (L j) (R j)).trans
    have T := mul_le_mul (mul_le_mul_of_nonneg_left U (show 0≤(c:ℝ)+H by positivity))
      V (Real.sqrt_nonneg _) (by positivity)
    convert T using 1 <;>ring
  exact series.norm_le_of_bounded ((weightBill_sum M lam).mul_right _) terms

end ImbalancedChen.Part3.OriginalTwistedRectangle20261113
end
