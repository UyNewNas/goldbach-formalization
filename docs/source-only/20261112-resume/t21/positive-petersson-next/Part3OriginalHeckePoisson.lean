import ImbalancedChen.Part3OriginalHeckeCuspSeries
import Mathlib.Analysis.Fourier.PoissonSummation

namespace ImbalancedChen.Part3.OriginalHeckePoisson20261112

noncomputable section
open Set Filter MeasureTheory Complex AddCircle Asymptotics Matrix
open scoped MatrixGroups UpperHalfPlane FourierTransform Topology
open OriginalHolomorphicCuspFilter20261112 OriginalHeckeFourierKernel20261112
open OriginalHeckeCuspSeries20261112 P3Period64NativeReconstructionSourceOnly (e e_add norm_e)

private theorem dilation (f : ℝ→ℂ) {b : ℝ} (hb : 0<b) (t : ℝ) :
    𝓕 (fun x => f (b*x)) t = (b⁻¹:ℝ) • (𝓕 f (t/b)) := by
  simp only [Real.fourier_real_eq_integral_exp_smul]
  let F := fun u : ℝ => Complex.exp (((-2*Real.pi*u*(t/b):ℝ):ℂ)*I) • f u
  have h (x : ℝ) : -2*Real.pi*(b*x)*(t/b) = -2*Real.pi*x*t := by field_simp;ring
  have H := Measure.integral_comp_mul_left F b
  simp only [F,h,abs_of_pos (inv_pos.mpr hb)] at H
  exact H

private theorem kernel_decay (k : ℕ) (hk : 2≤k) {s M b : ℝ}
    (hs : 0≤s) (hM : 0≤M) (hb : 0<b) :
    (fun x : ℝ => kernel k s M (b*x)) =O[cocompact ℝ] (fun x:ℝ => |x|^(-(2:ℝ))) := by
  rw [isBigO_iff]
  refine ⟨(b^2)⁻¹,?_⟩
  filter_upwards [cocompact_le_cofinite (eventually_cofinite_ne (0:ℝ))] with x hx
  refine (kernel_le hk hs hM (b*x)).trans ?_
  rw [Real.rpow_neg (abs_nonneg _)]
  norm_num only [Real.rpow_two,sq_abs,Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg x))]
  dsimp only [column]
  rw [← mul_inv,← mul_pow]
  exact inv_anti₀ (sq_pos_of_ne_zero (mul_ne_zero hb.ne' hx)) (by linarith)

/-- Every horizontal translate at this actual denominator, with the real scaling y/N. -/
theorem periodization (N k m : ℕ) [NeZero N] (hk : 2≤k) (C : ℕ+) (p : Params) (x : ℝ) :
    HasSum (fun n : ℤ => ((p.2.im/N:ℝ):ℂ) * transformed N k m C n p *
        e ((n:ℝ)*x/N))
      (∑' l : ℤ,kernel k p.1.val (Mval m C p.2) ((x+(l:ℝ)*N)/p.2.im)) := by
  let b : ℝ := N/p.2.im
  have hn : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  have hb : 0<b := div_pos hn p.2.im_pos
  let K := kernel k p.1.val (Mval m C p.2)
  let F := fun x : ℝ => K (b*x)
  have hf : Continuous F :=
    (show Differentiable ℝ K from fun u => (kernel_D ..).differentiableAt).continuous.comp (by fun_prop)
  have D (n:ℤ) : 𝓕 F (n:ℝ) = ((p.2.im/N:ℝ):ℂ)*transformed N k m C n p := by
    rw [dilation K hb]
    simp only [transformed,sample,b,inv_div,Complex.real_smul]
    congr 2 <;> ring
  obtain ⟨A,hA,hA'⟩ := transformed_price N k m hk p.2.im_pos
  have hF : Summable fun n:ℤ => ‖𝓕 F (n:ℝ)‖ := by
    apply (freqPrice_summable.mul_left ((p.2.im/N)*A)).of_nonneg_of_le (fun _ => norm_nonneg _) _
    intro n
    rw [D,norm_mul,Complex.norm_real,Real.norm_of_nonneg (div_nonneg p.2.im_pos.le hn.le),mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA' C n p le_rfl) (div_nonneg p.2.im_pos.le hn.le)
  have H := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hf (by norm_num : 1<(2:ℝ))
    (kernel_decay k hk p.1.property.1 (by dsimp [Mval];positivity) hb) hF.of_norm (x/N)
  have hz (l : ℤ) : F (x/N+l) = K ((x+(l:ℝ)*N)/p.2.im) := by
    dsimp [F,b];congr 1;field_simp [p.2.im_ne_zero,hn.ne'] <;>ring
  have he (n:ℤ) : fourier (T:=1) n ((x/(N:ℝ):ℝ):UnitAddCircle) = e ((n:ℝ)*x/N) := by
    rw [fourier_coe_apply]; dsimp [e];push_cast;congr 1;ring
  have ht : Summable fun n:ℤ => 𝓕 F n * e ((n:ℝ)*x/N) := by
    apply Summable.of_norm
    simpa only [norm_mul,norm_e,mul_one] using hF
  simp_rw [hz,he] at H
  rw [H]
  simpa only [D] using ht.hasSum

def denominator (N k m : ℕ) [NeZero N] (g : SL(2,ℤ)) (C : ℕ+) (p : Params) : ℂ :=
  let y := p.2.im
  let s := p.1.val
  let factor := ((1/(C:ℝ)^k*(C:ℝ)^(-2*s)*y^(-(k:ℝ)-s):ℝ):ℂ)
  factor * ∑ u : ZMod (C:ℕ), if IsUnit u then ∑ j : ZMod N,
    if (N:ℤ)∣(C:ℤ)*g 1 1 - Dval C u j*g 1 0 then
      chi C ((m:ℤ)*(u⁻¹).val) * ∑' l : ℤ,
        kernel k s (Mval m C p.2) ((p.2.re+(Dval C u j:ℝ)/(C:ℝ)+(l:ℝ)*N)/y)
    else 0 else 0

theorem denominator_modes (N k m : ℕ) [NeZero N] (hk : 2≤k) (g : SL(2,ℤ)) (C : ℕ+)
    (p : Params) : HasSum (fun n : ℤ => layer N k m g (C,n) p) (denominator N k m g C p) := by
  classical
  let x := p.2.re
  let y := p.2.im
  let s := p.1.val
  let P := fun (u : ZMod (C:ℕ)) (j : ZMod N) => x+(Dval C u j:ℝ)/(C:ℝ)
  let gate := fun (u : ZMod (C:ℕ)) (j : ZMod N) =>
    (N:ℤ)∣(C:ℤ)*g 1 1 - Dval C u j*g 1 0
  let K := kernel k s (Mval m C p.2)
  let A := fun (u : ZMod (C:ℕ)) (j : ZMod N) =>
    if IsUnit u ∧ gate u j then chi C ((m:ℤ)*(u⁻¹).val) else 0
  let G : ℂ := ((1/(C:ℝ)^k*(C:ℝ)^(-2*s)*y^(-(k:ℝ)-s):ℝ):ℂ)
  have hsum := (hasSum_sum (s:=Finset.univ) (fun u _ =>
    hasSum_sum (s:=Finset.univ) (fun j _ =>
      (periodization N k m hk C p (P u j)).mul_left (A u j)))).mul_left G
  have hval : denominator N k m g C p = G*∑ u,∑ j,A u j*∑' l:ℤ,K ((P u j+(l:ℝ)*N)/y) := by
    unfold denominator
    congr 1
    apply Finset.sum_congr rfl; intro u _
    by_cases hu : IsUnit u
    · simp only [hu,if_true,A,true_and]
      apply Finset.sum_congr rfl;intro j _
      by_cases h : gate u j <;> simp [gate] at h ⊢ <;> simp [h,P,K,x,y,s]
    · simp [A,hu]
  rw [hval]
  apply hsum.congr_fun
  intro n
  symm
  have E (u : ZMod (C:ℕ)) (j : ZMod N) :
      e ((n:ℝ)*P u j/N)=e ((n:ℝ)*x/N)*e ((n:ℝ)*(Dval C u j:ℝ)/((C:ℝ)*N)) := by
    rw [← e_add]; dsimp [P];congr 1;ring
  have hS : (∑ u,∑ j,A u j*e ((n:ℝ)*(Dval C u j:ℝ)/((C:ℝ)*N))) = cuspSum N C g m n := by
    unfold cuspSum
    apply Finset.sum_congr rfl;intro u _
    by_cases hu : IsUnit u
    · simp only [A,hu,true_and,if_true]
      apply Finset.sum_congr rfl;intro j _
      by_cases h : gate u j <;> simp [h,gate,residuePhase,mul_comm] at *
    · simp [A,hu]
  have Y : y^(-(k:ℝ)-s)*y = y^(1-(k:ℝ))*y^(-s) := by
    rw [← Real.rpow_add p.2.im_pos,← Real.rpow_add_one p.2.im_ne_zero]
    congr 1;ring
  simp_rw [E]
  rw [layer,← hS]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro u _
  apply Finset.sum_congr rfl;intro j _
  dsimp only [G,x,y,s] at Y ⊢
  push_cast
  have Y' := congrArg Complex.ofReal Y
  push_cast at Y'
  linear_combination (A u j * ((1:ℂ)/(C:ℂ)^k) * (((C:ℝ)^(-2*p.1.val):ℝ):ℂ) *
    e ((n:ℝ)*p.2.re/N) * e ((n:ℝ)*(Dval C u j:ℝ)/((C:ℝ)*N)) *
    transformed N k m C n p /(N:ℂ)) * Y'

/-- These are the grouped genuine positive-denominator sums before horizontal Fourier
expansion. The complete series converges jointly through s=0 on every height half-plane. -/
theorem denominators_sum (N k m : ℕ) [NeZero N] (hk : 2≤k) (hm : 0<m) (g : SL(2,ℤ))
    (p : Params) : HasSum (fun C : ℕ+ => denominator N k m g C p) (series N k m g p) := by
  obtain ⟨b,hb,h0,h⟩ := layer_majorant N k m hk hm (H:=p.2.im) p.2.im_pos
  have S := ((hb.mul_left (p.2.im^(1-(k:ℝ)))).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => h g i p le_rfl)).of_norm
  have hs := S.hasSum.prod_fiberwise (fun C => denominator_modes N k m hk g C p)
  exact hs

end
end ImbalancedChen.Part3.OriginalHeckePoisson20261112
