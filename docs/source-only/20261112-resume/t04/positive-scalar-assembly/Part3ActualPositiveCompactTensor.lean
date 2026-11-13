import ImbalancedChen.Part3OriginalPositiveHeightTest
import ImbalancedChen.Part3PrescribedLogTensorExpansion
import ImbalancedChen.Part3ProductConvolutionSecondDerivatives
import Batteries.Tactic.OpenPrivate

/-! The period-64 physical probes of the original row resolve its compact
two-height cutoff. All nonzero terms live in one positive height rectangle. -/
namespace ImbalancedChen.Part3.ActualPositiveCompactTensor20261112
noncomputable section
open Filter Set MeasureTheory Complex
open scoped Topology Classical ContDiff BigOperators
open ProductConvolutionSecondDerivatives20261026a
open P3TwoLogMixed22SourceOnly
open PrescribedLogTensorWindows20261112 PrescribedLogTensorCoefficients20261112
open PrescribedLogTensorExpansion20261112 (productAt product_bound)
open private heightTail heightTail_summable from ImbalancedChen.Part3PrescribedLogTensorExpansion

private def iterate (v : Plane) (F : Plane→ℂ) : ℕ→Plane→ℂ
  | 0 => F
  | n+1 => directional v (iterate v F n)

private theorem iterate_smooth {F : Plane→ℂ} (sm : ContDiff ℝ ∞ F) (v : Plane) (n : ℕ) :
    ContDiff ℝ ∞ (iterate v F n) := by induction n with
    | zero => exact sm
    | succ n ih => exact directional_cinfty ih v

private theorem iterate_compact {F : Plane→ℂ} (hc : HasCompactSupport F) (v : Plane) (n : ℕ) :
    HasCompactSupport (iterate v F n) := by induction n with
    | zero => exact hc
    | succ n ih => exact directional_hasCompactSupport ih v

private theorem iterate_x {F : Plane→ℂ} (sm : ContDiff ℝ ∞ F) (n : ℕ) (x y : ℝ) :
    iterate xDirection F n (x,y)=iteratedDeriv n (fun z => F (z,y)) x := by
  induction n generalizing x with
  | zero => simp [iterate]
  | succ n ih =>
    change directional xDirection _ (x,y)=_
    rw [directional_x_eq_slice (iterate_smooth sm _ n),iteratedDeriv_succ]
    congr 1; funext z; exact ih z

private theorem iterate_y {F : Plane→ℂ} (sm : ContDiff ℝ ∞ F) (n : ℕ) (x y : ℝ) :
    iterate yDirection F n (x,y)=iteratedDeriv n (fun z => F (x,z)) y := by
  induction n generalizing y with
  | zero => simp [iterate]
  | succ n ih =>
    change directional yDirection _ (x,y)=_
    rw [directional_y_eq_slice (iterate_smooth sm _ n),iteratedDeriv_succ]
    congr 1; funext z; exact ih z

theorem jet_decay {H : ℝ→ℝ→ℂ} (sm : ContDiff ℝ ∞ (Function.uncurry H))
    (hc : HasCompactSupport (Function.uncurry H)) (A : ℝ) : JetDecay H A := by
  intro i j
  let F := iterate xDirection (iterate yDirection (Function.uncurry H) j) i
  have eq (x y : ℝ) : F (x,y)=jet H i j x y := by
    rw [F,iterate_x (iterate_smooth sm _ _)]
    change iteratedDeriv i _ x=iteratedDeriv i _ x
    congr 1; funext t; exact iterate_y sm _ _ _
  let w := fun z : Plane => Real.exp (A*(|z.1|+|z.2|))
  have cF := iterate_compact (iterate_compact hc yDirection j) xDirection i
  have sF := iterate_smooth (iterate_smooth sm yDirection j) xDirection i
  have cP : HasCompactSupport (fun z => ‖F z‖*w z) := cF.norm.mul_right
  obtain ⟨B,b⟩ := cP.exists_bound_of_continuousOn (f:=fun z => ‖F z‖*w z)
    ((sF.continuous.norm.mul (by unfold w; fun_prop)).continuousOn)
  refine ⟨max B 0,le_max_right _ _,fun x y => ?_⟩
  by_cases h : F (x,y)=0
  · rw [←eq,h,norm_zero]; positivity
  have m : (x,y)∈tsupport (fun z => ‖F z‖*w z) := subset_tsupport _
    (mul_ne_zero (norm_ne_zero_iff.mpr h) (Real.exp_pos _).ne')
  have H := b (x,y) m
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)] at H
  rw [←eq,neg_mul,Real.exp_neg,← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
  exact H.trans (le_max_left _ _)

theorem absolute (H : ℝ→ℝ→ℂ) (sm : ContDiff ℝ ∞ (Function.uncurry H)) (hc : HasCompactSupport (Function.uncurry H)) :
    Summable (fun q : Modes => ‖coefficient H q‖) := by
  obtain ⟨B,_,h⟩ := coeff_decay H sm zero_le_one (jet_decay sm hc 1)
  have hd := summable_decay.mul_of_nonneg summable_decay (fun _ => by unfold decay; positivity) (fun _ => by unfold decay; positivity)
  have hi := heightTail_summable.mul_of_nonneg heightTail_summable (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  apply ((hi.mul_of_nonneg hd (fun p => by dsimp [heightTail]; positivity) (fun p => by dsimp [decay]; positivity)).mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro q
  have E : tail 1 q.1.1 q.1.2=heightTail q.1.1*heightTail q.1.2 := by unfold tail heightTail; rw [←Real.exp_add]; congr 1; ring
  simpa only [E,mul_assoc] using h q

private theorem cell_sum (H : ℝ→ℝ→ℂ) (sm : ContDiff ℝ ∞ (Function.uncurry H)) (hc : HasCompactSupport (Function.uncurry H)) (i j : ℤ) (x y : ℝ) :
    HasSum (fun kl : ℤ × ℤ => coefficient H ((i,j),kl) * productAt ((i,j),kl) (Real.exp x) (Real.exp y))
      (rho (x-(i:ℝ))*rho (y-(j:ℝ))*H x y) := by
  let v := x-(i:ℝ)
  let u := y-(j:ℝ)
  let G := cellKernel H i j
  have hprod (kl : ℤ × ℤ) : productAt ((i,j),kl) (Real.exp x) (Real.exp y) =
      ((win v:ℂ)*(win u:ℂ))*(basis kl.1 v*basis kl.2 u) := by
    simp only [productAt,rightPattern,star_star,pattern_exp,v,u]; ring
  have hwin (t : ℝ) : (win t : ℂ)*rho t = rho t := by
    by_cases h : rho t = 0
    · simp [h]
    · simp only [win_plateau (Ioo_subset_Icc_self (rho_nonzero h)),Complex.ofReal_one,one_mul]
  have target : ((win v:ℂ)*(win u:ℂ))*G u v = rho v*rho u*H x y := by
    dsimp [G,cellKernel,v,u]
    rw [show (i:ℝ)+(x-(i:ℝ))=x by ring,show (j:ℝ)+(y-(j:ℝ))=y by ring]
    linear_combination (win (y-(j:ℝ)):ℂ)*rho (y-(j:ℝ))*H x y*hwin (x-(i:ℝ)) +
      rho (x-(i:ℝ))*H x y*hwin (y-(j:ℝ))
  by_cases hwu : win u = 0
  · have hr : rho u = 0 := by simpa [hwu] using (hwin u).symm
    change HasSum _ (rho v*rho u*H x y)
    simpa only [hprod,hwu,hr,Complex.ofReal_zero,mul_zero,zero_mul] using
      (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0:ℂ)) 0)
  by_cases hwv : win v = 0
  · have hr : rho v = 0 := by simpa [hwv] using (hwin v).symm
    change HasSum _ (rho v*rho u*H x y)
    simpa only [hprod,hwv,hr,Complex.ofReal_zero,zero_mul,mul_zero] using
      (hasSum_zero : HasSum (fun _ : ℤ × ℤ => (0:ℂ)) 0)
  obtain ⟨B,hB,hb⟩ := cell_budget H sm (A := 0) le_rfl (jet_decay sm hc 0)
  have hu := win_nonzero hwu
  have hv := win_nonzero hwv
  have hs := C2_hasSum G (cell_regularity H sm i j) (cell_support H i j)
    (B*tail 0 i j) (mul_nonneg hB (Real.exp_pos _).le) (hb i j) u v
    ⟨by linarith [hu.1],by linarith [hu.2]⟩ ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have ha := (Equiv.prodComm ℤ ℤ).hasSum_iff.mpr hs
  have hs' := ha.mul_left ((win v:ℂ)*(win u:ℂ))
  rw [target] at hs'
  convert hs' using 1
  funext kl
  simp only [hprod,coefficient,Equiv.prodComm_apply,G,Function.comp_apply]
  ring

theorem reconstruct (H : ℝ→ℝ→ℂ) (sm : ContDiff ℝ ∞ (Function.uncurry H)) (hc : HasCompactSupport (Function.uncurry H)) (x y : ℝ) :
    HasSum (fun q : Modes => coefficient H q*productAt q (Real.exp x) (Real.exp y)) (H x y) := by
  let R := H x y
  have hs : Summable (fun q : Modes => coefficient H q*productAt q (Real.exp x) (Real.exp y)) :=
    (absolute H sm hc).of_norm_bounded (fun q => by
      rw [norm_mul]; simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (product_bound q _ _) (norm_nonneg (coefficient H q)))
  have hxy : (∑' ij : ℤ × ℤ, rho (x-(ij.1:ℝ))*rho (y-(ij.2:ℝ))*R) = R := by
    have hg := hs.prod.congr (fun ij => (cell_sum H sm hc ij.1 ij.2 x y).tsum_eq)
    rw [hg.tsum_prod]
    have hk (i : ℤ) : (∑' j : ℤ, rho (x-(i:ℝ))*rho (y-(j:ℝ))*R) = rho (x-(i:ℝ))*R := by
      simpa only [mul_one] using (((rho_sum y).mul_left (rho (x-(i:ℝ)))).mul_right R).tsum_eq
    simp_rw [hk]
    simpa only [one_mul] using ((rho_sum x).mul_right R).tsum_eq
  apply hs.hasSum_iff.mpr
  rw [hs.tsum_prod]
  calc
    _ = ∑' ij : ℤ × ℤ, rho (x-(ij.1:ℝ))*rho (y-(ij.2:ℝ))*R :=
      tsum_congr (fun ij => (cell_sum H sm hc ij.1 ij.2 x y).tsum_eq)
    _ = _ := hxy


private theorem center_bound {H : ℝ→ℝ→ℂ} (hc : HasCompactSupport (Function.uncurry H)) :
    ∃ B : ℝ,0≤B ∧ ∀ q : Modes,coefficient H q≠0 → |(q.1.1:ℝ)|≤B ∧ |(q.1.2:ℝ)|≤B := by
  obtain ⟨A,M⟩ := hc.exists_bound_of_continuousOn (f:=id) continuous_id.continuousOn
  refine ⟨max A 0+1,by positivity,fun q nz => ?_⟩
  have e : ∃ u v,cellKernel H q.1.1 q.1.2 u v≠0 := by
    by_contra! no
    have K : cellKernel H q.1.1 q.1.2=fun _ _ => 0 := funext (fun u => funext (no u))
    exact nz (by simp [coefficient,K,C2,coeff64_zero])
  obtain ⟨u,v,uv⟩ := e
  have a := mul_ne_zero_iff.mp uv
  have b := mul_ne_zero_iff.mp a.2
  have vv := rho_nonzero a.1
  have uu := rho_nonzero b.1
  have Z := M ((q.1.1:ℝ)+v,(q.1.2:ℝ)+u) (subset_tsupport _ b.2)
  have P := (Prod.norm_fst_le _).trans Z
  have Q := (Prod.norm_snd_le _).trans Z
  rw [Real.norm_eq_abs,abs_le] at P Q
  constructor <;> rw [abs_le] <;> constructor <;> linarith [le_max_left A 0,vv.1,vv.2,uu.1,uu.2]

theorem active_box {H : ℝ→ℝ→ℂ} (hc : HasCompactSupport (Function.uncurry H)) :
    ∃ B : ℝ,0≤B ∧ ∀ q : Modes,coefficient H q≠0 → ∀ a b,productAt q a b≠0 →
      a∈Icc (Real.exp (-B)) (Real.exp B) ∧ b∈Icc (Real.exp (-B)) (Real.exp B) := by
  obtain ⟨A,a,C⟩ := center_bound hc
  refine ⟨A+2,by linarith,fun q hn x y h => ?_⟩
  have h1 := mul_ne_zero_iff.mp h
  have h2 : pattern q.1.2 q.2.2 y≠0 := by simpa [rightPattern] using h1.2
  have X := pattern_support _ _ (subset_tsupport _ h1.1)
  have Y := pattern_support _ _ (subset_tsupport _ h2)
  obtain ⟨i,j⟩ := C q hn
  have a1 := abs_le.mp i; have a2 := abs_le.mp j
  exact ⟨⟨(Real.exp_le_exp.mpr (by linarith : -(A+2)≤(q.1.1:ℝ)-2)).trans X.1,
    X.2.trans (Real.exp_le_exp.mpr (by linarith))⟩,
    ⟨(Real.exp_le_exp.mpr (by linarith : -(A+2)≤(q.1.2:ℝ)-2)).trans Y.1,
    Y.2.trans (Real.exp_le_exp.mpr (by linarith))⟩⟩

end
end ImbalancedChen.Part3.ActualPositiveCompactTensor20261112
