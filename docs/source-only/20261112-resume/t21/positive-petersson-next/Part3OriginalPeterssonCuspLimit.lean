import ImbalancedChen.Part3OriginalHeckeLimitFamily
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace ImbalancedChen.Part3.OriginalPeterssonCuspLimit20261112

noncomputable section
open Set Complex UpperHalfPlane Matrix Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane ModularForm Modular Topology Manifold ComplexConjugate InnerProductSpace
open OriginalHeckeCosetRows20261112 OriginalHeckeRowSlash20261112
open OriginalHolomorphicPoincare20261112 OriginalHeckeCuspSeries20261112
open OriginalHeckeCuspExpansion20261112 OriginalHeckeStripPairing20261112
open OriginalHeckePhysicalRow20261112 OriginalHeckePoisson20261112 OriginalHeckeLimitFamily20261112
open OriginalHolomorphicPeterssonSpace20261112 OriginalPeterssonPretrace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open Gamma0FiniteMeasureCarrier20261024z OriginalHolomorphicCuspFrames20261110

private theorem seed_holo (m : ℕ) : MDiff (heckeSeed m 0) := by
  rw [mdifferentiable_iff]
  apply (show Differentiable ℂ (fun z : ℂ => (exp (2*Real.pi*I*z))^m) by fun_prop).differentiableOn.congr
  intro z hz
  simp [Function.comp_def,ofComplex_apply_of_im_pos hz,heckeSeed,q,Function.Periodic.qParam]

private theorem holo_sum {ι : Type*} (F : ι→ℍ→ℂ) (hF : ∀i, MDiff (F i))
    (bounds : ∀ A H : ℝ, 0<H → ∃ b : ι→ℝ, Summable b ∧
      ∀ i (w:ℍ), w∈verticalStrip A H → ‖F i w‖≤b i) :
    MDiff (fun w : ℍ => ∑' i,F i w) := by
  intro w;rw [mdifferentiableAt_iff]
  let A := |w.re|+1
  let H := w.im/2
  let U := {z : ℂ | |z.re|<A ∧ H<z.im}
  have hH : 0<H := half_pos w.im_pos
  have hU : IsOpen U := (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hp : (w:ℂ)∈U := ⟨by dsimp [A];linarith,by dsimp [H];linarith [w.im_pos]⟩
  obtain ⟨b,hb,hh⟩ := bounds A H hH
  apply (Complex.differentiableOn_tsum_of_summable_norm hb (F:=fun i => F i ∘ ofComplex)
    (fun i => (mdifferentiable_iff.mp (hF i)).mono (fun z hz => hH.trans hz.2)) hU ?_ _ hp).differentiableAt (hU.mem_nhds hp)
  intro i z hz
  apply hh
  rw [mem_verticalStrip_iff,ofComplex_apply_of_im_pos (hH.trans hz.2)]
  exact ⟨hz.1.le,hz.2.le⟩

private def denMatrix {N : ℕ} {g : SL(2,ℤ)} {C : ℕ+} (D : {D : ℤ // gateD N g C D}) : SL(2,ℤ) :=
  matrix (N:=N) (g:=g) ⟨![(C:ℤ),D.val],D.property.1,D.property.2,
    Or.inl (show 0<(C:ℤ) by exact_mod_cast C.property)⟩

private theorem den_bottom {N : ℕ} {g : SL(2,ℤ)} {C : ℕ+} (D : {D : ℤ // gateD N g C D}) :
    Gamma0ParabolicBottomRow20261025a.bottomRow (denMatrix D)=![(C:ℤ),D.val] := row_matrix _

private theorem row_zero_holo {N : ℕ} {g : SL(2,ℤ)} {C : ℕ+} (m r : ℕ)
    (D : {D : ℤ // gateD N g C D}) :
    MDiff (fun w : ℍ => term (2*r) m C D.val (zeroS,w)) := by
  have h : (fun w : ℍ => term (2*r) m C D.val (zeroS,w)) =
      (heckeSeed m 0 ∣[2*(r:ℤ)] denMatrix D) := by
    funext w
    have h' := physical_row r m (denMatrix D) C (congrFun (den_bottom D) 0) (zeroS,w)
    simpa only [show denMatrix D 1 1=D.val from congrFun (den_bottom D) 1] using h'.symm
  rw [h];exact (seed_holo m).slash _ _

private theorem fixed_price {N : ℕ} {g : SL(2,ℤ)} {C : ℕ+} (r m : ℕ) (hr : 0<r)
    (A H : ℝ) (hH : 0<H) (D : {D : ℤ // gateD N g C D}) (w : ℍ) (hw : w∈verticalStrip A H) :
    ‖term (2*r) m C D.val (zeroS,w)‖ ≤
      (EisensteinSeries.r (⟨⟨A,H⟩,hH⟩:ℍ))^(-(2*(r:ℝ)))*freqPrice D.val := by
  let V : Fin 2→ℤ := ![(C:ℤ),D.val]
  have E := physical_row r m (denMatrix D) C (congrFun (den_bottom D) 0) (zeroS,w)
  rw [show denMatrix D 1 1=D.val from congrFun (den_bottom D) 1] at E
  rw [← E]
  have nd : denom (denMatrix D) w=(V 0:ℂ)*w+(V 1:ℂ) := by
    rw [ModularGroup.denom_apply];simp only [show denMatrix D 1 0=(C:ℤ) from congrFun (den_bottom D) 0,
       show denMatrix D 1 1=D.val from congrFun (den_bottom D) 1];rfl
  have H' : ‖(heckeSeed m 0 ∣[2*(r:ℤ)] denMatrix D) w‖ ≤ ‖(V 0:ℂ)*w+V 1‖^(-(2*(r:ℝ))) := by
    simpa only [zero_mul,mul_zero,add_zero,Real.rpow_zero,one_mul,nd] using norm_seed_term r m 0 (denMatrix D) w
  refine H'.trans ((EisensteinSeries.summand_bound_of_mem_verticalStrip (by positivity) V hH hw).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have vc : (C:ℝ)≤‖V‖ := by simpa [V,← Int.norm_cast_real] using norm_le_pi_norm V 0
  have vd : |(D.val:ℝ)|≤‖V‖ := by simpa [V,← Int.norm_cast_real] using norm_le_pi_norm V 1
  have h1 : 1≤‖V‖ := (show (1:ℝ)≤C by exact_mod_cast C.property).trans vc
  have hr' : 1≤(r:ℝ) := by exact_mod_cast hr
  by_cases h0 : D.val=0
  · simpa [freqPrice,h0] using Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith : -(2*(r:ℝ))≤0)
  · have hd : 0<|(D.val:ℝ)| := abs_pos.mpr (by exact_mod_cast h0)
    calc
      _ ≤ ‖V‖^(-(2:ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ ≤ |(D.val:ℝ)|^(-(2:ℝ)) := Real.rpow_le_rpow_of_nonpos hd vd (by norm_num)
      _ = _ := by rw [Real.rpow_neg hd.le,Real.rpow_two,sq_abs];simp [freqPrice,h0,one_div]

theorem den_holo (N r m : ℕ) [NeZero N] (hr : 0<r) (g : SL(2,ℤ)) (C : ℕ+) :
    MDiff (fun w : ℍ => denominator N (2*r) m g C (zeroS,w)) := by
  let F := fun (D : {D : ℤ // gateD N g C D}) (w : ℍ) => term (2*r) m C D.val (zeroS,w)
  have B (A H : ℝ) (hH : 0<H) := ((freqPrice_summable.subtype _).mul_left
    ((EisensteinSeries.r (⟨⟨A,H⟩,hH⟩:ℍ))^(-(2*(r:ℝ)))))
  have hf := holo_sum F (row_zero_holo m r) (fun A H h =>
    ⟨_,B A H h,fun D w hw => fixed_price r m hr A H h D w hw⟩)
  have he (w : ℍ) : (∑' D,F D w)=denominator N (2*r) m g C (zeroS,w) := by
    apply denominator_integer
    apply Summable.of_norm
    apply (B |w.re| w.im w.im_pos).of_nonneg_of_le (fun _ => norm_nonneg _) _
    exact fun D => fixed_price r m hr |w.re| w.im w.im_pos D w (by simp [mem_verticalStrip_iff])
  simpa only [he] using hf

theorem Pzero_holo (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) :
    MDiff (Pzero N r m) := by
  let k := 2*r
  have hk : 2≤k := by dsimp [k];omega
  let F := fun (C : ℕ+) (w : ℍ) => denominator N k m 1 C (zeroS,w)
  have hF := holo_sum F (den_holo N r m hr 1) (by
    intro A H hH
    obtain ⟨b,hb,h0,h⟩ := layer_majorant N k m hk hm hH
    refine ⟨fun C => H^(1-(k:ℝ))*∑' n,b (C,n),hb.prod.mul_left _,fun C w hw => ?_⟩
    have hy := (mem_verticalStrip_iff A H w).mp hw |>.2
    let p : Params := (zeroS,w)
    have ph : w.im^(1-(k:ℝ))≤H^(1-(k:ℝ)) := Real.rpow_le_rpow_of_nonpos hH hy
      (by have hk' : 2≤(k:ℝ) := by exact_mod_cast hk;linarith)
    have l (n : ℤ) : ‖layer N k m 1 (C,n) p‖≤H^(1-(k:ℝ))*b (C,n) :=
      (h 1 (C,n) p hy).trans (mul_le_mul_of_nonneg_right ph (h0 _))
    have B := (hb.prod_factor C).mul_left (H^(1-(k:ℝ)))
    have S := B.of_nonneg_of_le (fun _ => norm_nonneg _) l
    dsimp [F]
    rw [← (denominator_modes N k m hk 1 C p).tsum_eq]
    exact (norm_tsum_le_tsum_norm S).trans ((S.tsum_le_tsum l B).trans_eq (by rw [tsum_mul_left])))
  have d : MDiff (fun w : ℍ => diagonal N m (1:SL(2,ℤ)) (zeroS,w)) := by
    simpa [diagonal,zeroS] using seed_holo m
  have he (w : ℍ) : (∑' C,F C w)=series N k m 1 (zeroS,w) :=
    (denominators_sum N k m hk hm 1 (zeroS,w)).tsum_eq
  simpa only [Pzero,expansion,he] using d.add hF

/-- The actual regularized holomorphic limit as a member of the full original space,
including r=1. Its definition uses the explicit jointly summable series. -/
def cuspLimit (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) : Forms N r where
  toFun := Pzero N r m
  slash_action_eq' a ha := by
    obtain ⟨g,hg,rfl⟩ := Subgroup.mem_map.mp ha
    exact Pzero_automorphic N r m hr hm ⟨g,hg⟩
  holo' := Pzero_holo N r m hr hm
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    exact (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr (fun g _ => zero_at_cusps N r m hr hm g)

theorem cuspLimit_pairing (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (f : Forms N r) :
    inner ℂ (cuspLimit N r m hr hm) f=(mass r m:ℂ)*raw N (NeZero.pos N) r 1 m f := by
  let μ := carrierMeasure N
  letI : IsFiniteMeasure μ := ⟨by simpa [μ,carrierMeasure] using gamma0Carrier_finite N⟩
  obtain ⟨K,hK,h⟩ := global_bound N r m hr hm
  obtain ⟨A,hA⟩ := section_bound f
  let F := fun n => petersson (2*(r:ℤ)) (heckeP N r m (sSeq n).val) f
  have meas (n : ℕ) : Continuous (heckeP N r m (sSeq n).val) := by
    have he (w : ℍ) : heckeP N r m (sSeq n).val w=expansion N r m 1 (sSeq n,w) := by
      simpa only [SlashAction.slash_one] using heckeP_expansion N r m hr hm 1 (sSeq n,w) (sSeq_pos n)
    simpa only [funext he] using
      (joint_continuous N r m hr hm 1).comp (continuous_const.prodMk continuous_id)
  have bound (n : ℕ) (w : ℍ) : ‖F n w‖≤K*A := by
    have W := h n w
    have V := hA w
    simp only [sectionValue,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg w.im_pos.le] at V
    have H := mul_le_mul W V (mul_nonneg (pow_nonneg w.im_pos.le _) (norm_nonneg _)) hK
    simp only [F,petersson,norm_mul,Complex.norm_conj,Complex.norm_real,norm_zpow,
      Real.norm_of_nonneg w.im_pos.le,show 2*(r:ℤ)=((2*r:ℕ):ℤ) by push_cast;rfl,zpow_natCast]
    calc
      _ = (w.im^r*‖heckeP N r m (sSeq n).val w‖)*(w.im^r*‖f w‖) := by rw [two_mul,pow_add];ring
      _ ≤ _ := H
  have L := tendsto_integral_of_dominated_convergence (μ:=μ) (F:=F)
    (f:=petersson (2*(r:ℤ)) (cuspLimit N r m hr hm) f) (fun _ => K*A)
    (fun n => (petersson_continuous _ (meas n) (ModularFormClass.holo f).continuous).aestronglyMeasurable)
    (integrable_const _) (fun n => .of_forall (bound n)) (.of_forall (fun w => by
      have t : Tendsto (fun n => heckeP N r m (sSeq n).val w) atTop (𝓝 (Pzero N r m w)) := by
        simpa only [SlashAction.slash_one,Pzero] using seq_limit N r m hr hm 1 w
      exact ((Complex.continuous_conj.continuousAt.tendsto.comp t).mul_const (f w)).mul_const _))
  have T := (heckeMass_at_zero (r:=r) (m:=m) hr hm).1.tendsto.comp
    (show Tendsto (fun n => (sSeq n).val) atTop (𝓝 0) from tendsto_subtype_rng.mp sSeq_zero)
  have H := (Complex.continuous_ofReal.continuousAt.tendsto.comp T).mul_const (raw N (NeZero.pos N) r 1 m f)
  rw [(heckeMass_at_zero hr hm).2] at H
  rw [inner_integral]
  apply tendsto_nhds_unique L
  exact H.congr (fun n => (hecke_pairing N r hr f hm (sSeq_pos n)).symm)

theorem cuspLimit_eq_Pvector (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) :
    cuspLimit N r m hr hm=Pvector N r 1 m := by
  apply ext_inner_right ℂ
  intro f
  rw [cuspLimit_pairing,Pvector_evaluates]

end
end ImbalancedChen.Part3.OriginalPeterssonCuspLimit20261112
