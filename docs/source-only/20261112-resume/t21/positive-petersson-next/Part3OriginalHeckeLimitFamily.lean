import ImbalancedChen.Part3OriginalHeckeCuspExpansion
import Mathlib.NumberTheory.ModularForms.Bounds

namespace ImbalancedChen.Part3.OriginalHeckeLimitFamily20261112

noncomputable section
open Set Complex UpperHalfPlane Matrix Filter
open scoped MatrixGroups UpperHalfPlane ModularForm Modular Topology
open OriginalHolomorphicPoincare20261112 OriginalHeckeCuspSeries20261112
open OriginalHeckeCuspExpansion20261112 OriginalHeckeStripPairing20261112

def zeroS : Icc (0:ℝ) 1 := ⟨0,by simp⟩
def sSeq (n : ℕ) : Icc (0:ℝ) 1 :=
  ⟨1/((n:ℝ)+1),by constructor
                    · positivity
                    · rw [div_le_one (by positivity)];positivity⟩

theorem sSeq_pos (n : ℕ) : 0<(sSeq n).val := by unfold sSeq;positivity
theorem sSeq_zero : Tendsto sSeq atTop (𝓝 zeroS) :=
  tendsto_subtype_rng.mpr tendsto_one_div_add_atTop_nhds_zero_nat

def Pzero (N r m : ℕ) [NeZero N] (w : ℍ) : ℂ := expansion N r m 1 (zeroS,w)

theorem joint_continuous (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (g : SL(2,ℤ)) :
    Continuous (expansion N r m g) := by
  apply continuous_iff_continuousAt.mpr;intro p
  have hd : Continuous (diagonal N m g) := by
    unfold diagonal;split_ifs
    · unfold heckeSeed q Function.Periodic.qParam
      fun_prop (disch := positivity)
    · exact continuous_const
  apply hd.continuousAt.add
  let H := p.2.im/2
  have hH : 0<H := by dsimp [H];positivity
  apply (series_continuous_above N (2*r) m g (by omega) hm hH p (by dsimp [H];linarith [p.2.im_pos])).continuousAt
  exact mem_of_superset ((isOpen_lt continuous_const (continuous_im.comp continuous_snd)).mem_nhds
    (show H<p.2.im by dsimp [H];linarith [p.2.im_pos])) (fun a h => h.le)

theorem seq_limit (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (g : SL(2,ℤ)) (w : ℍ) :
    Tendsto (fun n => (heckeP N r m (sSeq n).val ∣[2*(r:ℤ)] g) w) atTop
      (𝓝 (expansion N r m g (zeroS,w))) := by
  have H := (joint_continuous N r m hr hm g).continuousAt.tendsto.comp
    (sSeq_zero.prodMk_nhds (tendsto_const_nhds (x:=w)))
  exact H.congr (fun n => (heckeP_expansion N r m hr hm g (sSeq n,w) (sSeq_pos n)).symm)

theorem Pzero_slash (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (g : SL(2,ℤ)) (w : ℍ) :
    (Pzero N r m ∣[2*(r:ℤ)] g) w=expansion N r m g (zeroS,w) := by
  have H : Tendsto (fun n => heckeP N r m (sSeq n).val (g • w)) atTop (𝓝 (Pzero N r m (g • w))) := by
    simpa only [SlashAction.slash_one,Pzero] using seq_limit N r m hr hm 1 (g • w)
  have T := seq_limit N r m hr hm g w
  simp only [ModularForm.SL_slash_apply] at T ⊢
  exact tendsto_nhds_unique (H.mul_const (denom g w^(-(2*(r:ℤ))))) T

theorem Pzero_automorphic (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m)
    (g : CongruenceSubgroup.Gamma0 N) : (Pzero N r m ∣[2*(r:ℤ)] (g:SL(2,ℤ)))=Pzero N r m := by
  funext w;rw [Pzero_slash N r m hr hm]
  apply tendsto_nhds_unique (seq_limit N r m hr hm g w)
  simpa only [OriginalHeckeRowSlash20261112.heckeP_automorphic,SlashAction.slash_one,Pzero]
    using seq_limit N r m hr hm 1 w

theorem weighted_slash (r : ℕ) (f : ℍ→ℂ) (g : SL(2,ℤ)) (w : ℍ) :
    (g • w).im^r*‖f (g • w)‖=w.im^r*‖(f ∣[2*(r:ℤ)] g) w‖ := by
  rw [ModularGroup.im_smul_eq_div_normSq,Complex.normSq_eq_norm_sq,ModularForm.SL_slash_apply,
    norm_mul,norm_zpow,div_pow,zpow_neg,show 2*(r:ℤ)=((2*r:ℕ):ℤ) by push_cast;rfl,zpow_natCast,
    pow_mul]
  ring

private theorem poly_exp_bounds (r : ℕ) {c : ℝ} (hc : 0<c) :
    ∃ K : ℝ, ∀ y : ℝ, 0<y → y^r*(1+y)*Real.exp (-(c*y))≤K := by
  have hb (j : ℕ) (y : ℝ) (hy : 0<y) :
      y^j*Real.exp (-(c*y))≤(j.factorial:ℝ)/c^j := by
    have h := Real.pow_div_factorial_le_exp (mul_nonneg hc.le hy.le) j
    rw [Real.exp_neg]
    field_simp [hc.ne',(Real.exp_pos _).ne',Nat.factorial_ne_zero] at h ⊢
    simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using h
  refine ⟨(r.factorial:ℝ)/c^r+((r+1).factorial:ℝ)/c^(r+1),fun y hy => ?_⟩
  have h := add_le_add (hb r y hy) (hb (r+1) y hy)
  simpa only [pow_succ,mul_one,add_mul,mul_add,mul_assoc] using h

private theorem abs_diagonal (N r m : ℕ) {g : SL(2,ℤ)} (p : Params) :
    p.2.im^r*‖diagonal N m g p‖ ≤ p.2.im^r*(1+p.2.im)*Real.exp (-(2*Real.pi*m*p.2.im)) := by
  have h : p.2.im^p.1.val≤1+p.2.im := by
    rcases le_total 1 p.2.im with h|h
    · exact (by simpa using Real.rpow_le_rpow_of_exponent_le h p.1.property.2 :
        p.2.im^p.1.val≤p.2.im).trans (by linarith)
    · exact (Real.rpow_le_one p.2.im_pos.le h p.1.property.1).trans (by linarith [p.2.im_pos])
  unfold diagonal;split_ifs
  · rw [heckeSeed,norm_mul,q_norm,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg p.2.im_pos.le _)]
    rw [← mul_assoc];gcongr
  · rw [norm_zero,mul_zero];positivity

theorem global_bound (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) :
    ∃ K : ℝ, 0≤K ∧ ∀ n (w : ℍ), w.im^r*‖heckeP N r m (sSeq n).val w‖≤K := by
  obtain ⟨b,hb,h0,h⟩ := layer_majorant N (2*r) m (by omega) hm (H:=1/2) (by norm_num)
  obtain ⟨D,hD⟩ := poly_exp_bounds r (by positivity : 0<2*Real.pi*(m:ℝ))
  let B := ∑' i,b i
  have B0 : 0≤B := tsum_nonneg h0
  let K := D+(1/2:ℝ)^(1-(r:ℝ))*B
  have help (n : ℕ) (w : ℍ) : w.im^r*‖heckeP N r m (sSeq n).val w‖≤K := by
    obtain ⟨a,ha⟩ := ModularGroup.exists_smul_mem_fd w
    let u := a • w
    let p : Params := (sSeq n,u)
    have hy : (1/2:ℝ)≤u.im := by
      have H := ModularGroup.three_le_four_mul_im_sq_of_mem_fd ha
      change 3≤4*u.im^2 at H
      nlinarith [u.im_pos]
    have hw : a⁻¹ • u=w := by dsimp [u];simp
    have W := weighted_slash r (heckeP N r m (sSeq n).val) a⁻¹ u
    rw [hw,heckeP_expansion N r m hr hm a⁻¹ p (sSeq_pos n)] at W
    rw [W]
    have hs := (hb.mul_left (u.im^(1-((2*r:ℕ):ℝ)))).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => h a⁻¹ i p hy)
    have H : ‖series N (2*r) m a⁻¹ p‖≤u.im^(1-((2*r:ℕ):ℝ))*B := (norm_tsum_le_tsum_norm hs).trans
        ((hs.tsum_le_tsum (fun i => h a⁻¹ i p hy) (hb.mul_left _)).trans_eq (by rw [tsum_mul_left]))
    have pow : u.im^r*u.im^(1-((2*r:ℕ):ℝ))=u.im^(1-(r:ℝ)) := by
      rw [← Real.rpow_natCast u.im r,← Real.rpow_add u.im_pos];push_cast;congr 1;ring
    have expLe : 1-(r:ℝ)≤0 := by have H : (1:ℝ)≤r := by exact_mod_cast hr;linarith
    calc
      _ ≤ u.im^r*(‖diagonal N m a⁻¹ p‖+‖series N (2*r) m a⁻¹ p‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le ..) (pow_nonneg u.im_pos.le _)
      _ ≤ D+(1/2:ℝ)^(1-(r:ℝ))*B := by
        rw [mul_add]
        apply add_le_add ((abs_diagonal N r m p).trans (hD u.im u.im_pos))
        exact (mul_le_mul_of_nonneg_left H (pow_nonneg u.im_pos.le _)).trans (by
          rw [← mul_assoc,pow];exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos (by norm_num : 0<(1/2:ℝ)) hy expLe) B0)
  exact ⟨K,(mul_nonneg (pow_nonneg (UpperHalfPlane.im_pos _).le _)
    (norm_nonneg _)).trans (help 0 UpperHalfPlane.I),help⟩

theorem zero_at_cusps (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (g : SL(2,ℤ)) :
    IsZeroAtImInfty (Pzero N r m ∣[2*(r:ℤ)] g) := by
  obtain ⟨K,hK,h⟩ := high_cusp_bound N (2*r) m (by omega) hm
  have b : Tendsto (fun y : ℝ => Real.exp (-(2*Real.pi*m*y))+K*y^(1-((2*r:ℕ):ℝ))) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (2*Real.pi*m) (by positivity)
    have h2 := (tendsto_rpow_neg_atTop (by have hr' : 1≤(r:ℝ) := by exact_mod_cast hr
                                              push_cast;linarith : 0<((2*r:ℕ):ℝ)-1)).const_mul K
    simpa [neg_sub] using h1.add h2
  rw [isZeroAtImInfty_iff];intro ε hε
  obtain ⟨A,hA⟩ := eventually_atTop.mp (b.eventually (gt_mem_nhds hε))
  refine ⟨max A 1,fun w hw => ?_⟩
  let p : Params := (zeroS,w)
  have d : ‖diagonal N m g p‖≤Real.exp (-(2*Real.pi*m*w.im)) := by
    unfold diagonal;split_ifs <;>simp [p,zeroS,heckeSeed,q_norm] <;> positivity
  rw [Pzero_slash N r m hr hm]
  exact (norm_add_le ..).trans ((add_le_add d (h g p ((le_max_right ..).trans hw))).trans
    ((hA w.im ((le_max_left ..).trans hw)).le))

end
end ImbalancedChen.Part3.OriginalHeckeLimitFamily20261112
