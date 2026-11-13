import ImbalancedChen.Part3OriginalExceptionalNativeEnvelope

/-! On strict complementary orders bounded away from zero, the
ordinary large-Y price has no logarithm. The Mellin phase is arbitrary. -/
namespace ImbalancedChen.Part3.OriginalSwitchedOrderAwayZero20261113
noncomputable section
open Set MeasureTheory Complex
open CommonSmoothCutoff OriginalSwitchedMellinRows20261113 (wave wave_norm)
open GeneralComplexISeriesSourceOnly (generalICore) ActualGeneralJBesselSourceOnly (generalJ)
open ActualPositiveJRotationPair20261112 (complementaryKernel)
open ActualPrescribedPositiveJ20261112 (exceptionalWeight)
open OriginalExceptionalCoreBounds20261113 (core_band)

private theorem kernel_bound {T η : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<η) :
    ∃ C δ : ℝ,0<C ∧ 0<δ ∧ δ≤1 ∧ ∀ s : ℝ,η≤s → s≤T → ∀ x : ℝ,0<x → x≤δ →
      ‖complementaryKernel x (s/2)‖≤C*(x/2)^(-s) := by
  obtain ⟨_,K,d,_,kp,dp,d1,H⟩ := core_band tp t1
  refine ⟨4*Real.pi*K/η,d,by positivity,dp,d1,fun s se st x xp xd => ?_⟩
  let b := x/2
  let z : ℂ := -((b:ℂ)^2)
  have bp : 0<b := by dsimp [b];positivity
  have b1 : b≤1 := by dsimp [b];linarith [xd.trans d1]
  have sp := ep.trans_le se
  have sz : ‖z‖≤d := by
    rw [show ‖z‖=b^2 by simp [z,norm_pow,Complex.norm_real,Real.norm_of_nonneg bp.le]]
    exact (by nlinarith only [mul_nonneg bp.le (sub_nonneg.mpr b1)] : b^2≤b).trans
      ((by dsimp only [b];linarith : b≤x).trans xd)
  have a := (H (-s) (by simpa only [abs_neg,abs_of_pos sp] using st) z sz).2.1
  have b' := (H s (by simpa only [abs_of_pos sp] using st) z sz).2.1
  rw [Complex.ofReal_neg] at a
  have p : b^s≤b^(-s) := by
    apply Real.rpow_le_rpow_of_exponent_ge bp b1
    linarith
  have M : ‖generalJ (-(s:ℂ)) x‖≤b^(-s)*K := by
    rw [generalJ,norm_mul,show (b:ℂ)^(-(s:ℂ))=((b^(-s):ℝ):ℂ) by rw [←Complex.ofReal_neg,←Complex.ofReal_cpow bp.le],
      Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg bp.le _)]
    exact mul_le_mul_of_nonneg_left a (Real.rpow_nonneg bp.le _)
  have P : ‖generalJ (s:ℂ) x‖≤b^(-s)*K := by
    rw [generalJ,norm_mul,←Complex.ofReal_cpow bp.le,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg bp.le _)]
    exact mul_le_mul p b' (norm_nonneg _) (Real.rpow_nonneg bp.le _)
  have den : η≤Real.sin (Real.pi*(s/2)) := se.trans (by
    simpa only [show Real.pi/2*s=Real.pi*(s/2) by ring] using Real.le_sin_mul sp.le (st.trans t1.le))
  have dn := ep.trans_le den
  have E := (norm_sub_le (generalJ (-(s:ℂ)) x) (generalJ (s:ℂ) x)).trans (add_le_add M P)
  rw [complementaryKernel,if_neg (show s/2≠0 by positivity),
    show -2*((s/2:ℝ):ℂ)= -(s:ℂ) by push_cast;ring,
    show 2*((s/2:ℝ):ℂ)=(s:ℂ) by push_cast;ring,norm_mul,norm_div,norm_mul,
    Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_real,Real.norm_of_nonneg dn.le]
  calc
    _ ≤ (2*Real.pi/η)*(b^(-s)*K+b^(-s)*K) :=
      mul_le_mul (div_le_div_of_nonneg_left (by positivity) ep den) E (norm_nonneg _) (by positivity)
    _ = _ := by dsimp only [b];ring

theorem away_ceiling {T η : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<η) :
    ∃ C Y₀ : ℝ,0<C ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ s : ℝ,η≤s → s≤T → ∀ t : ℝ,
      ‖exceptionalWeight (fun x => (dyadicCutoff (Y*x):ℂ)*wave x (-t)) (s/2)‖≤C*Y^s := by
  obtain ⟨K,δ,kp,dp,d1,h⟩ := kernel_bound tp t1 ep
  have y1 : 1≤3/δ := (le_div_iff₀ dp).mpr (by linarith)
  refine ⟨24*K,3/δ,by positivity,y1,fun Y hy s se st t => ?_⟩
  have yp := zero_lt_one.trans_le (y1.trans hy)
  have sp := ep.trans_le se
  let S := Icc ((1/2)/Y) (3/Y)
  let F := fun x : ℝ => complementaryKernel x (s/2)*((dyadicCutoff (Y*x):ℂ)*wave x (-t))/(x:ℂ)
  have support (x : ℝ) (nz : F x≠0) : x∈S := by
    have n : dyadicCutoff (Y*x)≠0 := by intro z;exact nz (by simp [F,z])
    have l := dyadicCutoff_tsupport_subset (subset_tsupport _ n)
    exact ⟨(div_le_iff₀ yp).mpr (by simpa only [mul_comm Y x] using l.1),
      (le_div_iff₀ yp).mpr (by simpa only [mul_comm Y x] using l.2)⟩
  have pos {x : ℝ} (hx : x∈S) := (div_pos (by norm_num : (0:ℝ)<1/2) yp).trans_le hx.1
  have point (x : ℝ) (hx : x∈S) : ‖F x‖≤8*Y*(K*Y^s) := by
    have xp := pos hx
    have upper : x≤δ := hx.2.trans ((div_le_iff₀ yp).mpr (by simpa only [mul_comm Y δ] using (div_le_iff₀ dp).mp hy))
    have yl := (div_le_iff₀ yp).mp hx.1
    have ib : (x/2)⁻¹≤4*Y := (inv_le_comm₀ (by positivity) (by positivity)).mpr (by
      rw [inv_eq_one_div,div_le_iff₀ (by positivity : 0<4*Y)]
      nlinarith only [yl])
    have pow : (x/2)^(-s)≤4*Y^s := by
      rw [Real.rpow_neg_eq_inv_rpow]
      calc
        _ ≤ (4*Y)^s := Real.rpow_le_rpow (by positivity) ib sp.le
        _ = (4:ℝ)^s*Y^s := Real.mul_rpow (by norm_num) yp.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) (st.trans t1.le)) (Real.rpow_nonneg yp.le _)
    have cov := (h s se st x xp upper).trans (mul_le_mul_of_nonneg_left pow kp.le)
    simp only [F,norm_div,norm_mul,wave_norm,mul_one,Complex.norm_real,
      Real.norm_of_nonneg xp.le,Real.norm_of_nonneg (dyadicCutoff_nonneg _)]
    rw [div_le_iff₀ xp]
    have m := mul_le_mul cov (dyadicCutoff_le_one (Y*x)) (dyadicCutoff_nonneg _) (by positivity)
    nlinarith only [m,mul_le_mul_of_nonneg_right yl (by positivity : 0≤K*Y^s)]
  have e₁ : (∫ x in Ioi (0:ℝ),F x)=∫ x,F x := setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by by_contra nz;exact hx (pos (support x nz)))
  have e₂ : (∫ x in S,F x)=∫ x,F x := setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by by_contra nz;exact hx (support x nz))
  change ‖∫ x in Ioi (0:ℝ),F x‖≤_
  rw [e₁,←e₂]
  apply (norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top point).trans
  rw [show volume.real S=3/Y-(1/2)/Y from Real.volume_real_Icc_of_le (div_le_div_of_nonneg_right (by norm_num) yp.le)]
  calc
    _ ≤ (8*Y*(K*Y^s))*(3/Y) := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
    _ = _ := by field_simp [yp.ne'] <;> ring

end
end ImbalancedChen.Part3.OriginalSwitchedOrderAwayZero20261113
