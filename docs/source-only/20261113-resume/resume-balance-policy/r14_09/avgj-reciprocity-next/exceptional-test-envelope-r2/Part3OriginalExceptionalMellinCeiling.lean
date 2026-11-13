import ImbalancedChen.Part3OriginalExceptionalTestFloor

/-! The reflected Mellin transform is bounded uniformly in its
oscillation. The logarithm accounts for order close to zero. -/
namespace ImbalancedChen.Part3.OriginalExceptionalMellinCeiling20261113
noncomputable section
open Set MeasureTheory Complex
open CommonSmoothCutoff OriginalSwitchedMellinRows20261113 (wave wave_norm)
open OriginalExceptionalBandKernel20261113 (band_kernel)
open ActualPositiveJRotationPair20261112 (complementaryKernel)
open ActualPrescribedPositiveJ20261112 (exceptionalWeight)

theorem tested_ceiling {T : ℝ} (t0 : 0≤T) (t1 : T<1) :
    ∃ K Y₀ : ℝ,0<K ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ s : ℝ,0<s → s≤T → ∀ t : ℝ,
      ‖exceptionalWeight (fun x => (dyadicCutoff (Y*x):ℂ)*wave x (-t)) (s/2)‖≤
        K*(1+Real.log (4*Y))*Y^s := by
  obtain ⟨c,K,δ,_,kp,dp,d1,h⟩ := band_kernel t0 t1
  have y1 : 1≤3/δ := (le_div_iff₀ dp).mpr (by linarith)
  refine ⟨24*K,3/δ,by positivity,y1,fun Y hy s sp st t => ?_⟩
  have yp := zero_lt_one.trans_le (y1.trans hy)
  let S := Icc ((1/2)/Y) (3/Y)
  let F := fun x : ℝ => complementaryKernel x (s/2)*
    ((dyadicCutoff (Y*x):ℂ)*wave x (-t))/(x:ℂ)
  let A := K*(1+Real.log (4*Y))*Y^s
  have ln : 0≤Real.log (4*Y) := Real.log_nonneg (by linarith [y1.trans hy])
  have ap : 0≤A := by dsimp only [A];positivity
  have support (x : ℝ) (nz : F x≠0) : x∈S := by
    have n : dyadicCutoff (Y*x)≠0 := by
      intro z
      exact nz (by simp [F,z])
    have l := dyadicCutoff_tsupport_subset (subset_tsupport _ n)
    exact ⟨(div_le_iff₀ yp).mpr (by simpa only [mul_comm Y x] using l.1),
      (le_div_iff₀ yp).mpr (by simpa only [mul_comm Y x] using l.2)⟩
  have pos {x : ℝ} (hx : x∈S) := (div_pos (by norm_num : (0:ℝ)<1/2) yp).trans_le hx.1
  have upper {x : ℝ} (hx : x∈S) : x≤δ := hx.2.trans ((div_le_iff₀ yp).mpr
    (by simpa only [mul_comm Y δ] using (div_le_iff₀ dp).mp hy))
  have point (x : ℝ) (hx : x∈S) : ‖F x‖≤8*Y*A := by
    have xp := pos hx
    have bp : 0<x/2 := by positivity
    have yl := (div_le_iff₀ yp).mp hx.1
    have ib : (x/2)⁻¹≤4*Y := (inv_le_comm₀ bp (by positivity)).mpr (by
      rw [inv_eq_one_div,div_le_iff₀ (by positivity : 0<4*Y)]
      nlinarith only [yl])
    have logb : |Real.log (x/2)|≤Real.log (4*Y) := by
      rw [abs_of_nonpos (Real.log_nonpos bp.le (by linarith only [upper hx,d1])),←Real.log_inv]
      exact Real.log_le_log (inv_pos.mpr bp) ib
    have pow : (x/2)^(-s)≤4*Y^s := by
      rw [Real.rpow_neg_eq_inv_rpow]
      calc
        _ ≤ (4*Y)^s := Real.rpow_le_rpow (inv_nonneg.mpr bp.le) ib sp.le
        _ = (4:ℝ)^s*Y^s := Real.mul_rpow (by norm_num) yp.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) (st.trans t1.le)) (Real.rpow_nonneg yp.le _)
    have kernel : ‖complementaryKernel x (s/2)‖≤4*A := by
      apply (h s x sp st xp (upper hx)).2.trans
      calc
        _ ≤ (K*(1+Real.log (4*Y)))*(4*Y^s) := mul_le_mul
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl logb) kp.le) pow
          (Real.rpow_nonneg bp.le _) (by positivity)
        _ = _ := by dsimp only [A]; ring
    rw [show ‖F x‖=‖complementaryKernel x (s/2)‖*dyadicCutoff (Y*x)/x by
      simp only [F,norm_div,norm_mul,wave_norm,mul_one,Complex.norm_real,
        Real.norm_of_nonneg xp.le,Real.norm_of_nonneg (dyadicCutoff_nonneg _)]]
    rw [div_le_iff₀ xp]
    calc
      _ ≤ (4*A)*1 := mul_le_mul kernel (dyadicCutoff_le_one _) (dyadicCutoff_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right yl ap]
  have incl : S⊆Ioi (0:ℝ) := fun _ hx => pos hx
  have e₁ : (∫ x in Ioi (0:ℝ),F x)=∫ x,F x := setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by by_contra nz;exact hx (incl (support x nz)))
  have e₂ : (∫ x in S,F x)=∫ x,F x := setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by by_contra nz;exact hx (support x nz))
  change ‖∫ x in Ioi (0:ℝ),F x‖≤_
  rw [e₁,←e₂]
  apply (norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top point).trans
  rw [show volume.real S=3/Y-(1/2)/Y from
      Real.volume_real_Icc_of_le (div_le_div_of_nonneg_right (by norm_num) yp.le)]
  calc
    _ ≤ (8*Y*A)*(3/Y) := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
    _ = _ := by dsimp only [A]; field_simp [yp.ne'] <;> ring

end
end ImbalancedChen.Part3.OriginalExceptionalMellinCeiling20261113
