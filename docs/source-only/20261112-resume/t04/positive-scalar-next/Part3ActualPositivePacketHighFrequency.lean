import ImbalancedChen.Part3ActualPositiveScalarPacket
import ImbalancedChen.Part3ProductConvolutionSecondDerivatives
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Group.Prod

/-! One true compact Green transfer in one logarithmic height yields
the third power required by the fixed-level unit-band estimate. -/
namespace ImbalancedChen.Part3.ActualPositivePacketHighFrequency20261112

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology ContDiff
open RadialSchrodingerL2Form20261025a ComplexOrderKRadialRegularitySourceOnly
open ActualKLCompactTestIntegrationByParts20261025a ActualKRadialLogConjugation20261025a
open ProductConvolutionSecondDerivatives20261026a ActualPositiveScalarPacket20261112
open ActualPositiveSmallHeightKBound20261112 (regular_small_product)

def coords : (ℝ×ℝ) ≃ₜ (ℝ×ℝ) where
  toFun z := (z.1/2+z.2,z.1/2-z.2)
  invFun z := (z.1+z.2,(z.1-z.2)/2)
  left_inv z := by ext <;> simp <;> ring
  right_inv z := by ext <;> simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem coords_measure : MeasurePreserving coords volume volume := by
  let a (z : Plane) := (z.1,z.1/2+z.2)
  let b (z : Plane) := (z.1,-z.1+z.2)
  have A : MeasurePreserving a volume volume :=
    (MeasurePreserving.id (volume:Measure ℝ)).skew_product (g:=fun s w : ℝ => s/2+w)
      (by fun_prop) (Eventually.of_forall fun s => map_add_left_eq_self volume (s/2))
  have B : MeasurePreserving b volume volume :=
    (MeasurePreserving.id (volume:Measure ℝ)).skew_product (g:=fun x y : ℝ => -x+y)
      (by fun_prop) (Eventually.of_forall fun x => map_add_left_eq_self volume (-x))
  have S : MeasurePreserving (Prod.swap : Plane→Plane) volume volume := measurePreserving_swap
  have E : (coords : Plane→Plane)=b ∘ Prod.swap ∘ a := by funext z; ext <;> dsimp [coords,b,a] <;> ring
  rw [E]; exact B.comp (S.comp A)

def heights (η h : RadialTest) (z : Plane) : ℂ := envelope η h (coords.symm z)
def offset (R : ℝ) := Real.log (2*Real.pi)-R/2

def transform (F : Plane→ℂ) (c t : ℝ) := ∫ z : Plane,
  F z*radialK ((t:ℂ)*I) (z.1+c)*radialK ((t:ℂ)*I) (z.2+c)

theorem heights_smooth (η h : RadialTest) : ContDiff ℝ ∞ (heights η h) :=
  (η.smooth.comp (contDiff_fst.add contDiff_snd)).mul
    (h.smooth.comp ((contDiff_fst.sub contDiff_snd).div_const 2))

theorem heights_compact (η h : RadialTest) : HasCompactSupport (heights η h) :=
  (envelope_compact η h).comp_homeomorph coords.symm

theorem packet_transform (η h : RadialTest) (R t : ℝ) :
    packet η h R ((t:ℂ)*I)=4*transform (heights η h) (offset R) t := by
  rw [transform,← integral_const_mul,← coords_measure.integral_comp coords.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with z
  change envelope η h z*raw _ _ _=4*(heights η h (coords z)*_*_)
  rw [heights,Homeomorph.symm_apply_apply]
  have e (v : ℝ) : Real.exp (v+offset R)=2*Real.exp (Real.log Real.pi+(v-R/2)) := by
    rw [offset,Real.log_mul (by norm_num) Real.pi_pos.ne',
      show v+(Real.log 2+Real.log Real.pi-R/2)=Real.log 2+(Real.log Real.pi+(v-R/2)) by ring,
      Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  change _=4*(envelope η h z*radialK _ (z.1/2+z.2+offset R)*radialK _ (z.1/2-z.2+offset R))
  simp only [raw,radialK,e,logCenter]
  ring_nf

private def dxx (F : Plane→ℂ) := directional xDirection (directional xDirection F)

private def transfer (F : Plane→ℂ) (c : ℝ) (z : Plane) : ℂ :=
  -dxx F z+(Real.exp (2*(z.1+c)):ℂ)*F z

private theorem transfer_cont {F : Plane→ℂ} (sm : ContDiff ℝ ∞ F) (c : ℝ) :
    Continuous (transfer F c) :=
  (directional_cinfty (directional_cinfty sm _) _).continuous.neg.add
    ((by fun_prop : Continuous fun z : Plane => (Real.exp (2*(z.1+c)):ℂ)).mul sm.continuous)

private theorem transfer_comp {F : Plane→ℂ} (hc : HasCompactSupport F) (c : ℝ) :
    HasCompactSupport (transfer F c) :=
  (directional_hasCompactSupport (directional_hasCompactSupport hc _) _).neg.add hc.mul_left

private theorem slice_comp {F : Plane→ℂ} (hc : HasCompactSupport F) (c y : ℝ) :
    HasCompactSupport (fun r : ℝ => F (r-c,y)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hc.image (f:=fun z : Plane => z.1+c) (continuous_fst.add continuous_const))
  intro r hr
  exact ⟨(r-c,y),subset_tsupport _ hr,by simp⟩

private theorem row_transfer {F : Plane→ℂ} (sm : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (c t y : ℝ) : (t:ℂ)^2*(∫ x : ℝ,F (x,y)*radialK ((t:ℂ)*I) (x+c)) =
      ∫ x : ℝ,transfer F c (x,y)*radialK ((t:ℂ)*I) (x+c) := by
  let T : RadialTest := ⟨fun r => F (r-c,y),sm.comp ((contDiff_id.sub contDiff_const).prodMk contDiff_const),
    slice_comp hc c y⟩
  have q (r : ℝ) : deriv (deriv T.function) r=dxx F (r-c,y) := by
    have d : deriv T.function=fun u => deriv (fun v : ℝ => F (v,y)) (u-c) := by
      funext u; exact deriv_comp_sub_const _ _ _
    rw [d,deriv_comp_sub_const]
    exact (second_x_eq_slice sm (r-c,y)).symm
  have A := (actualKtransform_hamiltonian T t).symm
  rw [actualKtransform,actualKtransform,hamiltonianTest_function] at A
  rw [← integral_add_right_eq_self (fun r : ℝ => T.function r*radialK ((t:ℂ)*I) r) c,
      ← integral_add_right_eq_self (fun r : ℝ => logSchrodinger T.function r*radialK ((t:ℂ)*I) r) c] at A
  simpa only [T,logSchrodinger,Complex.real_smul,q,add_sub_cancel_right,transfer] using A

private theorem transform_L1 {F : Plane→ℂ} (con : Continuous F) (hc : HasCompactSupport F)
    (t c : ℝ) : Integrable (fun z : Plane => F z*radialK ((t:ℂ)*I) (z.1+c)*radialK ((t:ℂ)*I) (z.2+c)) :=
  ((con.mul ((radialK_C2 _).continuous.comp (continuous_fst.add continuous_const))).mul
    ((radialK_C2 _).continuous.comp (continuous_snd.add continuous_const))).integrable_of_hasCompactSupport
      hc.mul_right.mul_right

private theorem twice_frequency {F : Plane→ℂ} (sm : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (c t : ℝ) : (t:ℂ)^2*transform F c t=transform (transfer F c) c t := by
  simp only [transform]
  rw [integral_prod_symm _ (transform_L1 sm.continuous hc t c),
    integral_prod_symm _ (transform_L1 (transfer_cont sm c) (transfer_comp hc c) t c),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [integral_mul_const,integral_mul_const,← mul_assoc,row_transfer sm hc]

private def price (F : Plane→ℂ) (c₀ : ℝ) (z : Plane) :=
  ‖dxx F z‖+Real.exp (2*(z.1+c₀))*‖F z‖

private theorem price_L1 {F : Plane→ℂ} (sm : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (c₀ : ℝ) : Integrable (price F c₀) :=
  (((directional_cinfty (directional_cinfty sm _) _).continuous.norm).add
    ((by fun_prop : Continuous fun z : Plane => Real.exp (2*(z.1+c₀))).mul sm.continuous.norm)).integrable_of_hasCompactSupport
      ((directional_hasCompactSupport (directional_hasCompactSupport hc _) _).norm.add hc.norm.mul_left)

private theorem transfer_le {F : Plane→ℂ} {c c₀ : ℝ} (cc : c≤c₀) (z : Plane) :
    ‖transfer F c z‖≤price F c₀ z := by
  unfold transfer price
  apply (norm_add_le _ _).trans
  simp only [norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  gcongr

theorem uniform_transform {F : Plane→ℂ} (sm : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (c₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ c≤c₀,∀ t : ℝ,1≤|t| →
      Real.cosh (Real.pi*t)*‖transform F c t‖≤C/|t|^3 := by
  let K := tsupport F ∪ tsupport (dxx F)
  have hK : IsCompact K := hc.union (directional_hasCompactSupport (directional_hasCompactSupport hc _) _)
  obtain ⟨U,hu⟩ := hK.exists_bound_of_continuousOn (f:=fun z : Plane => max z.1 z.2)
    (continuous_fst.max continuous_snd).continuousOn
  obtain ⟨C,c0,B⟩ := regular_small_product (Real.exp (U+c₀))
  let A := ∫ z : Plane,price F c₀ z
  have a0 : 0≤A := integral_nonneg fun z => by dsimp [price]; positivity
  refine ⟨A*C,mul_nonneg a0 c0,fun c cc t ht => ?_⟩
  have tt : 0<|t| := lt_of_lt_of_le zero_lt_one ht
  have ch := Real.cosh_pos (Real.pi*t)
  let m := (C/|t|)/Real.cosh (Real.pi*t)
  have m0 : 0≤m := by dsimp [m]; positivity
  have point (z : Plane) : ‖transfer F c z*radialK ((t:ℂ)*I) (z.1+c)*radialK ((t:ℂ)*I) (z.2+c)‖≤price F c₀ z*m := by
    by_cases hz : z∈K
    · have V := (le_abs_self (max z.1 z.2)).trans (by simpa only [Real.norm_eq_abs] using hu z hz)
      have k := B t ht _ ⟨Real.exp_pos _,Real.exp_le_exp.mpr (add_le_add ((le_max_left _ _).trans V) cc)⟩
        _ ⟨Real.exp_pos _,Real.exp_le_exp.mpr (add_le_add ((le_max_right _ _).trans V) cc)⟩
      rw [mul_assoc,norm_mul]
      exact mul_le_mul (transfer_le cc z) ((le_div_iff₀ ch).mpr (by simpa only [mul_comm] using k))
        (norm_nonneg _) (by unfold price; positivity)
    · have a : F z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (Or.inl h))
      have b : dxx F z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (Or.inr h))
      simp [transfer,price,a,b]
  have H : ‖transform (transfer F c) c t‖≤A*m := by
    dsimp only [transform,A]
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le ((price_L1 sm hc c₀).mul_const _) (ae_of_all _ point)
  rw [← twice_frequency sm hc,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs] at H
  apply (le_div_iff₀ (pow_pos tt 3)).mpr
  have Hb := (le_div_iff₀ ch).mp (show |t|^2*‖transform F c t‖≤(A*(C/|t|))/Real.cosh (Real.pi*t) by
    simpa only [m,mul_div_assoc] using H)
  have Hc := (le_div_iff₀ tt).mp (show (|t|^2*‖transform F c t‖)*Real.cosh (Real.pi*t)≤(A*C)/|t| by
    simpa only [mul_div_assoc] using Hb)
  convert Hc using 1 <;> ring

/-- Fixed smooth compact product and ratio windows; the bound is uniform
in all translations R≥0, including R→∞. -/
theorem packet_high (η h : RadialTest) :
    ∃ C : ℝ,0≤C ∧ ∀ R≥(0:ℝ),∀ t : ℝ,1≤|t| →
      Real.cosh (Real.pi*t)*‖packet η h R ((t:ℂ)*I)‖≤C/|t|^3 := by
  obtain ⟨C,c0,B⟩ := uniform_transform (heights_smooth η h) (heights_compact η h) (Real.log (2*Real.pi))
  refine ⟨4*C,by positivity,fun R hR t ht => ?_⟩
  have H := B (offset R) (by unfold offset; linarith) t ht
  rw [packet_transform,norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ = 4*(Real.cosh (Real.pi*t)*‖transform (heights η h) (offset R) t‖) := by ring
    _ ≤ 4*(C/|t|^3) := mul_le_mul_of_nonneg_left H (by norm_num)
    _ = _ := by ring

end
end ImbalancedChen.Part3.ActualPositivePacketHighFrequency20261112
