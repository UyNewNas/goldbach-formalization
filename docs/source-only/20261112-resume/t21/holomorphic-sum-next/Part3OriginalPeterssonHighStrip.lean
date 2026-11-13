import ImbalancedChen.Part3OriginalPeterssonNormalizedOrbits
import ImbalancedChen.Part3ActualHighStripCircleMeasure

/-! The unscaled Petersson energy of a normalized high strip is bounded by that of
a finite number of translates of the actual carrier. No dimension or level-aspect
estimate enters. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPeterssonHighStrip20261112
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup UpperHalfPlane Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Pointwise InnerProductSpace ENNReal
open ModularFundamentalFiniteMeasure20261024z Gamma0FiniteMeasureCarrier20261024z
open Gamma0GeneralCuspWidth20261025a Gamma0GeneralCuspUnitPeriod20261025a
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open ActualCuspStripCutoff20261025a (highWidthStrip)

def energy {N r : ℕ} (f : Forms N r) (w : ℍ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖sectionValue f w‖^2)

theorem energy_carrier (N r : ℕ) [NeZero N] (f : Forms N r) :
    ∫⁻ w in gamma0Carrier N,energy f w=ENNReal.ofReal (‖f‖^2) := by
  have E (w : ℍ) : petersson (2*(r:ℤ)) f f w=((‖sectionValue f w‖^2:ℝ):ℂ) := by
    rw [←section_inner,inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
  have H := inner_integral N r f f
  simp_rw [E] at H
  rw [inner_self_eq_norm_sq_to_K,integral_ofReal,←Complex.ofReal_pow,Complex.ofReal_inj] at H
  rw [H]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (section_memLp f).aestronglyMeasurable).mp (section_memLp f))
    (ae_of_all _ fun _ => sq_nonneg _)).symm

private theorem energy_invariant {N r : ℕ} (f : Forms N r) (g : CongruenceSubgroup.Gamma0 N) (w : ℍ) :
    energy f (g.val • w)=energy f w := by
  have H := SlashInvariantFormClass.petersson_smul (τ:=w) (f:=f) (f':=f)
    (show mapGL ℝ g.val ∈ levelGroup N from Subgroup.mem_map.mpr ⟨g.val,g.property,rfl⟩)
  change petersson (2*(r:ℤ)) f f (g.val • w)=_ at H
  rw [←section_inner,←section_inner,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,
    ←Complex.ofReal_pow,←Complex.ofReal_pow,Complex.ofReal_inj] at H
  exact congrArg ENNReal.ofReal H

private theorem translate_integral (g : SL(2,ℤ)) (S : Set ℍ) (F : ℍ→ℝ≥0∞) :
    (∫⁻ w in S,F (g • w))=∫⁻ w in g • S,F w :=
  (measurePreserving_smul (mapGL ℝ g) (volume : Measure ℍ)).setLIntegral_comp_emb
    (measurableEmbedding_const_smul _) F S

theorem translated_cell (N r : ℕ) [NeZero N] (f : Forms N r) (g : SL(2,ℤ)) :
    (∫⁻ w in g • modularFD,energy f w)≤ENNReal.ofReal (‖f‖^2) := by
  let a : gamma0Classes N := QuotientGroup.mk g⁻¹
  let v : SL(2,ℤ) := Quotient.out a
  have hc : g⁻¹∈v • (CongruenceSubgroup.Gamma0 N : Set SL(2,ℤ)) := by
    rw [←QuotientGroup.eq_class_eq_leftCoset]
    exact (Quotient.out_eq' a).symm
  rw [mem_leftCoset_iff] at hc
  let γ : CongruenceSubgroup.Gamma0 N := ⟨v⁻¹*g⁻¹,hc⟩
  have sub : γ.val • (g • modularFD) ⊆ gamma0Carrier N := by
    rw [smul_smul,show γ.val*g=v⁻¹ by dsimp [γ];group]
    exact Set.subset_iUnion (fun q => inverseClassRep N q • modularFD) a
  calc
    _ = ∫⁻ w in g • modularFD,energy f (γ.val • w) := by simp_rw [energy_invariant f γ]
    _ = _ := translate_integral γ.val _ _
    _ ≤ _ := (lintegral_mono_set sub).trans_eq (energy_carrier N r f)

private theorem scaled_frame (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (w : ℍ) :
    frameGL N (NeZero.pos N) g • w=g •
      (⟨((cuspWidth N g:ℕ):ℂ)*w,by
        simp only [Complex.mul_im,Complex.natCast_im,zero_mul,add_zero,Complex.natCast_re]
        exact mul_pos (Nat.cast_pos.mpr (cuspWidth_pos N (NeZero.pos N) g)) w.im_pos⟩ : ℍ) := by
  let W := cuspWidth N g
  have hw : 0<(W:ℝ) := Nat.cast_pos.mpr (cuspWidth_pos N (NeZero.pos N) g)
  have hs : Real.sqrt (W:ℝ)≠0 := (Real.sqrt_pos.mpr hw).ne'
  have sq : ((Real.sqrt (W:ℝ):ℝ):ℂ)^2=(W:ℂ) := by exact_mod_cast Real.sq_sqrt hw.le
  have H : mapGL ℝ (integralReal g)=mapGL ℝ g := by
    apply Units.ext;ext i j;simp [integralReal,mapGL_coe_matrix,SpecialLinearGroup.map_apply_coe]
  rw [frameGL,normalizedScaling,map_mul,mul_smul,H]
  apply congrArg (fun u : ℍ => g • u)
  apply UpperHalfPlane.ext
  change ((widthDiagonal W _ • w:ℍ):ℂ)=_
  rw [coe_specialLinearGroup_apply]
  simp [widthDiagonal,div_eq_mul_inv,mul_assoc]
  <;>push_cast <;>field_simp [Complex.ofReal_ne_zero.mpr hs]
  <;>linear_combination (w:ℂ)*sq

private theorem near_cell {W : ℕ} {u : ℍ} (hx : u.re∈Ico (0:ℝ) W) (hy : 1≤u.im) :
    ∃ l : Fin (W+1),u∈(ModularGroup.T^(l.val:ℤ)) • modularFD := by
  let n := ⌊u.re+1/2⌋₊
  have hn : n<W+1 := (Nat.floor_lt (by linarith [hx.1])).mpr (by push_cast;linarith [hx.2])
  have h1 : (n:ℝ)≤u.re+1/2 := Nat.floor_le (by linarith [hx.1])
  have h2 : u.re+1/2<(n:ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨⟨n,hn⟩,?_⟩
  rw [mem_smul_set_iff_inv_smul_mem,←zpow_neg,modular_T_zpow_smul]
  change 1≤Complex.normSq _ ∧ |_ |≤1/2
  simp only [Complex.normSq_apply,UpperHalfPlane.coe_vadd,UpperHalfPlane.vadd_re,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,zero_add,
    Int.cast_neg,Int.cast_natCast]
  constructor
  · nlinarith [sq_nonneg (-(n:ℝ)+u.re),sq_nonneg (u.im-1)]
  · exact abs_le.mpr ⟨by linarith,by linarith⟩

def frameEnergy {N r : ℕ} [NeZero N] (f : Forms N r) (g : SL(2,ℤ)) (w : ℍ) : ℝ≥0∞ :=
  ENNReal.ofReal (w.im^(2*r)*‖frameForm N (NeZero.pos N) r f g w‖^2)

theorem frame_energy_eq {N r : ℕ} [NeZero N] (f : Forms N r) (g : SL(2,ℤ)) (w : ℍ) :
    frameEnergy f g w=energy f (frameGL N (NeZero.pos N) g • w) := by
  let A := frameGL N (NeZero.pos N) g
  let F := frameForm N (NeZero.pos N) r f g
  have H := petersson_slash (2*(r:ℤ)) f f A w
  change petersson (2*(r:ℤ)) F F w=_ at H
  have detA : A.det.val=1 := by simp [A,frameGL]
  simp only [detA,abs_one,Complex.ofReal_one,one_zpow,one_mul,UpperHalfPlane.σ,one_pos,if_true] at H
  rw [←section_inner f f,inner_self_eq_norm_sq_to_K] at H
  have E : ((w.im^(2*r)*‖F w‖^2:ℝ):ℂ)=petersson (2*(r:ℤ)) F F w := by
    rw [petersson,show 2*(r:ℤ)=((2*r:ℕ):ℤ) by push_cast;rfl,zpow_natCast,
      ←Complex.normSq_eq_conj_mul_self,←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.normSq_eq_norm_sq]
    exact congrArg Complex.ofReal (mul_comm _ _)
  apply congrArg ENNReal.ofReal
  exact_mod_cast E.trans H

/-- Valid for both original cusps, including every composite level. -/
theorem high_strip_energy (N r : ℕ) [NeZero N] (f : Forms N r) (g : SL(2,ℤ)) :
    (∫⁻ w in highWidthStrip 1 1,frameEnergy f g w) ≤
      ((cuspWidth N g+1:ℕ):ℝ≥0∞)*ENNReal.ofReal (‖f‖^2) := by
  let W := cuspWidth N g
  let S := highWidthStrip 1 1
  let cells := fun l : Fin (W+1) => (g*ModularGroup.T^(l.val:ℤ)) • modularFD
  let A := frameGL N (NeZero.pos N) g
  have hw : 1≤(W:ℝ) := by exact_mod_cast cuspWidth_pos N (NeZero.pos N) g
  have sub : (fun w : ℍ => A • w) '' S ⊆ ⋃ l,cells l := by
    rintro _ ⟨w,⟨hx,hy⟩,rfl⟩
    let u : ℍ := ⟨(W:ℂ)*w,by simp [Complex.mul_im];positivity⟩
    have ux : u.re=(W:ℝ)*w.re := by simp [u,Complex.mul_re]
    have uy : u.im=(W:ℝ)*w.im := by simp [u,Complex.mul_im]
    obtain ⟨l,hl⟩ := near_cell (W:=W) (u:=u)
      (by rw [ux]; exact ⟨mul_nonneg (by linarith) hx.1,
        by simpa using mul_lt_mul_of_pos_left hx.2 (by linarith : 0<(W:ℝ))⟩)
      (by rw [uy];exact one_le_mul_of_one_le_of_one_le hw hy)
    apply Set.mem_iUnion.mpr
    refine ⟨l,?_⟩
    change frameGL N _ g • w∈(g*_) • modularFD
    rw [scaled_frame,mul_smul,mem_smul_set_iff_inv_smul_mem,inv_smul_smul]
    exact hl
  simp_rw [frame_energy_eq]
  calc
    _ = ∫⁻ w in (fun w : ℍ => A • w) '' S,energy f w :=
      (measurePreserving_smul A (volume : Measure ℍ)).setLIntegral_comp_emb
        (measurableEmbedding_const_smul _) _ S
    _ ≤ _ := lintegral_mono_set sub
    _ ≤ ∑' l,∫⁻ w in cells l,energy f w := lintegral_iUnion_le cells _
    _ ≤ _ := by
      rw [tsum_fintype]
      calc
        _ ≤ ∑ _l : Fin (W+1),ENNReal.ofReal (‖f‖^2) :=
          Finset.sum_le_sum fun l _ => translated_cell N r f _
        _ = _ := by simp [W,nsmul_eq_mul]

end ImbalancedChen.Part3.OriginalPeterssonHighStrip20261112
end
