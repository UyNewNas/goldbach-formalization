import ImbalancedChen.Part3OriginalHighStripFourierMass

/-! A fixed positive Fourier coefficient on the complete Petersson space. The lower
bound for the incomplete Gamma integral is uniform in the actual even weight. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicBasisMass20261112
open Set MeasureTheory Complex Matrix
open scoped UpperHalfPlane MatrixGroups BigOperators InnerProductSpace ComplexConjugate ENNReal
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalPeterssonPretrace20261112 OriginalPeterssonNormalization20261112
open OriginalPeterssonHighStrip20261112 OriginalHighStripFourierMass20261112
open Gamma0GeneralCuspWidth20261025a (cuspWidth)

private theorem mass_pos {r m : ℕ} (hr : 0<r) (hm : 0<m) : 0<mass r m := by
  have one : (1:ℝ)≤r := by exact_mod_cast hr
  exact mul_pos (pow_pos (one_div_pos.mpr (by positivity)) _) (Real.Gamma_pos_of_pos (by linarith))

private theorem translated_mass {r m : ℕ} (hr : 0<r) (hm : 0<m) {A : ℝ} (hA : 0≤A) :
    ENNReal.ofReal (Real.exp (-(4*Real.pi*m))*mass r m*A) ≤
      ∫⁻ y in Ici (1:ℝ),ENNReal.ofReal (y^(2*r-2)*Real.exp (-(4*Real.pi*m*y))*A) := by
  let b : ℝ := 4*Real.pi*m
  let k := 2*r-2
  let F := fun y : ℝ => y^k*Real.exp (-(b*y))
  let C := Real.exp (-b)*A
  let G := fun y : ℝ => ENNReal.ofReal (F y*A)
  have hI : IntegrableOn F (Ioi 0) := by
    by_contra hc
    have h := mass_integral hr hm
    change (∫ y in Ioi (0:ℝ),F y)=_ at h
    rw [integral_undef hc] at h
    exact (mass_pos hr hm).ne' h.symm
  have init : ENNReal.ofReal (Real.exp (-b)*mass r m*A) =
      ∫⁻ y in Ioi (0:ℝ),ENNReal.ofReal (C*F y) := by
    rw [←ofReal_integral_eq_lintegral_ofReal (hI.const_mul C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hA) (mul_nonneg (pow_nonneg hy.le _) (Real.exp_pos _).le)),
      integral_const_mul,show (∫ y in Ioi (0:ℝ),F y)=mass r m from mass_integral hr hm]
    apply congrArg ENNReal.ofReal; dsimp [C];ring
  calc
    _ = _ := init
    _ ≤ ∫⁻ y in Ioi (0:ℝ),G (y+1) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      apply ENNReal.ofReal_le_ofReal
      dsimp [C,F,G]
      rw [show -(b*(y+1))=(-b)+(-(b*y)) by ring,Real.exp_add]
      calc
        _ = y^k*(Real.exp (-b)*Real.exp (-(b*y))*A) := by ring
        _ ≤ (y+1)^k*(Real.exp (-b)*Real.exp (-(b*y))*A) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.le (by linarith) _) (by positivity)
        _ = _ := by ring
    _ = ∫⁻ y in (fun t : ℝ => t+1) '' Ioi 0,G y :=
      (measurePreserving_add_right (volume : Measure ℝ) 1).setLIntegral_comp_emb
        (Homeomorph.addRight (1:ℝ)).isClosedEmbedding.measurableEmbedding G _
    _ ≤ _ := lintegral_mono_set (by rintro _ ⟨t,ht,rfl⟩;change 1≤t+1;linarith [show 0<t from ht])

def basisCost (N m : ℕ) (g : SL(2,ℤ)) : ℝ :=
  ((cuspWidth N g+1:ℕ):ℝ)*Real.exp (4*Real.pi*m)

theorem raw_bound (N r : ℕ) [NeZero N] (hr : 0<r) {m : ℕ} (hm : 0<m)
    (f : Forms N r) (g : SL(2,ℤ)) :
    mass r m*‖raw N (NeZero.pos N) r g m f‖^2≤basisCost N m g*‖f‖^2 := by
  let a := ‖raw N (NeZero.pos N) r g m f‖^2
  let b : ℝ := 4*Real.pi*m
  have L := (translated_mass hr hm (A:=a) (sq_nonneg _)).trans
    ((strip_fourier_mass N r hr f g m).trans (high_strip_energy N r f g))
  have hc : ((cuspWidth N g+1:ℕ):ℝ≥0∞)*ENNReal.ofReal (‖f‖^2)=
      ENNReal.ofReal (((cuspWidth N g+1:ℕ):ℝ)*‖f‖^2) := by
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast]
  rw [hc,ENNReal.ofReal_le_ofReal_iff (by positivity)] at L
  have H := mul_le_mul_of_nonneg_left L (Real.exp_pos b).le
  calc
    _ = Real.exp b*(Real.exp (-b)*mass r m*a) := by
      rw [Real.exp_neg];dsimp [a];field_simp [(Real.exp_pos b).ne'] <;>ring
    _ ≤ _ := H
    _ = _ := by unfold basisCost;dsimp [b];ring

theorem fourier_functional (N j : ℕ) [NeZero N] {m : ℕ} (hm : 0<m)
    (g : SL(2,ℤ)) (f : Forms N (j+1)) :
    (4*Real.pi*Real.Gamma (2*(j:ℝ)+1))*‖frameR N (NeZero.pos N) (j+1) f g m‖^2≤
      basisCost N m g*‖f‖^2 := by
  have h := raw_bound N (j+1) (by omega) hm f g
  have hv := normalization_factor (j:=j) hm hm
  have sr : Real.sqrt (m:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne'
  have cs : 0≤coefficientScale j m := by unfold coefficientScale;positivity
  rw [div_self sr,one_pow,one_mul,←sq] at hv
  rw [raw_eq_scaled_R N _ j f g hm,norm_mul,Complex.norm_real,Real.norm_of_nonneg cs,mul_pow,←mul_assoc,hv] at h
  exact h

/-- The full ONB on the same cusp in both slots. Applying the coefficient functional
to its own Riesz vector bounds its norm without a dimension factor. -/
theorem basis_mass (N j : ℕ) [NeZero N] {m : ℕ} (hm : 0<m) (g : SL(2,ℤ)) :
    (4*Real.pi*Real.Gamma (2*(j:ℝ)+1))*
      (∑ i,‖frameR N (NeZero.pos N) (j+1) (formsBasis N (j+1) i) g m‖^2)
      ≤basisCost N m g := by
  let v := Rvector N (j+1) g m
  have E := full_basis_product N (j+1) g g m m
  simp_rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq] at E
  rw [inner_self_eq_norm_sq_to_K,←Complex.ofReal_pow,←Complex.ofReal_sum,Complex.ofReal_inj] at E
  rw [E]
  change (4*Real.pi*Real.Gamma (2*(j:ℝ)+1))*‖v‖^2≤_
  by_cases h : v=0
  · simp [h,basisCost] <;>positivity
  · have V := fourier_functional N j hm g v
    have eval : frameR N (NeZero.pos N) (j+1) v g m=((‖v‖^2:ℝ):ℂ) := by
      rw [←Rvector_evaluates,inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
    rw [eval,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _),sq (‖v‖^2),←mul_assoc] at V
    exact le_of_mul_le_mul_right V (sq_pos_of_pos (norm_pos_iff.mpr h))

end ImbalancedChen.Part3.OriginalHolomorphicBasisMass20261112
end
