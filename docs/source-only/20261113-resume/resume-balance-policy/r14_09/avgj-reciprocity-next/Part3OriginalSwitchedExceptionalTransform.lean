import ImbalancedChen.Part3OriginalSwitchedMellinRows
import ImbalancedChen.Part3ActualPositiveNativeDiagonal

/-! Mellin transport for the positive-sign complementary transform, including
the original dx/x and the common physical infinity rows. -/
namespace ImbalancedChen.Part3.OriginalSwitchedExceptionalTransform20261113
noncomputable section
open Set MeasureTheory Complex Finset
open scoped BigOperators
open CommonSmoothCutoff OriginalSwitchedMellinRows20261113 ActualGeneralJBesselSourceOnly
open ActualPositiveJRotationPair20261112 ActualPrescribedPositiveJ20261112
open ActualPositiveNativeDiagonal20261112 OriginalExceptionalJNativeCompletion20261110
open MediumGlobalDyadicOwnership20261028

private def kernelDensity (Y a x : ℝ) : ℂ :=
  complementaryKernel x a * (dyadicCutoff (Y*x) : ℂ)/(x:ℂ)

/-- Absolute integrability on the original measure, including all strict
exceptional orders 0 < 2a < 1. -/
private theorem kernel_integrable {Y a : ℝ} (hY : 0<Y) (ha : 0<a) (ha' : a<1/2) :
    IntegrableOn (kernelDensity Y a) (Ioi 0) := by
  let S := Icc ((1/2)/Y) (3/Y)
  have pos {x : ℝ} (hx : x ∈ S) : 0<x :=
    lt_of_lt_of_le (div_pos (by norm_num) hY) hx.1
  have HJ (ν : ℂ) (hν : -1<ν.re) : ContinuousOn (generalJ ν) S :=
    fun x hx => (generalJ_differentiableAt hν (pos hx)).continuousAt.continuousWithinAt
  have Hminus : -1 < (-2*(a:ℂ)).re := by simp; linarith
  have Hplus : -1 < (2*(a:ℂ)).re := by simp; linarith
  have HK : ContinuousOn (fun x => complementaryKernel x a) S := by
    simp only [complementaryKernel,if_neg ha.ne']
    exact continuousOn_const.mul ((HJ _ Hminus).sub (HJ _ Hplus))
  have hs : Function.support (kernelDensity Y a) ⊆ S := by
    intro x hx
    have hn : dyadicCutoff (Y*x) ≠ 0 := by
      intro hz
      exact hx (by simp [kernelDensity,hz])
    have H := dyadicCutoff_tsupport_subset (subset_tsupport _ hn)
    exact ⟨(div_le_iff₀ hY).mpr (by simpa [mul_comm] using H.1),
      (le_div_iff₀ hY).mpr (by simpa [mul_comm] using H.2)⟩
  have H : ContinuousOn (kernelDensity Y a) S :=
    (HK.mul ((Complex.continuous_ofReal.comp
      (dyadicCutoff_contDiff.continuous.comp (continuous_const.mul continuous_id))).continuousOn)).div
        Complex.continuous_ofReal.continuousOn
        (fun x hx => Complex.ofReal_ne_zero.mpr (pos hx).ne')
  exact ((integrableOn_iff_integrable_of_support_subset hs).mp
    (H.integrableOn_compact isCompact_Icc)).integrableOn

def switchedTest (Y D : ℝ) (m n : ℕ) (x : ℝ) : ℂ :=
  (dyadicCutoff (Y*x) : ℂ) *
    (dyadicCutoff (4*Real.pi*Real.sqrt ((m:ℝ)*(n:ℝ))/(D*x)) : ℂ)

/-- All variables of integration belong to their literal Lebesgue measures.
The Mellin density is L1 and every oscillatory factor has norm one. -/
theorem exceptional_weight_switch {Y D a : ℝ} (hY : 0<Y) (hD : 0<D)
    (ha : 0<a) (ha' : a<1/2) {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    exceptionalWeight (switchedTest Y D m n) a =
      ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ,
        (density t * wave (4*Real.pi/D) t * wave (m:ℝ) (t/2) * wave (n:ℝ) (t/2)) *
          exceptionalWeight (fun x => (dyadicCutoff (Y*x) : ℂ)*wave x (-t)) a := by
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let y (x : ℝ) := 4*Real.pi*Real.sqrt ((m:ℝ)*(n:ℝ))/(D*x)
  let F (x t : ℝ) := kernelDensity Y a x * (wave (y x) t * density t)
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have HK : Integrable (kernelDensity Y a) μ := kernel_integrable hY ha ha'
  have hposμ : ∀ᵐ x : ℝ ∂μ, 0<x := ae_restrict_mem measurableSet_Ioi
  have Hosc : Measurable (fun p : ℝ × ℝ => wave (y p.1) p.2) := by
    unfold wave y
    fun_prop
  have HF : Integrable (fun p : ℝ × ℝ => F p.1 p.2) (μ.prod volume) := by
    apply (HK.norm.mul_prod density_integrable.norm).mono'
      ((HK.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst).mul
        (Hosc.aestronglyMeasurable.mul
          (density_integrable.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_snd)))
    exact Filter.Eventually.of_forall (fun p => by simp [F,norm_mul])
  calc
    _ = ∫ x, ((2*Real.pi)⁻¹ : ℝ) • (∫ t : ℝ, F x t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hposμ] with x hx
      have hy : 0<y x := by dsimp [y]; positivity
      change complementaryKernel x a * ((dyadicCutoff (Y*x) : ℂ)*(dyadicCutoff (y x) : ℂ)) /
        (x:ℂ) = _
      rw [cutoff_inversion hy]
      simp only [F,kernelDensity,integral_const_mul,Complex.real_smul]
      ring
    _ = ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, ∫ x, F x t ∂μ := by
      rw [integral_smul,integral_integral_swap HF]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [exceptionalWeight,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hposμ] with x hx
      simp only [F,y,kernelDensity]
      rw [half_split hD hm' hn' hx]
      ring

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- The order in this identity is the one read off the actual exceptional
index, without a uniform gap input. -/
theorem native_exceptional_weight_switch (z : ℕ+) (i : ↥(exceptional z)) {Y Q : ℝ}
    (hY : 0<Y) (hQ : 0<Q) {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    exceptionalWeight (switchedTest Y ((z.val:ℝ)*Q) m n) (complementaryHeight z.val i.val) =
      ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ,
        (density t * wave (4*Real.pi/((z.val:ℝ)*Q)) t *
          wave (m:ℝ) (t/2) * wave (n:ℝ) (t/2)) *
          exceptionalWeight (fun x => (dyadicCutoff (Y*x) : ℂ)*wave x (-t))
            (complementaryHeight z.val i.val) := by
  have R := complementary_range z.val ((mem_exceptional z i.val).mp i.property).2
  exact exceptional_weight_switch hY (mul_pos (by exact_mod_cast z.property) hQ)
    R.1 R.2.1 hm hn

/-- Open the actual complementary trace row, use the switched cutoff, and
factor the two native half-frequency sums *under* the Bessel integral. -/
theorem native_weighted_row (z : ℕ+) (i : ↥(exceptional z)) (j : ℕ) (ω : ℝ)
    {Y Q : ℝ} (hY : 0<Y) (hQ : 0<Q) :
    (∑ m ∈ dyadicWindow j, ∑ n ∈ dyadicWindow j, star (nativeRow z i.val ω m) *
      nativeRow z i.val ω n * exceptionalWeight (switchedTest Y ((z.val:ℝ)*Q) m n)
        (complementaryHeight z.val i.val)) =
      ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, (density t * wave (4*Real.pi/((z.val:ℝ)*Q)) t *
        (star (twistedRow (dyadicWindow j) (nativeRow z i.val ω) (-(t/2))) *
          twistedRow (dyadicWindow j) (nativeRow z i.val ω) (t/2))) *
        exceptionalWeight (fun x => (dyadicCutoff (Y*x) : ℂ)*wave x (-t))
          (complementaryHeight z.val i.val) := by
  classical
  let S := dyadicWindow j
  let v := nativeRow z i.val ω
  let a := complementaryHeight z.val i.val
  let D := (z.val:ℝ)*Q
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let row (t : ℝ) := star (twistedRow S v (-(t/2)))*twistedRow S v (t/2)
  let F (x t : ℝ) := kernelDensity Y a x *
    (wave (4*Real.pi/D) t*wave x (-t)*density t*row t)
  have R := complementary_range z.val ((mem_exceptional z i.val).mp i.property).2
  have HK : Integrable (kernelDensity Y a) μ := kernel_integrable hY R.1 R.2.1
  have hposμ : ∀ᵐ x : ℝ ∂μ, 0<x := ae_restrict_mem measurableSet_Ioi
  let L := ∑ m ∈ S, ‖v m‖
  have rowBound (t : ℝ) : ‖row t‖ ≤ L*L := by
    rw [row,norm_mul,norm_star]
    exact mul_le_mul (row_norm_le S v _) (row_norm_le S v _) (norm_nonneg _) (by dsimp [L]; positivity)
  have HM : Measurable (fun p : ℝ × ℝ =>
      wave (4*Real.pi/D) p.2*wave p.1 (-p.2)*row p.2) := by
    unfold wave row twistedRow
    fun_prop
  have HF : Integrable (fun p : ℝ × ℝ => F p.1 p.2) (μ.prod volume) := by
    have HKD : AEStronglyMeasurable (fun p : ℝ × ℝ => kernelDensity Y a p.1) (μ.prod volume) :=
      HK.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
    have HD : AEStronglyMeasurable (fun p : ℝ × ℝ => density p.2) (μ.prod volume) :=
      density_integrable.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_snd
    apply ((HK.norm.mul_prod density_integrable.norm).mul_const (L*L)).mono'
    · exact ((HKD.mul HD).mul HM.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall (fun p => by dsimp [F]; ring))
    · filter_upwards [] with p
      simp only [F,norm_mul,wave_norm,one_mul,mul_one]
      calc
        _ ≤ ‖kernelDensity Y a p.1‖*(‖density p.2‖*(L*L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rowBound _) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
  let b (m n : ℕ) (x : ℝ) := (star (v m)*v n) *
    (dyadicCutoff (4*Real.pi*Real.sqrt ((m:ℝ)*(n:ℝ))/(D*x)) : ℂ)
  have hb (m n : ℕ) : Integrable (fun x => kernelDensity Y a x * b m n x) μ := by
    apply HK.mul_bdd (c := ‖star (v m)*v n‖)
    · unfold b
      exact (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (dyadicCutoff_contDiff.continuous.measurable.comp (by fun_prop)))).aestronglyMeasurable
    · filter_upwards [] with x
      calc
        ‖b m n x‖ = ‖star (v m)*v n‖ *
            dyadicCutoff (4*Real.pi*Real.sqrt ((m:ℝ)*(n:ℝ))/(D*x)) := by
          simp only [b,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (dyadicCutoff_nonneg _)]
        _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) (dyadicCutoff_le_one _)
  calc
    _ = ∫ x, ∑ m ∈ S, ∑ n ∈ S, kernelDensity Y a x * b m n x ∂μ := by
      rw [integral_finsetSum S (fun m _ => integrable_finsetSum S (fun n _ => hb m n))]
      apply sum_congr rfl
      intro m hm
      rw [integral_finsetSum S (fun n _ => hb m n)]
      apply sum_congr rfl
      intro n hn
      rw [exceptionalWeight,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [kernelDensity,switchedTest,b,v,D,a]
      ring
    _ = ∫ x, ((2*Real.pi)⁻¹ : ℝ) • (∫ t : ℝ, F x t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hposμ] with x hx
      simp only [← mul_sum]
      have hrow := native_switched_row z i j ω hQ hx
      change (∑ m ∈ S, ∑ n ∈ S, b m n x) = _ at hrow
      rw [hrow]
      simp only [F,row,integral_const_mul,Complex.real_smul]
      dsimp [D,S,v]
      ring
    _ = ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, ∫ x, F x t ∂μ := by
      rw [integral_smul,integral_integral_swap HF]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [exceptionalWeight,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [F,row,S,v,kernelDensity,a,D]
      ring

end
end ImbalancedChen.Part3.OriginalSwitchedExceptionalTransform20261113
