import ImbalancedChen.Part3CompactHeightMellinInversion
import ImbalancedChen.Part3ActualPositiveLatticeSmoothCover
import ImbalancedChen.Part3OriginalExceptionalJNativeCompletion

/-! The switched cutoff on the literal full positive frequency block.
The fixed smooth Mellin density is chosen before the level, row, height,
phase or spectral index. -/
namespace ImbalancedChen.Part3.OriginalSwitchedMellinRows20261113
noncomputable section
open Set MeasureTheory Complex Finset
open scoped BigOperators MatrixGroups FourierTransform SchwartzMap
open CommonSmoothCutoff CompactHeightMellinInversion20261027 SmoothZeroHeightSeedProfiles20261026b
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualCuspEigenbasisNativeLabels20261026b
open MediumGlobalDyadicOwnership20261028 ActualIntervalGeometricSumSourceOnly
open OriginalExceptionalJNativeCompletion20261110

def cutoffSeed : SmoothHeightSeed where
  toFun := fun y => (dyadicCutoff y : ℂ)
  continuous := Complex.continuous_ofReal.comp dyadicCutoff_contDiff.continuous
  compact := dyadicCutoff_hasCompactSupport.comp_left (g := Complex.ofRealCLM) (map_zero _)
  positive := by
    intro x hx
    change x ∈ tsupport (dyadicCutoffSchwartz : ℝ → ℂ) at hx
    rw [dyadicCutoffSchwartz_tsupport_eq_tight] at hx
    change 0 < x
    linarith [hx.1]
  cinfty := Complex.ofRealCLM.contDiff.comp dyadicCutoff_contDiff

def density (t : ℝ) : ℂ := mellinAngular cutoffSeed 0 t

theorem density_integrable : Integrable density := mellinAngular_integrable cutoffSeed 0

/-- A single constant works at every geometry and for every spectral row. -/
theorem density_decay : ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ‖density t‖ ≤ B/(1+t^4) := by
  let b := 2*Real.pi
  have hb : 1 ≤ b := by dsimp [b]; linarith [Real.pi_gt_three]
  have hb0 : 0 < b := by linarith
  obtain ⟨C,hC,h⟩ := schwartz_norm_le_rapidDecay (𝓕 (logSchwartz cutoffSeed 0)) 4
  refine ⟨C*b^4, by positivity, fun t => ?_⟩
  have H : ‖density t‖ ≤ C/(1+|b⁻¹*t|)^4 := h _
  have he : b*(1+|b⁻¹*t|) = b+|t| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hb0), mul_add, mul_one, ← mul_assoc,
      mul_inv_cancel₀ hb0.ne', one_mul]
  have aux : 1+t^4 ≤ (1+|t|)^4 := by
    have h4 : |t|^4=t^4 := by
      rcases le_total 0 t with ht | ht
      · rw [abs_of_nonneg ht]
      · rw [abs_of_nonpos ht]; ring
    rw [← h4]
    nlinarith [abs_nonneg t,sq_nonneg |t|,pow_nonneg (abs_nonneg t) 3]
  have den : 1+t^4 ≤ b^4*(1+|b⁻¹*t|)^4 := by
    rw [← mul_pow, he]
    exact aux.trans (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  apply H.trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    C*(1+t^4) ≤ C*(b^4*(1+|b⁻¹*t|)^4) := mul_le_mul_of_nonneg_left den hC.le
    _ = _ := by ring

/-- Positive real base to imaginary order, in angular Mellin frequency. -/
def wave (y t : ℝ) : ℂ := Complex.exp (((t*Real.log y : ℝ) : ℂ)*I)

@[simp] theorem wave_zero (y : ℝ) : wave y 0 = 1 := by simp [wave]
@[simp] theorem wave_norm (y t : ℝ) : ‖wave y t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem star_wave (y t : ℝ) : star (wave y t) = wave y (-t) := by
  unfold wave
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

theorem cutoff_inversion {y : ℝ} (hy : 0 < y) :
    (dyadicCutoff y : ℂ) =
      ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, wave y t*density t := by
  simpa [cutoffSeed,wave,density] using compact_height_mellin_inversion cutoffSeed 0 hy

private theorem oscillatory_integrable (y : ℝ) :
    Integrable (fun t : ℝ => wave y t*density t) := by
  apply density_integrable.bdd_mul
    (show AEStronglyMeasurable (wave y) volume from by unfold wave; fun_prop)
  exact Filter.Eventually.of_forall (fun t => (wave_norm y t).le)

theorem half_split {D m n x : ℝ} (hD : 0<D) (hm : 0<m) (hn : 0<n)
    (hx : 0<x) (t : ℝ) :
    wave (4*Real.pi*Real.sqrt (m*n)/(D*x)) t =
      wave (4*Real.pi/D) t * wave x (-t) * wave m (t/2) * wave n (t/2) := by
  have hp : 0 < 4*Real.pi := by positivity
  have hmn := mul_pos hm hn
  unfold wave
  rw [Real.log_div (mul_pos hp (Real.sqrt_pos.mpr hmn)).ne' (mul_pos hD hx).ne',
    Real.log_mul hp.ne' (Real.sqrt_pos.mpr hmn).ne', Real.log_sqrt hmn.le,
    Real.log_mul hm.ne' hn.ne', Real.log_mul hD.ne' hx.ne', Real.log_div hp.ne' hD.ne']
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

def twistedRow (S : Finset ℕ) (v : ℕ → ℂ) (t : ℝ) := ∑ m ∈ S, v m * wave (m : ℝ) t

/-- The Mellin coefficient bound uses only the original row's finite l1 norm.
The oscillatory factors have unit modulus for all angular frequencies. -/
theorem row_norm_le (S : Finset ℕ) (v : ℕ → ℂ) (t : ℝ) :
    ‖twistedRow S v t‖ ≤ ∑ m ∈ S, ‖v m‖ := by
  simpa only [twistedRow,norm_mul,wave_norm,mul_one] using
    (norm_sum_le S (fun m => v m*wave (m:ℝ) t))

/-- Open both sides of one native row and perform Mellin inversion. The
left half twist is conjugated, so the two displayed frequencies differ. -/
theorem switched_row (S : Finset ℕ) (hp : ∀ m ∈ S, 0<m) (v : ℕ → ℂ)
    {D x : ℝ} (hD : 0<D) (hx : 0<x) :
    (∑ m ∈ S, ∑ n ∈ S, star (v m)*v n *
      (dyadicCutoff (4*Real.pi*Real.sqrt ((m:ℝ)*(n:ℝ))/(D*x)) : ℂ)) =
      ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, wave (4*Real.pi/D) t * wave x (-t) *
        density t * (star (twistedRow S v (-(t/2))) * twistedRow S v (t/2)) := by
  classical
  let y (m n : ℕ) := 4*Real.pi*Real.sqrt ((m:ℝ)*(n:ℝ))/(D*x)
  let F (m n : ℕ) (t : ℝ) := (star (v m)*v n)*(wave (y m n) t*density t)
  have hF (m n) : Integrable (F m n) := (oscillatory_integrable (y m n)).const_mul _
  have hfint (m : ℕ) :
      (∫ t : ℝ, ∑ n ∈ S, F m n t) = ∑ n ∈ S, ∫ t : ℝ, F m n t :=
    integral_finsetSum S (fun n _ => hF m n)
  have hterm (m) (hm : m ∈ S) (n) (hn : n ∈ S) :
      star (v m)*v n*(dyadicCutoff (y m n) : ℂ) =
        ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, F m n t := by
    have hm' : (0:ℝ)<m := by exact_mod_cast hp m hm
    have hn' : (0:ℝ)<n := by exact_mod_cast hp n hn
    rw [cutoff_inversion (show 0<y m n by dsimp [y]; positivity)]
    simp only [F,integral_const_mul,Complex.real_smul]
    ring
  change (∑ m ∈ S, ∑ n ∈ S, star (v m)*v n*(dyadicCutoff (y m n) : ℂ)) = _
  calc
    _ = ∑ m ∈ S, ∑ n ∈ S, ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, F m n t := by
      apply sum_congr rfl
      intro m hm
      exact sum_congr rfl (hterm m hm)
    _ = ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, ∑ m ∈ S, ∑ n ∈ S, F m n t := by
      rw [integral_finsetSum S (fun m _ => integrable_finsetSum S (fun n _ => hF m n))]
      simp_rw [hfint, Finset.smul_sum]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [twistedRow,Complex.star_def,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro n hn
      have hs : conj (wave (m:ℝ) (-(t/2))) = wave (m:ℝ) (t/2) := by
        simpa only [Complex.star_def,neg_neg] using star_wave (m:ℝ) (-(t/2))
      rw [hs]
      simp only [F,y,Complex.star_def]
      rw [half_split hD (by exact_mod_cast hp m hm) (by exact_mod_cast hp n hn) hx]
      ring

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

def nativeRow (z : ℕ+) (i : actualCuspBasisIndex z z.property) (ω : ℝ) (m : ℕ) : ℂ :=
  phaseAt ω m * basisRhoK z z.property i (1 : SL(2,ℤ)) (m : ℤ)

/-- Direct specialization to a row of T08's full exceptional energy. -/
theorem native_switched_row (z : ℕ+) (i : ↥(exceptional z)) (j : ℕ) (ω : ℝ)
    {Q x : ℝ} (hQ : 0<Q) (hx : 0<x) :
    (∑ m ∈ dyadicWindow j, ∑ n ∈ dyadicWindow j,
      star (nativeRow z i.val ω m)*nativeRow z i.val ω n *
        (dyadicCutoff (4*Real.pi*Real.sqrt ((m:ℝ)*(n:ℝ))/((z.val:ℝ)*Q*x)) : ℂ)) =
      ((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, wave (4*Real.pi/((z.val:ℝ)*Q)) t * wave x (-t) *
        density t * (star (twistedRow (dyadicWindow j) (nativeRow z i.val ω) (-(t/2))) *
          twistedRow (dyadicWindow j) (nativeRow z i.val ω) (t/2)) := by
  refine switched_row _ (fun m hm => ?_) _ (mul_pos (by exact_mod_cast z.property) hQ) hx
  change m ∈ Ico (2^j) _ at hm
  exact lt_of_lt_of_le (pow_pos (by decide : 0<2) _) (mem_Ico.mp hm).1

end
end ImbalancedChen.Part3.OriginalSwitchedMellinRows20261113
