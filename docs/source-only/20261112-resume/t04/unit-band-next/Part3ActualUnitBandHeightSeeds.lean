import ImbalancedChen.Part3ActualUnitBandMellinProbe
import ImbalancedChen.Part3ActualSignedPoincareEnvelope
import ImbalancedChen.Part3ActualCutPlaneKZeroModel
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Smooth cutoff height seeds with the literal frequency 2 pi |m|,
and their actual Whittaker probes as the cutoffs tend to one. -/
namespace ImbalancedChen.Part3.ActualUnitBandHeightSeeds20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology Distributions ContDiff
open ActualUnitBandMellinProbe20261112 ActualLogHorocycleAdjoint20261112
open SmoothZeroHeightSeedProfiles20261026b ComplexOrderKBridgeSourceOnly
open ActualCutPlaneKZeroModel20261026b OriginalContinuousPoincarePackets20261110
open ImaginaryOrderKBesselSourceOnly

def window (k : ℕ) (u : ℝ) : ℝ :=
  Real.smoothTransition ((k:ℝ)+1-u)*Real.smoothTransition ((k:ℝ)+1+u)

theorem window_bounds (k : ℕ) (u : ℝ) : 0≤window k u ∧ window k u≤1 :=
  ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)⟩

theorem window_eventually (u : ℝ) : ∀ᶠ k : ℕ in atTop, window k u=1 := by
  obtain ⟨n,hn⟩ := exists_nat_ge |u|
  filter_upwards [eventually_ge_atTop n] with k hk
  have e : |u|≤(k:ℝ) := hn.trans (by exact_mod_cast hk)
  rw [window,Real.smoothTransition.one_of_one_le (by linarith [(abs_le.mp e).2]),
    Real.smoothTransition.one_of_one_le (by linarith [(abs_le.mp e).1]),one_mul]

def carrier (u : ℝ) : ℂ := (Real.exp u : ℂ)*complexOrderK 0 (Real.exp u)
def modulation (T u : ℝ) : ℂ := Complex.exp (((T:ℂ)*I)*(u:ℂ))

theorem smooth_carrier : ContDiff ℝ ∞ carrier := by
  have E : carrier=fun u : ℝ => (Real.exp u:ℂ)*cutPlaneKZero (Real.exp u:ℂ) := by
    funext u
    rw [carrier,cutPlaneKZero_real (Real.exp_pos u)]
  rw [E,contDiff_iff_contDiffAt]
  intro u
  have h := (cutPlaneKZero_analyticAt (Complex.ofReal_mem_slitPlane.mpr (Real.exp_pos u))).restrictScalars ℝ
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun v : ℝ => (Real.exp v:ℂ)) u).mul
    (h.contDiffAt.comp u (by fun_prop))

theorem zero_kernel (q : ℝ) : complexOrderK 0 q=(imaginaryOrderK 0 q : ℂ) := by
  simpa using complexOrderK_imaginary 0 q

theorem carrier_nonneg (u : ℝ) : carrier u=(‖carrier u‖ : ℂ) := by
  rw [carrier,zero_kernel,← Complex.ofReal_mul,Complex.norm_real,
    Real.norm_of_nonneg (mul_pos (Real.exp_pos _) (imaginaryOrderK_zero_pos (Real.exp_pos _))).le]

theorem modulation_norm (T u : ℝ) : ‖modulation T u‖=1 := by
  simp [modulation,Complex.norm_exp,Complex.mul_re]

def logSeed (C T : ℝ) (k : ℕ) : LogTest where
  toFun := fun u => (window k (u+Real.log C) : ℂ)*carrier (u+Real.log C)*modulation T (u+Real.log C)
  contDiff' := by
    have S : ContDiff ℝ ∞ (fun u : ℝ => carrier (u+Real.log C)) := smooth_carrier.comp (by fun_prop)
    unfold window modulation
    fun_prop
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (-(k:ℝ)-1-Real.log C) ((k:ℝ)+1-Real.log C)))
    intro u hu
    by_contra H
    rcases not_and_or.mp H with l|r
    · have z := Real.smoothTransition.zero_of_nonpos (show (k:ℝ)+1+(u+Real.log C)≤0 by linarith)
      exact hu (by simp [window,z])
    · have z := Real.smoothTransition.zero_of_nonpos (show (k:ℝ)+1-(u+Real.log C)≤0 by linarith)
      exact hu (by simp [window,z])
  tsupport_subset' := subset_univ _

def seed (C T : ℝ) (k : ℕ) : SmoothHeightSeed := fromLog (logSeed C T k)

theorem seed_real (C : ℝ) (k : ℕ) (y : ℝ) : (seed C 0 k).toFun y=(‖(seed C 0 k).toFun y‖ : ℂ) := by
  by_cases h : 0<y
  · obtain ⟨u,rfl⟩ : y∈Set.range Real.exp := by rw [Real.range_exp]; exact h
    rw [seed,fromLog_exp]
    change (Real.exp (u/2):ℂ)*((window k _ : ℂ)*carrier _*modulation 0 _)=_
    have p := window_bounds k (u+Real.log C)
    simp only [logSeed,modulation,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,norm_mul,
      Complex.norm_real,Real.norm_of_nonneg p.1,Real.norm_of_nonneg (Real.exp_pos _).le,Complex.ofReal_mul]
    exact congrArg (fun z : ℂ => (Real.exp (u/2):ℂ)*((window k (u+Real.log C):ℂ)*z))
      (carrier_nonneg _)
  · have z := image_eq_zero_of_notMem_tsupport (f := (seed C 0 k).toFun) (fun hmem => h ((seed C 0 k).positive hmem))
    simp [z]

theorem seed_norm (C T : ℝ) (k : ℕ) (y : ℝ) : ‖(seed C T k).toFun y‖=‖(seed C 0 k).toFun y‖ := by
  by_cases h : 0<y
  · have E := Real.exp_log h
    rw [← E,seed,seed,fromLog_exp,fromLog_exp]
    simp only [logSeed,norm_mul,modulation_norm]
  · have z (t : ℝ) := image_eq_zero_of_notMem_tsupport (f := (seed C t k).toFun) (fun hm => h ((seed C t k).positive hm))
    rw [z T,z 0]

def rate (m : ℤ) : ℝ := 2*Real.pi*|(m:ℝ)|
theorem rate_pos {m : ℤ} (hm : m≠0) : 0<rate m :=
  mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hm))

private theorem exp_half (y : ℝ) (hy : 0<y) : Real.exp (Real.log y/2)=Real.sqrt y := by
  apply (sq_eq_sq₀ (Real.exp_pos _).le (Real.sqrt_nonneg _)).mp
  rw [sq,← Real.exp_add,show Real.log y/2+Real.log y/2=Real.log y by ring,Real.exp_log hy,Real.sq_sqrt hy.le]

private theorem mod_conj (T : ℝ) {q : ℝ} (hq : 0<q) :
    star (modulation T (Real.log q))=(q:ℂ)^(-((T:ℂ)*I)) := by
  rw [modulation,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),← Complex.ofReal_log hq.le]
  simp only [Complex.star_def,← Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I]
  congr 1
  ring

theorem cutoff_probe (m : ℤ) (hm : m≠0) (T : ℝ) (k : ℕ) (ν : ℂ) :
    orderProbe m (seed (rate m) T k).toFun ν =
      2*∫ q in Ioi (0:ℝ),(window k (Real.log q):ℂ)*probeDensity T ν q := by
  let C := rate m
  have hC : 0<C := rate_pos hm
  let V := fun q : ℝ => (window k (Real.log q):ℂ)*probeDensity T ν q
  have J := integral_comp_mul_left_Ioi' V 0 hC
  rw [mul_zero,← integral_smul] at J
  change (∫ y in Ioi (0:ℝ), ((y⁻¹)^2 : ℝ) • (star ((seed C T k).toFun y)*orderRadial m ν y))=2*∫ q in Ioi (0:ℝ),V q
  rw [← J,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have qpos := mul_pos hC hy
  have S := fromLog_exp (logSeed C T k) (Real.log y)
  rw [Real.exp_log hy,exp_half y hy] at S
  have sumlog : Real.log y+Real.log C=Real.log (C*y) := by rw [Real.log_mul hC.ne' hy.ne',add_comm]
  have Kstar : star (complexOrderK 0 (C*y))=complexOrderK 0 (C*y) := by
    rw [zero_kernel,Complex.star_def,Complex.conj_ofReal]
  change (fromLog (logSeed C T k)).toFun y=_ at S
  simp only [logSeed,sumlog,carrier,Real.exp_log qpos] at S
  change ((y⁻¹)^2 : ℝ) • (star ((fromLog (logSeed C T k)).toFun y)*_) = _
  simp only [S,orderRadial,← show C=2*Real.pi*|(m:ℝ)| from rfl,star_mul',Kstar,mod_conj T qpos,
    V,probeDensity,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv]
  simp only [Complex.star_def,Complex.conj_ofReal]
  have sq := congrArg (fun x : ℝ => (x:ℂ)) (Real.sq_sqrt hy.le)
  push_cast at sq
  let coeff := 2*(C:ℂ)*(window k (Real.log (C*y)):ℂ)*((C:ℂ)*(y:ℂ))^(-((T:ℂ)*I))*
    complexOrderK 0 (C*y)*complexOrderK ν (C*y)
  field_simp [Complex.ofReal_ne_zero.mpr hy.ne'] <;> first
    | linear_combination (norm := (dsimp only [coeff]; ring)) coeff*sq
    | linear_combination (norm := (dsimp only [coeff]; ring)) (y:ℂ)*coeff*sq

theorem cutoff_limit (m : ℤ) (hm : m≠0) (T : ℝ) {ν : ℂ} (hν : |ν.re|<1) :
    Tendsto (fun k => orderProbe m (seed (rate m) T k).toFun ν) atTop (𝓝 (2*probeIntegral T ν)) := by
  have h := probe_integrable T hν
  simp_rw [cutoff_probe m hm]
  apply tendsto_const_nhds.mul
  apply tendsto_integral_of_dominated_convergence (fun q => ‖probeDensity T ν q‖)
  · intro k
    exact ((Complex.continuous_ofReal.measurable.comp (by unfold window; fun_prop : Measurable (fun q : ℝ => window k (Real.log q)))).aestronglyMeasurable.mul h.aestronglyMeasurable)
  · exact h.norm
  · intro k
    exact ae_of_all _ (fun q => by rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (window_bounds _ _).1]; exact mul_le_of_le_one_left (norm_nonneg _) (window_bounds _ _).2)
  · exact ae_of_all _ (fun q => tendsto_const_nhds.congr' ((window_eventually (Real.log q)).mono (fun k H => by simp [H])))

end
end ImbalancedChen.Part3.ActualUnitBandHeightSeeds20261112
