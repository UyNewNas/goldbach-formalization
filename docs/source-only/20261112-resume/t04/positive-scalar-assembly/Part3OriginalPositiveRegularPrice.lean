import ImbalancedChen.Part3OriginalPositiveResponseLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Real-frequency envelopes for the two successive limits. The first
constant depends on the ratio window; the second is uniform in that window. -/
namespace ImbalancedChen.Part3.OriginalPositiveRegularPrice20261112

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ContDiff
open OriginalPositiveRatioWindows20261112 OriginalPositiveResponseLimit20261112
open ActualPositiveScalarPacket20261112 ActualPositiveCenteredKLimit20261112
open ActualPositiveSmallHeightKBound20261112 ActualPositivePacketHighFrequency20261112
open ActualPositiveSmallHeightWaves20261112 (radius)
open ActualPositiveHolomorphicWeights20261112 (expMass expMass_nonneg)
open ComplexOrderKBridgeSourceOnly RadialSchrodingerL2Form20261025a
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalPositiveStripContour20261112 (angular wave angular_derivative norm_wave_real)
open private regular_gamma from ImbalancedChen.Part3OriginalPositiveResponseLimit
open private coth_large from ImbalancedChen.Part3ActualPositiveSmallHeightKBound
open private abs_exp_integrable from ImbalancedChen.Part3OriginalPositiveStripContour

theorem line_meas (η H : RadialTest) (R : ℝ) :
    StronglyMeasurable (fun t : ℝ => packet η H R ((t:ℂ)*I)) := by
  let k (t : ℝ) (x : ℝ) := complexOrderK ((t:ℂ)*I) (2*Real.exp x)
  have km : StronglyMeasurable (Function.uncurry k) := by
    have hx : Continuous (fun p : (ℝ×ℝ)×ℝ =>
      complexOrderIntegrand ((p.1.1:ℂ)*I) (2*Real.exp p.1.2) p.2) := by
      unfold complexOrderIntegrand; fun_prop
    exact hx.stronglyMeasurable.integral_prod_right' (ν:=volume.restrict (Ioi (0:ℝ)))
  have a : Measurable (fun p : ℝ×(ℝ×ℝ) => (p.1,logCenter R p.2.1+p.2.2)) := by unfold logCenter; fun_prop
  have b : Measurable (fun p : ℝ×(ℝ×ℝ) => (p.1,logCenter R p.2.1-p.2.2)) := by unfold logCenter; fun_prop
  exact ((envelope_cont η H).stronglyMeasurable.comp_measurable measurable_snd |>.mul
    (stronglyMeasurable_const.mul ((km.comp_measurable a).mul (km.comp_measurable b)))).integral_prod_right'

theorem kernel_bound (t w : ℝ) : ‖limitKernel ((t:ℂ)*I) w‖≤4*w^2 := by
  by_cases z : t=0
  · subst t; simp [limit_zero,norm_mul,norm_pow,Real.norm_eq_abs,sq_abs]
  have A := regular_gamma z
  have pp := (Real.pi_pos.mul (abs_pos.mpr z))
  have d : t*Real.sinh (Real.pi*t)=|t|*Real.sinh (Real.pi*|t|) := by
    rcases le_or_gt 0 t with ht|ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht,mul_neg,Real.sinh_neg]; ring
  have hs : Real.pi*|t|≤Real.sinh (Real.pi*|t|) := Real.self_le_sinh_iff.mpr pp.le
  have den : 0<t*Real.sinh (Real.pi*t) := d ▸ mul_pos (abs_pos.mpr z) (Real.sinh_pos_iff.mpr pp)
  have nn := Real.sin_sq_le_sq (x:=t*w)
  rw [limit_nonzero (mul_ne_zero (ofReal_ne_zero.mpr z) I_ne_zero),show 4*Gamma ((t:ℂ)*I)*Gamma (-((t:ℂ)*I))=
    2*(2*Gamma ((t:ℂ)*I)*Gamma (-((t:ℂ)*I))) by ring,A,
    show (t:ℂ)*I*(w:ℂ)=((t*w:ℝ):ℂ)*I by push_cast; ring,Complex.sinh_mul_I,← ofReal_sin]
  simp only [norm_mul,norm_pow,norm_div,Complex.norm_I,mul_one,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,sq_abs,abs_of_pos Real.pi_pos,← abs_mul,abs_of_pos den]
  rw [show ∀ a b c : ℝ,2*(a/b)*c=(2*a*c)/b by intros; ring,div_le_iff₀ den]
  nlinarith [mul_le_mul_of_nonneg_left nn (by linarith [Real.pi_pos] : 0≤4*Real.pi),
    mul_le_mul_of_nonneg_left hs (mul_nonneg (abs_nonneg t) (sq_nonneg w)),sq_abs t,d]

private theorem gamma_annulus :
    ∃ G : ℝ,0≤G ∧ ∀ t : ℝ,radius≤|t| → |t|≤1 → ‖Gamma ((t:ℂ)*I)‖≤G := by
  let K : Set ℝ := Icc (-1:ℝ) 1 ∩ {t | radius≤|t|}
  have hc : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  obtain ⟨C,H⟩ := hc.exists_bound_of_continuousOn (f:=fun t : ℝ => Gamma ((t:ℂ)*I)) (by
    intro t ht
    have nt : t≠0 := fun z => by have e := ht.2; norm_num [z,radius] at e
    have D := differentiableAt_Gamma ((t:ℂ)*I) (fun n e => nt (by simpa using congrArg Complex.im e))
    exact D.continuousAt.comp_continuousWithinAt (Complex.continuous_ofReal.mul continuous_const).continuousWithinAt)
  exact ⟨max C 0,le_max_right _ _,fun t a b => (H t ⟨abs_le.mp b,a⟩).trans (le_max_left _ _)⟩

private theorem compact_real (η H : RadialTest) (mass : ∫ s : ℝ,η.function s=1)
    (zero : ∫ w : ℝ,H.function w=0) :
    ∃ C R₀ : ℝ,0≤C ∧ ∀ R≥R₀,∀ t : ℝ,|t|≤1 → ‖packet η H R ((t:ℂ)*I)‖≤C := by
  obtain ⟨D,S₀,d0,E⟩ := packet_disk_error η H mass zero
  obtain ⟨S,_,hs⟩ := test_radius η
  obtain ⟨U,_,hu⟩ := test_radius H
  obtain ⟨G,g0,Gt⟩ := gamma_annulus
  let B := 2*Real.exp (Real.log Real.pi+S/2+U)
  let A := ∫ z : ℝ×ℝ,‖envelope η H z‖
  let K := ∫ w : ℝ,‖H.function w‖*(4*w^2)
  let M := 4*(G*expMass B)^2
  have A0 : 0≤A := integral_nonneg fun _ => norm_nonneg _
  have K0 : 0≤K := integral_nonneg fun _ => by positivity
  have M0 : 0≤M := by dsimp [M]; positivity
  refine ⟨max (D+K) (A*M),max 0 S₀,(add_nonneg d0 K0).trans (le_max_left _ _),fun R hr t ht => ?_⟩
  have r0 := (le_max_left (0:ℝ) S₀).trans hr
  by_cases v : |t|≤radius
  · have L := E R ((le_max_right _ _).trans hr) ((t:ℂ)*I) (by simpa using v)
    have resp : ‖response H ((t:ℂ)*I)‖≤K := by
      apply norm_integral_le_of_norm_le ((H.smooth.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport H.compact.norm.mul_right)
      exact ae_of_all _ fun w => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kernel_bound t w) (norm_nonneg _)
    apply (norm_le_insert' _ (response H ((t:ℂ)*I))).trans
    apply le_trans _ (le_max_left _ _)
    have k := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith : -R/4≤0)) d0
    linarith only [resp,L,k]
  · have tt : t≠0 := fun e => v (by norm_num [e,radius])
    have gc := Gt t (le_of_lt (lt_of_not_ge v)) ht
    have Kb (x : ℝ) (hx : x≤Real.log Real.pi+S/2+U) :
        ‖complexOrderK ((t:ℂ)*I) (2*Real.exp x)‖≤G*expMass B := by
      exact (K_bound t tt (by positivity) (by dsimp [B]; gcongr)).trans (mul_le_mul_of_nonneg_right gc (expMass_nonneg _))
    apply le_trans _ (le_max_right _ _)
    dsimp only [A]; rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le ((envelope_L1 η H).norm.mul_const M) (ae_of_all _ _)
    intro z
    by_cases h : envelope η H z=0
    · simp [h]
    have a := (abs_le.mp (hs _ (left_ne_zero_of_mul h))).2
    have b := abs_le.mp (hu _ (right_ne_zero_of_mul h))
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [raw,norm_mul,norm_mul]
    norm_num only [Complex.norm_ofNat]
    dsimp [M]; rw [pow_two]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (Kb _ (by unfold logCenter; linarith))
      (Kb _ (by unfold logCenter; linarith)) (norm_nonneg _) (mul_nonneg g0 (expMass_nonneg _))) (by norm_num)

private theorem combine (U C : ℝ) (u0 : 0≤U) (c0 : 0≤C) {f : ℝ→ℂ}
    (lo : ∀ t,|t|≤1 → ‖f t‖≤U) (hi : ∀ t,1≤|t| → Real.cosh (Real.pi*t)*‖f t‖≤C/|t|^3) :
    ∀ t, (1+|t|)^3*Real.cosh (Real.pi*t)*‖f t‖≤8*(Real.cosh Real.pi*U+C) := by
  intro t
  rcases le_or_gt |t| 1 with l|l
  · have v : Real.cosh (Real.pi*t)≤Real.cosh Real.pi := by
      rw [Real.cosh_le_cosh,abs_mul,abs_of_pos Real.pi_pos]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left l Real.pi_pos.le
    have H : (1+|t|)^3≤8 := by norm_num1; nlinarith [pow_le_pow_left₀ (by positivity : 0≤1+|t|) (by linarith : 1+|t|≤2) 3]
    exact (mul_le_mul (mul_le_mul H v (Real.cosh_pos _).le (by norm_num)) (lo t l) (norm_nonneg _)
      (by positivity)).trans (by nlinarith)
  · have x := (le_div_iff₀ (pow_pos (lt_trans zero_lt_one l) 3)).mp (hi t l.le)
    have q : (1+|t|)^3≤8*|t|^3 := by
      simpa only [mul_pow,show (2:ℝ)^3=8 by norm_num] using pow_le_pow_left₀ (by positivity : 0≤1+|t|) (by linarith : 1+|t|≤2*|t|) 3
    calc
      _ ≤ 8*|t|^3*Real.cosh (Real.pi*t)*‖f t‖ := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (Real.cosh_pos Real.pi).le u0]

theorem packet_regular_price (η H : RadialTest) (mass : ∫ s : ℝ,η.function s=1)
    (zero : ∫ w : ℝ,H.function w=0) :
    ∃ D R₀ : ℝ,0≤D ∧ ∀ R≥R₀,∀ t : ℝ,
      (1+|t|)^3*Real.cosh (Real.pi*t)*‖packet η H R ((t:ℂ)*I)‖≤D := by
  obtain ⟨U,R₀,u,Hl⟩ := compact_real η H mass zero
  obtain ⟨C,c,Hh⟩ := packet_high η H
  exact ⟨8*(Real.cosh Real.pi*U+C),max 0 R₀,by positivity,fun R hR =>
    combine U C u c (Hl R ((le_max_right _ _).trans hR)) (Hh R ((le_max_left _ _).trans hR))⟩

private theorem exp_second (w : ℝ) : Real.exp (-|w|)*w^2≤8*Real.exp (-|w|/2) := by
  have p := Real.pow_div_factorial_le_exp (show 0≤|w|/2 by positivity) 2
  norm_num at p
  have q : w^2≤8*Real.exp (|w|/2) := by nlinarith [sq_abs w]
  have e : Real.exp (-|w|)*Real.exp (|w|/2)=Real.exp (-|w|/2) := by rw [←Real.exp_add]; congr 1; ring
  nlinarith [mul_le_mul_of_nonneg_left q (Real.exp_pos (-|w|)).le]

private theorem ratio_angular_second (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,∀ t : ℝ,(2*|t|)^2*‖angular (ratio ell hY n).function (2*(t:ℂ))‖≤C := by
  obtain ⟨K,k,H⟩ := ratio_jets ell hY 2
  let C := ∫ w : ℝ,K*Real.exp (-|w|)
  have c0 : 0≤C := integral_nonneg fun _ => by positivity
  refine ⟨C,c0,fun n t => ?_⟩
  let T := ratio ell hY n
  let ξ := 2*(t:ℂ)
  let D (j : ℕ) := iteratedDeriv j T.function
  have d (j : ℕ) : ContDiff ℝ ∞ (D j) := T.smooth.contDiff_iteratedDeriv j (by simp)
  have c (j : ℕ) : HasCompactSupport (D j) := by
    induction j with
    | zero => simpa [D] using T.compact
    | succ j ih => simpa only [D,iteratedDeriv_succ] using ih.deriv
  have Ij (j : ℕ) : Integrable (fun w : ℝ => D j w*wave ξ w) :=
    ((d j).continuous.mul (by unfold wave; fun_prop)).integrable_of_hasCompactSupport (c j).mul_right
  have step (j : ℕ) : angular (D (j+1)) ξ=I*ξ*angular (D j) ξ :=
    angular_derivative (fun w => by rw [show D (j+1)=deriv (D j) by rw [D,iteratedDeriv_succ]]; exact ((d j).differentiable (by simp) w).hasDerivAt) (Ij j) (Ij (j+1))
  have A := step 1
  rw [step 0] at A
  have E := congrArg norm A
  simp only [D,iteratedDeriv_zero,ξ,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_ofNat] at E
  have B : ‖angular (D 2) ξ‖≤C := by
    apply norm_integral_le_of_norm_le ((abs_exp_integrable zero_lt_one).const_mul K |>.congr (ae_of_all _ fun w => by simp))
    exact ae_of_all _ fun w => by rw [norm_mul,norm_wave_real]; simp only [ξ,Complex.mul_im,Complex.ofReal_im,Complex.ofNat_im,zero_mul,mul_zero,add_zero,Real.exp_zero,mul_one]; exact H n w
  calc
    _ = ‖angular (D 2) ξ‖ := by dsimp only [D,ξ]; rw [E]; ring
    _ ≤ C := B

theorem response_regular_price (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ D : ℝ,0≤D ∧ ∀ n : ℕ,∀ t : ℝ,
      (1+|t|)^3*Real.cosh (Real.pi*t)*‖response (ratio ell hY n) ((t:ℂ)*I)‖≤D := by
  obtain ⟨K,k,H⟩ := ratio_jets ell hY 0
  simp only [iteratedDeriv_zero] at H
  let U := ∫ w : ℝ,(32*K)*Real.exp (-|w|/2)
  have u0 : 0≤U := integral_nonneg fun w => by positivity
  have lo (n : ℕ) (t : ℝ) : ‖response (ratio ell hY n) ((t:ℂ)*I)‖≤U := by
    apply norm_integral_le_of_norm_le (((abs_exp_integrable (a:=1/2) (by norm_num)).const_mul (32*K)).congr (ae_of_all _ fun x => by congr 2 <;> ring))
    exact ae_of_all _ fun w => by
      rw [norm_mul]
      calc
        _ ≤ (K*Real.exp (-|w|))*(4*w^2) := mul_le_mul (H _ _) (kernel_bound _ _) (norm_nonneg _) (by positivity)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (exp_second w) k]
  obtain ⟨C,c0,c⟩ := ratio_angular_second ell hY
  let B := 2*Real.pi*(1+(Real.sinh Real.pi)⁻¹)*C
  have b0 : 0≤B := by dsimp [B]; positivity
  refine ⟨8*(Real.cosh Real.pi*U+B),by positivity,fun n => combine U B u0 b0 (fun t _ => lo n t) (fun t ht => ?_)⟩
  have tp := lt_of_lt_of_le zero_lt_one ht
  have sg := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos tp)
  have cz : Real.cosh (Real.pi*t)=Real.cosh (Real.pi*|t|) := by rw [← Real.cosh_abs,abs_mul,abs_of_pos Real.pi_pos]
  have sz : |Real.sinh (Real.pi*t)|=Real.sinh (Real.pi*|t|) := by
    rcases le_or_gt 0 t with p|p
    · rw [abs_of_nonneg p,abs_of_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le p))]
    · rw [abs_of_neg p,mul_neg,Real.sinh_neg,abs_of_neg (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos p))]
  have coth := coth_large (by linarith [mul_le_mul_of_nonneg_left ht Real.pi_pos.le] : Real.pi≤Real.pi*|t|)
  rw [ratio_regular ell hY (abs_pos.mp tp),norm_mul,norm_div,norm_mul,norm_mul,Complex.norm_ofNat,
    Complex.norm_real,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,sz,cz]
  apply (le_div_iff₀ (pow_pos tp 3)).mpr
  have h := c n t
  field_simp [tp.ne',sg.ne']
  dsimp [B]
  nlinarith [norm_nonneg (angular (ratio ell hY n).function (2*(t:ℂ))),
      mul_le_mul_of_nonneg_right coth (mul_nonneg (by positivity : 0≤2*Real.pi*|t|^2) (norm_nonneg _)),
    mul_le_mul_of_nonneg_left h (by positivity : 0≤2*Real.pi*(1+(Real.sinh Real.pi)⁻¹)*Real.sinh (Real.pi*|t|))]

end
end ImbalancedChen.Part3.OriginalPositiveRegularPrice20261112
