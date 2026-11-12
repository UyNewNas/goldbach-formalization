import ImbalancedChen.Part3ActualPositiveCenteredKLimit
import ImbalancedChen.Part3ActualKLCompactTestIntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual compact log-product packet and its limiting scalar
coefficient. Both tests use unscaled Lebesgue measure. -/
namespace ImbalancedChen.Part3.ActualPositiveScalarPacket20261112

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ContDiff
open RadialSchrodingerL2Form20261025a ComplexOrderKBridgeSourceOnly
open ComplexOrderKRadialRegularitySourceOnly ActualPositiveCenteredKLimit20261112
open ActualPositiveSmallHeightWaves20261112 (radius)

def logCenter (R s : ℝ) := Real.log Real.pi+(s-R)/2

def raw (ν : ℂ) (L w : ℝ) : ℂ :=
  4*(complexOrderK ν (2*Real.exp (L+w))*complexOrderK ν (2*Real.exp (L-w)))

def envelope (η h : RadialTest) (z : ℝ×ℝ) := η.function z.1*h.function z.2

def packet (η h : RadialTest) (R : ℝ) (ν : ℂ) : ℂ :=
  ∫ z : ℝ×ℝ,envelope η h z*raw ν (logCenter R z.1) z.2

def response (h : RadialTest) (ν : ℂ) : ℂ := ∫ w : ℝ,h.function w*limitKernel ν w

theorem test_radius (T : RadialTest) :
    ∃ U : ℝ,0≤U ∧ ∀ w : ℝ,T.function w≠0 → |w|≤U := by
  obtain ⟨C,H⟩ := T.compact.exists_bound_of_continuousOn (f:=id) continuous_id.continuousOn
  exact ⟨max C 0,le_max_right _ _,fun w hw => (by simpa using H w (subset_tsupport _ hw)).trans (le_max_left _ _)⟩

theorem envelope_compact (η h : RadialTest) : HasCompactSupport (envelope η h) := by
  apply HasCompactSupport.of_support_subset_isCompact (η.compact.prod h.compact)
  intro z hz
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hz),subset_tsupport _ (right_ne_zero_of_mul hz)⟩

theorem envelope_cont (η h : RadialTest) : Continuous (envelope η h) :=
  (η.smooth.continuous.comp continuous_fst).mul (h.smooth.continuous.comp continuous_snd)

theorem envelope_L1 (η h : RadialTest) : Integrable (envelope η h) :=
  (envelope_cont η h).integrable_of_hasCompactSupport (envelope_compact η h)

theorem Klog_cont (ν : ℂ) : Continuous (fun x : ℝ => complexOrderK ν (2*Real.exp x)) := by
  have E (x : ℝ) : 2*Real.exp x=Real.exp (Real.log 2+x) := by
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  simp_rw [E]
  exact (radialK_C2 ν).continuous.comp (continuous_const.add continuous_id)

private theorem limit_cont (ν : ℂ) : Continuous (limitKernel ν) := by
  have A : Continuous sinhc := (differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (s:=Set.univ) (c:=0) univ_mem).mpr
      Complex.differentiable_sinh.differentiableOn)).continuous
  unfold limitKernel
  exact (continuous_const.mul (Complex.continuous_ofReal.pow 2)).mul
    ((A.comp (continuous_const.mul Complex.continuous_ofReal)).pow 2)

theorem raw_cont (ν : ℂ) : Continuous (fun z : ℝ×ℝ => raw ν z.1 z.2) := by
  unfold raw
  exact continuous_const.mul (((Klog_cont ν).comp (continuous_fst.add continuous_snd)).mul
    ((Klog_cont ν).comp (continuous_fst.sub continuous_snd)))

theorem raw_L1 (η h : RadialTest) (R : ℝ) (ν : ℂ) :
    Integrable (fun z : ℝ×ℝ => envelope η h z*raw ν (logCenter R z.1) z.2) :=
  ((envelope_cont η h).mul ((raw_cont ν).comp (by dsimp [logCenter]; fun_prop))).integrable_of_hasCompactSupport
    (envelope_compact η h).mul_right

private theorem central_cont (R : ℝ) (ν : ℂ) :
    Continuous (fun s : ℝ => 4*complexOrderK ν (2*Real.exp (logCenter R s))^2) :=
  continuous_const.mul (((Klog_cont ν).comp (by unfold logCenter; fun_prop)).pow 2)

theorem response_integrable (h : RadialTest) (ν : ℂ) :
    Integrable (fun w : ℝ => h.function w*limitKernel ν w) :=
  (h.smooth.continuous.mul (limit_cont ν)).integrable_of_hasCompactSupport h.compact.mul_right

theorem centered_identity (η h : RadialTest) (mass : ∫ s : ℝ,η.function s=1)
    (zero : ∫ w : ℝ,h.function w=0) (R : ℝ) (ν : ℂ) :
    packet η h R ν-response h ν=∫ z : ℝ×ℝ,envelope η h z*
      (centered ν (logCenter R z.1) z.2-limitKernel ν z.2) := by
  let mid (s : ℝ) := 4*complexOrderK ν (2*Real.exp (logCenter R s))^2
  have X : Integrable (fun z : ℝ×ℝ => envelope η h z*mid z.1) :=
    ((envelope_cont η h).mul ((central_cont R ν).comp continuous_fst)).integrable_of_hasCompactSupport
      (envelope_compact η h).mul_right
  have Y : Integrable (fun z : ℝ×ℝ => envelope η h z*limitKernel ν z.2) :=
    ((envelope_cont η h).mul ((limit_cont ν).comp continuous_snd)).integrable_of_hasCompactSupport
      (envelope_compact η h).mul_right
  have x : (∫ z : ℝ×ℝ,envelope η h z*mid z.1)=0 := by
    simp_rw [envelope,show ∀ a b c : ℂ,a*b*c=(a*c)*b by intros; ring]
    rw [integral_prod_mul,zero,mul_zero]
  have y : (∫ z : ℝ×ℝ,envelope η h z*limitKernel ν z.2)=response h ν := by
    simp_rw [envelope,mul_assoc]; rw [integral_prod_mul,mass,one_mul,response]
  have eqn (z : ℝ×ℝ) : envelope η h z*(centered ν (logCenter R z.1) z.2-limitKernel ν z.2)=
    (envelope η h z*raw ν (logCenter R z.1) z.2-envelope η h z*mid z.1)-envelope η h z*limitKernel ν z.2 := by
    unfold centered raw mid; ring
  simp_rw [eqn]
  rw [integral_sub ((raw_L1 η h R ν).sub X) Y,integral_sub (raw_L1 η h R ν) X,x,y,sub_zero,packet]

private theorem integrate_error (η h : RadialTest) (mass : ∫ s : ℝ,η.function s=1)
    (zero : ∫ w : ℝ,h.function w=0) (R : ℝ) (ν : ℂ) (C : ℝ)
    (H : ∀ z : ℝ×ℝ,envelope η h z≠0 →
      ‖centered ν (logCenter R z.1) z.2-limitKernel ν z.2‖≤C) :
    ‖packet η h R ν-response h ν‖≤(∫ z : ℝ×ℝ,‖envelope η h z‖)*C := by
  rw [centered_identity η h mass zero,← integral_mul_const]
  apply norm_integral_le_of_norm_le ((envelope_L1 η h).norm.mul_const _) (ae_of_all _ _)
  intro z
  by_cases hz : envelope η h z=0
  · simp [hz]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (H z hz) (norm_nonneg _)

private theorem center_bounds {S U R s : ℝ} (hs : |s|≤S)
    (r : 2*(Real.log Real.pi+U)+S≤R) :
    logCenter R s≤-U ∧ Real.exp (logCenter R s/2)≤
      Real.exp (Real.log Real.pi/2+S/4)*Real.exp (-R/4) := by
  constructor
  · unfold logCenter; linarith [(abs_le.mp hs).2]
  · rw [← Real.exp_add,Real.exp_le_exp]; unfold logCenter; linarith [(abs_le.mp hs).2]

theorem packet_disk_error (η h : RadialTest) (mass : ∫ s : ℝ,η.function s=1)
    (zero : ∫ w : ℝ,h.function w=0) :
    ∃ C R₀ : ℝ,0≤C ∧ ∀ R≥R₀,∀ ν : ℂ,‖ν‖≤radius →
      ‖packet η h R ν-response h ν‖≤C*Real.exp (-R/4) := by
  obtain ⟨S,_,sp⟩ := test_radius η
  obtain ⟨U,_,su⟩ := test_radius h
  obtain ⟨C,c0,hd⟩ := disk_error U
  let A := ∫ z : ℝ×ℝ,‖envelope η h z‖
  have a0 : 0≤A := integral_nonneg fun _ => norm_nonneg _
  refine ⟨A*C*Real.exp (Real.log Real.pi/2+S/4),2*(Real.log Real.pi+U)+S,by positivity,fun R hR ν hv => ?_⟩
  have H (z : ℝ×ℝ) (hz : envelope η h z≠0) := center_bounds (sp _ (left_ne_zero_of_mul hz)) hR
  have E := integrate_error η h mass zero R ν (C*(Real.exp (Real.log Real.pi/2+S/4)*Real.exp (-R/4))) (fun z hz =>
    (hd ν hv _ (H z hz).1 _ (su _ (right_ne_zero_of_mul hz))).trans
      (mul_le_mul_of_nonneg_left (H z hz).2 c0))
  convert E using 1 <;> dsimp [A] <;> ring

/-- Fixed order convergence includes every real t and all physical
complementary slots. The value at ν=0 comes from the same integral. -/
theorem packet_limit (η h : RadialTest) (mass : ∫ s : ℝ,η.function s=1)
    (zero : ∫ w : ℝ,h.function w=0) {ν : ℂ} (ord : |ν.re|≤radius) :
    Tendsto (fun R : ℝ => packet η h R ν) atTop (𝓝 (response h ν)) := by
  have H : ∃ C R₀ : ℝ,0≤C ∧ ∀ R≥R₀,‖packet η h R ν-response h ν‖≤C*Real.exp (-R/4) := by
    by_cases v : ‖ν‖≤radius
    · obtain ⟨C,R,c,L⟩ := packet_disk_error η h mass zero
      exact ⟨C,R,c,fun x hx => L x hx _ v⟩
    obtain ⟨S,_,sp⟩ := test_radius η
    obtain ⟨U,_,su⟩ := test_radius h
    have nz : ν≠0 := fun z => v (by norm_num [z,radius])
    obtain ⟨C,c0,L⟩ := fixed_error nz ord U
    let A := ∫ z : ℝ×ℝ,‖envelope η h z‖
    have a0 : 0≤A := integral_nonneg fun _ => norm_nonneg _
    refine ⟨A*C*Real.exp (Real.log Real.pi/2+S/4),2*(Real.log Real.pi+U)+S,by positivity,fun R hR => ?_⟩
    have H (z : ℝ×ℝ) (hz : envelope η h z≠0) := center_bounds (sp _ (left_ne_zero_of_mul hz)) hR
    have E := integrate_error η h mass zero R ν (C*(Real.exp (Real.log Real.pi/2+S/4)*Real.exp (-R/4))) (fun z hz =>
      (L _ (H z hz).1 _ (su _ (right_ne_zero_of_mul hz))).trans (mul_le_mul_of_nonneg_left (H z hz).2 c0))
    convert E using 1 <;> dsimp [A] <;> ring
  obtain ⟨C,R,c,B⟩ := H
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have T : Tendsto (fun R : ℝ => -R/4) atTop atBot := by
    simpa [neg_div] using (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<4)).neg_atTop
  have e := (Real.tendsto_exp_atBot.comp T).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [mul_zero] using e)
  exact (eventually_ge_atTop R).mono B

theorem response_zero (h : RadialTest) : response h 0= -4*∫ w : ℝ,h.function w*(w:ℂ)^2 := by
  simp only [response,limit_zero]; rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun _ => by ring)

theorem response_nonzero (h : RadialTest) (zero : ∫ w : ℝ,h.function w=0) {ν : ℂ} (nz : ν≠0) :
    response h ν=2*Gamma ν*Gamma (-ν)*∫ w : ℝ,h.function w*cosh (2*ν*(w:ℂ)) := by
  have X := (h.smooth.continuous.mul (by fun_prop :
    Continuous (fun w : ℝ => cosh (2*ν*(w:ℂ))))).integrable_of_hasCompactSupport h.compact.mul_right
  have Y := h.smooth.continuous.integrable_of_hasCompactSupport h.compact
  rw [response]
  simp_rw [limit_cosh nz,show ∀ x y z : ℂ,x*(z*(y-1))=z*(x*y-x) by intros; ring]
  rw [integral_const_mul,integral_sub X Y,zero,sub_zero]

end
end ImbalancedChen.Part3.ActualPositiveScalarPacket20261112
