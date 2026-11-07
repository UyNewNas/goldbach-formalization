import ImbalancedChen.P5ActualHBChartEventualClosure
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- The cutoff depends ONLY on original R labels and their number. It is
-- fixed before HB order, occurrence words, tuples or selected slots.
namespace ImbalancedChen.P5Z.OriginalChartRoughCutoff
noncomputable section
open Classical Filter
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow ActualHBMediumBranchPartition
open SmoothChartHBDyadicPartition SmoothChartPhysicalHBBranch
open ActualMultiGroupHBChartScale ActualHBChartEventualClosure

def roughF (t : ℝ) : ℝ := t^(1/(Real.log (Real.log t))^3)

def argument (K : ℕ) (Rs : List ℝ) : ℝ :=
  (2 : ℝ)^(6*K+2) * ((2 : ℝ)^Rs.length * Rs.prod)

def chartCutoff (K : ℕ) (Rs : List ℝ) : ℝ := roughF (argument K Rs)

def envelope (K : ℕ) : ℝ := (2 : ℝ)^(6*K+2) * (2 : ℝ)^K * scaleConstant K

def threshold (K : ℕ) : ℝ := max (envelope K) (Real.exp (Real.exp 3))

theorem envelope_pos (K : ℕ) : 0 < envelope K := by
  unfold envelope
  exact mul_pos (mul_pos (by positivity) (by positivity)) (scaleConstant_pos K)

theorem chartX_eq_prod (gs : List Group) : chartX gs = (gs.map Group.R).prod := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [chartX,List.map_cons,List.prod_cons,ih]

theorem argument_eq (K : ℕ) (gs : List Group) :
    argument K (gs.map Group.R) = (2 : ℝ)^(6*K+2)*chartXplus gs := by
  simp only [argument,List.length_map,chartXplus,chartX_eq_prod]

theorem roughF_eq_exp {t : ℝ} (ht : 0 < t) :
    roughF t = Real.exp (Real.log t / (Real.log (Real.log t))^3) := by
  rw [roughF,Real.rpow_def_of_pos ht]
  congr 1
  ring

-- Reuse the proved antitonicity of log(u)/u^(1/3). Cubing its positive
-- cross-products gives monotonicity of log(t)/(loglog(t))^3.
theorem roughF_mono {x v : ℝ} (hx : 1 < x)
    (hell : 3 ≤ Real.log (Real.log x)) (hxv : x ≤ v) : roughF x ≤ roughF v := by
  have hxp : 0 < x := by linarith
  have hv : 1 < v := hx.trans_le hxv
  have hvp : 0 < v := by linarith
  have hLx := Real.log_pos hx
  have hLv := Real.log_pos hv
  have hlogs := Real.log_le_log hxp hxv
  have hells := Real.log_le_log hLx hlogs
  have hellx : 0 < Real.log (Real.log x) := by linarith
  have hellv : 0 < Real.log (Real.log v) := by linarith
  have hbx : Real.exp ((1/3 : ℝ)⁻¹) ≤ Real.log x := by
    norm_num
    exact (Real.le_log_iff_exp_le hLx).mp hell
  have hbv : Real.exp ((1/3 : ℝ)⁻¹) ≤ Real.log v := hbx.trans hlogs
  have hm := Real.log_div_self_rpow_antitoneOn (a:=1/3) (by norm_num)
    hbx hbv hlogs
  have hrx := Real.rpow_pos_of_pos hLx (1/3 : ℝ)
  have hrv := Real.rpow_pos_of_pos hLv (1/3 : ℝ)
  have hcross := (div_le_div_iff₀ hrv hrx).mp hm
  have hcubes := pow_le_pow_left₀ (mul_nonneg hellv.le hrx.le) hcross 3
  have hrootx : ((Real.log x)^(1/3 : ℝ))^3 = Real.log x := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hLx.le]
    norm_num
  have hrootv : ((Real.log v)^(1/3 : ℝ))^3 = Real.log v := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hLv.le]
    norm_num
  rw [mul_pow,mul_pow,hrootx,hrootv] at hcubes
  have hquot : Real.log x/(Real.log (Real.log x))^3 ≤
      Real.log v/(Real.log (Real.log v))^3 := by
    apply (div_le_div_iff₀ (pow_pos hellx 3) (pow_pos hellv 3)).mpr
    nlinarith
  rw [roughF_eq_exp hxp,roughF_eq_exp hvp]
  exact Real.exp_le_exp.mpr hquot

theorem roughF_upper {x v : ℝ} (hx : 1 < x)
    (hell : 3 ≤ Real.log (Real.log x)) (hxv : x ≤ v) (hvx : v ≤ x^2) :
    roughF v ≤ x^(2/(Real.log (Real.log x))^3) := by
  have hxp : 0 < x := by linarith
  have hv : 1 < v := hx.trans_le hxv
  have hvp : 0 < v := by linarith
  have hLx := Real.log_pos hx
  have hLv := Real.log_pos hv
  have hlogs := Real.log_le_log hxp hxv
  have hells := Real.log_le_log hLx hlogs
  have hellx : 0 < Real.log (Real.log x) := by linarith
  have hellv : 0 < Real.log (Real.log v) := by linarith
  have hden := pow_le_pow_left₀ hellx.le hells 3
  have hlogupper : Real.log v ≤ 2*Real.log x := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hvp hvx
  have hquot : Real.log v/(Real.log (Real.log v))^3 ≤
      (2*Real.log x)/(Real.log (Real.log x))^3 := by
    exact (div_le_div_of_nonneg_left hLv.le (pow_pos hellx 3) hden).trans
      (div_le_div_of_nonneg_right hlogupper (pow_nonneg hellx.le 3))
  rw [roughF_eq_exp hvp,Real.rpow_def_of_pos hxp]
  apply Real.exp_le_exp.mpr
  calc
    Real.log v/(Real.log (Real.log v))^3 ≤
        (2*Real.log x)/(Real.log (Real.log x))^3 := hquot
    _ = Real.log x*(2/(Real.log (Real.log x))^3) := by ring

-- This lemma handles EVERY concrete local x returned by phase3. Its
-- (S) upper inequality is a proved intermediate, not a primitive oracle
-- in the actual chart theorem below.
theorem cutoff_bounds_of_geometry (K : ℕ) (gs : List Group) (hrank : gs.length ≤ K)
    {x : ℝ} (hxp : 0 < x)
    (hS : x ≤ (2 : ℝ)^(6*gs.length-1)*chartXplus gs)
    (hXx : chartX gs ≤ scaleConstant K*x) (hxlarge : threshold K ≤ x) :
    3 ≤ Real.log (Real.log x) ∧ roughF x ≤ chartCutoff K (gs.map Group.R) ∧
      chartCutoff K (gs.map Group.R) ≤ x^(2/(Real.log (Real.log x))^3) := by
  let v := argument K (gs.map Group.R)
  have hXp := (whole_geometry gs).1
  have hXplus : 0 ≤ chartXplus gs := by unfold chartXplus; positivity
  have hxv : x ≤ v := by
    calc
      x ≤ (2 : ℝ)^(6*gs.length-1)*chartXplus gs := hS
      _ ≤ (2 : ℝ)^(6*K+2)*chartXplus gs :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) hXplus
      _ = v := (argument_eq K gs).symm
  have hvEnvelope : v ≤ envelope K*x := by
    rw [show v = (2 : ℝ)^(6*K+2)*chartXplus gs from argument_eq K gs]
    calc
      (2 : ℝ)^(6*K+2)*chartXplus gs ≤
          (2 : ℝ)^(6*K+2)*((2 : ℝ)^K*chartX gs) := by
        unfold chartXplus
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrank) hXp.le) (by positivity)
      _ ≤ (2 : ℝ)^(6*K+2)*((2 : ℝ)^K*(scaleConstant K*x)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hXx (by positivity)) (by positivity)
      _ = envelope K*x := by unfold envelope; ring
  have hxEnv : envelope K ≤ x := (le_max_left _ _).trans hxlarge
  have hxExp : Real.exp (Real.exp 3) ≤ x := (le_max_right _ _).trans hxlarge
  have hx1 : 1 < x :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 3)).trans_le hxExp
  have hLx := Real.log_pos hx1
  have hlog : Real.exp 3 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hxExp
  have hell : 3 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hLx).mpr hlog
  have hvx : v ≤ x^2 := by
    have h := mul_le_mul_of_nonneg_right hxEnv hxp.le
    nlinarith [hvEnvelope]
  exact ⟨hell,roughF_mono hx1 hell hxv,roughF_upper hx1 hell hxv hvx⟩

-- One T threshold is before all chart groups, HB choices and selected
-- occurrences. Only the original complete smooth-trim support is used.
theorem actual_cutoff_eventually (K : ℕ) {kappa0 : ℝ} (hkappa : kappa0 < 1) :
    ∃ T0 : ℝ, 1 < T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ gs : List Group,
      gs.length ≤ K → T^(1-kappa0) ≤ chartN gs →
      ∀ (left right : List Block) (b : Block), blocks gs = left++b::right →
        ∃ pl p pr, integers gs = pl++p::pr ∧
          let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
          3 ≤ Real.log (Real.log x) ∧ roughF x ≤ chartCutoff K (gs.map Group.R) ∧
            chartCutoff K (gs.map Group.R) ≤ x^(2/(Real.log (Real.log x))^3) := by
  let A : ℝ := (2 : ℝ)^K*scaleConstant K
  have hA : 0 < A := by dsimp [A]; exact mul_pos (by positivity) (scaleConstant_pos K)
  have he : ∀ᶠ T : ℝ in atTop, 1 < T ∧ A*threshold K ≤ T^(1-kappa0) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kappa0)).eventually
        (eventually_ge_atTop (A*threshold K))] with T h1 h2
    exact ⟨h1,h2⟩
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp he
  let T0 : ℝ := max 2 Q
  refine ⟨T0,by dsimp [T0]; linarith [le_max_left (2 : ℝ) Q],?_⟩
  intro T hT gs hrank htrim left right b hsplit
  obtain ⟨hT1,hlarge⟩ := hQ T ((le_max_right (2 : ℝ) Q).trans hT)
  obtain ⟨pl,p,pr,hints,hl,hp,hr,howner,hxp,hXx,hS,hxX⟩ :=
    actual_complementary_scale gs left right b hsplit
  let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
  have hXp := (whole_geometry gs).1
  have hXxK : chartX gs ≤ scaleConstant K*x :=
    hXx.trans (mul_le_mul_of_nonneg_right (scaleConstant_mono hrank) hxp.le)
  have hN := (original_product_geometry gs).2.1
  have hbound : T^(1-kappa0) ≤ A*x := by
    calc
      T^(1-kappa0) ≤ chartN gs := htrim
      _ ≤ (2 : ℝ)^gs.length*chartX gs := hN
      _ ≤ (2 : ℝ)^K*chartX gs := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrank) hXp.le
      _ ≤ (2 : ℝ)^K*(scaleConstant K*x) :=
        mul_le_mul_of_nonneg_left hXxK (by positivity)
      _ = A*x := by dsimp [A]; ring
  have hxlarge : threshold K ≤ x := (mul_le_mul_left hA).mp (hlarge.trans hbound)
  have hcut := cutoff_bounds_of_geometry K gs hrank hxp hS hXxK hxlarge
  exact ⟨pl,p,pr,hints,hcut⟩

end
end ImbalancedChen.P5Z.OriginalChartRoughCutoff
