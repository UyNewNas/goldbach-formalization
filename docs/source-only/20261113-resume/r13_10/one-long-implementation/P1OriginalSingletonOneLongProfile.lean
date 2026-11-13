import ImbalancedChen.P1OriginalSingletonOneLongFibres

/-! The actual q-independent one-variable geometric/log profile. Its
reciprocal group logarithm is the existing genuine smooth normalizer,
not a reciprocal logarithm of the selected HB factor. No profile norm
estimate or final one-long estimate is assumed in this construction. -/
namespace ImbalancedChen.P1OriginalSingletonOneLongProfile
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open P5Z.ActualEtaPsiOccurrenceBudget
open P5Z.ActualRoughHeathBrownWords P5Z.HBRightClosedDyadicRoles
open P5Z.ActualHBDyadicProductWindow P5Z.ActualHBPostModulusLogCutoff
open P5Z.ActualLowerNormalizedAtlasOccurrence
open P5Z.ActualLowerNormalizedHBSource
open P5Z.ExactOriginalSmoothDyadicPartition (R)
open P5Z.GroupedOccurrenceLogShift P5Z.AllWordAmbientOccurrenceBound
open P5Z.ActualOccurrencePlateauWordBudget

def realProfile (kap : ℝ) (B N cj : ℕ) (kap0 x : ℝ) : ℝ :=
  ambient kap B N (fun _ : Fin 1=>x)*eta (x/(N : ℝ)^(1-kap0))*psi (x/R cj)

theorem realProfile_smooth (kap : ℝ) (B N cj : ℕ) (kap0 : ℝ) :
    ContDiff ℝ ∞ (realProfile kap B N cj kap0) := by
  have hA : ContDiff ℝ ∞ (fun x : ℝ=>ambient kap B N (fun _ : Fin 1=>x)) :=
    (ambient_smooth kap B N).comp (contDiff_pi.mpr (fun _=>contDiff_id))
  exact (hA.mul (eta_smooth.comp (contDiff_id.div_const _))).mul
    (psi_smooth.comp (contDiff_id.div_const _))

theorem realProfile_nat (kap : ℝ) (B N cj : ℕ) (kap0 : ℝ) (n : ℕ) :
    realProfile kap B N cj kap0 (n : ℝ)=scalarProfile kap B N cj kap0 n := by
  exact (scalarProfile_eq_ambient kap B N cj kap0 n).symm

/-- The existing actual chart budget supplies a fixed polylogarithmic
zeroth/Euler-first norm for the SAME complete real profile. The auxiliary
chart base is frozen at X while differentiating in t; it is not varied in
that derivative. No amplitude or derivative bound is an input. -/
theorem realProfile_uniform_euler (B : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ (kap : ℝ) (N cj : ℕ) (kap0 X : ℝ),
      0<(N : ℝ) → 0<X →
      |realProfile kap B N cj kap0 X|≤C*Real.log ((N : ℝ)+2)^(B*12) ∧
      |X*deriv (realProfile kap B N cj kap0) X|≤C*Real.log ((N : ℝ)+2)^(B*12) := by
  obtain ⟨C,hC,hbudget⟩ := complete_chart_word_budget B
  refine ⟨C,hC,?_⟩
  intro kap N cj kap0 X hN hX
  let t0 : ℝ := Real.log 2/2
  have ht0 : 0<t0 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have ht1 : t0<Real.log 2 := by dsimp [t0]; linarith [Real.log_pos (by norm_num : (1 : ℝ)<2)]
  let Us : Fin 1→ℝ := fun _=>X*Real.exp (-t0)
  let Rs : Fin 1→ℝ := fun _=>R cj
  let z0 : Fin 1→ℝ := fun _=>t0
  let G : (Fin 1→ℝ)→ℝ := chart kap B N id Us Rs kap0
  let H : ℝ→ℝ := fun t=>realProfile kap B N cj kap0 (X*Real.exp t)
  have hUs : ∀ a,0<Us a := fun _=>mul_pos hX (Real.exp_pos _)
  have hRs : ∀ i,0<Rs i := fun _=>P5Z.ExactOriginalSmoothDyadicPartition.R_pos cj
  have local_dictionary : (fun t : ℝ=>G (z0+Pi.single (0 : Fin 1) t))=ᶠ[𝓝 (0 : ℝ)] H := by
    filter_upwards [Ioo_mem_nhds (show -t0<(0 : ℝ) by linarith)
      (show (0 : ℝ)<Real.log 2-t0 by linarith)] with t ht
    have hplateau : c (t0+t)=1 := c_eq_one ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hcoordinate : (z0+Pi.single (0 : Fin 1) t) 0=t0+t := by simp [z0]
    have hproduct (i : Fin 1) :
        groupProduct id Us i (z0+Pi.single (0 : Fin 1) t)=X*Real.exp t := by
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      have hscale : (X*Real.exp (-t0))*Real.exp (t0+t)=X*Real.exp t := by
        calc
          (X*Real.exp (-t0))*Real.exp (t0+t)=X*(Real.exp (-t0)*Real.exp (t0+t)) := by ring
          _=X*Real.exp (-t0+(t0+t)) := by rw [Real.exp_add]
          _=X*Real.exp t := by rw [show -t0+(t0+t)=t by ring]
      simpa [groupProduct,groupBase,groupLog,Us,hcoordinate] using hscale
    simp only [G,chart,actualEta,actualPsi,plateau,hproduct,Fin.prod_univ_one,
      hcoordinate,hplateau,mul_one,H,realProfile]
  have hvalue : G z0=realProfile kap B N cj kap0 X := by
    simpa [H] using local_dictionary.eq_of_nhds
  have hderivative : deriv H 0=X*deriv (realProfile kap B N cj kap0) X := by
    have hd := (((realProfile_smooth kap B N cj kap0).differentiable (by simp))
      (X*Real.exp 0)).hasDerivAt.comp 0 ((Real.hasDerivAt_exp 0).const_mul X)
    simpa only [H,Function.comp_def,Real.exp_zero,mul_one,one_mul,mul_comm] using hd.deriv
  have hzero := hbudget kap N 1 id Us Rs kap0 [] z0 hN hUs hRs (by norm_num) (by simp)
  have hone := hbudget kap N 1 id Us Rs kap0 [(0 : Fin 1)] z0 hN hUs hRs (by norm_num) (by norm_num)
  change |G z0|≤_ at hzero
  change |deriv (fun t : ℝ=>G (z0+Pi.single (0 : Fin 1) t)) 0|≤_ at hone
  rw [hvalue] at hzero
  rw [local_dictionary.deriv_eq,hderivative] at hone
  exact ⟨hzero,hone⟩

theorem scaled_realProfile_derivative (kap : ℝ) (B N cj : ℕ) (kap0 A v : ℝ) :
    deriv (fun x : ℝ=>realProfile kap B N cj kap0 (A*x)) v=
      A*deriv (realProfile kap B N cj kap0) (A*v) := by
  have hd := (((realProfile_smooth kap B N cj kap0).differentiable (by simp))
    (A*v)).hasDerivAt.comp v ((hasDerivAt_id v).const_mul A)
  simpa only [Function.comp_def,mul_one,one_mul,mul_comm] using hd.deriv

/-- A fixed smooth extension, equal to one on the full CLOSED normalized
HB atom [1,2]. It adds no integer endpoint or arithmetic restriction. -/
def slotCutoff (v : ℝ) : ℝ := eta (2*v)*chi (v/2)

theorem slotCutoff_smooth : ContDiff ℝ ∞ slotCutoff := by
  exact (eta_smooth.comp (contDiff_const.mul contDiff_id)).mul
    ((contDiff_const.sub eta_smooth).comp (contDiff_id.div_const _))

theorem slotCutoff_one {v : ℝ} (hv : v∈Icc (1 : ℝ) 2) : slotCutoff v=1 := by
  have he := eta_one (by linarith [hv.1] : 2≤2*v)
  have hc := eta_zero (by linarith [hv.2] : v/2≤1)
  simp [slotCutoff,chi,he,hc]

theorem slotCutoff_zero_left {v : ℝ} (hv : v≤1/2) : slotCutoff v=0 := by
  simp only [slotCutoff,eta_zero (by linarith : 2*v≤1),zero_mul]

theorem slotCutoff_zero_right {v : ℝ} (hv : 4≤v) : slotCutoff v=0 := by
  simp only [slotCutoff,chi,eta_one (by linarith : 2≤v/2),sub_self,mul_zero]

theorem slotCutoff_C1_constants :
    ∃ S : ℝ,1≤S ∧ ∀ v∈Icc (1/2 : ℝ) 4,|slotCutoff v|≤S ∧ |deriv slotCutoff v|≤S := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (1/2 : ℝ) 4)).exists_bound_of_continuousOn
    slotCutoff_smooth.continuous.continuousOn
  have hs : ContDiff ℝ 1 slotCutoff := slotCutoff_smooth.of_le (by simp)
  have hd : ContinuousOn (deriv slotCutoff) (Set.univ : Set ℝ) :=
    hs.contDiffOn.continuousOn_deriv_of_isOpen isOpen_univ (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Icc (1/2 : ℝ) 4)).exists_bound_of_continuousOn
    (hd.mono (subset_univ _))
  refine ⟨max 1 (max M D),le_max_left _ _,?_⟩
  intro v hv
  constructor
  · simpa only [Real.norm_eq_abs] using
      (hM v hv).trans ((le_max_left M D).trans (le_max_right 1 (max M D)))
  · simpa only [Real.norm_eq_abs] using
      (hD v hv).trans ((le_max_right M D).trans (le_max_right 1 (max M D)))

def longProfile (kap : ℝ) (B N cj : ℕ) (kap0 : ℝ) (m U : ℕ)
    (useLog : Bool) (v : ℝ) : ℂ :=
  if 0<v then
    ((realProfile kap B N cj kap0 ((m : ℝ)*(U : ℝ)*v)*slotCutoff v*
      (if useLog then Real.log ((U : ℝ)*v) else 1) : ℝ) : ℂ)
  else 0

theorem longProfile_zero_left (kap : ℝ) (B N cj : ℕ) (kap0 : ℝ) (m U : ℕ)
    (useLog : Bool) {v : ℝ} (hv : v≤1/2) :
    longProfile kap B N cj kap0 m U useLog v=0 := by
  by_cases hp : 0<v <;> simp [longProfile,hp,slotCutoff_zero_left hv]

theorem longProfile_zero_right (kap : ℝ) (B N cj : ℕ) (kap0 : ℝ) (m U : ℕ)
    (useLog : Bool) {v : ℝ} (hv : 4≤v) :
    longProfile kap B N cj kap0 m U useLog v=0 := by
  have hp : 0<v := by linarith
  simp [longProfile,hp,slotCutoff_zero_right hv]

theorem longProfile_compact (kap : ℝ) (B N cj : ℕ) (kap0 : ℝ) (m U : ℕ)
    (useLog : Bool) : HasCompactSupport (longProfile kap B N cj kap0 m U useLog) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (1/2 : ℝ) 4))
  intro v hv
  constructor
  · by_contra h
    exact hv (longProfile_zero_left kap B N cj kap0 m U useLog (lt_of_not_ge h).le)
  · by_contra h
    exact hv (longProfile_zero_right kap B N cj kap0 m U useLog (lt_of_not_ge h).le)

/-- Global smoothness is proved from the actual extension. In particular,
the apparent log(Uv) singularity is absent in a whole neighbourhood of 0. -/
theorem longProfile_smooth (kap : ℝ) (B N cj : ℕ) (kap0 : ℝ) (m U : ℕ)
    (hU : 0<U) (useLog : Bool) :
    ContDiff ℝ ∞ (longProfile kap B N cj kap0 m U useLog) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : 0<v
  · have hgeom : ContDiffAt ℝ ∞ (fun x : ℝ=>
        realProfile kap B N cj kap0 ((m : ℝ)*(U : ℝ)*x)*slotCutoff x) v :=
      ((realProfile_smooth kap B N cj kap0).comp
        (contDiff_const.mul contDiff_id)).contDiffAt.mul slotCutoff_smooth.contDiffAt
    have hUp : (0 : ℝ)<U := by exact_mod_cast hU
    have hlog : ContDiffAt ℝ ∞ (fun x : ℝ=>Real.log ((U : ℝ)*x)) v :=
      (Real.contDiffAt_log (mul_pos hUp hv).ne').comp v
        (contDiff_const.mul contDiff_id).contDiffAt
    have hraw : ContDiffAt ℝ ∞ (fun x : ℝ=>
        ((realProfile kap B N cj kap0 ((m : ℝ)*(U : ℝ)*x)*slotCutoff x*
          (if useLog then Real.log ((U : ℝ)*x) else 1) : ℝ) : ℂ)) v := by
      cases useLog with
      | false => simpa using Complex.ofRealCLM.contDiff.contDiffAt.comp v hgeom
      | true => exact Complex.ofRealCLM.contDiff.contDiffAt.comp v (hgeom.mul hlog)
    have heq : longProfile kap B N cj kap0 m U useLog =ᶠ[𝓝 v]
        (fun x : ℝ=>
          ((realProfile kap B N cj kap0 ((m : ℝ)*(U : ℝ)*x)*slotCutoff x*
            (if useLog then Real.log ((U : ℝ)*x) else 1) : ℝ) : ℂ)) := by
      filter_upwards [Ioi_mem_nhds hv] with x hx
      simp only [longProfile,if_pos hx]
    exact hraw.congr_of_eventuallyEq heq
  · have heq : longProfile kap B N cj kap0 m U useLog =ᶠ[𝓝 v] 0 := by
      filter_upwards [Iio_mem_nhds (show v<(1/2 : ℝ) by linarith [le_of_not_gt hv])] with x hx
      exact longProfile_zero_left kap B N cj kap0 m U useLog hx.le
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ=>(0 : ℂ)) v).congr_of_eventuallyEq heq

def profileHeight (N : ℕ) : ℝ := 1+Real.log (8*(N : ℝ)+8)

/-- A genuine global fixed-polylog C1 supplier for the actual long
profile. The exponent is 12B+1 (73 for the original B=6), because it
reuses the already proved whole-chart budget instead of postulating a
sharper first-order envelope. All constants precede N, m, U and v. -/
theorem longProfile_uniform_C1 (B : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ (kap : ℝ) (N cj : ℕ) (kap0 : ℝ) (m U : ℕ),
      0<N → 0<m → 0<U → U≤2*N → ∀ (useLog : Bool) (v : ℝ),
      ‖longProfile kap B N cj kap0 m U useLog v‖+
        ‖deriv (longProfile kap B N cj kap0 m U useLog) v‖≤
          C*profileHeight N^(B*12+1) := by
  obtain ⟨Cg,hCg,hgeom⟩ := realProfile_uniform_euler B
  obtain ⟨S,hS,hcut⟩ := slotCutoff_C1_constants
  have hSnonneg : 0≤S := zero_le_one.trans hS
  refine ⟨10*Cg*S,by positivity,?_⟩
  intro kap N cj kap0 m U hN hm hU hUcap useLog v
  let F := longProfile kap B N cj kap0 m U useLog
  let A : ℝ := (m : ℝ)*(U : ℝ)
  let L : ℝ := profileHeight N
  let T : ℝ := Cg*L^(B*12)
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hUp : (0 : ℝ)<U := by exact_mod_cast hU
  have hAp : 0<A := mul_pos (by exact_mod_cast hm) hUp
  have hS0 : 0≤S := zero_le_one.trans hS
  have hL : 1≤L := by
    dsimp [L,profileHeight]
    have := Real.log_nonneg (show (1 : ℝ)≤8*(N : ℝ)+8 by nlinarith [hNr.le])
    linarith
  have hT : 0≤T := by dsimp [T]; positivity
  have hbudget : Cg*Real.log ((N : ℝ)+2)^(B*12)≤T := by
    have hl0 : 0≤Real.log ((N : ℝ)+2) := Real.log_nonneg (by nlinarith [hNr.le])
    have hl1 : Real.log ((N : ℝ)+2)≤L := by
      have hh := Real.log_le_log (by positivity : (0 : ℝ)<(N : ℝ)+2)
        (show (N : ℝ)+2≤8*(N : ℝ)+8 by nlinarith [hNr.le])
      dsimp [L,profileHeight]
      linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hl1 _) hCg
  by_cases hv : v∈Icc (1/2 : ℝ) 4
  · have hvp : 0<v := by linarith [hv.1]
    let f : ℝ→ℝ := fun x=>realProfile kap B N cj kap0 (A*x)
    let g : ℝ→ℝ := fun x=>if useLog then Real.log ((U : ℝ)*x) else 1
    let gd : ℝ := if useLog then 1/v else 0
    have hb := hgeom kap N cj kap0 (A*v) hNr (mul_pos hAp hvp)
    have hf0 : |f v|≤T := hb.1.trans hbudget
    have hf1 : |deriv f v|≤2*T := by
      have he : v*|deriv f v|=|(A*v)*deriv (realProfile kap B N cj kap0) (A*v)| := by
        rw [show deriv f v=A*deriv (realProfile kap B N cj kap0) (A*v) from
          scaled_realProfile_derivative kap B N cj kap0 A v]
        simp only [abs_mul,abs_of_pos hAp,abs_of_pos hvp]
        ring
      have hmain : v*|deriv f v|≤T := by rw [he]; exact hb.2.trans hbudget
      nlinarith [abs_nonneg (deriv f v),hv.1,
        mul_nonneg (sub_nonneg.mpr hv.1) (abs_nonneg (deriv f v))]
    obtain ⟨hc0,hc1⟩ := hcut v hv
    have hg0 : |g v|≤2*L := by
      cases useLog with
      | false => simp only [g,Bool.false_eq_true,if_false,abs_one]; linarith
      | true =>
        have hU1 : (1 : ℝ)≤U := by exact_mod_cast hU
        have hlo : (1/2 : ℝ)≤(U : ℝ)*v := by
          have hh := mul_le_mul_of_nonneg_right hU1 hvp.le
          nlinarith [hv.1]
        have hhi : (U : ℝ)*v≤8*(N : ℝ)+8 := by
          have hh := mul_le_mul (show (U : ℝ)≤2*(N : ℝ) by exact_mod_cast hUcap)
            hv.2 hvp.le (by positivity : (0 : ℝ)≤2*(N : ℝ))
          nlinarith
        have hlolog := Real.log_le_log (by norm_num : (0 : ℝ)<1/2) hlo
        have hhilog := Real.log_le_log (mul_pos hUp hvp) hhi
        have hhalf : Real.log (1/2 : ℝ)=-Real.log 2 := by rw [one_div,Real.log_inv]
        have htwo : Real.log 2≤L := by
          have hh := Real.log_le_log (by norm_num : (0 : ℝ)<2)
            (show (2 : ℝ)≤8*(N : ℝ)+8 by nlinarith [hNr.le])
          dsimp [L,profileHeight]
          linarith
        rw [hhalf] at hlolog
        have hup : Real.log ((U : ℝ)*v)≤L := by
          dsimp [L,profileHeight]
          linarith
        change |Real.log ((U : ℝ)*v)|≤2*L
        exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hg1 : |gd|≤2 := by
      cases useLog with
      | false => simp [gd]
      | true =>
        simp only [gd,if_true,abs_of_pos (one_div_pos.mpr hvp)]
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/2) hv.1
    have hdf : HasDerivAt f (deriv f v) v :=
      (((realProfile_smooth kap B N cj kap0).comp
        (contDiff_const.mul contDiff_id)).differentiable (by simp) v).hasDerivAt
    have hdc : HasDerivAt slotCutoff (deriv slotCutoff v) v :=
      (slotCutoff_smooth.differentiable (by simp) v).hasDerivAt
    have hdg : HasDerivAt g gd v := by
      cases useLog with
      | false => simpa [g,gd] using hasDerivAt_const v (1 : ℝ)
      | true =>
        have hh := (Real.hasDerivAt_log (mul_pos hUp hvp).ne').comp v
          ((hasDerivAt_id v).const_mul (U : ℝ))
        convert hh using 1 <;> simp only [g,gd,if_true,Function.comp_def] <;>
          field_simp [hUp.ne',hvp.ne'] <;> ring
    let raw : ℝ→ℂ := fun x=>((f x*slotCutoff x*g x : ℝ) : ℂ)
    have hdRaw := ((hdf.mul hdc).mul hdg).ofReal_comp
    have heq : F=ᶠ[𝓝 v] raw := by
      filter_upwards [Ioi_mem_nhds hvp] with x hx
      simp only [F,longProfile,if_pos hx,raw,f,g,A]
    have hvalue : ‖F v‖≤T*S*(2*L) := by
      rw [heq.eq_of_nhds]
      change ‖((f v*slotCutoff v*g v : ℝ) : ℂ)‖≤_
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul]
      gcongr <;> first | assumption | positivity
    have hder : ‖deriv F v‖≤(2*T*S+T*S)*(2*L)+T*S*2 := by
      rw [heq.deriv_eq]
      change ‖deriv raw v‖≤_
      rw [hdRaw.deriv,Complex.norm_real,Real.norm_eq_abs]
      calc
        _≤|(deriv f v*slotCutoff v+f v*deriv slotCutoff v)*g v|+
            |f v*slotCutoff v*gd| := abs_add _ _
        _≤(|deriv f v|*|slotCutoff v|+|f v|*|deriv slotCutoff v|)*|g v|+
            |f v|*|slotCutoff v|*|gd| := by
          simp only [abs_mul]
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right (by simpa only [abs_mul] using
              abs_add (deriv f v*slotCutoff v) (f v*deriv slotCutoff v)) (abs_nonneg _)) _
        _≤(2*T*S+T*S)*(2*L)+T*S*2 := by
          gcongr <;> first | assumption | positivity
    have hspare : 0≤2*T*S*(L-1) := mul_nonneg (by positivity) (sub_nonneg.mpr hL)
    calc
      ‖F v‖+‖deriv F v‖≤T*S*(2*L)+((2*T*S+T*S)*(2*L)+T*S*2) := add_le_add hvalue hder
      _≤10*T*S*L := by nlinarith [hspare]
      _=(10*Cg*S)*L^(B*12+1) := by dsimp [T]; rw [pow_succ]; ring
  · have houtside : v<1/2 ∨ 4<v := by
      simp only [mem_Icc,not_and_or,not_le] at hv
      exact hv
    have heq : F=ᶠ[𝓝 v] 0 := by
      rcases houtside with hl | hr
      · filter_upwards [Iio_mem_nhds hl] with x hx
        exact longProfile_zero_left kap B N cj kap0 m U useLog hx.le
      · filter_upwards [Ioi_mem_nhds hr] with x hx
        exact longProfile_zero_right kap B N cj kap0 m U useLog hx.le
    rw [heq.eq_of_nhds,heq.deriv_eq]
    simp only [norm_zero,deriv_const,zero_add]
    positivity

theorem longProfile_integer (kap : ℝ) (B N cj : ℕ) (kap0 : ℝ) (m U n : ℕ)
    (hU : 0<U) (hn : U<n) (hn2 : n≤2*U) (useLog : Bool) :
    longProfile kap B N cj kap0 m U useLog ((n : ℝ)/(U : ℝ))=
      (scalarProfile kap B N cj kap0 (m*n) : ℂ)*
        (if useLog then (Real.log (n : ℝ) : ℂ) else 1) := by
  have hUp : (0 : ℝ)<U := by exact_mod_cast hU
  have hnp : (0 : ℝ)<n := by exact_mod_cast (hU.trans hn)
  have hx : (n : ℝ)/(U : ℝ)∈Icc (1 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hUp).mpr
      simpa only [one_mul] using (show (U : ℝ)≤n by exact_mod_cast hn.le)
    · apply (div_le_iff₀ hUp).mpr
      exact_mod_cast hn2
  have hmul : (U : ℝ)*((n : ℝ)/(U : ℝ))=(n : ℝ) := by field_simp [hUp.ne']
  have hm : (m : ℝ)*(U : ℝ)*((n : ℝ)/(U : ℝ))=((m*n : ℕ) : ℝ) := by
    rw [mul_assoc,hmul,Nat.cast_mul]
  simp only [longProfile,if_pos (div_pos hnp hUp),slotCutoff_one hx,mul_one,hm,hmul,realProfile_nat]
  cases useLog <;> simp

/-- Exact one/log factor of a real HB slot, with the strict rough mask
untouched. The function passed to finite E5 contains all geometry. -/
theorem actual_long_profile (kap : ℝ) (B N cj : ℕ) (kap0 z y : ℝ)
    (m U n : ℕ) (hU : 0<U) (hn : U<n) (hn2 : n≤2*U)
    (role : Role) (hr : role=.one ∨ role=.logarithm) :
    actual z y role n*(scalarProfile kap B N cj kap0 (m*n) : ℂ)=
      longProfile kap B N cj kap0 m U (decide (role=.logarithm)) ((n : ℝ)/(U : ℝ))*
        Part3.roughOneSlot z n := by
  rw [longProfile_integer kap B N cj kap0 m U n hU hn hn2]
  rcases hr with rfl | rfl <;> simp [actual,roughLog] <;> ring

/-- Termwise exclusion. It also covers a block whose aggregate signed
blockCoefficient cancels to zero, so no aggregate-activity inference is used. -/
theorem long_mobius_rectangle_zero (z y : ℝ) (j : ℕ)
    (bs : Fin (2*(j+1))→Block) (a : Fin (2*(j+1)))
    (ha : rowRoles j a=.mobius) (hy : y<(lower (bs a) : ℝ))
    (n : Fin (2*(j+1))→ℕ) (hn : n∈P5Z.OrderedFactorTupleRectangleReindex.rectangle bs) :
    hbSlots z (fun _=>y) (rowRoles j) n=0 := by
  have hlow : (lower (bs a) : ℝ)≤n a := by
    exact_mod_cast (owns_bounds ((P5Z.OrderedFactorTupleRectangleReindex.mem_rectangle _ _).mp hn a)).1
  unfold hbSlots
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp only [ha,actual,roughMuTrunc,if_neg (not_le.mpr (hy.trans_le hlow))]

end
end ImbalancedChen.P1OriginalSingletonOneLongProfile
