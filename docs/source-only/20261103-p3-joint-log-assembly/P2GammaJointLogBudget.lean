import ImbalancedChen.P2GammaDyadicJointRowEstimate
import ImbalancedChen.P2GammaPrimitiveScaleThreshold

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Balance the actual two-lane dyadic family bound. Every fixed logarithmic
order is chosen before the common local-scale threshold. The primitive
inputs of the scalar lemmas are supplied from actual occupancy downstream.
No family conductor estimate, error bound or coefficient energy is assumed
by the final actual-source theorem in the next module.
-/
namespace ImbalancedChen.P2GammaJointLogBudget
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaDyadicJointRowEstimate P2GammaDyadicSmallConductorFamily
open P2GammaDyadicFamilyEnergy P2GammaDyadicHeadIntervals
open P2GammaConductorScaleThreshold P2GammaRetainedLowRankLevel

/-- Avoid relying on a numerical approximation to log 2. -/
def logConstant : ℝ := 2 + |Real.log 2|
def cutOrder (A J : ℕ) : ℕ := A+J+4
def primeOrder (A J : ℕ) : ℕ := A+J+2*cutOrder A J+3
def highConstant (J : ℕ) : ℝ :=
  2*logConstant^J*(64+256*(lsLogCoefficient+1)*dyadicCountCoefficient+128*lsLogCoefficient)
def totalConstant (C : ℝ) (A J : ℕ) : ℝ :=
  2*dyadicCountCoefficient*logConstant*(32*C*logConstant^J+highConstant J)

theorem logConstant_ge_two : 2 ≤ logConstant := by
  unfold logConstant
  linarith [abs_nonneg (Real.log 2)]

theorem highConstant_pos (J : ℕ) : 0 < highConstant J := by
  have := logConstant_ge_two
  have := lsLogCoefficient_pos
  have := dyadicCountCoefficient_pos
  unfold highConstant
  positivity

theorem totalConstant_pos {C : ℝ} (hC : 0 < C) (A J : ℕ) :
    0 < totalConstant C A J := by
  have := logConstant_ge_two
  have := dyadicCountCoefficient_pos
  have := highConstant_pos J
  unfold totalConstant
  positivity

/-- The one extra logarithm in the joint row bound is paid before grids. -/
theorem log_doubled_scale {x V : ℝ} (hx : 0 < x) (hl : 1 ≤ Real.log x)
    (hV : 1 ≤ V) (hVx : V ≤ x) :
    0 ≤ 1+Real.log (2*V) ∧ 1+Real.log (2*V) ≤ logConstant*Real.log x := by
  have hVp : 0 < V := by linarith
  have hlogV := Real.log_le_log hVp hVx
  have hlog2 : Real.log 2 ≤ |Real.log 2| := le_abs_self _
  have hprod : |Real.log 2| ≤ |Real.log 2|*Real.log x := by
    nlinarith [abs_nonneg (Real.log 2)]
  constructor
  · have := Real.log_nonneg (show 1 ≤ 2*V by linarith)
    linarith
  · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hVp.ne']
    unfold logConstant
    nlinarith

/-- Logarithmic gauge for arbitrary caps, including zero. -/
theorem gauge_le_double_log {x : ℝ} (hx : 1 ≤ x) (hl : 1 ≤ Real.log x)
    (Q : ℕ) (hQ : (Q : ℝ) ≤ x) : logGauge Q ≤ 2*Real.log x := by
  have hlog := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) (Q : ℝ))) (max_le hx hQ)
  unfold logGauge
  linarith

theorem depth_le_local_log {x M : ℝ} (hx : 0 < x) (hl : 1 ≤ Real.log x)
    (hM : 1 ≤ M) (hMx : M ≤ x) (P : ℕ) (hP : (P : ℝ) ≤ 2*M) :
    (depth P : ℝ) ≤ dyadicCountCoefficient*logConstant*Real.log x := by
  have hh := log_doubled_scale hx hl hM hMx
  have hmax : max 1 (P : ℝ) ≤ 2*M := max_le (by linarith) hP
  have hlog := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) (P : ℝ))) hmax
  have hg : logGauge P ≤ logConstant*Real.log x := by
    unfold logGauge
    linarith [hh.2]
  exact (depth_le_logGauge P).trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hg dyadicCountCoefficient_pos.le)

/-- The explicit joint beta bound, not a separate row-energy premise. -/
theorem joint_energy_bound (cs : List ℕ) (J : ℕ)
    (hJ : (cs.length+3)^2-1 ≤ J) {x M V h : ℝ} {P : ℕ}
    (hx : 0 < x) (hl : 1 ≤ Real.log x) (hM : 1 ≤ M) (hV : 1 ≤ V)
    (hMV : M*V=x) (hh : 0 ≤ h) (hP : (P : ℝ) ≤ 2*M) :
    Real.sqrt P*Real.sqrt (betaBound cs h V) ≤
      (2*logConstant^J)*h*Real.sqrt x*(Real.log x)^J := by
  let l := Real.log x
  have hlp : 0 < l := by dsimp [l]; linarith
  have hVp : 0 < V := by linarith
  have hVx : V ≤ x := by nlinarith
  obtain ⟨ha,hb⟩ := log_doubled_scale hx hl hV hVx
  have hg := logConstant_ge_two
  have hgl : 1 ≤ logConstant*l := by nlinarith
  have hpow : (1+Real.log (2*V))^((cs.length+3)^2-1) ≤ (logConstant*l)^(J*2) :=
    (pow_le_pow_left₀ ha hb _).trans
      (pow_le_pow_right₀ hgl (hJ.trans (by omega)))
  have hbeta : betaBound cs h V ≤ h^2*(2*V)*(logConstant*l)^(J*2) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    _ = (P : ℝ)*betaBound cs h V := by
      rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg P),Real.sq_sqrt (betaBound_nonneg cs h hV)]
    _ ≤ (2*M)*(h^2*(2*V)*(logConstant*l)^(J*2)) :=
      mul_le_mul hP hbeta (betaBound_nonneg cs h hV) (by positivity)
    _ = _ := by
      rw [pow_mul]
      simp only [mul_pow,Real.sq_sqrt hx.le]
      rw [← hMV]
      dsimp [l]
      ring

/-- Scalar square-root geometry from the complete factor floors. The
ambient padded lengths need only upper bounds, not long subintervals. -/
theorem cap_root_geometry {x M V eta : ℝ} {P R : ℕ}
    (hx : 0 < x) (hMV : M*V=x) (hMp : x^eta ≤ M) (hVp : x^eta ≤ V)
    (hP : (P : ℝ) ≤ 2*M) (hR : (R : ℝ) ≤ 2*V) :
    Real.sqrt P*Real.sqrt R ≤ 4*Real.sqrt x ∧
    Real.sqrt P+Real.sqrt R ≤ 4*Real.sqrt x/x^(eta/2) := by
  have hM : 0 < M := (Real.rpow_pos_of_pos hx eta).trans_le hMp
  have hV : 0 < V := (Real.rpow_pos_of_pos hx eta).trans_le hVp
  have hp : Real.sqrt P ≤ 2*Real.sqrt M := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt hM.le]
    nlinarith
  have hr : Real.sqrt R ≤ 2*Real.sqrt V := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt hV.le]
    nlinarith
  have hroots : Real.sqrt M*Real.sqrt V = Real.sqrt x := by
    rw [← Real.sqrt_mul hM.le,hMV]
  have ht : 0 < x^(eta/2) := Real.rpow_pos_of_pos hx _
  have ht2 : (x^(eta/2))^2=x^eta := by
    rw [pow_two,← Real.rpow_add hx]
    congr 1
    ring
  have htM : x^(eta/2) ≤ Real.sqrt M := by
    apply (sq_le_sq₀ ht.le (Real.sqrt_nonneg _)).mp
    rw [ht2,Real.sq_sqrt hM.le]
    exact hMp
  have htV : x^(eta/2) ≤ Real.sqrt V := by
    apply (sq_le_sq₀ ht.le (Real.sqrt_nonneg _)).mp
    rw [ht2,Real.sq_sqrt hV.le]
    exact hVp
  constructor
  · calc
      _ ≤ (2*Real.sqrt M)*(2*Real.sqrt V) :=
        mul_le_mul hp hr (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by rw [← hroots]; ring
  · apply (le_div_iff₀ ht).mpr
    have hm := mul_le_mul_of_nonneg_left htV (Real.sqrt_nonneg M)
    have hv := mul_le_mul_of_nonneg_left htM (Real.sqrt_nonneg V)
    rw [hroots] at hm
    have hroots' : Real.sqrt V*Real.sqrt M=Real.sqrt x := by rw [mul_comm,hroots]
    rw [hroots'] at hv
    calc
      _ ≤ (2*Real.sqrt M+2*Real.sqrt V)*x^(eta/2) :=
        mul_le_mul_of_nonneg_right (add_le_add hp hr) ht.le
      _ ≤ _ := by nlinarith

/-- Scalar version of the inherited high ledger; its three genuine costs
are kept. e may include the later selector height, so the threshold does not. -/
theorem high_factor_balanced (A J P R Q b0 : ℕ) {x l E e : ℝ}
    (hx : 0 ≤ x) (hl : 1 ≤ l) (hE0 : 0 ≤ E) (he : 0 ≤ e)
    (hE : E ≤ e*Real.sqrt x*l^J)
    (hp : Real.sqrt P*Real.sqrt R ≤ 4*Real.sqrt x)
    (hs : Real.sqrt P+Real.sqrt R ≤ 4*Real.sqrt x/l^(cutOrder A J))
    (hq : (Q : ℝ) ≤ Real.sqrt x/l^(cutOrder A J))
    (hg : logGauge Q ≤ 2*l) (hcut : l^(cutOrder A J) ≤ (2 : ℝ)^b0) :
    E*highFactor P R Q b0 (logGauge Q) ≤
      e*(64+256*(lsLogCoefficient+1)*dyadicCountCoefficient+128*lsLogCoefficient)*
        x/l^(A+1) := by
  have hlp : 0 < l := by linarith
  have hg0 := (logGauge_one_le Q).trans hg
  have hcoef := lsLogCoefficient_pos
  have hdyad := dyadicCountCoefficient_pos
  have hr (i : ℕ) (hi : i ≤ 3) : l^(J+i)/l^(cutOrder A J) ≤ 1/l^(A+1) := by
    apply (div_le_div_iff₀ (pow_pos hlp _) (pow_pos hlp _)).mpr
    rw [one_mul,← pow_add]
    apply pow_le_pow_right₀ hl
    dsimp [cutOrder]
    omega
  have h1 : 8*E*Real.sqrt P*Real.sqrt R*logGauge Q/(2 : ℝ)^b0 ≤
      (64*e*x)*(l^(J+1)/l^(cutOrder A J)) := by
    calc
      _ = 8*E*(Real.sqrt P*Real.sqrt R)*logGauge Q/(2 : ℝ)^b0 := by ring
      _ ≤ 8*(e*Real.sqrt x*l^J)*(4*Real.sqrt x)*(2*l)/l^(cutOrder A J) := by gcongr
      _ = _ := by
        conv_rhs => rw [← Real.sq_sqrt hx]
        rw [pow_succ]
        ring
  have h2 : 8*(lsLogCoefficient+1)*dyadicCountCoefficient*E*
      (Real.sqrt P+Real.sqrt R)*(logGauge Q)^3 ≤
      (256*(lsLogCoefficient+1)*dyadicCountCoefficient*e*x)*
        (l^(J+3)/l^(cutOrder A J)) := by
    calc
      _ ≤ 8*(lsLogCoefficient+1)*dyadicCountCoefficient*(e*Real.sqrt x*l^J)*
          (4*Real.sqrt x/l^(cutOrder A J))*(2*l)^3 := by gcongr
      _ = _ := by
        conv_rhs => rw [← Real.sq_sqrt hx]
        rw [pow_add]
        ring
  have h3 : 64*lsLogCoefficient*E*(Q : ℝ)*logGauge Q ≤
      (128*lsLogCoefficient*e*x)*(l^(J+1)/l^(cutOrder A J)) := by
    calc
      _ ≤ 64*lsLogCoefficient*(e*Real.sqrt x*l^J)*
          (Real.sqrt x/l^(cutOrder A J))*(2*l) := by gcongr
      _ = _ := by
        conv_rhs => rw [← Real.sq_sqrt hx]
        rw [pow_succ]
        ring
  have hh1 := h1.trans (mul_le_mul_of_nonneg_left (hr 1 (by omega)) (by positivity))
  have hh2 := h2.trans (mul_le_mul_of_nonneg_left (hr 3 (by omega)) (by positivity))
  have hh3 := h3.trans (mul_le_mul_of_nonneg_left (hr 1 (by omega)) (by positivity))
  unfold highFactor
  nlinarith [add_le_add (add_le_add hh1 hh2) hh3]

/-- Actual lowCost, including the square of the dyadic cutoff and both
totient logarithms. The stronger prime order is fixed before calling SW. -/
theorem low_cost_balanced (A J : ℕ) (cs : List ℕ) (hJ : cs.length+2 ≤ J)
    {C h x M V : ℝ} {Q b0 : ℕ}
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hx : 0 < x) (hl : 1 ≤ Real.log x)
    (hM : 1 ≤ M) (hV : 1 ≤ V) (hMV : M*V=x)
    (hg : logGauge Q ≤ 2*Real.log x)
    (hcut : (2 : ℝ)^b0 ≤ 2*(Real.log x)^(cutOrder A J)) :
    lowCost C h M V x cs (primeOrder A J : ℝ) Q b0 ≤
      (32*C*logConstant^J)*h*x/(Real.log x)^(A+1) := by
  let l := Real.log x
  have hlp : 0 < l := by dsimp [l]; linarith
  have hVx : V ≤ x := by nlinarith
  obtain ⟨ha,hb⟩ := log_doubled_scale hx hl hV hVx
  have hgl : 1 ≤ logConstant*l := by have := logConstant_ge_two; nlinarith
  have hp : (1+Real.log (2*V))^(cs.length+2) ≤ (logConstant*l)^J :=
    (pow_le_pow_left₀ ha hb _).trans (pow_le_pow_right₀ hgl hJ)
  have hQ0 := logGauge_one_le Q
  unfold lowCost
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.rpow_natCast]
  calc
    _ ≤ C*M*(h*(2*V)*(logConstant*l)^J)*
        (2*l^(cutOrder A J))^2*(2*l)^2/l^(primeOrder A J) := by gcongr
    _ = (32*C*logConstant^J)*h*x/l^(A+1) := by
      rw [← hMV]
      simp only [primeOrder,cutOrder,pow_add,mul_pow,pow_mul]
      field_simp [hlp.ne'] <;> ring

/-- Uniform scalar threshold. No original word, selector height, chart,
source row, modulus or coefficient policy enters its choice. -/
theorem exists_joint_scalar_threshold (A J : ℕ) :
    ∃ x0 : ℝ,1 < x0 ∧ ∀ x : ℝ,x0 ≤ x →
      ∀ M V : ℝ,1 ≤ M → 1 ≤ V → M*V=x →
      x^(34/1135 : ℝ) ≤ M → x^(34/1135 : ℝ) ≤ V →
      ∀ P R Q : ℕ,(P : ℝ) ≤ 2*M → (R : ℝ) ≤ 2*V → (Q : ℝ) ≤ x^(9/20 : ℝ) →
      ∀ cs : List ℕ,cs.length+2 ≤ J → (cs.length+3)^2-1 ≤ J →
      ∀ C h : ℝ,0 ≤ C → 0 ≤ h →
      let b0 := cutoffExponent (Real.log x) (cutOrder A J)
      (2*(depth P : ℝ))*(lowCost C h M V x cs (primeOrder A J : ℝ) Q b0+
        (Real.sqrt P*Real.sqrt (betaBound cs h V))*highFactor P R Q b0 (logGauge Q)) ≤
          totalConstant C A J*h*x/(Real.log x)^A := by
  obtain ⟨x1,hx1⟩ := eventually_atTop.mp
    (eventually_log_power_le_fixed_power (cutOrder A J) (17/1135) (by norm_num))
  obtain ⟨x2,hx2⟩ := eventually_atTop.mp
    (eventually_log_power_le_fixed_power (cutOrder A J) (1/20) (by norm_num))
  refine ⟨max 2 (max x1 x2),by linarith [le_max_left (2 : ℝ) (max x1 x2)],?_⟩
  intro x hx M V hM hV hMV hMp hVp P R Q hP hR hQ cs hJ1 hJ2 C h hC hh
  dsimp only
  have hxge : 2 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hx1' : x1 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx2' : x2 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  obtain ⟨hl,hpow⟩ := hx1 x hx1'
  have hlev := (hx2 x hx2').2
  let l := Real.log x
  let b0 := cutoffExponent l (cutOrder A J)
  have hlp : 0 < l := by dsimp [l]; linarith
  have hQx : (Q : ℝ) ≤ x := hQ.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ x by linarith) (show (9/20 : ℝ) ≤ 1 by norm_num))
  have hg := gauge_le_double_log (show 1 ≤ x by linarith) hl Q hQx
  have hcut := cutoffExponent_bounds l hl (cutOrder A J)
  have hroots := cap_root_geometry hxpos hMV hMp hVp hP hR
  have hlength : Real.sqrt P+Real.sqrt R ≤ 4*Real.sqrt x/l^(cutOrder A J) := by
    apply hroots.2.trans
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos hlp _)
    simpa using hpow
  have hlevel : (Q : ℝ) ≤ Real.sqrt x/l^(cutOrder A J) := by
    apply (le_div_iff₀ (pow_pos hlp _)).mpr
    calc
      _ ≤ x^(9/20 : ℝ)*x^(1/20 : ℝ) :=
        mul_le_mul hQ hlev (by positivity) (Real.rpow_nonneg hxpos.le _)
      _ = Real.sqrt x := by rw [← Real.rpow_add hxpos]; norm_num [Real.sqrt_eq_rpow]
  have he := joint_energy_bound cs J hJ2 hxpos hl hM hV hMV hh hP
  have hhig := high_factor_balanced A J P R Q b0 hxpos.le hl
    (by positivity) (show 0 ≤ (2*logConstant^J)*h by have := logConstant_ge_two; positivity)
    he hroots.1 hlength hlevel hg hcut.1
  have hhi : (Real.sqrt P*Real.sqrt (betaBound cs h V))*highFactor P R Q b0 (logGauge Q) ≤
      highConstant J*h*x/l^(A+1) := by
    convert hhig using 1 <;> unfold highConstant <;> ring
  have hlo := low_cost_balanced A J cs hJ1 hC hh hxpos hl hM hV hMV hg hcut.2
  have hMx : M ≤ x := by nlinarith
  have hd := depth_le_local_log hxpos hl hM hMx P hP
  have hK0 : 0 ≤ (32*C*logConstant^J+highConstant J)*h*x/l^(A+1) := by
    have := logConstant_ge_two
    have := highConstant_pos J
    positivity
  calc
    _ ≤ (2*(depth P : ℝ))*((32*C*logConstant^J+highConstant J)*h*x/l^(A+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [add_le_add hlo hhi]
    _ ≤ (2*(dyadicCountCoefficient*logConstant*l))*
        ((32*C*logConstant^J+highConstant J)*h*x/l^(A+1)) :=
      mul_le_mul_of_nonneg_right (by linarith) hK0
    _ = _ := by
      unfold totalConstant
      rw [pow_succ]
      field_simp [hlp.ne'] <;> ring

end
end ImbalancedChen.P2GammaJointLogBudget
