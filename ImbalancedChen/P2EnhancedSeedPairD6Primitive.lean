import ImbalancedChen.P2EnhancedSeedSingletonPrimitive
import ImbalancedChen.FinitePiIntegral

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The literal D6 piece of the original seven-piece second-seed feedback.
Its actual argument is STRICTLY BETWEEN ONE AND TWO everywhere. The
constant upper model therefore needs no support truncation, but its
eventual count use still needs the admitted larger-S comparison licence.
Here geometry, same-Q cutoff inheritance, real integrability, genuine
Fubini and the exact one-variable logarithmic primitive are proved.
No enhanced H/h, lambda, J2omega, table entry or saved pass is an input.
-/

namespace ImbalancedChen.P2EnhancedSeedPairD6Primitive

noncomputable section

open Set MeasureTheory Filter Classical
open scoped Interval BigOperators
open P2EnhancedSeedSingletonPrimitive (S s0 parameters seedUpper)
open P5OriginalActionMassBound (Point)

def uLo : ℝ := 50/227
def uHi : ℝ := 100/353
def vLo : ℝ := 10/29
def vHi : ℝ := 25/61
def D6 : Set Point := P5OriginalActionMassBound.W2Pair6 parameters
def closedRectangle : Set Point := Icc ![uLo,vLo] ![uHi,vHi]
def fixedProfile (x : Point) : ℝ := s0*(1-x 0-x 1)
def pairKernel (x : Point) : ℝ := 1/(x 0*x 1*(1-x 0-x 1))
def feedback (J : ℝ) (x : Point) : ℝ := seedUpper J (fixedProfile x)*pairKernel x

theorem D6_dictionary (x : Point) :
    x ∈ D6 ↔ uLo<x 0 ∧ x 0<uHi ∧ vLo<x 1 ∧ x 1<vHi := by
  norm_num [D6,P5OriginalActionMassBound.W2Pair6,parameters,
    P5OriginalActionMassBound.a0,P5OriginalActionMassBound.a1,
    P5OriginalActionMassBound.a2,P5OriginalActionMassBound.a3,uLo,uHi,vLo,vHi]

theorem D6_vec (u v : ℝ) : (![u,v] : Point) ∈ D6 ↔
    u ∈ Ioo uLo uHi ∧ v ∈ Ioo vLo vHi := by
  rw [D6_dictionary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,mem_Ioo]
  tauto

theorem measurableSet_D6 : MeasurableSet D6 :=
  P5OriginalActionMassBound.W2Pair6_measurable parameters

theorem D6_subset_closed : D6 ⊆ closedRectangle := by
  intro x hx
  have h := (D6_dictionary x).mp hx
  constructor <;> intro i <;> fin_cases i
  · exact h.1.le
  · exact h.2.2.1.le
  · exact h.2.1.le
  · exact h.2.2.2.le

theorem closed_geometry {x : Point} (hx : x ∈ closedRectangle) :
    0<x 0 ∧ 0<x 1 ∧ 0<1-x 0-x 1 := by
  have hu0 := hx.1 0
  have hu1 := hx.2 0
  have hv0 := hx.1 1
  have hv1 := hx.2 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,uLo,uHi,vLo,vHi] at hu0 hu1 hv0 hv1
  constructor
  · linarith only [hu0]
  constructor
  · linarith only [hv0]
  · linarith only [hu1,hv1]

theorem D6_actual_profile {x : Point} (hx : x ∈ D6) :
    1<fixedProfile x ∧ fixedProfile x<2 := by
  have h := (D6_dictionary x).mp hx
  dsimp [uLo,uHi,vLo,vHi] at h
  dsimp [fixedProfile,s0]
  constructor <;> linarith only [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem fixedProfile_eq_original (x : Point) :
    fixedProfile x=P5OriginalFeedbackDomains.fixedPairProfile parameters x := rfl

/-- The entire original D6 has the literal seed model value, including
its genuine rho<2 portion. No max-two query replacement is inserted. -/
theorem feedback_eq_constant (J : ℝ) {x : Point} (hx : x ∈ D6) :
    feedback J x=J*pairKernel x := by
  have hp := D6_actual_profile hx
  have hs : fixedProfile x ∈ Icc (1 : ℝ) S :=
    ⟨hp.1.le,hp.2.le.trans (by norm_num [S])⟩
  rw [feedback,seedUpper,indicator_of_mem hs]

/-- Same total Q, child residual and physical cutoff remain distinct.
The inherited larger-S comparison is below the child's actual cutoff,
which is below BOTH appended primes and their shared old ceiling chi. -/
theorem D6_cutoff_inheritance {L chi alpha : ℝ} (hL : 0<L)
    (hchi : L/S<chi) (ha : 2≤alpha) {x : Point} (hx : x ∈ D6) :
    0<L*(1-x 0-x 1) ∧
      (L*(1-x 0-x 1))/S≤L*uLo ∧ L*uLo<L*x 0 ∧
      L*x 0<L*x 1 ∧ L*x 1<L/S ∧ L/S<chi ∧
      2*x 1<1 ∧ x 1+2*x 0<1 ∧
      alpha≤P5OriginalFeedbackDomains.pairChildAlpha alpha x := by
  have h := (D6_dictionary x).mp hx
  have hg := closed_geometry (D6_subset_closed hx)
  have hp := D6_actual_profile hx
  have hscalar : (1-x 0-x 1)/S≤uLo := by
    dsimp [S,uLo]
    dsimp [fixedProfile,s0] at hp
    linarith only [hp.2]
  have hc := mul_le_mul_of_nonneg_left hscalar hL.le
  have hscalarV : x 1<1/S := by
    dsimp [vHi] at h
    have hv := h.2.2.2
    dsimp [S]
    linarith only [hv]
  have hcut : L*x 1<L/S := by
    have hm := mul_lt_mul_of_pos_left hscalarV hL
    convert hm using 1 <;> ring
  have halpha := P5OriginalFeedbackDomains.alpha_transport_mono (by linarith : 1≤alpha)
    hg.2.2 (show 1-x 0-x 1≤1 by linarith [hg.1,hg.2.1])
  have hsquares : 2*x 1<1 ∧ x 1+2*x 0<1 := by
    dsimp [uHi,vHi] at h
    constructor <;> linarith only [h.2.1,h.2.2.2]
  exact ⟨mul_pos hL hg.2.2,by convert hc using 1 <;> ring,
    mul_lt_mul_of_pos_left h.1 hL,
    mul_lt_mul_of_pos_left (by dsimp [uHi,vLo] at h; linarith only [h.2.1,h.2.2.1]) hL,
    hcut,hchi,hsquares.1,hsquares.2,halpha⟩

theorem continuousOn_pairKernel : ContinuousOn pairKernel closedRectangle := by
  apply continuousOn_const.div
  · fun_prop
  · intro x hx
    have h := closed_geometry hx
    exact (mul_pos (mul_pos h.1 h.2.1) h.2.2).ne'

theorem integrableOn_pairKernel : IntegrableOn pairKernel D6 :=
  (continuousOn_pairKernel.integrableOn_compact isCompact_Icc).mono_set D6_subset_closed

/-- Exact antiderivative on every positive affine slice. This reusable
primitive supplies the actual log formula, not an assumed slice integral. -/
theorem pair_inner_log_integral {u l r : ℝ}
    (hu : 0<u) (hl : 0<l) (hlr : l≤r) (hr : r<1-u) :
    (∫ v in Ioo l r,1/(u*v*(1-u-v)))=
      (1/(u*(1-u)))*Real.log (r*(1-u-l)/(l*(1-u-r))) := by
  have hr0 := hl.trans_le hlr
  have hA : 0<1-u := hr0.trans hr
  have hAl : 0<1-u-l := by linarith only [hlr,hr]
  have hAr : 0<1-u-r := by linarith only [hr]
  let F := fun v : ℝ => (Real.log v-Real.log (1-u-v))/(u*(1-u))
  have hc : ContinuousOn (fun v : ℝ => 1/(u*v*(1-u-v))) (Icc l r) := by
    apply continuousOn_const.div
    · fun_prop
    · intro v hv
      exact (mul_pos (mul_pos hu (hl.trans_le hv.1)) (by linarith [hv.2] : 0<1-u-v)).ne'
  have hd : ∀ v ∈ uIcc l r,HasDerivAt F (1/(u*v*(1-u-v))) v := by
    intro v hv
    rw [uIcc_of_le hlr] at hv
    have hv0 := hl.trans_le hv.1
    have hAv : 0<1-u-v := by linarith only [hv.2,hr]
    have hlog2 := ((hasDerivAt_const v (1-u)).sub (hasDerivAt_id v)).log hAv.ne'
    have hderiv := ((Real.hasDerivAt_log hv0.ne').sub hlog2).div_const (u*(1-u))
    apply hderiv.congr_deriv
    field_simp [hu.ne',hA.ne',hv0.ne',hAv.ne'] <;> ring
  rw [integral_Ioo_eq_integral_Ioc,← intervalIntegral.integral_of_le hlr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hlr)]
  have hlog : (Real.log r-Real.log (1-u-r))-(Real.log l-Real.log (1-u-l))=
      Real.log (r*(1-u-l)/(l*(1-u-r))) := by
    rw [Real.log_div (mul_ne_zero hr0.ne' hAl.ne') (mul_ne_zero hl.ne' hAr.ne'),
      Real.log_mul hr0.ne' hAl.ne',Real.log_mul hl.ne' hAr.ne']
    ring
  dsimp only [F]
  rw [← sub_div,hlog]
  ring

theorem D6_inner_slice {u : ℝ} (hu : u ∈ Ioo uLo uHi) :
    (∫ v in Ioo vLo vHi,pairKernel ![u,v])=
      Real.log (vHi*(1-u-vLo)/(vLo*(1-u-vHi)))/(u*(1-u)) := by
  have hu0 : 0<u := lt_trans (by norm_num [uLo]) hu.1
  have hl : (0 : ℝ)<vLo := by norm_num [vLo]
  have hlr : vLo≤vHi := by norm_num [vLo,vHi]
  have hr : vHi<1-u := by dsimp [vHi,uHi] at *; linarith only [hu.2]
  have h := pair_inner_log_integral hu0 hl hlr hr
  simpa only [pairKernel,Matrix.cons_val_zero,Matrix.cons_val_one,one_div,div_eq_mul_inv,mul_comm]
    using h

/-- Genuine two-dimensional D6 Fubini. The open rectangle is literal. -/
theorem integral_D6_nested :
    (∫ x in D6,pairKernel x)=∫ u in Ioo uLo uHi,∫ v in Ioo vLo vHi,pairKernel ![u,v] := by
  let F := D6.indicator pairKernel
  have hF : Integrable F := integrableOn_pairKernel.integrable_indicator measurableSet_D6
  have htwo : (∫ x : Point,F x)=∫ u : ℝ,∫ v : ℝ,F ![u,v] := by
    calc
      _ = ∫ u : ℝ,∫ v : ℝ,∫ z : Fin 0 → ℝ,F (Fin.cons u (Fin.cons v z)) := integral_fin_pair F hF
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with u
        apply integral_congr_ae
        filter_upwards [] with v
        rw [integral_fin_zero]
        rfl
  have hp (u v : ℝ) : F ![u,v]=(Ioo uLo uHi).indicator
      (fun u => (Ioo vLo vHi).indicator (fun v => pairKernel ![u,v]) v) u := by
    by_cases hu : u ∈ Ioo uLo uHi <;> by_cases hv : v ∈ Ioo vLo vHi <;>
      simp_all only [F,Set.indicator_apply,D6_vec,and_true,true_and,and_false,false_and,
        if_true,if_false,and_self]
  calc
    _ = ∫ x : Point,F x := (integral_indicator measurableSet_D6).symm
    _ = ∫ u : ℝ,∫ v : ℝ,F ![u,v] := htwo
    _ = ∫ u : ℝ,(Ioo uLo uHi).indicator (fun u => ∫ v in Ioo vLo vHi,pairKernel ![u,v]) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ Ioo uLo uHi
      · rw [indicator_of_mem hu]
        simp_rw [hp,indicator_of_mem hu]
        exact integral_indicator measurableSet_Ioo
      · rw [indicator_of_notMem hu]
        simp_rw [hp,indicator_of_notMem hu]
        simp only [integral_zero]
    _ = _ := integral_indicator measurableSet_Ioo

/-- The exact outer logarithmic slice used by the ORIGINAL D6 feedback
certificate. The model constant J is factored once, before division by5. -/
theorem D6_feedback_outer_log (J : ℝ) :
    (∫ x in D6,feedback J x)=J*∫ u in Ioo uLo uHi,
      Real.log (vHi*(1-u-vLo)/(vLo*(1-u-vHi)))/(u*(1-u)) := by
  calc
    _ = ∫ x in D6,J*pairKernel x := by
      apply setIntegral_congr_fun measurableSet_D6
      intro x hx
      exact feedback_eq_constant J hx
    _ = J*(∫ x in D6,pairKernel x) := integral_const_mul _ _
    _ = J*(∫ u in Ioo uLo uHi,∫ v in Ioo vLo vHi,pairKernel ![u,v]) := by rw [integral_D6_nested]
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact D6_inner_slice hu

end

end ImbalancedChen.P2EnhancedSeedPairD6Primitive
