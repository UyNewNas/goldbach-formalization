import ImbalancedChen.P5OriginalFeedbackDomains
import ImbalancedChen.P2TableActionSoundness
import ImbalancedChen.Certificates.RationalLogCertificate

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Bottom real primitives in second-seed-certified-finite-feedback.tex.
These are explicit seed MODEL functions and actual integral comparisons,
not assertions that an enhanced count has already licensed that seed.
The inherited lower-child physical cutoff admits the child's comparison
at S even when the lower parent itself does not admit argument S. Child
arguments 1<=v<2 are retained. The three singleton feedback terms have
the exact support start67/227, and a rational Darboux lower endpoint is
proved against their real logarithmic kernel. No numerical replay or
2327/100000, lambda>13/100, H248 table or enhanced action licence is assumed.
-/

namespace ImbalancedChen.P2EnhancedSeedSingletonPrimitive

noncomputable section

open Set MeasureTheory Filter Classical
open scoped Interval BigOperators
open P5OriginalFeedbackDomains
open Certificates

def S : ℝ := 11/5
def s0 : ℝ := 227/50
def a0 : ℝ := 50/227
def uStar : ℝ := 67/227
def cap : Fin 3 → ℝ := ![5/11,10/29,25/61]
def profile (u : ℝ) : ℝ := s0*(1-u)

def parameters : P5OriginalActionMassBound.W2Parameters :=
  ⟨11/5,227/50,353/100,29/10,61/25⟩

theorem parameters_geometry : P5OriginalActionMassBound.W2Geometry parameters := by
  norm_num [P5OriginalActionMassBound.W2Geometry,parameters,P5OriginalActionMassBound.a0,
    P5OriginalActionMassBound.a1,P5OriginalActionMassBound.a2,P5OriginalActionMassBound.a3,
    P5OriginalActionMassBound.b]

theorem original_singleton_domain (j : Fin 3) :
    P5OriginalActionMassBound.W2SingletonDomain parameters j=Ioo a0 (cap j) := by
  fin_cases j <;> norm_num [P5OriginalActionMassBound.W2SingletonDomain,
    P5OriginalActionMassBound.W2Singleton2,P5OriginalActionMassBound.W2Singleton3,
    P5OriginalActionMassBound.W2Singleton4,parameters,a0,cap,
    P5OriginalActionMassBound.a0,P5OriginalActionMassBound.a2,P5OriginalActionMassBound.a3,
    P5OriginalActionMassBound.b]

theorem original_singleton_profile (u : ℝ) :
    singletonProfile parameters.s0 u=profile u := rfl

def seedUpper (J w : ℝ) : ℝ := (Icc (1 : ℝ) S).indicator (fun _ => J) w
def seedLower (J w : ℝ) : ℝ :=
  (Icc (2 : ℝ) (1+S)).indicator (fun w => J*Real.log (S/(w-1))) w
def singletonLogKernel (u : ℝ) : ℝ := Real.log (S/(profile u-1))/(u*(1-u))
def singletonFeedback (J u : ℝ) : ℝ := seedLower J (profile u)/(u*(1-u))

/-- This is the exact ordinary Buchstab transfer of the explicit constant
short-support model. It is NOT a premise about the actual unknown h. -/
theorem seedLower_eq_buchstab_integral {J w : ℝ} (hw : w ∈ Icc (2 : ℝ) (1+S)) :
    seedLower J w=∫ t in (w-1)..S,J/t := by
  rw [seedLower,indicator_of_mem hw]
  have hw0 : 0<w-1 := by linarith [hw.1]
  have hS : 0<S := by norm_num [S]
  symm
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos hw0 hS]

/-- Physical admission of the lower parent suffices: the child may use
the seed at S without assuming L/S<=chi for the lower parent itself. -/
theorem lower_child_cutoff_admission {L chi w v alpha : ℝ}
    (hL : 0<L) (hw : 2≤w) (hv : v ∈ Icc (w-1) S)
    (hphysical : L/w≤chi) (halpha : 2≤alpha) :
    0<L/(v+1) ∧ L/(S+1)≤L/(v+1) ∧ L/(v+1)≤chi ∧
      (L*v/(v+1))/S≤L/(v+1) ∧ 2*(L/(v+1))≤L ∧
      L/2≤L*v/(v+1) ∧ 0<L*v/(v+1) ∧
      alpha≤alpha+(alpha-1)/v := by
  have hv1 : 1≤v := by linarith [hv.1]
  have hv0 : 0<v := by linarith
  have hd : 0<v+1 := by linarith
  have hw0 : 0<w := by linarith
  have hS : 0<S := by norm_num [S]
  have hprime : 0<L/(v+1) := div_pos hL hd
  have hcomp : (L*v/(v+1))/S≤L/(v+1) := by
    apply (div_le_iff₀ hS).mpr
    have hm := mul_le_mul_of_nonneg_left hv.2 hprime.le
    convert hm using 1 <;> ring
  have hsquare : 2*(L/(v+1))≤L := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith only [mul_nonneg hL.le (sub_nonneg.mpr hv1)]
  have hres : L/2≤L*v/(v+1) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [mul_nonneg hL.le (sub_nonneg.mpr hv1)]
  exact ⟨hprime,div_le_div_of_nonneg_left hL.le hd (by linarith [hv.2]),
    (div_le_div_of_nonneg_left hL.le hw0 (by linarith [hv.1])).trans hphysical,
    hcomp,hsquare,hres,lt_of_lt_of_le (by linarith only [hL]) hres,
    le_add_of_nonneg_right (div_nonneg (by linarith) hv0.le)⟩

theorem literal_bounds (j : Fin 3) :
    0<a0 ∧ a0<uStar ∧ uStar<cap j ∧ cap j≤5/11 ∧ (5/11 : ℝ)<1/2 := by
  fin_cases j <;> norm_num [a0,uStar,cap]

theorem profile_gt_two {u : ℝ} (hu : u≤(5/11 : ℝ)) : 2<profile u := by
  dsimp [profile,s0]
  linarith only [hu]

theorem profile_short_support_iff (u : ℝ) : profile u≤1+S ↔ uStar≤u := by
  dsimp [profile,s0,S,uStar]
  constructor <;> intro h <;> linarith only [h]

theorem singletonFeedback_eq_truncated (J : ℝ) (j : Fin 3) {u : ℝ}
    (hu : u ∈ Icc a0 (cap j)) :
    singletonFeedback J u=(Ici uStar).indicator (fun u => J*singletonLogKernel u) u := by
  have hp := profile_gt_two (hu.2.trans (literal_bounds j).2.2.2.1)
  by_cases hs : uStar≤u
  · have hprof : profile u ∈ Icc (2 : ℝ) (1+S) :=
      ⟨hp.le,(profile_short_support_iff u).mpr hs⟩
    rw [singletonFeedback,seedLower,indicator_of_mem hprof,indicator_of_mem hs,singletonLogKernel]
    ring
  · have hprof : profile u ∉ Icc (2 : ℝ) (1+S) := fun h =>
      hs ((profile_short_support_iff u).mp h.2)
    rw [singletonFeedback,seedLower,indicator_of_notMem hprof,zero_div,indicator_of_notMem hs]

theorem singletonLogKernel_nonneg {u : ℝ} (hu : u ∈ Icc uStar (5/11 : ℝ)) :
    0≤singletonLogKernel u := by
  have hu0 : 0<u := lt_of_lt_of_le (by norm_num [uStar]) hu.1
  have hp := profile_gt_two hu.2
  have hs := (profile_short_support_iff u).mpr hu.1
  have hratio : 1≤S/(profile u-1) :=
    (le_div_iff₀ (by linarith : 0<profile u-1)).mpr (by linarith)
  exact div_nonneg (Real.log_nonneg hratio) (mul_nonneg hu0.le (by linarith [hu.2]))

theorem continuousOn_singletonLogKernel {l r : ℝ}
    (hl : 0<l) (hr : r≤(5/11 : ℝ)) : ContinuousOn singletonLogKernel (Icc l r) := by
  have hprofile : Continuous profile := by unfold profile; fun_prop
  have hratio : ContinuousOn (fun u => S/(profile u-1)) (Icc l r) :=
    continuousOn_const.div (hprofile.continuousOn.sub continuousOn_const)
      (fun u hu => by have hp:=profile_gt_two (hu.2.trans hr); linarith)
  have hlog : ContinuousOn (fun u => Real.log (S/(profile u-1))) (Icc l r) := by
    apply hratio.log
    intro u hu
    have hp := profile_gt_two (hu.2.trans hr)
    exact (div_pos (by norm_num [S]) (by linarith : 0<profile u-1)).ne'
  exact hlog.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    (fun u hu => mul_ne_zero (ne_of_gt (hl.trans_le hu.1)) (by linarith [hu.2,hr]))

theorem integrableOn_singletonFeedback (J : ℝ) (j : Fin 3) :
    IntegrableOn (singletonFeedback J) (Icc a0 (cap j)) := by
  have hb := literal_bounds j
  have hi := ((continuousOn_singletonLogKernel hb.1 hb.2.2.2.1).const_mul J).integrableOn_compact
    isCompact_Icc
  apply (hi.indicator measurableSet_Ici).congr_fun ?_ measurableSet_Icc
  intro u hu
  exact (singletonFeedback_eq_truncated J j hu).symm

/-- Exact support reduction of EACH of the three actual singleton terms.
The threshold and cap endpoints stay literal; no lower query below two
and no discarded endpoint correction is hidden in this equality. -/
theorem singleton_feedback_integral_exact (J : ℝ) (j : Fin 3) :
    (∫ u in Icc a0 (cap j),singletonFeedback J u)=
      J*∫ u in Icc uStar (cap j),singletonLogKernel u := by
  have hset : Icc a0 (cap j) ∩ Ici uStar=Icc uStar (cap j) := by
    ext u
    have ha := (literal_bounds j).2.1.le
    simp only [mem_inter_iff,mem_Icc,mem_Ici]
    constructor
    · exact fun h => ⟨h.2,h.1.2⟩
    · exact fun h => ⟨⟨ha.trans h.1,h.2⟩,h.1⟩
  calc
    _ = ∫ u in Icc a0 (cap j),(Ici uStar).indicator (fun u => J*singletonLogKernel u) u := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      exact singletonFeedback_eq_truncated J j hu
    _ = ∫ u in Icc a0 (cap j) ∩ Ici uStar,J*singletonLogKernel u :=
      setIntegral_indicator measurableSet_Ici
    _ = _ := by rw [hset,integral_const_mul]

/-- Exact binding to the existing W2 domain API. Open/closed replacement
here is paid by real singleton nullity, never arithmetic endpoint emptiness. -/
theorem singleton_feedback_original_domain_exact (J : ℝ) (j : Fin 3) :
    (∫ u in P5OriginalActionMassBound.W2SingletonDomain parameters j,singletonFeedback J u)=
      J*∫ u in Icc uStar (cap j),singletonLogKernel u := by
  have hleft : ∀ᵐ u : ℝ ∂volume,u≠a0 := by rw [ae_iff]; simp
  have hright : ∀ᵐ u : ℝ ∂volume,u≠cap j := by rw [ae_iff]; simp
  have hsets : Ioo a0 (cap j)=ᵐ[volume] Icc a0 (cap j) := by
    filter_upwards [hleft,hright] with u hL hR
    apply propext
    constructor
    · exact fun h => ⟨h.1.le,h.2.le⟩
    · exact fun h => ⟨lt_of_le_of_ne h.1 hL.symm,lt_of_le_of_ne h.2 hR⟩
  rw [original_singleton_domain]
  exact (setIntegral_congr_set hsets).trans (singleton_feedback_integral_exact J j)

/-- A true endpoint lower bound on the logarithmic kernel. The reciprocal
uses the RIGHT endpoint because u(1-u) increases on these literal pieces. -/
theorem singleton_kernel_cell_lower {l r u : ℝ}
    (hl : uStar≤l) (hlr : l≤r) (hr : r≤(5/11 : ℝ)) (hu : u ∈ Icc l r) :
    Real.log (S/(profile l-1))/(r*(1-r))≤singletonLogKernel u := by
  have hl0 : 0<l := lt_of_lt_of_le (by norm_num [uStar]) hl
  have hu0 := hl0.trans_le hu.1
  have hr0 := hl0.trans_le hlr
  have hpL := profile_gt_two (hlr.trans hr)
  have hpU := profile_gt_two (hu.2.trans hr)
  have hprof : profile u≤profile l := by dsimp [profile,s0]; linarith only [hu.1]
  have hratio := div_le_div_of_nonneg_left (by norm_num [S] : 0≤S)
    (by linarith : 0<profile u-1) (by linarith only [hprof])
  have hlog := Real.log_le_log (div_pos (by norm_num [S]) (by linarith : 0<profile l-1)) hratio
  have hlog0 : 0≤Real.log (S/(profile l-1)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by linarith : 0<profile l-1)).mpr
    have hs := (profile_short_support_iff l).mpr hl
    linarith only [hs]
  have hden0 : 0<u*(1-u) := mul_pos hu0 (by linarith [hu.2,hr])
  have hden : u*(1-u)≤r*(1-r) := by
    have hm : 0≤(r-u)*(1-r-u) :=
      mul_nonneg (sub_nonneg.mpr hu.2) (by linarith [hu.2,hr])
    nlinarith only [hm]
  exact (div_le_div_of_nonneg_left hlog0 hden0 hden).trans
    (div_le_div_of_nonneg_right hlog hden0.le)

def rationalArgument (l : ℚ) : ℚ := (11/5)/((227/50)*(1-l)-1)
def cellLower (terms : ℕ) (l r : ℚ) : ℚ :=
  logSeriesLower (rationalArgument l) terms/(r*(1-r))

theorem rational_cell_lower (terms : ℕ) (l r : ℚ)
    (hl : (67/227 : ℚ)≤l) (hlr : l≤r) (hr : r≤(5/11 : ℚ))
    {u : ℝ} (hu : u ∈ Icc (l : ℝ) (r : ℝ)) :
    (cellLower terms l r : ℝ)≤singletonLogKernel u := by
  have hlR : uStar≤(l : ℝ) := by exact_mod_cast hl
  have hlrR : (l : ℝ)≤r := by exact_mod_cast hlr
  have hrR : (r : ℝ)≤5/11 := by exact_mod_cast hr
  have hp := profile_gt_two (hlrR.trans hrR)
  have hs := (profile_short_support_iff (l : ℝ)).mpr hlR
  have hargR : 1≤S/(profile (l : ℝ)-1) :=
    (le_div_iff₀ (by linarith : 0<profile (l : ℝ)-1)).mpr (by linarith only [hs])
  have heq : (rationalArgument l : ℝ)=S/(profile (l : ℝ)-1) := by
    simp only [rationalArgument,profile,s0,S,Rat.cast_div,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_one]
  have harg : 1≤rationalArgument l := by rw [← heq] at hargR; exact_mod_cast hargR
  let c : RationalLogCertificate :=
    ⟨rationalArgument l,terms,logSeriesLower (rationalArgument l) terms,logSeriesUpper (rationalArgument l) terms⟩
  have hc : c.check=true := by
    simpa only [RationalLogCertificate.check,decide_eq_true_eq] using
      (show c.Valid from ⟨harg,le_rfl,le_rfl⟩)
  have hlog := (RationalLogCertificate.check_sound c hc).1
  change (logSeriesLower (rationalArgument l) terms : ℝ)≤Real.log (rationalArgument l : ℝ) at hlog
  rw [heq] at hlog
  have hr0 : (0 : ℝ)<r := by
    have hl0 : (0 : ℝ)<l := lt_of_lt_of_le (by norm_num [uStar]) hlR
    exact hl0.trans_le hlrR
  have hden : 0<(r : ℝ)*(1-r) := mul_pos hr0 (by linarith only [hrR])
  have h := (div_le_div_of_nonneg_right hlog hden.le).trans
    (singleton_kernel_cell_lower hlR hlrR hrR hu)
  simpa only [cellLower,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_one] using h

/-- A genuine finite Darboux-cell comparison with an ACTUAL real
integral. Only rational geometry and explicit Taylor terms are inputs. -/
theorem rational_cell_integral_lower (terms : ℕ) (l r : ℚ)
    (hl : (67/227 : ℚ)≤l) (hlr : l≤r) (hr : r≤(5/11 : ℚ)) :
    (((r-l)*cellLower terms l r : ℚ) : ℝ)≤
      ∫ u in (l : ℝ)..(r : ℝ),singletonLogKernel u := by
  have hlR : uStar≤(l : ℝ) := by exact_mod_cast hl
  have hlrR : (l : ℝ)≤r := by exact_mod_cast hlr
  have hrR : (r : ℝ)≤5/11 := by exact_mod_cast hr
  have hl0 : (0 : ℝ)<l := lt_of_lt_of_le (by norm_num [uStar]) hlR
  have hi := (continuousOn_singletonLogKernel hl0 hrR).intervalIntegrable_of_Icc hlrR
  have h := intervalIntegral.integral_mono_on hlrR intervalIntegrable_const hi
    (fun u hu => rational_cell_lower terms l r hl hlr hr hu)
  simpa only [intervalIntegral.integral_const,smul_eq_mul,Rat.cast_mul,Rat.cast_sub] using h

end

end ImbalancedChen.P2EnhancedSeedSingletonPrimitive
