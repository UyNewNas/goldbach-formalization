import ImbalancedChen.P2EnhancedSeedPairD6Primitive

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Two new bottom layers of the original seven-piece seed calculation:
(1) ALL THREE original singleton lower children retain the same total Q,
actual residual level, physical cutoff and old common ceiling after their
next Buchstab prime. Arguments1<=v<2 are retained, not clipped away.
(2) Explicit rational Darboux lower cells for the TRUE D6 outer logarithm.
Only rational cell geometry and finite Taylor order are inputs. There is
no enhanced-count, lambda, J2omega, table-value or numerical-pass premise.
-/

namespace ImbalancedChen.P2EnhancedSeedInheritedCellBounds

noncomputable section

open Set MeasureTheory Classical
open scoped Interval
open Certificates
open P2EnhancedSeedSingletonPrimitive
open P2EnhancedSeedPairD6Primitive (uLo uHi vLo vHi)

/-- The physical lower-child cutoff is La0, not a newly imposed Lchild/S.
Its own Buchstab children inherit the seed comparison legitimately. -/
theorem three_singleton_nested_cutoff {L chi alpha : ℝ}
    (hL : 0<L) (hchi : L/S<chi) (ha : 2≤alpha) (j : Fin 3) {u v : ℝ}
    (hu : u ∈ P5OriginalActionMassBound.W2SingletonDomain parameters j)
    (hv : v ∈ Icc (profile u-1) S) :
    0<L*(1-u) ∧
      ((L*(1-u))*v/(v+1))/S≤(L*(1-u))/(v+1) ∧
      (L*(1-u))/(v+1)≤L*a0 ∧ L*a0<L*u ∧ L*u<L/S ∧ L/S<chi ∧
      2*((L*(1-u))/(v+1))≤L*(1-u) ∧
      (L*(1-u))/2≤(L*(1-u))*v/(v+1) ∧
      alpha≤P5OriginalFeedbackDomains.singletonChildAlpha alpha u ∧
      P5OriginalFeedbackDomains.singletonChildAlpha alpha u≤
        P5OriginalFeedbackDomains.singletonChildAlpha alpha u+
          (P5OriginalFeedbackDomains.singletonChildAlpha alpha u-1)/v := by
  rw [original_singleton_domain] at hu
  have hb := literal_bounds j
  have huHi : u<(5/11 : ℝ) := hu.2.trans_le hb.2.2.2.1
  have hres : 0<L*(1-u) := mul_pos hL (by linarith only [huHi])
  have hprofile := profile_gt_two huHi.le
  have hphys : (L*(1-u))/(profile u)=L*a0 := by
    dsimp [profile,s0,a0]
    field_simp [ne_of_gt (show 0<1-u by linarith only [huHi])]
    <;> ring
  have huAmb : u ∈ P5OriginalActionMassBound.singletonAmbient := by
    have hmin : (1/5 : ℝ)<a0 := by norm_num [a0]
    exact ⟨hmin.le.trans hu.1.le,by linarith only [huHi]⟩
  have hA := P5OriginalFeedbackDomains.singletonChildAlpha_ge_parent ha huAmb
  obtain ⟨hq0,hqlo,hqphys,hcompare,hsquare,hreslo,hrespos,hA2⟩ :=
    lower_child_cutoff_admission hres hprofile.le hv
      (show (L*(1-u))/(profile u)≤L*a0 by rw [hphys]) (ha.trans hA)
  have hSmall : L*a0<L*u := mul_lt_mul_of_pos_left hu.1 hL
  have hOld : L*u<L/S := by
    have hm := mul_lt_mul_of_pos_left huHi hL
    dsimp [S]
    convert hm using 1 <;> ring
  exact ⟨hres,hcompare,hqphys,hSmall,hOld,hchi,hsquare,hreslo,hA,hA2⟩

def d6LogArgument (u : ℝ) : ℝ := vHi*(1-u-vLo)/(vLo*(1-u-vHi))
def d6OuterSlice (u : ℝ) : ℝ := Real.log (d6LogArgument u)/(u*(1-u))
def d6RationalArgument (l : ℚ) : ℚ :=
  (25/61)*(1-l-10/29)/((10/29)*(1-l-25/61))
def d6CellLower (terms : ℕ) (l r : ℚ) : ℚ :=
  logSeriesLower (d6RationalArgument l) terms/(r*(1-r))

theorem d6_argument_positive {u : ℝ} (hu : u ∈ Icc uLo uHi) :
    0<u ∧ 0<1-u ∧ 0<vLo*(1-u-vHi) ∧ 1≤d6LogArgument u := by
  have hu0 : 0<u := lt_of_lt_of_le (by norm_num [uLo]) hu.1
  have hres : 0<1-u-vHi := by dsimp [uHi,vHi] at *; linarith only [hu.2]
  have hden : 0<vLo*(1-u-vHi) := mul_pos (by norm_num [vLo]) hres
  refine ⟨hu0,by dsimp [uHi] at hu; linarith only [hu.2],hden,?_⟩
  apply (le_div_iff₀ hden).mpr
  dsimp [vLo,vHi]
  dsimp [uHi] at hu
  nlinarith only [hu.2]

theorem d6_argument_mono {l u : ℝ}
    (hl : l ∈ Icc uLo uHi) (hu : u ∈ Icc l uHi) : d6LogArgument l≤d6LogArgument u := by
  have hlD := (d6_argument_positive hl).2.2.1
  have huD := (d6_argument_positive ⟨hl.1.trans hu.1,hu.2⟩).2.2.1
  apply (div_le_div_iff₀ hlD huD).mpr
  dsimp [vLo,vHi]
  nlinarith only [hu.1]

theorem d6_real_cell_lower {l r u : ℝ}
    (hl : uLo≤l) (hlr : l≤r) (hr : r≤uHi) (hu : u ∈ Icc l r) :
    Real.log (d6LogArgument l)/(r*(1-r))≤d6OuterSlice u := by
  have hL := d6_argument_positive ⟨hl,hlr.trans hr⟩
  have hU := d6_argument_positive ⟨hl.trans hu.1,hu.2.trans hr⟩
  have hlog0 := Real.log_nonneg hL.2.2.2
  have hlog := Real.log_le_log (zero_lt_one.trans_le hL.2.2.2)
    (d6_argument_mono ⟨hl,hlr.trans hr⟩ ⟨hu.1,hu.2.trans hr⟩)
  have hden0 := mul_pos hU.1 hU.2.1
  have hden : u*(1-u)≤r*(1-r) := by
    have hm : 0≤(r-u)*(1-r-u) := mul_nonneg (sub_nonneg.mpr hu.2)
      (by dsimp [uHi] at hr; linarith only [hu.2,hr])
    nlinarith only [hm]
  exact (div_le_div_of_nonneg_left hlog0 hden0 hden).trans
    (div_le_div_of_nonneg_right hlog hden0.le)

theorem d6_rational_cell_lower (terms : ℕ) (l r : ℚ)
    (hl : (50/227 : ℚ)≤l) (hlr : l≤r) (hr : r≤(100/353 : ℚ))
    {u : ℝ} (hu : u ∈ Icc (l : ℝ) (r : ℝ)) :
    (d6CellLower terms l r : ℝ)≤d6OuterSlice u := by
  have hlR : uLo≤(l : ℝ) := by exact_mod_cast hl
  have hlrR : (l : ℝ)≤r := by exact_mod_cast hlr
  have hrR : (r : ℝ)≤uHi := by exact_mod_cast hr
  have hL := d6_argument_positive ⟨hlR,hlrR.trans hrR⟩
  have heq : (d6RationalArgument l : ℝ)=d6LogArgument (l : ℝ) := by
    simp only [d6RationalArgument,d6LogArgument,vLo,vHi,Rat.cast_div,Rat.cast_sub,
      Rat.cast_mul,Rat.cast_ofNat,Rat.cast_one]
  have harg : 1≤d6RationalArgument l := by
    have hh := hL.2.2.2
    rw [← heq] at hh
    exact_mod_cast hh
  let c : RationalLogCertificate := ⟨d6RationalArgument l,terms,
    logSeriesLower (d6RationalArgument l) terms,logSeriesUpper (d6RationalArgument l) terms⟩
  have hc : c.check=true := by
    simpa only [RationalLogCertificate.check,decide_eq_true_eq] using
      (show c.Valid from ⟨harg,le_rfl,le_rfl⟩)
  have hlog := (RationalLogCertificate.check_sound c hc).1
  change (logSeriesLower (d6RationalArgument l) terms : ℝ)≤Real.log (d6RationalArgument l : ℝ) at hlog
  rw [heq] at hlog
  have hR := d6_argument_positive ⟨hlR.trans hlrR,hrR⟩
  have h := (div_le_div_of_nonneg_right hlog (mul_pos hR.1 hR.2.1).le).trans
    (d6_real_cell_lower hlR hlrR hrR hu)
  simpa only [d6CellLower,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_one] using h

theorem continuousOn_d6OuterSlice : ContinuousOn d6OuterSlice (Icc uLo uHi) := by
  have hArg : ContinuousOn d6LogArgument (Icc uLo uHi) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro u hu
      exact (d6_argument_positive hu).2.2.1.ne'
  have hlog := hArg.log (fun u hu => (zero_lt_one.trans_le (d6_argument_positive hu).2.2.2).ne')
  exact hlog.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    (fun u hu => (mul_pos (d6_argument_positive hu).1 (d6_argument_positive hu).2.1).ne')

/-- Actual finite rational cell lower soundness for the untruncated D6
outer integral, not a saved numerical coefficient or a cell-bound premise. -/
theorem d6_rational_cell_integral_lower (terms : ℕ) (l r : ℚ)
    (hl : (50/227 : ℚ)≤l) (hlr : l≤r) (hr : r≤(100/353 : ℚ)) :
    (((r-l)*d6CellLower terms l r : ℚ) : ℝ)≤
      ∫ u in (l : ℝ)..(r : ℝ),d6OuterSlice u := by
  have hlR : uLo≤(l : ℝ) := by exact_mod_cast hl
  have hlrR : (l : ℝ)≤r := by exact_mod_cast hlr
  have hrR : (r : ℝ)≤uHi := by exact_mod_cast hr
  have hc := continuousOn_d6OuterSlice.mono
    (show Icc (l : ℝ) (r : ℝ) ⊆ Icc uLo uHi from fun u hu =>
      ⟨hlR.trans hu.1,hu.2.trans hrR⟩)
  have h := intervalIntegral.integral_mono_on hlrR intervalIntegrable_const
    (hc.intervalIntegrable_of_Icc hlrR) (fun u hu => d6_rational_cell_lower terms l r hl hlr hr hu)
  simpa only [intervalIntegral.integral_const,smul_eq_mul,Rat.cast_mul,Rat.cast_sub] using h

end

end ImbalancedChen.P2EnhancedSeedInheritedCellBounds
