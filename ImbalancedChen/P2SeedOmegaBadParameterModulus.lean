import ImbalancedChen.P2SeedOmegaBadGlobalCost
import ImbalancedChen.P5ZU1011BuchstabTailLipschitz

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Uniform alpha modulus of the actual original bad Gamma5 integral.
The original bad domain is fixed and its rough arguments stay on the
TRUE unbounded Buchstab tail. The omega modulus is an existing proved
actual-function theorem, not a presumed gain or numerical certificate.
All constants below are independent of an upper bound on alpha.
-/

namespace ImbalancedChen.P2SeedOmegaBadParameterModulus
noncomputable section
open Set MeasureTheory Filter
open scoped Interval Topology
open P2SeedOmegaLiteralFibre
open P2SeedOmegaBadGlobalCost
open P2SeedOmegaBadCellSemantics (actualBadKernel)

theorem actual_bad_kernel_parameter_modulus {alpha beta u v : ℝ}
    (ha : 2≤alpha) (hb : 2≤beta)
    (hu : u ∈ Icc corner a2) (hv : v ∈ Icc (badLower u) a2) :
    |actualBadKernel alpha u v-actualBadKernel beta u v|≤400*|alpha-beta| := by
  have hg := bad_closed_geometry hu hv
  have hargA := bad_argument_lower ha hu.2 hv.2
  have hargB := bad_argument_lower hb hu.2 hv.2
  have hω := P5Z.U1011BuchstabTailLipschitz.abs_sub_le_half
    (by linarith only [hargA] : 2≤badArgument alpha u v)
    (by linarith only [hargB] : 2≤badArgument beta u v)
  have heArg : badArgument alpha u v-badArgument beta u v=s0*(alpha-beta) := by
    unfold badArgument
    ring
  rw [heArg,abs_mul,abs_of_pos (by norm_num [s0] : 0<s0)] at hω
  have hcoef : 0≤K*s0/4 := by norm_num [K,s0]
  have hcoef24 : (K*s0/4)*s0/2≤24 := by norm_num [K,s0]
  have hu4 : (1/4:ℝ)≤u := by dsimp [corner] at hu; linarith only [hu.1]
  have hv4 : (1/4:ℝ)≤v := hu4.trans ((le_max_left u (1-2*u)).trans hv.1)
  have hden : (1/16:ℝ)≤u*v := by
    have h := mul_le_mul hu4 hv4 (by norm_num : (0:ℝ)≤1/4) hg.1.le
    norm_num only [show (1/4:ℝ)*(1/4)=1/16 by norm_num] at h
    exact h
  have he : actualBadKernel alpha u v-actualBadKernel beta u v=
      (K*s0/4)*(LiLiuPrereqBuchstab.buchstab (badArgument alpha u v)-
        LiLiuPrereqBuchstab.buchstab (badArgument beta u v))/(u*v) := by
    unfold actualBadKernel
    ring
  rw [he,abs_div,abs_mul,abs_of_nonneg hcoef,abs_of_pos (mul_pos hg.1 hg.2.1)]
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hω hcoef) (mul_pos hg.1 hg.2.1).le
  have h2 := div_le_div_of_nonneg_left
    (mul_nonneg hcoef (div_nonneg (mul_nonneg (by norm_num [s0]) (abs_nonneg _))
      (by norm_num))) (by norm_num : (0:ℝ)<1/16) hden
  calc
    _ ≤ ((K*s0/4)*(s0*|alpha-beta|/2))/(u*v) := h1
    _ ≤ ((K*s0/4)*(s0*|alpha-beta|/2))/(1/16) := h2
    _ ≤ 400*|alpha-beta| := by
      have h := mul_le_mul_of_nonneg_right hcoef24 (abs_nonneg (alpha-beta))
      nlinarith only [h,abs_nonneg (alpha-beta)]

/-- One explicit error constant works on the full unbounded parameter
family. Both actual integrals are supplied by the previous genuine
continuity/integrability theorem, including the moving max endpoint. -/
theorem actual_bad_cost_parameter_modulus {alpha beta : ℝ}
    (ha : 2≤alpha) (hb : 2≤beta) :
    |actualBadCost alpha-actualBadCost beta|≤400*|alpha-beta| := by
  have hC : 0≤400*|alpha-beta| := mul_nonneg (by norm_num) (abs_nonneg _)
  have huLR : corner≤a2 := by norm_num [corner,a2]
  have hinner : ∀ u ∈ Icc corner a2,
      |(∫ v in badLower u..a2,actualBadKernel alpha u v)-
        (∫ v in badLower u..a2,actualBadKernel beta u v)|≤400*|alpha-beta| := by
    intro u hu
    have hg := bad_fibre_geometry hu
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=badLower u) (b:=a2) (C:=400*|alpha-beta|)
      (f:=fun v => actualBadKernel alpha u v-actualBadKernel beta u v)
      (fun v hv => by
        rw [uIoc_of_le hg.2.2.1] at hv
        simpa only [Real.norm_eq_abs] using
          actual_bad_kernel_parameter_modulus ha hb hu ⟨hv.1.le,hv.2⟩)
    rw [intervalIntegral.integral_sub (actual_bad_inner_intervalIntegrable alpha hu)
      (actual_bad_inner_intervalIntegrable beta hu)] at h
    have hw : a2-badLower u≤1 := by
      have hl := hg.2.1
      dsimp [a2]
      linarith only [hl]
    have hm := mul_le_mul_of_nonneg_left hw hC
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hg.2.2.1)] at h
    exact h.trans (by simpa only [mul_one] using hm)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=corner) (b:=a2) (C:=400*|alpha-beta|)
    (f:=fun u => (∫ v in badLower u..a2,actualBadKernel alpha u v)-
      (∫ v in badLower u..a2,actualBadKernel beta u v))
    (fun u hu => by
      rw [uIoc_of_le huLR] at hu
      simpa only [Real.norm_eq_abs] using hinner u ⟨hu.1.le,hu.2⟩)
  rw [intervalIntegral.integral_sub (actual_bad_outer_intervalIntegrable alpha)
    (actual_bad_outer_intervalIntegrable beta)] at h
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr huLR)] at h
  have hw : a2-corner≤1 := by norm_num [a2,corner]
  have hm := mul_le_mul_of_nonneg_left hw hC
  exact h.trans (by simpa only [mul_one] using hm)

def extendedCost (alpha : ℝ) : ℝ := actualBadCost (max 2 alpha)

theorem extendedCost_lipschitz : LipschitzWith 400 extendedCost := by
  apply LipschitzWith.of_dist_le_mul
  intro alpha beta
  have h := actual_bad_cost_parameter_modulus
    (le_max_left (2:ℝ) alpha) (le_max_left (2:ℝ) beta)
  have hm := abs_max_sub_max_le_max (2:ℝ) alpha 2 beta
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (alpha-beta))] at hm
  have hs := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤400)
  simpa only [extendedCost,Real.dist_eq,NNReal.coe_ofNat] using h.trans hs

/-- A true parameter integral limit, valid at alpha=2 as well. The only
limit hypothesis is convergence of the actual inherited parameter. -/
theorem actual_bad_cost_tendsto {ι : Type*} {l : Filter ι} {A : ι → ℝ}
    {alpha : ℝ} (ha : 2≤alpha) (hA : ∀ᶠ i in l,2≤A i)
    (hlim : Tendsto A l (𝓝 alpha)) :
    Tendsto (fun i => actualBadCost (A i)) l (𝓝 (actualBadCost alpha)) := by
  have h := extendedCost_lipschitz.continuous.continuousAt.tendsto.comp hlim
  have he : (fun i => extendedCost (A i))=ᶠ[l](fun i => actualBadCost (A i)) := by
    filter_upwards [hA] with i hi
    simp only [extendedCost,max_eq_right hi]
  have hval : extendedCost alpha=actualBadCost alpha := by
    simp only [extendedCost,max_eq_right ha]
  rw [hval] at h
  exact h.congr' he

end
end ImbalancedChen.P2SeedOmegaBadParameterModulus
