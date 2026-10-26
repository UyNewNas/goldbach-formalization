import ImbalancedChen.P2SeedOmegaLiteralFunctional
import ImbalancedChen.P2BuchstabRationalSemantics
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original BAD Gamma5 actual-omega double integral on rational cells.
The omega upper value is DERIVED from the actual delayed Buchstab recurrence
in P2BuchstabRationalSemantics, never from a desired integral inequality.
The original alpha-dependent argument, positive K*s0/4 coefficient, both
prime denominators, whole closed cells, and every endpoint are retained.
No concrete recurrence array or covering partition for the seed is supplied;
the saved 8192-cell PASS and Q80 lower floor remain OPEN for Dots.
-/

namespace ImbalancedChen.P2SeedOmegaBadCellSemantics
noncomputable section
open Set MeasureTheory
open scoped Interval
open P2SeedOmegaLiteralFibre
open Certificates.P2BuchstabRationalSemantics

structure Cell where
  ul : ℚ
  ur : ℚ
  vl : ℚ
  vr : ℚ
  alphaLo : ℚ
  alphaHi : ℚ

/-- Only rational geometry and parameter matching. Equality boundaries
are permitted, so zero-width cells and the switching line are explicit. -/
def Cell.Valid (c : Cell) : Prop :=
  (19/58:ℚ)≤c.ul ∧ c.ul≤c.ur ∧ c.ur≤(10/29:ℚ) ∧
  c.ur≤c.vl ∧ c.vl≤c.vr ∧ c.vr≤(10/29:ℚ) ∧
  1≤c.vl+2*c.ul ∧ 2≤c.alphaLo ∧ c.alphaLo≤c.alphaHi

theorem Cell.closed_support (c : Cell) (hc : c.Valid) {alpha u v : ℝ}
    (ha : alpha ∈ Icc (c.alphaLo:ℝ) (c.alphaHi:ℝ))
    (hu : u ∈ Icc (c.ul:ℝ) (c.ur:ℝ))
    (hv : v ∈ Icc (c.vl:ℝ) (c.vr:ℝ)) :
    u ∈ Icc corner a2 ∧ v ∈ Icc (max u (1-2*u)) a2 ∧
      2≤alpha ∧ (4313/725:ℝ)≤badArgument alpha u v := by
  rcases hc with ⟨hl,hur,hu2,huv,hvr,hv2,hgate,ha2,hAA⟩
  have hlR : corner≤(c.ul:ℝ) := by exact_mod_cast hl
  have hu2R : (c.ur:ℝ)≤a2 := by exact_mod_cast hu2
  have huvR : (c.ur:ℝ)≤(c.vl:ℝ) := by exact_mod_cast huv
  have hv2R : (c.vr:ℝ)≤a2 := by exact_mod_cast hv2
  have hgateR : (1:ℝ)≤(c.vl:ℝ)+2*(c.ul:ℝ) := by exact_mod_cast hgate
  have ha2R : (2:ℝ)≤(c.alphaLo:ℝ) := by exact_mod_cast ha2
  have hU : u ∈ Icc corner a2 := ⟨hlR.trans hu.1,hu.2.trans hu2R⟩
  have hV : v ∈ Icc (max u (1-2*u)) a2 := by
    refine ⟨max_le_iff.mpr ⟨hu.2.trans (huvR.trans hv.1),?_⟩,hv.2.trans hv2R⟩
    linarith only [hgateR,hu.1,hv.1]
  have hA := ha2R.trans ha.1
  exact ⟨hU,hV,hA,bad_argument_lower hA hU.2 hV.2⟩

def actualBadKernel (alpha u v : ℝ) : ℝ :=
  (K*s0/4)*LiLiuPrereqBuchstab.buchstab (badArgument alpha u v)/(u*v)

def Cell.rationalUpper (c : Cell) (num : ℚ) : ℚ :=
  ((681/100:ℚ)*(227/50)/4)*(num/(2:ℚ)^80)/(c.ul*c.vl)

/-- Original affine rough argument lies in the SAME grid cell as the
recurrence data. These are rational comparisons, not sample evaluations. -/
theorem Cell.argument_in_grid (c : Cell) {m k : ℕ}
    (hl : grid m k≤(227/50:ℚ)*(c.alphaLo-c.ur-c.vr))
    (hr : (227/50:ℚ)*(c.alphaHi-c.ul-c.vl)≤grid m (k+1))
    {alpha u v : ℝ}
    (ha : alpha ∈ Icc (c.alphaLo:ℝ) (c.alphaHi:ℝ))
    (hu : u ∈ Icc (c.ul:ℝ) (c.ur:ℝ))
    (hv : v ∈ Icc (c.vl:ℝ) (c.vr:ℝ)) :
    badArgument alpha u v ∈ Icc (grid m k:ℝ) (grid m (k+1):ℝ) := by
  have hlR : (grid m k:ℝ)≤(227/50:ℝ)*
      ((c.alphaLo:ℝ)-(c.ur:ℝ)-(c.vr:ℝ)) := by exact_mod_cast hl
  have hrR : (227/50:ℝ)*((c.alphaHi:ℝ)-(c.ul:ℝ)-(c.vl:ℝ))≤
      (grid m (k+1):ℝ) := by exact_mod_cast hr
  dsimp [badArgument,s0]
  constructor <;> linarith only [hlR,hrR,ha.1,ha.2,hu.1,hu.2,hv.1,hv.2]

/-- Rationally licensed WHOLE-CELL bound for the actual switched kernel.
The only functional input is a certified earlier-node recurrence array. -/
theorem Cell.actual_kernel_upper (c : Cell) (hc : c.Valid)
    {m k : ℕ} {nodes : List NodeEnclosure} (hnodes : check m nodes=true)
    (hk : k+1<nodes.length) (num : ℚ) (hnum : 0≤num)
    (hcap : (2:ℚ)^80*(entry nodes (k+1)).upper≤num*grid m k)
    (hl : grid m k≤(227/50:ℚ)*(c.alphaLo-c.ur-c.vr))
    (hr : (227/50:ℚ)*(c.alphaHi-c.ul-c.vl)≤grid m (k+1))
    {alpha u v : ℝ}
    (ha : alpha ∈ Icc (c.alphaLo:ℝ) (c.alphaHi:ℝ))
    (hu : u ∈ Icc (c.ul:ℝ) (c.ur:ℝ))
    (hv : v ∈ Icc (c.vl:ℝ) (c.vr:ℝ)) :
    actualBadKernel alpha u v≤(c.rationalUpper num:ℝ) := by
  have hs := c.argument_in_grid hl hr ha hu hv
  have homega := check_cell_upper_scaled hnodes hk
    (S:=(2:ℚ)^80) (by positivity) hnum hcap hs
  have hU : (0:ℝ)<(c.ul:ℝ) := by
    have h := hc.1
    have hR : (19/58:ℝ)≤(c.ul:ℝ) := by exact_mod_cast h
    linarith only [hR]
  have hUV : (c.ul:ℝ)≤(c.vl:ℝ) := by
    have hQ : c.ul≤c.vl := hc.2.1.trans hc.2.2.2.1
    exact_mod_cast hQ
  have hV := hU.trans_le hUV
  have hu0 := hU.trans_le hu.1
  have hv0 := hV.trans_le hv.1
  have hden : (c.ul:ℝ)*(c.vl:ℝ)≤u*v :=
    mul_le_mul hu.1 hv.1 hV.le hu0.le
  have hnR : (0:ℝ)≤(num:ℝ)/(2:ℝ)^80 := by
    apply div_nonneg
    · exact_mod_cast hnum
    · positivity
  have hC : (0:ℝ)≤K*s0/4 := by norm_num [K,s0]
  have hω : LiLiuPrereqBuchstab.buchstab (badArgument alpha u v)≤
      (num:ℝ)/(2:ℝ)^80 := by
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using homega
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hω hC) (mul_pos hu0 hv0).le
  have h2 := div_le_div_of_nonneg_left (mul_nonneg hC hnR) (mul_pos hU hV) hden
  have h := h1.trans h2
  simpa only [actualBadKernel,Cell.rationalUpper,K,s0,
    Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using h

private def safeKernel (alpha : ℝ) (p : ℝ×ℝ) : ℝ :=
  actualBadKernel alpha (max a0 p.1) (max a0 p.2)

private theorem continuous_safeKernel (alpha : ℝ) : Continuous (safeKernel alpha) := by
  have hu : Continuous (fun p : ℝ×ℝ => max a0 p.1) := continuous_const.max continuous_fst
  have hv : Continuous (fun p : ℝ×ℝ => max a0 p.2) := continuous_const.max continuous_snd
  have ha0 : 0<a0 := by norm_num [a0]
  have harg : Continuous (fun p : ℝ×ℝ => badArgument alpha
      (max a0 p.1) (max a0 p.2)) := continuous_const.mul ((continuous_const.sub hu).sub hv)
  exact (continuous_const.mul (LiLiuPrereqBuchstab.continuous_buchstab.comp harg)).div
    (hu.mul hv) (fun p => (mul_pos (ha0.trans_le (le_max_left _ _))
      (ha0.trans_le (le_max_left _ _))).ne')

private theorem safeKernel_eq {alpha u v : ℝ} (hu : a0≤u) (hv : a0≤v) :
    safeKernel alpha (u,v)=actualBadKernel alpha u v := by
  simp only [safeKernel,max_eq_right hu,max_eq_right hv]

/-- Actual original double-integral cell cost is bounded by its rational
volume times the derived recurrence cap. No integrability premise is
hidden: a continuous extension proves both iterated integrals exist. -/
theorem Cell.actual_double_integral_upper (c : Cell) (hc : c.Valid)
    {m k : ℕ} {nodes : List NodeEnclosure} (hnodes : check m nodes=true)
    (hk : k+1<nodes.length) (num : ℚ) (hnum : 0≤num)
    (hcap : (2:ℚ)^80*(entry nodes (k+1)).upper≤num*grid m k)
    (hl : grid m k≤(227/50:ℚ)*(c.alphaLo-c.ur-c.vr))
    (hr : (227/50:ℚ)*(c.alphaHi-c.ul-c.vl)≤grid m (k+1))
    {alpha : ℝ} (ha : alpha ∈ Icc (c.alphaLo:ℝ) (c.alphaHi:ℝ)) :
    (∫ u in (c.ul:ℝ)..(c.ur:ℝ),∫ v in (c.vl:ℝ)..(c.vr:ℝ),
      actualBadKernel alpha u v)≤
      (((c.ur-c.ul)*(c.vr-c.vl)*c.rationalUpper num:ℚ):ℝ) := by
  have huLR : (c.ul:ℝ)≤(c.ur:ℝ) := by exact_mod_cast hc.2.1
  have hvLR : (c.vl:ℝ)≤(c.vr:ℝ) := by exact_mod_cast hc.2.2.2.2.1
  have hU : a0≤(c.ul:ℝ) := by
    have h : (19/58:ℝ)≤(c.ul:ℝ) := by exact_mod_cast hc.1
    dsimp [a0]
    linarith only [h]
  have hV : a0≤(c.vl:ℝ) := by
    have huv : (c.ur:ℝ)≤(c.vl:ℝ) := by exact_mod_cast hc.2.2.2.1
    exact hU.trans (huLR.trans huv)
  have hsafe := continuous_safeKernel alpha
  have hinner : Continuous (fun u : ℝ => ∫ v in (c.vl:ℝ)..(c.vr:ℝ),
      safeKernel alpha (u,v)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f:=fun u v => safeKernel alpha (u,v)) hsafe (c.vl:ℝ) (c.vr:ℝ)
  have hbound : ∀ u ∈ Icc (c.ul:ℝ) (c.ur:ℝ),
      (∫ v in (c.vl:ℝ)..(c.vr:ℝ),safeKernel alpha (u,v))≤
        ((c.vr:ℝ)-(c.vl:ℝ))*(c.rationalUpper num:ℝ) := by
    intro u hu
    have hcont : Continuous (fun v : ℝ => safeKernel alpha (u,v)) :=
      hsafe.comp (continuous_const.prodMk continuous_id)
    have h := intervalIntegral.integral_mono_on hvLR
      (hcont.intervalIntegrable (c.vl:ℝ) (c.vr:ℝ)) intervalIntegrable_const
      (fun v hv => by
        rw [safeKernel_eq (hU.trans hu.1) (hV.trans hv.1)]
        exact c.actual_kernel_upper hc hnodes hk num hnum hcap hl hr ha hu hv)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using h
  have houter := intervalIntegral.integral_mono_on huLR
    (hinner.intervalIntegrable (c.ul:ℝ) (c.ur:ℝ)) intervalIntegrable_const hbound
  have heq : (∫ u in (c.ul:ℝ)..(c.ur:ℝ),∫ v in (c.vl:ℝ)..(c.vr:ℝ),
      safeKernel alpha (u,v))=
      (∫ u in (c.ul:ℝ)..(c.ur:ℝ),∫ v in (c.vl:ℝ)..(c.vr:ℝ),
        actualBadKernel alpha u v) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le huLR] at hu
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hvLR] at hv
    exact safeKernel_eq (hU.trans hu.1) (hV.trans hv.1)
  rw [heq] at houter
  simpa only [intervalIntegral.integral_const,smul_eq_mul,
    Rat.cast_mul,Rat.cast_sub,mul_assoc] using houter

end
end ImbalancedChen.P2SeedOmegaBadCellSemantics
