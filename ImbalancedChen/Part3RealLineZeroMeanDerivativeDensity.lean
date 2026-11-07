import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Zero-integral smooth compact tests are dense in L2 of the REAL LINE with
Lebesgue measure. The compensating normalized bump spreads over a larger
and larger interval, has integral one, and has squared L2 norm at most
1/(2R). Subtracting the original integral times that bump costs arbitrarily
little in L2. This uses Mathlib's genuine compact smooth Lp density.

Every zero-integral smooth compact function has a genuinely smooth compact
primitive: FTC gives the derivative, and its two tails vanish because the
original support is bounded and the whole integral is zero. Combining the
two facts proves actual compact derivatives dense in L2. There is no
hDense/hPrimitive or distributional conclusion used as a premise.
-/

namespace ImbalancedChen.Part3.RealLineZeroMeanDerivativeDensity20261025a

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff

abbrev RealLineL2 := Lp ℂ 2 (volume : Measure ℝ)

theorem norm_toLp_sq (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    ‖hg.toLp g‖^2=∫ x : ℝ,‖g x‖^2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,
    ← integral_re (L2.integrable_inner (hg.toLp g) (hg.toLp g))]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx,← InnerProductSpace.norm_sq_eq_re_inner]

/-- A true expanding smooth bump, normalized by its actual integral. -/
def spreadingBump (R : ℝ) (hR : 0<R) : ContDiffBump (0:ℝ) where
  rIn := R
  rOut := 2*R
  rIn_pos := hR
  rIn_lt_rOut := by linarith

def normalizedSpread (R : ℝ) (hR : 0<R) (x : ℝ) : ℂ :=
  ((spreadingBump R hR).normed volume x:ℂ)

theorem normalizedSpread_contDiff (R : ℝ) (hR : 0<R) :
    ContDiff ℝ ∞ (normalizedSpread R hR) :=
  Complex.ofRealCLM.contDiff.comp (spreadingBump R hR).contDiff_normed

theorem normalizedSpread_compact (R : ℝ) (hR : 0<R) :
    HasCompactSupport (normalizedSpread R hR) := by
  exact (spreadingBump R hR).hasCompactSupport_normed.comp_left Complex.ofReal_zero

theorem normalizedSpread_memLp (R : ℝ) (hR : 0<R) :
    MemLp (normalizedSpread R hR) 2 volume :=
  (normalizedSpread_contDiff R hR).continuous.memLp_of_hasCompactSupport
    (normalizedSpread_compact R hR)

theorem normalizedSpread_integral (R : ℝ) (hR : 0<R) :
    (∫ x : ℝ,normalizedSpread R hR x)=1 := by
  rw [normalizedSpread,integral_complex_ofReal,(spreadingBump R hR).integral_normed]
  simp

/-- Actual L2 decay of the spreading correction, with an explicit rate. -/
theorem normalizedSpread_norm_sq_le (R : ℝ) (hR : 0<R) :
    ‖(normalizedSpread_memLp R hR).toLp (normalizedSpread R hR)‖^2≤1/(2*R) := by
  let b := spreadingBump R hR
  have hpoint (x : ℝ) : ‖normalizedSpread R hR x‖^2≤(1/(2*R))*b.normed volume x := by
    have hnonneg := b.nonneg_normed (μ := volume) x
    have hup : b.normed volume x≤1/(2*R) := by
      simpa only [b,spreadingBump,Real.volume_real_closedBall hR.le] using
        b.normed_le_div_measure_closedBall_rIn volume x
    have hmul := mul_le_mul_of_nonneg_right hup hnonneg
    simpa only [normalizedSpread,b,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hnonneg,pow_two] using hmul
  have hintSq : Integrable (fun x : ℝ => ‖normalizedSpread R hR x‖^2) :=
    (memLp_two_iff_integrable_sq_norm
      (normalizedSpread_contDiff R hR).continuous.aestronglyMeasurable).1
        (normalizedSpread_memLp R hR)
  rw [norm_toLp_sq]
  have hle := integral_mono hintSq (b.integrable_normed.const_mul (1/(2*R))) hpoint
  simpa only [integral_const_mul,b.integral_normed,mul_one] using hle

def spreadVector (n : ℕ) : RealLineL2 :=
  (normalizedSpread_memLp ((n:ℝ)+1) (by positivity)).toLp
    (normalizedSpread ((n:ℝ)+1) (by positivity))

/-- The integral-one correcting bumps converge to zero in actual L2 while
their supports expand. This is the real-line feature absent on a circle. -/
theorem normalizedSpread_L2_tendsto_zero : Tendsto spreadVector atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt ((ε^2)⁻¹)
  refine ⟨N,?_⟩
  intro n hn
  have hcast : (N:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hR : 0<(n:ℝ)+1 := by positivity
  have hlarge : 1/ε^2<(n:ℝ)+1 := by
    rw [one_div]
    linarith
  have hmul : 1<((n:ℝ)+1)*ε^2 :=
    (div_lt_iff₀ (sq_pos_of_pos hε)).mp hlarge
  have hrate : 1/(2*((n:ℝ)+1))<ε^2 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hR)).mpr
    nlinarith [sq_nonneg ε]
  have hsq : ‖spreadVector n‖^2<ε^2 :=
    (normalizedSpread_norm_sq_le ((n:ℝ)+1) hR).trans_lt hrate
  rw [dist_zero_right]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq

theorem exists_integral_one_small_L2 (δ : ℝ) (hδ : 0<δ) :
    ∃ (b : ℝ → ℂ) (hb : MemLp b 2 volume),
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ (∫ x : ℝ,b x)=1 ∧ ‖hb.toLp b‖≤δ := by
  let R : ℝ := (δ^2)⁻¹
  have hR : 0<R := inv_pos.mpr (sq_pos_of_pos hδ)
  refine ⟨normalizedSpread R hR,normalizedSpread_memLp R hR,
    normalizedSpread_contDiff R hR,normalizedSpread_compact R hR,
    normalizedSpread_integral R hR,?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) hδ.le).mp
  have hbound := normalizedSpread_norm_sq_le R hR
  have hrate : 1/(2*R)=δ^2/2 := by
    dsimp [R]
    field_simp [hδ.ne']
    ring
  rw [hrate] at hbound
  exact hbound.trans (by nlinarith [sq_nonneg δ])

/-- Correct one actual smooth compact function to zero integral while
making the L2 change smaller than the requested tolerance. -/
theorem smooth_compact_zero_mean_correction (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (ε : ℝ) (hε : 0<ε) :
    ∃ (k : ℝ → ℂ) (hk : MemLp k 2 volume),
      ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧ (∫ x : ℝ,k x)=0 ∧
      ‖(hg.continuous.memLp_of_hasCompactSupport hc).toLp g-hk.toLp k‖<ε := by
  let c : ℂ := ∫ x : ℝ,g x
  have hden : 0<‖c‖+1 := by positivity
  let δ : ℝ := ε/(2*(‖c‖+1))
  have hδ : 0<δ := div_pos hε (mul_pos (by norm_num) hden)
  obtain ⟨b,hb,hbs,hbc,hbi,hbn⟩ := exists_integral_one_small_L2 δ hδ
  let k : ℝ → ℂ := g-c • b
  have hks : ContDiff ℝ ∞ k := hg.sub (hbs.const_smul c)
  have hkc : HasCompactSupport k := hc.sub hbc.smul_left
  have hkm : MemLp k 2 volume := hks.continuous.memLp_of_hasCompactSupport hkc
  have hgm : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hc
  have hkint : (∫ x : ℝ,k x)=0 := by
    rw [k,integral_sub (hg.continuous.integrable_of_hasCompactSupport hc)
      ((hbs.continuous.integrable_of_hasCompactSupport hbc).const_smul c),
      integral_smul,hbi,smul_eq_mul,mul_one]
    exact sub_self c
  have hLp : hgm.toLp g-hkm.toLp k=c • hb.toLp b := by
    apply Lp.ext
    filter_upwards [hgm.coeFn_toLp,hkm.coeFn_toLp,hb.coeFn_toLp,
      Lp.coeFn_sub (hgm.toLp g) (hkm.toLp k),Lp.coeFn_smul c (hb.toLp b)]
      with x hgx hkx hbx hsub hsmul
    rw [hsub,hsmul,hgx,hkx,hbx]
    change g x-(g x-c • b x)=c • b x
    abel
  refine ⟨k,hkm,hks,hkc,hkint,?_⟩
  rw [hLp,norm_smul]
  have hle := mul_le_mul_of_nonneg_left hbn (norm_nonneg c)
  have hsmall : ‖c‖*δ<ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (mul_pos (by norm_num) hden)).mpr
    nlinarith [norm_nonneg c]
  exact hle.trans_lt hsmall

def zeroMeanSmoothL2 : Set RealLineL2 :=
  {f | ∃ g : ℝ → ℂ, f=ᵐ[volume] g ∧ HasCompactSupport g ∧
    ContDiff ℝ ∞ g ∧ (∫ x : ℝ,g x)=0}

/-- Genuine zero-integral C-infinity compact tests are dense on the real
line. Integral is not continuous in the unweighted L2 norm on this line. -/
theorem zeroMeanSmoothL2_dense : Dense zeroMeanSmoothL2 := by
  let S : Set RealLineL2 := {f | ∃ g : ℝ → ℂ, f=ᵐ[volume] g ∧
    HasCompactSupport g ∧ ContDiff ℝ ∞ g}
  have hS : Dense S := Lp.dense_hasCompactSupport_contDiff (p := 2) (by norm_num)
  have hsub : S⊆closure zeroMeanSmoothL2 := by
    rintro f ⟨g,hfg,hgc,hgs⟩
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨k,hk,hks,hkc,hki,herr⟩ := smooth_compact_zero_mean_correction g hgs hgc ε hε
    have hgm : MemLp g 2 volume := hgs.continuous.memLp_of_hasCompactSupport hgc
    have hgf : hgm.toLp g=f := Lp.ext (hgm.coeFn_toLp.trans hfg.symm)
    refine ⟨hk.toLp k,⟨k,hk.coeFn_toLp,hkc,hks,hki⟩,?_⟩
    rw [dist_eq_norm,← hgf]
    exact herr
  intro f
  exact (closure_minimal hsub isClosed_closure) (hS f)

/-- A literal FTC primitive with compact support: the left tail has not
yet met the support, and the right tail is the zero whole-line integral. -/
theorem exists_smooth_compact_primitive (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hz : (∫ x : ℝ,g x)=0) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ deriv h=g := by
  obtain ⟨R,hR,hsupp⟩ := hc.isBounded.subset_ball_lt 0 (0:ℝ)
  have hs : Function.support g⊆Ioo (-R) R := by
    intro x hx
    have ht := hsupp (subset_tsupport g hx)
    simpa only [Real.ball_eq_Ioo,zero_sub,zero_add] using ht
  let h : ℝ → ℂ := fun x => ∫ t in (-R)..x,g t
  have hder (x : ℝ) : HasDerivAt h (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable _ _)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuous.continuousAt
  have hdeq : deriv h=g := funext fun x => (hder x).deriv
  have hsm : ContDiff ℝ ∞ h :=
    contDiff_infty_iff_deriv.mpr ⟨fun x => (hder x).differentiableAt,by rwa [hdeq]⟩
  have hleft (x : ℝ) (hx : x≤-R) : h x=0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [uIoc_of_ge hx] at ht
    have hta : t≤-R := ht.2
    apply Function.not_mem_support.mp
    intro htg
    exact (not_lt_of_ge hta) (hs htg).1
  have hright (x : ℝ) (hx : R≤x) : h x=0 := by
    have hsupport : Function.support g⊆Ioc (-R) x := by
      intro t ht
      exact ⟨(hs ht).1,((hs ht).2.le.trans hx)⟩
    exact (intervalIntegral.integral_eq_integral_of_support_subset hsupport).trans hz
  have hcomp : HasCompactSupport h := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R) R))
    intro x hx
    by_cases hxa : -R≤x
    · have hxr : R<x := lt_of_not_ge (fun h => hx ⟨hxa,h⟩)
      exact hright x hxr.le
    · exact hleft x (lt_of_not_ge hxa).le
  exact ⟨h,hsm,hcomp,hdeq⟩

/-- Actual compact smooth derivatives approximate any real-line L2 input.
This is the 1D supplier for weak horizontal derivative annihilation. -/
theorem exists_compact_smooth_derivative_approximation (g : ℝ → ℂ)
    (hg : MemLp g 2 volume) (ε : ℝ) (hε : 0<ε) :
    ∃ (h : ℝ → ℂ) (hder : MemLp (deriv h) 2 volume),
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      ‖hg.toLp g-hder.toLp (deriv h)‖<ε := by
  obtain ⟨v,hv,hdist⟩ := Metric.mem_closure_iff.mp (zeroMeanSmoothL2_dense (hg.toLp g)) ε hε
  obtain ⟨k,hvk,hkc,hks,hki⟩ := hv
  obtain ⟨h,hhs,hhc,hhder⟩ := exists_smooth_compact_primitive k hks hkc hki
  have hkm : MemLp k 2 volume := hks.continuous.memLp_of_hasCompactSupport hkc
  have hdm : MemLp (deriv h) 2 volume := by rwa [hhder]
  have hEq : hdm.toLp (deriv h)=v := by
    apply Lp.ext
    exact hdm.coeFn_toLp.trans ((Filter.Eventually.of_forall fun x => congrFun hhder x).trans hvk.symm)
  exact ⟨h,hdm,hhs,hhc,by simpa only [dist_eq_norm,hEq] using hdist⟩

end
end ImbalancedChen.Part3.RealLineZeroMeanDerivativeDensity20261025a
