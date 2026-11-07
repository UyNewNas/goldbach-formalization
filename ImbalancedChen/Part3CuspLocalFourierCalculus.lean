import ImbalancedChen.Part3ActualMaassFourierODE

/-!
# Genuine cusp-local coefficient calculus and the actual Maass ODE

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

All original C2, periodicity and PDE assumptions concern ONLY y>Y.
Compact integral differentiation is reused through the actual domain
coordinate t=y-Y>0, then transported back. No PDE is assumed, extended,
or solved below Y. Original partial derivatives and literal horizontal
coefficient integrals are retained. The coefficient equation holds for
every signed integer n, including zero.
-/

namespace ImbalancedChen.Part3.CuspLocalFourierCalculus20261026b

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ActualMaassFourierODE20261026a
attribute [local instance] Measure.Subtype.measureSpace

local instance periodCell_finite : IsFiniteMeasure (volume : Measure PeriodCell) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_lt_top

def cuspDomain (Y : ℝ) : Set (ℝ × ℝ) := {p | Y<p.2}
theorem cuspDomain_isOpen (Y : ℝ) : IsOpen (cuspDomain Y) :=
  isOpen_lt continuous_const continuous_snd

/-- Translation here is solely a local coordinate for integral
regularity. It carries upperDomain precisely into the given open cusp. -/
private def shift (Y : ℝ) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := F (p.1,p.2+Y)

private theorem shift_continuousOn {Y : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : ContinuousOn F (cuspDomain Y)) : ContinuousOn (shift Y F) upperDomain := by
  exact hF.comp (by fun_prop) (fun p hp => by change Y<p.2+Y; change 0<p.2 at hp; linarith)

/-- Genuine compact differentiation of the original cusp-local period
integral, with all domination paid on compact rectangles above Y. -/
theorem periodIntegral_hasDerivAt_local {Y : ℝ} {F G : ℝ × ℝ → ℂ}
    (hF : ContinuousOn F (cuspDomain Y)) (hG : ContinuousOn G (cuspDomain Y))
    (hd : ∀ x t : ℝ, Y<t → HasDerivAt (fun s => F (x,s)) (G (x,t)) t)
    {y : ℝ} (hy : Y<y) : HasDerivAt (periodIntegral F) (periodIntegral G y) y := by
  have hshift (x t : ℝ) (ht : 0<t) :
      HasDerivAt (fun s => shift Y F (x,s)) (shift Y G (x,t)) t := by
    simpa only [shift,Function.comp_def,mul_one] using
      (hd x (t+Y) (by linarith)).comp t ((hasDerivAt_id t).add_const Y)
  have hs := periodIntegral_hasDerivAt (shift_continuousOn hF) (shift_continuousOn hG)
    hshift (sub_pos.mpr hy)
  have hb := hs.comp y ((hasDerivAt_id y).sub_const Y)
  simpa only [Function.comp_def,periodIntegral,shift,sub_add_cancel,mul_one] using hb

/-- Original cusp-local continuity suffices for coefficient continuity;
no globally continuous extension of the original function is used. -/
theorem periodIntegral_continuousOn_local {Y : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : ContinuousOn F (cuspDomain Y)) :
    ContinuousOn (periodIntegral F) (Ioi Y) := by
  have hs := periodIntegral_continuousOn (shift_continuousOn hF)
  have hb := hs.comp (by fun_prop : ContinuousOn (fun t : ℝ => t-Y) (Ioi Y))
    (fun t ht => sub_pos.mpr ht)
  simpa only [Function.comp_def,periodIntegral,shift,sub_add_cancel] using hb

theorem partialX_contDiffOn_local {Y : ℝ} {u : ℝ × ℝ → ℂ} {n k : ℕ∞ω}
    (hu : ContDiffOn ℝ n u (cuspDomain Y)) (hk : k+1≤n) :
    ContDiffOn ℝ k (partialX u) (cuspDomain Y) :=
  (hu.fderiv_of_isOpen (cuspDomain_isOpen Y) hk).clm_apply contDiffOn_const

theorem partialY_contDiffOn_local {Y : ℝ} {u : ℝ × ℝ → ℂ} {n k : ℕ∞ω}
    (hu : ContDiffOn ℝ n u (cuspDomain Y)) (hk : k+1≤n) :
    ContDiffOn ℝ k (partialY u) (cuspDomain Y) :=
  (hu.fderiv_of_isOpen (cuspDomain_isOpen Y) hk).clm_apply contDiffOn_const

theorem horizontal_hasDerivAt_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : DifferentiableOn ℝ u (cuspDomain Y)) (x : ℝ) {y : ℝ} (hy : Y<y) :
    HasDerivAt (fun t => u (t,y)) (partialX u (x,y)) x :=
  ((hu (x,y) hy).differentiableAt ((cuspDomain_isOpen Y).mem_nhds hy)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

theorem vertical_hasDerivAt_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : DifferentiableOn ℝ u (cuspDomain Y)) (x : ℝ) {y : ℝ} (hy : Y<y) :
    HasDerivAt (fun t => u (x,t)) (partialY u (x,y)) y :=
  ((hu (x,y) hy).differentiableAt ((cuspDomain_isOpen Y).mem_nhds hy)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

theorem continuous_slice_local {Y : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : ContinuousOn F (cuspDomain Y)) {y : ℝ} (hy : Y<y) :
    Continuous (fun x : ℝ => F (x,y)) :=
  hF.comp_continuous (by fun_prop) (fun _ => hy)

private theorem phased_continuousOn_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u (cuspDomain Y)) (n : ℤ) :
    ContinuousOn (phased n u) (cuspDomain Y) :=
  ((phase_continuous n).comp continuous_fst).continuousOn.mul hu

theorem coefficient_continuousOn_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u (cuspDomain Y)) (n : ℤ) :
    ContinuousOn (coefficient u n) (Ioi Y) :=
  periodIntegral_continuousOn_local (phased_continuousOn_local hu n)

/-- The first actual height derivative of the literal coefficient. -/
theorem coefficient_hasDerivAt_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 1 u (cuspDomain Y)) (n : ℤ) {y : ℝ} (hy : Y<y) :
    HasDerivAt (coefficient u n) (coefficient (partialY u) n y) y := by
  apply periodIntegral_hasDerivAt_local (phased_continuousOn_local hu.continuousOn n)
    (phased_continuousOn_local (partialY_contDiffOn_local hu
      (by norm_num : (0 : ℕ∞ω)+1≤1)).continuousOn n)
  intro x t ht
  exact (vertical_hasDerivAt_local (hu.differentiableOn (by norm_num)) x ht).const_mul (phase n x)

theorem coefficient_deriv_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 1 u (cuspDomain Y)) (n : ℤ) {y : ℝ} (hy : Y<y) :
    deriv (coefficient u n) y=coefficient (partialY u) n y :=
  (coefficient_hasDerivAt_local hu n hy).deriv

/-- The second actual coefficient derivative uses only the original
second partial derivative above Y. -/
theorem coefficient_deriv_hasDerivAt_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u (cuspDomain Y)) (n : ℤ) {y : ℝ} (hy : Y<y) :
    HasDerivAt (deriv (coefficient u n)) (coefficient (partialY (partialY u)) n y) y := by
  have heq : deriv (coefficient u n)=ᶠ[𝓝 y] coefficient (partialY u) n := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact coefficient_deriv_local (hu.of_le (by norm_num)) n ht
  exact (coefficient_hasDerivAt_local (partialY_contDiffOn_local hu (by norm_num)) n hy).
    congr_of_eventuallyEq heq

theorem coefficient_contDiffOn_two_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u (cuspDomain Y)) (n : ℤ) :
    ContDiffOn ℝ 2 (coefficient u n) (Ioi Y) := by
  have hdy : ContDiffOn ℝ 1 (partialY u) (cuspDomain Y) := partialY_contDiffOn_local hu (by norm_num)
  have hdy2 : ContinuousOn (partialY (partialY u)) (cuspDomain Y) :=
    (partialY_contDiffOn_local hdy (by norm_num : (0 : ℕ∞ω)+1≤1)).continuousOn
  have hdc : ContDiffOn ℝ 1 (coefficient (partialY u) n) (Ioi Y) := by
    rw [show (1 : ℕ∞ω)=0+1 by rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (coefficient_hasDerivAt_local hdy n hy).differentiableAt.differentiableWithinAt,
      by simp,?_⟩
    apply (contDiffOn_zero.mpr (coefficient_continuousOn_local hdy2 n)).congr
    intro y hy
    exact coefficient_deriv_local hdy n hy
  rw [show (2 : ℕ∞ω)=1+1 by norm_num,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun y hy => (coefficient_hasDerivAt_local (hu.of_le (by norm_num)) n hy).
      differentiableAt.differentiableWithinAt,by simp,?_⟩
  apply hdc.congr
  intro y hy
  exact coefficient_deriv_local (hu.of_le (by norm_num)) n hy

private theorem partialX_periodic_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : DifferentiableOn ℝ u (cuspDomain Y))
    (hp : ∀ x y : ℝ, Y<y → u (x+1,y)=u(x,y))
    (x : ℝ) {y : ℝ} (hy : Y<y) : partialX u (x+1,y)=partialX u (x,y) := by
  have hs := (horizontal_hasDerivAt_local hu (x+1) hy).comp x ((hasDerivAt_id x).add_const 1)
  have heq : (fun t : ℝ => u (t+1,y))=fun t => u (t,y) := funext (fun t => hp t y hy)
  have hd : HasDerivAt (fun t => u (t,y)) (partialX u (x+1,y)) x := by
    simpa only [Function.comp_def,mul_one,heq] using hs
  exact hd.unique (horizontal_hasDerivAt_local hu x hy)

private theorem coefficient_partialX_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 1 u (cuspDomain Y))
    (hp : ∀ x y : ℝ, Y<y → u (x+1,y)=u(x,y))
    (n : ℤ) {y : ℝ} (hy : Y<y) :
    coefficient (partialX u) n y=(2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*coefficient u n y := by
  simp only [coefficient_eq_fourierCoeffOn]
  apply P3CuspHorizontalDerivativeParsevalSourceOnly.derivative_fourier_coefficient
  · intro x _
    exact horizontal_hasDerivAt_local (hu.differentiableOn (by norm_num)) x hy
  · simpa using hp 0 y hy
  · exact (continuous_slice_local (partialX_contDiffOn_local hu
      (by norm_num : (0 : ℕ∞ω)+1≤1)).continuousOn hy).intervalIntegrable 0 1

/-- The actual periodic cusp-local PDE implies the literal coefficient
ODE for ALL integers n. No data below Y or coefficient ODE is assumed. -/
theorem actual_coefficient_maass_ode_local {Y : ℝ} {u : ℝ × ℝ → ℂ}
    (hu : ContDiffOn ℝ 2 u (cuspDomain Y))
    (hp : ∀ x y : ℝ, Y<y → u (x+1,y)=u(x,y))
    (lambda : ℂ) (hPDE : ∀ p ∈ cuspDomain Y,
      -(p.2 : ℂ)^2*(partialX (partialX u) p+partialY (partialY u) p)=lambda*u p)
    (n : ℤ) {y : ℝ} (hy : Y<y) :
    -(y : ℂ)^2*(deriv (deriv (coefficient u n)) y-
      ((2*Real.pi*(n : ℝ) : ℝ) : ℂ)^2*coefficient u n y)=lambda*coefficient u n y := by
  have hxx : ContinuousOn (partialX (partialX u)) (cuspDomain Y) :=
    (partialX_contDiffOn_local (partialX_contDiffOn_local hu (by norm_num) :
      ContDiffOn ℝ 1 _ _) (by norm_num : (0 : ℕ∞ω)+1≤1)).continuousOn
  have hyy : ContinuousOn (partialY (partialY u)) (cuspDomain Y) :=
    (partialY_contDiffOn_local (partialY_contDiffOn_local hu (by norm_num) :
      ContDiffOn ℝ 1 _ _) (by norm_num : (0 : ℕ∞ω)+1≤1)).continuousOn
  have hiXX : Integrable (fun x : PeriodCell => phased n (partialX (partialX u)) (x,y)) volume :=
    ((continuous_slice_local (phased_continuousOn_local hxx n) hy).
    comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiYY : Integrable (fun x : PeriodCell => phased n (partialY (partialY u)) (x,y)) volume :=
    ((continuous_slice_local (phased_continuousOn_local hyy n) hy).
    comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : -(y : ℂ)^2*(coefficient (partialX (partialX u)) n y+
      coefficient (partialY (partialY u)) n y)=lambda*coefficient u n y := by
    unfold coefficient periodIntegral
    rw [← integral_add hiXX hiYY,← integral_const_mul,← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      have h := hPDE (x,y) hy
      dsimp [phased]
      linear_combination phase n x*h)
  have hX2 : coefficient (partialX (partialX u)) n y =
      -((2*Real.pi*(n : ℝ) : ℝ) : ℂ)^2*coefficient u n y := by
    rw [coefficient_partialX_local (partialX_contDiffOn_local hu (by norm_num))
      (fun x y hy => partialX_periodic_local (hu.differentiableOn (by norm_num)) hp x hy) n hy,
      coefficient_partialX_local (hu.of_le (by norm_num)) hp n hy]
    push_cast
    linear_combination (2*(Real.pi : ℂ)*(n : ℂ))^2*coefficient u n y*Complex.I_sq
  rw [hX2] at hsum
  rw [(coefficient_deriv_hasDerivAt_local hu n hy).deriv]
  convert hsum using 1 <;> ring

end
end ImbalancedChen.Part3.CuspLocalFourierCalculus20261026b
