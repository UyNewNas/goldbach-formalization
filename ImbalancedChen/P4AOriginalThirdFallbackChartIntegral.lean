import ImbalancedChen.P4AOriginalThirdFallbackSlope
import ImbalancedChen.ActualExtendedThirdLowerFactorRegularity
import ImbalancedChen.LogPrimeBoxIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-! The two original chart integrals use the actual lower factor, the
physical tent caps, the complete Jacobian, and the original factor four.
The 4096 open cell interiors have disjoint physical images. -/
namespace ImbalancedChen.P4AOriginalThirdFallbackChartIntegral
noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
open P4AOriginalThirdFallbackArchive
open P4AOriginalThirdFallbackSlope

abbrev Point := Fin 3 → ℝ
def lo (c : Cell) : Point := ![(ua c : ℝ),(va c : ℝ),(wa c : ℝ)]
def hi (c : Cell) : Point := ![(ub c : ℝ),(vb c : ℝ),(wb c : ℝ)]
def box (c : Cell) : Set Point := univ.pi (fun i => Ioo (lo c i) (hi c i))
def chart (b : Bool) (t : Point) : Point :=
  ![X (t 0),Y b (t 0) (t 1) (t 2),Z b (t 0) (t 1) (t 2)]
def kernel (p : Point) : ℝ :=
  physicalIntegrand (p 0) (p 1) (p 2) (VariableEnvelope.v (p 0)) (VariableEnvelope.v (p 1+p 2))
def pullback (b : Bool) (t : Point) : ℝ := jac b (t 0) (t 1) * kernel (chart b t)
def coefficient (c : Cell) : ℝ := 24*|(branch c.1 : ℝ)|*(h : ℝ)^3*(slope c : ℝ)/(den c : ℝ)
def estimator (c : Cell) (t : Point) : ℝ := coefficient c*((t 0)^2*(1-t 1)*1)
def chartSum : ℝ := ∑ c : Cell, ∫ t in box c, pullback c.1 t

theorem box_measurable (c : Cell) : MeasurableSet (box c) := MeasurableSet.pi countable_univ (fun _ _ => measurableSet_Ioo)
theorem box_closed (c : Cell) {t : Point} (ht : t ∈ box c) : t ∈ Icc (lo c) (hi c) :=
  ⟨fun i => (ht i (mem_univ _)).1.le,fun i => (ht i (mem_univ _)).2.le⟩

theorem old_cap {u : ℝ} (hu : 0 ≤ u) : VariableEnvelope.v (X u) = O u := by
  have hm : VariableEnvelope.mu ≤ X u := by
    norm_num [VariableEnvelope.mu,X,mu,h] <;> linarith
  rw [VariableEnvelope.v_eq_C hm]
  norm_num [VariableEnvelope.C,X,mu,h,O,peak] <;> ring

theorem new_cap (b : Bool) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    VariableEnvelope.v (S b u v) = A u v := by
  have hn := mul_nonneg hu hv
  cases b
  · have hm : S false u v ≤ VariableEnvelope.mu := by
      norm_num [S,mu,h,branch,VariableEnvelope.mu] <;> nlinarith
    rw [VariableEnvelope.v_eq_A hm]
    norm_num [S,mu,h,peak,branch,A,VariableEnvelope.A] <;> ring
  · have hm : VariableEnvelope.mu ≤ S true u v := by
      norm_num [S,mu,h,branch,VariableEnvelope.mu] <;> nlinarith
    rw [VariableEnvelope.v_eq_C hm]
    norm_num [S,mu,h,peak,branch,A,VariableEnvelope.C] <;> ring

private theorem mono_w : MonotoneOn (fun w : ℝ => (1-w/2)*w^3) (Icc 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) (f' := fun w => w^2*(3-2*w))
  · fun_prop
  · intro w hw
    have hd := ((hasDerivAt_const w (1:ℝ)).sub ((hasDerivAt_id w).div_const 2)).mul (hasDerivAt_pow 3 w)
    exact (hd.congr_deriv (by dsimp; ring)).hasDerivWithinAt
  · intro w hw
    have hI : w ∈ Icc (0:ℝ) 1 := interior_subset hw
    exact mul_nonneg (sq_nonneg _) (by linarith [hI.2])

theorem pointwise (c : Cell) {t : Point} (ht : t ∈ Icc (lo c) (hi c)) :
    estimator c t ≤ pullback c.1 t := by
  let u := t 0
  let v := t 1
  let w := t 2
  have hu : u ∈ Icc (ua c : ℝ) (ub c : ℝ) := ⟨ht.1 0,ht.2 0⟩
  have hv : v ∈ Icc (va c : ℝ) (vb c : ℝ) := ⟨ht.1 1,ht.2 1⟩
  have hw : w ∈ Icc (wa c : ℝ) (wb c : ℝ) := ⟨ht.1 2,ht.2 2⟩
  obtain ⟨hu',hv',hw'⟩ := unit_bounds c hu hv hw
  obtain ⟨hSup,ho,hod,hn⟩ := box_geometry c hu hv hw
  have hder := certified_derivative (c := c) ho hod hn
  obtain ⟨_,_,_,_,_,_,_,hden,_,hslope,_⟩ := original_rows c
  have hS := positive_s (b := c.1) hu' hv'
  have hX : 0 < X u := by dsimp [X]; norm_num [mu,h] <;> linarith [hu'.1]
  have hW : 0 < w := by linarith [hw'.1]
  have hW1 : 0 < 1-w/2 := by linarith [hw'.2]
  have hZ : 0 < Z c.1 u v w := by unfold Z; positivity
  have hyEq : Y c.1 u v w = S c.1 u v*(1-w/2) := by unfold Y Z; ring
  have hY : 0 < Y c.1 u v w := hyEq.symm ▸ mul_pos hS hW1
  have hwU : (wb c : ℝ) ∈ Icc (5/9 : ℝ) 1 :=
    (unit_bounds c hu hv ⟨hw.1.trans hw.2,le_rfl⟩).2.2
  have hXU : X u ≤ (xQ (ub c) : ℝ) := by
    simp [X,xQ,h] <;> linarith [hu.2]
  have hfrac := mono_w ⟨hW.le,hw'.2⟩ ⟨by linarith [hwU.1],hwU.2⟩ hw.2
  have hpart : 0 < X u*(S c.1 u v)^3*((1-w/2)*w^3) := by positivity
  have hupper : X u*(S c.1 u v)^3*((1-w/2)*w^3) ≤ (den c : ℝ) := by
    have hle := mul_le_mul hXU (pow_le_pow_left₀ hS.le hSup 3) (pow_nonneg hS.le 3) (hX.le.trans hXU)
    have hle' := mul_le_mul hle hfrac (mul_nonneg hW1.le (pow_nonneg hW.le 3)) ((mul_nonneg hX.le (pow_nonneg hS.le 3)).trans hle)
    simpa [den,mul_assoc] using hle'
  have hsl : (0:ℝ) ≤ (slope c : ℝ) := by exact_mod_cast hslope.le
  let num := 24*|(branch c.1 : ℝ)|*(h : ℝ)^3*(slope c : ℝ)*u^2*(1-v)
  have hh : 0 ≤ (h : ℝ) := by norm_num [h]
  have hnum : 0 ≤ num := by dsimp [num]; exact mul_nonneg (by positivity) (sub_nonneg.mpr hv'.2)
  have hJac : 0 ≤ jac c.1 u v := by dsimp [jac]; positivity
  have hCaps (L : ℝ) : (L-X u-Y c.1 u v w-Z c.1 u v w)/Z c.1 u v w = argument c.1 L u v w := by
    unfold argument Y
    ring
  have hsum : Y c.1 u v w + Z c.1 u v w = S c.1 u v := by unfold Y; ring
  change estimator c t ≤ jac c.1 u v *
    physicalIntegrand (X u) (Y c.1 u v w) (Z c.1 u v w) (VariableEnvelope.v (X u))
      (VariableEnvelope.v (Y c.1 u v w + Z c.1 u v w))
  rw [hsum,old_cap hu'.1,new_cap c.1 hu'.1 hv'.1,physicalIntegrand,hCaps,hCaps]
  calc
    estimator c t = num/(den c : ℝ) := by dsimp [estimator,coefficient,num,u,v]; ring
    _ ≤ num/(X u*(S c.1 u v)^3*((1-w/2)*w^3)) := div_le_div_of_nonneg_left hnum hpart hupper
    _ = jac c.1 u v * (4*((slope c : ℝ)*(argument c.1 (A u v) u v w - argument c.1 (O u) u v w))/
          (X u*Y c.1 u v w*(Z c.1 u v w)^2)) := by
      rw [hyEq]
      dsimp only [num,jac,argument,Z,A,O]
      field_simp [hX.ne',hS.ne',hW.ne',hW1.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hder (by norm_num : (0:ℝ) ≤ 4)) (by positivity)) hJac

private theorem bounds_order (c : Cell) : ∀ i, lo c i ≤ hi c i := by
  intro i
  fin_cases i <;> norm_num [lo,hi,ua,ub,va,vb,wa,wb] <;> linarith

theorem estimator_mass (c : Cell) : (∫ t in box c, estimator c t) = (rationalContribution c : ℝ) := by
  let f : Fin 3 → ℝ → ℝ := ![fun x => x^2,fun x => 1-x,fun _ => 1]
  have hprod : (fun t : Point => (t 0)^2*(1-t 1)*1) = fun t => ∏ i, f i (t i) := by
    funext t
    simp [Fin.prod_univ_three,f]
  unfold estimator
  rw [integral_const_mul,hprod]
  unfold box
  rw [volume_pi,Measure.restrict_pi_pi,integral_fintype_prod_eq_prod,Fin.prod_univ_three]
  have ha := bounds_order c
  have h0 : (∫ x in Ioo (lo c 0) (hi c 0), f 0 x) = ((hi c 0)^3-(lo c 0)^3)/3 := by
    rw [integral_Ioo_eq_integral_Ioc,← intervalIntegral.integral_of_le (ha 0)]
    change (∫ x in lo c 0..hi c 0, x^2) = _
    rw [integral_pow]
    norm_num
  have h1 : (∫ x in Ioo (lo c 1) (hi c 1), f 1 x) =
      (hi c 1-lo c 1)-((hi c 1)^2-(lo c 1)^2)/2 := by
    rw [integral_Ioo_eq_integral_Ioc,← intervalIntegral.integral_of_le (ha 1)]
    change (∫ x in lo c 1..hi c 1,1-x) = _
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _),integral_id]
    simp <;> ring
  have h2 : (∫ x in Ioo (lo c 2) (hi c 2), f 2 x) = hi c 2-lo c 2 := by
    rw [integral_Ioo_eq_integral_Ioc,← intervalIntegral.integral_of_le (ha 2)]
    change (∫ _ in lo c 2..hi c 2,(1:ℝ)) = _
    simp
  rw [h0,h1,h2]
  simp [lo,hi,rationalContribution,coefficient,mass] <;> ring

theorem continuousOn_pullback (c : Cell) : ContinuousOn (pullback c.1) (Icc (lo c) (hi c)) := by
  let D := Icc (lo c) (hi c)
  let x : Point → ℝ := fun t => X (t 0)
  let y : Point → ℝ := fun t => Y c.1 (t 0) (t 1) (t 2)
  let z : Point → ℝ := fun t => Z c.1 (t 0) (t 1) (t 2)
  have hx : Continuous x := by unfold x X; fun_prop
  have hy : Continuous y := by unfold y Y Z S; fun_prop
  have hz : Continuous z := by unfold z Z S; fun_prop
  have hcap : Continuous VariableEnvelope.v := by unfold VariableEnvelope.v VariableEnvelope.A VariableEnvelope.C; fun_prop
  have hn (t : Point) (ht : t ∈ D) : 0 < x t ∧ 0 < y t ∧ 0 < z t := by
    obtain ⟨hu,hv,hw⟩ := unit_bounds c (u := t 0) (v := t 1) (w := t 2)
      ⟨ht.1 0,ht.2 0⟩ ⟨ht.1 1,ht.2 1⟩ ⟨ht.1 2,ht.2 2⟩
    have hS := positive_s (b := c.1) hu hv
    have hW : 0 < t 2 := by linarith [hw.1]
    have hW' : 0 < 1-t 2/2 := by linarith [hw.2]
    refine ⟨?_,?_,?_⟩
    · dsimp [x,X]; norm_num [mu,h] <;> linarith [hu.1]
    · change 0 < S c.1 (t 0) (t 1)-S c.1 (t 0) (t 1)*t 2/2
      nlinarith only [mul_pos hS hW']
    · dsimp [z,Z]; positivity
  have hprof (L : Point → ℝ) (hL : Continuous L) : ContinuousOn
      (fun t => actualExtendedThirdLowerFactor ((L t-x t-y t-z t)/z t)) D :=
    continuous_actualExtendedThirdLowerFactor.comp_continuousOn
      ((((hL.sub hx).sub hy).sub hz).continuousOn.div hz.continuousOn (fun t ht => (hn t ht).2.2.ne'))
  have hj : Continuous (fun t : Point => jac c.1 (t 0) (t 1)) := by unfold jac S; fun_prop
  apply hj.continuousOn.mul
  apply (continuousOn_const.mul ((hprof _ (hcap.comp (hy.add hz))).sub (hprof _ (hcap.comp hx)))).div
    (((hx.mul hy).mul (hz.pow 2)).continuousOn)
  intro t ht
  obtain ⟨h0,h1,h2⟩ := hn t ht
  exact (mul_pos (mul_pos h0 h1) (pow_pos h2 2)).ne'

theorem row_le_integral (c : Cell) : (rationalContribution c : ℝ) ≤ ∫ t in box c, pullback c.1 t := by
  rw [← estimator_mass]
  have hest : Continuous (estimator c) := by unfold estimator; fun_prop
  apply setIntegral_mono_on (hest.integrableOn_Icc.mono_set (fun _ ht => box_closed c ht))
    (((continuousOn_pullback c).integrableOn_compact isCompact_Icc).mono_set (fun _ ht => box_closed c ht))
    (box_measurable c)
  exact fun t ht => pointwise c (box_closed c ht)

theorem original_sixth_slot_le_chartSum : currentUpperEighteenGains 5 ≤ chartSum :=
  original_slot_le_contributions.trans (Finset.sum_le_sum (fun c _ => row_le_integral c))

end
end ImbalancedChen.P4AOriginalThirdFallbackChartIntegral

