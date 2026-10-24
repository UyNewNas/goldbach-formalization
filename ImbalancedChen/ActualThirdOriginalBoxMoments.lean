import ImbalancedChen.ActualThirdOriginalLocalCurvature
import ImbalancedChen.Part4ActualThirdOriginalClosedSplitAggregation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral


/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Actual normalized f=lower=(1-TMinus)/(2*exp gamma), not numerator L=s*f.
Global concavity on [2,infinity) follows from the true coupled first derivative
and source order. The initial log formula is not extended beyond4.
The clamped extension is NOT asserted concave across2.
-/

namespace ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

noncomputable section
open Set MeasureTheory

/-- The actual derivative numerator is nonnegative and antitone. Dividing by
positive increasing s preserves antitonicity; no second derivative at knots
or synthetic DDE assumption is required. -/
theorem lowerSlope_antitone : AntitoneOn lowerSlope (Ioi 2) := by
  intro x hx y hy hxy
  change 2 < x at hx
  change 2 < y at hy
  have hx0 : 0 < x := by linarith [hx]
  have hx1 : x-1 ∈ Ioi (1 : ℝ) := by change 1 < x-1; linarith [hx]
  have hy1 : y-1 ∈ Ioi (1 : ℝ) := by change 1 < y-1; linarith [hy]
  have horder : lower x ≤ upper (x-1) :=
    (lower_le_upper (le_of_lt hx)).trans
      (upper_antitone_gt_one hx1 (by change 1 < x; linarith [hx]) (by linarith))
  have hup : upper (y-1) ≤ upper (x-1) :=
    upper_antitone_gt_one hx1 hy1 (by linarith)
  have hlow : lower x ≤ lower y :=
    lower_monotone
      (show x ∈ Ici (2 : ℝ) from by change 2 ≤ x; exact hx.le)
      (show y ∈ Ici (2 : ℝ) from by change 2 ≤ y; exact hy.le) hxy
  exact div_le_div₀ (sub_nonneg.mpr horder) (sub_le_sub hup hlow) hx0 hxy

/-- Closed-endpoint continuity at2 is supplied by the actual source series.
Differentiability and derivative order are used only on the open interior. -/
theorem lower_concaveOn_Ici_two : ConcaveOn ℝ (Ici 2) lower := by
  have hcont : ContinuousOn lower (Ici 2) := continuousOn_thirdTailLowerFactor
  have hdiff : DifferentiableOn ℝ lower (interior (Ici 2)) := by
    intro s hs
    have hs2 : 2 < s := by simpa only [interior_Ici, mem_Ioi] using hs
    exact (hasDerivAt_lower hs2).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (deriv lower) (interior (Ici 2)) := by
    intro x hx y hy hxy
    have hx2 : 2 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hy2 : 2 < y := by simpa only [interior_Ici, mem_Ioi] using hy
    rw [(hasDerivAt_lower hx2).deriv, (hasDerivAt_lower hy2).deriv]
    exact lowerSlope_antitone hx2 hy2 hxy
  exact AntitoneOn.concaveOn_of_deriv (convex_Ici 2) hcont hdiff hanti

/-- Concavity of precisely the function queried by IndependentSieve.at.
This is restricted to[2,infinity), not the entire clamped real line. -/
theorem actual_lower_concaveOn_Ici_two :
    ConcaveOn ℝ (Ici 2) actualExtendedThirdLowerFactor := by
  apply lower_concaveOn_Ici_two.congr
  intro s hs
  exact lower_eq_actual hs

/-- Endpoint query lower bounds are sufficient for the old-argument chord.
The lower endpoint estimates need not themselves be ordered. -/
theorem actual_lower_query_chord {a b w flo fhi : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hlo : flo ≤ actualExtendedThirdLowerFactor a)
    (hhi : fhi ≤ actualExtendedThirdLowerFactor b) :
    flo+w*(fhi-flo) ≤ actualExtendedThirdLowerFactor ((1-w)*a+w*b) := by
  have hw : 0 ≤ 1-w := sub_nonneg.mpr hw1
  have hc := actual_lower_concaveOn_Ici_two.2 ha hb hw hw0
    (show (1-w)+w=1 by ring)
  simp only [smul_eq_mul] at hc
  calc
    flo+w*(fhi-flo) = (1-w)*flo+w*fhi := by ring
    _ ≤ (1-w)*actualExtendedThirdLowerFactor a+w*actualExtendedThirdLowerFactor b :=
      add_le_add (mul_le_mul_of_nonneg_left hlo hw) (mul_le_mul_of_nonneg_left hhi hw0)
    _ ≤ _ := hc

/-- The precise pointwise ratio form used when mean_upper has low<high,
low>=2, and the actual minorant argument lies between those endpoints. -/
theorem actual_lower_query_endpoint_chord {a b t flo fhi : ℝ}
    (ha : 2 ≤ a) (hab : a < b) (ht : t ∈ Icc a b)
    (hlo : flo ≤ actualExtendedThirdLowerFactor a)
    (hhi : fhi ≤ actualExtendedThirdLowerFactor b) :
    flo+(t-a)/(b-a)*(fhi-flo) ≤ actualExtendedThirdLowerFactor t := by
  let w : ℝ := (t-a)/(b-a)
  have hd : 0 < b-a := sub_pos.mpr hab
  have hw0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hw1 : w ≤ 1 := (div_le_one hd).2 (by linarith [ht.2])
  have harg : (1-w)*a+w*b=t := by
    dsimp [w]
    field_simp [hd.ne']
    ring
  have hc := actual_lower_query_chord ha (ha.trans hab.le) hw0 hw1 hlo hhi
  rw [harg] at hc
  exact hc

/-- Actual Jensen upper bound for a normalized positive weight measure.
The geometric weight normalization, argument support and integrability are
explicit: this does not silently certify a leaf's reciprocal density moments. -/
theorem actual_lower_Jensen_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (q : α → ℝ)
    (hq : ∀ᵐ x ∂μ, 2 ≤ q x)
    (hi : Integrable q μ)
    (hfi : Integrable (actualExtendedThirdLowerFactor ∘ q) μ) :
    (∫ x, actualExtendedThirdLowerFactor (q x) ∂μ) ≤
      actualExtendedThirdLowerFactor (∫ x, q x ∂μ) := by
  exact actual_lower_concaveOn_Ici_two.le_map_integral
    continuous_actualExtendedThirdLowerFactor.continuousOn isClosed_Ici hq hi hfi

end
end ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Concrete ordinary closed box for original mean_upper. No symmetric-half rule
is applied here. The normalized density is exactly1/(x*y*z^2) divided by its
mass; the original factor4 cancels in probability normalization.
-/
namespace ImbalancedChen.OriginalThirdBoxMomentsSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdCompactPartitionSourceOnly

abbrev BoxPoint := Fin 3 → ℝ

def boxWeight (t : BoxPoint) : ℝ := (1/t 0)*(1/t 1)*(1/(t 2)^2)
def zMass (a b : ℝ) : ℝ := (b-a)/(a*b)
def boxMass (a b : BoxPoint) : ℝ :=
  Real.log (b 0/a 0)*Real.log (b 1/a 1)*zMass (a 2) (b 2)
def boxEX (a b : BoxPoint) : ℝ := (b 0-a 0)/Real.log (b 0/a 0)
def boxEY (a b : BoxPoint) : ℝ := (b 1-a 1)/Real.log (b 1/a 1)
def boxEZInv (a b : BoxPoint) : ℝ := (a 2+b 2)/(2*a 2*b 2)
def boxProbability (a b : BoxPoint) : Measure BoxPoint :=
  (volume.restrict (Icc a b)).withDensity
    (fun t => ENNReal.ofReal (boxWeight t/boxMass a b))
def affineArgument (A B C E : ℝ) (t : BoxPoint) : ℝ :=
  (A+B*t 0+C*t 1)/t 2+E

private theorem log_ratio_pos {a b : ℝ} (ha : 0<a) (hab : a<b) :
    0<Real.log (b/a) := Real.log_pos ((one_lt_div ha).2 hab)

private theorem integral_reciprocal_Icc {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, 1/x) = Real.log (b/a) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact integral_one_div_of_pos ha (ha.trans_le hab)

private theorem integral_reciprocal_sq_Icc {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, 1/x^2) = zMass a b := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have heq : (fun x : ℝ => 1/x^2) = (fun x => x^(-2:ℤ)) := by
    funext x
    simp [zpow_neg, one_div]
  rw [heq, integral_zpow (Or.inr ⟨by norm_num,
    notMem_uIcc_of_lt ha (ha.trans_le hab)⟩)]
  unfold zMass
  norm_num [zpow_neg, zpow_natCast]
  field_simp [ha.ne', (ha.trans_le hab).ne']
  ring

private theorem integral_reciprocal_cu_Icc {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, (1/x)/x^2) = (1/a^2-1/b^2)/2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have heq : (fun x : ℝ => (1/x)/x^2) = (fun x => x^(-3:ℤ)) := by
    funext x
    simp [zpow_neg, div_eq_mul_inv, pow_succ, mul_inv_rev]
  rw [heq, integral_zpow (Or.inr ⟨by norm_num,
    notMem_uIcc_of_lt ha (ha.trans_le hab)⟩)]
  norm_num [zpow_neg, zpow_natCast, one_div]
  ring

private theorem integral_self_div_Icc {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, x/x) = b-a := by
  have heq : (∫ x in Icc a b, x/x) = ∫ x in Icc a b, (1:ℝ) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact div_self (ha.trans_le hx.1).ne'
  rw [heq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simp

/-- Fubini over precisely the closed Cartesian box, not a clipped domain. -/
theorem integral_box_tensor (a b : BoxPoint) (fx fy fz : ℝ → ℝ) :
    (∫ t in Icc a b, fx (t 0)*fy (t 1)*fz (t 2)) =
      (∫ x in Icc (a 0) (b 0), fx x)*
      (∫ y in Icc (a 1) (b 1), fy y)*
      (∫ z in Icc (a 2) (b 2), fz z) := by
  have hmeasure : (volume : Measure BoxPoint).restrict (Icc a b) =
      Measure.pi (fun i : Fin 3 => (volume : Measure ℝ).restrict (Icc (a i) (b i))) := by
    rw [← pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  rw [hmeasure]
  have h := integral_fintype_prod_eq_prod
    (E := fun _ : Fin 3 => ℝ)
    (μ := fun i : Fin 3 => (volume : Measure ℝ).restrict (Icc (a i) (b i)))
    (fun i : Fin 3 => (![fx,fy,fz] i))
  simpa only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using h

theorem integral_boxWeight (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) :
    (∫ t in Icc a b, boxWeight t) = boxMass a b := by
  unfold boxWeight boxMass
  rw [integral_box_tensor a b (fun x : ℝ => 1/x) (fun y : ℝ => 1/y)
      (fun z : ℝ => 1/z^2), integral_reciprocal_Icc (ha 0) (hab 0),
    integral_reciprocal_Icc (ha 1) (hab 1), integral_reciprocal_sq_Icc (ha 2) (hab 2)]

theorem boxMass_pos (a b : BoxPoint) (ha : ∀i,0<a i) (hab : ∀i,a i<b i) :
    0<boxMass a b := by
  exact mul_pos (mul_pos (log_ratio_pos (ha 0) (hab 0))
    (log_ratio_pos (ha 1) (hab 1)))
    (div_pos (sub_pos.mpr (hab 2)) (mul_pos (ha 2) ((ha 2).trans (hab 2))))

private theorem boxWeight_nonneg (a b : BoxPoint) (ha : ∀i,0<a i)
    {t : BoxPoint} (ht : t ∈ Icc a b) : 0≤boxWeight t := by
  have hx := (ha 0).trans_le (ht.1 0)
  have hy := (ha 1).trans_le (ht.1 1)
  have hz := (ha 2).trans_le (ht.1 2)
  unfold boxWeight
  positivity

private theorem continuousOn_boxWeight (a b : BoxPoint) (ha : ∀i,0<a i) :
    ContinuousOn boxWeight (Icc a b) := by
  have hcoord (i : Fin 3) : ContinuousOn (fun t : BoxPoint => t i) (Icc a b) :=
    (continuous_apply i).continuousOn
  have hn (i : Fin 3) (t : BoxPoint) (ht : t∈Icc a b) : t i≠0 :=
    ((ha i).trans_le (ht.1 i)).ne'
  exact ((continuousOn_const.div (hcoord 0) (hn 0)).mul
    (continuousOn_const.div (hcoord 1) (hn 1))).mul
    (continuousOn_const.div ((hcoord 2).pow 2) (fun t ht => pow_ne_zero 2 (hn 2 t ht)))

private theorem measurable_boxWeight : Measurable boxWeight := by
  exact ((measurable_const.div (measurable_pi_apply 0)).mul
    (measurable_const.div (measurable_pi_apply 1))).mul
    (measurable_const.div ((measurable_pi_apply 2).pow_const 2))

/-- The original reciprocal density really normalizes to probability. -/
theorem boxProbability_isProbability (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) : IsProbabilityMeasure (boxProbability a b) := by
  have hm := boxMass_pos a b ha hab
  have hint : IntegrableOn (fun t : BoxPoint => boxWeight t / boxMass a b)
      (Icc a b) (volume : Measure BoxPoint) :=
    ((continuousOn_boxWeight a b ha).integrableOn_compact
      (μ := (volume : Measure BoxPoint)) isCompact_Icc).div_const (boxMass a b)
  have hn : ∀ᵐ t ∂volume.restrict (Icc a b), 0≤boxWeight t/boxMass a b := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_nonneg (boxWeight_nonneg a b ha ht) hm.le
  constructor
  rw [boxProbability, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint hn, integral_div,
    integral_boxWeight a b ha (fun i => (hab i).le), div_self hm.ne']
  simp

/-- Concrete Radon-Nikodym formula for this box, including the normalizer. -/
theorem integral_boxProbability (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) (g : BoxPoint → ℝ) :
    (∫ t, g t ∂boxProbability a b) =
      (∫ t in Icc a b, boxWeight t*g t)/boxMass a b := by
  rw [boxProbability, integral_withDensity_eq_integral_toReal_smul
    ((measurable_boxWeight.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hm := boxMass_pos a b ha hab
  calc
    _ = ∫ t in Icc a b, (boxWeight t*g t)/boxMass a b := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [ENNReal.toReal_ofReal (div_nonneg (boxWeight_nonneg a b ha ht) hm.le), smul_eq_mul]
      ring
    _ = _ := integral_div _ _

/-- Separable moment formula under the actual box probability. -/
theorem boxProbability_tensor (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) (fx fy fz : ℝ → ℝ) :
    (∫ t, fx (t 0)*fy (t 1)*fz (t 2) ∂boxProbability a b) =
      ((∫ x in Icc (a 0) (b 0), fx x/x)*
       (∫ y in Icc (a 1) (b 1), fy y/y)*
       (∫ z in Icc (a 2) (b 2), fz z/z^2))/boxMass a b := by
  rw [integral_boxProbability a b ha hab]
  have heq : (fun t : BoxPoint => boxWeight t*(fx (t 0)*fy (t 1)*fz (t 2))) =
      (fun t => (fx (t 0)/t 0)*(fy (t 1)/t 1)*(fz (t 2)/(t 2)^2)) := by
    funext t
    simp only [boxWeight, div_eq_mul_inv]
    ring
  rw [heq, integral_box_tensor a b (fun x : ℝ => fx x/x)
    (fun y : ℝ => fy y/y) (fun z : ℝ => fz z/z^2)]

/-- The five moments used to expand both original affine mean arguments. -/
theorem boxProbability_moments (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) :
    (∫ t, t 0 ∂boxProbability a b)=boxEX a b ∧
    (∫ t, t 1 ∂boxProbability a b)=boxEY a b ∧
    (∫ t, 1/t 2 ∂boxProbability a b)=boxEZInv a b ∧
    (∫ t, t 0/t 2 ∂boxProbability a b)=boxEX a b*boxEZInv a b ∧
    (∫ t, t 1/t 2 ∂boxProbability a b)=boxEY a b*boxEZInv a b := by
  have h0 := boxProbability_tensor a b ha hab (fun x=>x) (fun _=>1) (fun _=>1)
  have h1 := boxProbability_tensor a b ha hab (fun _=>1) (fun y=>y) (fun _=>1)
  have hz := boxProbability_tensor a b ha hab (fun _=>1) (fun _=>1) (fun z=>1/z)
  have h0z := boxProbability_tensor a b ha hab (fun x=>x) (fun _=>1) (fun z=>1/z)
  have h1z := boxProbability_tensor a b ha hab (fun _=>1) (fun y=>y) (fun z=>1/z)
  simp only [mul_one, one_mul, mul_one_div] at h0 h1 hz h0z h1z
  rw [integral_self_div_Icc (ha 0) (hab 0).le,
    integral_reciprocal_Icc (ha 1) (hab 1).le,
    integral_reciprocal_sq_Icc (ha 2) (hab 2).le] at h0
  rw [integral_reciprocal_Icc (ha 0) (hab 0).le,
    integral_self_div_Icc (ha 1) (hab 1).le,
    integral_reciprocal_sq_Icc (ha 2) (hab 2).le] at h1
  rw [integral_reciprocal_Icc (ha 0) (hab 0).le,
    integral_reciprocal_Icc (ha 1) (hab 1).le,
    integral_reciprocal_cu_Icc (ha 2) (hab 2).le] at hz
  rw [integral_self_div_Icc (ha 0) (hab 0).le,
    integral_reciprocal_Icc (ha 1) (hab 1).le,
    integral_reciprocal_cu_Icc (ha 2) (hab 2).le] at h0z
  rw [integral_reciprocal_Icc (ha 0) (hab 0).le,
    integral_self_div_Icc (ha 1) (hab 1).le,
    integral_reciprocal_cu_Icc (ha 2) (hab 2).le] at h1z
  have hlx := (log_ratio_pos (ha 0) (hab 0)).ne'
  have hly := (log_ratio_pos (ha 1) (hab 1)).ne'
  have haz := (ha 2).ne'
  have hbz := ((ha 2).trans (hab 2)).ne'
  have hdz := (sub_pos.mpr (hab 2)).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]; unfold boxMass boxEX zMass
    field_simp [hlx,hly,haz,hbz,hdz]
  · rw [h1]; unfold boxMass boxEY zMass
    field_simp [hlx,hly,haz,hbz,hdz]
  · rw [hz]; unfold boxMass boxEZInv zMass
    field_simp [hlx,hly,haz,hbz,hdz]
    ring
  · rw [h0z]; unfold boxMass boxEX boxEZInv zMass
    field_simp [hlx,hly,haz,hbz,hdz]
    ring
  · rw [h1z]; unfold boxMass boxEY boxEZInv zMass
    field_simp [hlx,hly,haz,hbz,hdz]
    ring

/-- Every continuous box observable is genuinely integrable for this density. -/
theorem integrable_boxProbability_of_continuousOn (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) {g : BoxPoint → ℝ}
    (hg : ContinuousOn g (Icc a b)) : Integrable g (boxProbability a b) := by
  unfold boxProbability
  apply (integrable_withDensity_iff_integrable_smul'
    ((measurable_boxWeight.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
  have hint : IntegrableOn (fun t : BoxPoint => (boxWeight t/boxMass a b)*g t)
      (Icc a b) volume :=
    (((continuousOn_boxWeight a b ha).div_const (boxMass a b)).mul hg).integrableOn_compact
      isCompact_Icc
  apply hint.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [ENNReal.toReal_ofReal (div_nonneg (boxWeight_nonneg a b ha ht)
    (boxMass_pos a b ha hab).le), smul_eq_mul]

theorem boxProbability_ae_mem (a b : BoxPoint) :
    ∀ᵐ t ∂boxProbability a b, t∈Icc a b := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Icc)

private theorem continuousOn_affineArgument (a b : BoxPoint)
    (ha : ∀i,0<a i) (A B C E : ℝ) :
    ContinuousOn (affineArgument A B C E) (Icc a b) := by
  have h0 : ContinuousOn (fun t : BoxPoint => t 0) (Icc a b) :=
    (continuous_apply 0).continuousOn
  have h1 : ContinuousOn (fun t : BoxPoint => t 1) (Icc a b) :=
    (continuous_apply 1).continuousOn
  have h2 : ContinuousOn (fun t : BoxPoint => t 2) (Icc a b) :=
    (continuous_apply 2).continuousOn
  exact (((continuousOn_const.add (h0.const_mul B)).add (h1.const_mul C)).div h2
    (fun t ht => ((ha 2).trans_le (ht.1 2)).ne')).add continuousOn_const

/-- Exact expectation of both generator affine arguments, including mixed
x/z and y/z moments; independence is proved by the tensor integral above. -/
theorem boxProbability_affine_mean (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) (A B C E : ℝ) :
    (∫ t, affineArgument A B C E t ∂boxProbability a b) =
      (A+B*boxEX a b+C*boxEY a b)*boxEZInv a b+E := by
  let : IsProbabilityMeasure (boxProbability a b) :=
    boxProbability_isProbability a b ha hab
  have h2 : ContinuousOn (fun t : BoxPoint => t 2) (Icc a b) :=
    (continuous_apply 2).continuousOn
  have hz : ∀ t∈Icc a b, t 2≠0 := fun t ht => ((ha 2).trans_le (ht.1 2)).ne'
  have hi : Integrable (fun t : BoxPoint => 1/t 2) (boxProbability a b) :=
    integrable_boxProbability_of_continuousOn a b ha hab (continuousOn_const.div h2 hz)
  have hx : Integrable (fun t : BoxPoint => t 0/t 2) (boxProbability a b) :=
    integrable_boxProbability_of_continuousOn a b ha hab
      ((show Continuous (fun t : BoxPoint => t 0) from continuous_apply 0).continuousOn.div h2 hz)
  have hy : Integrable (fun t : BoxPoint => t 1/t 2) (boxProbability a b) :=
    integrable_boxProbability_of_continuousOn a b ha hab
      ((show Continuous (fun t : BoxPoint => t 1) from continuous_apply 1).continuousOn.div h2 hz)
  have heq : affineArgument A B C E =
      (fun t : BoxPoint => A*(1/t 2)+B*(t 0/t 2)+C*(t 1/t 2)+E) := by
    funext t
    unfold affineArgument
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  change (∫ t : BoxPoint,
    A*(1/t 2)+B*(t 0/t 2)+C*(t 1/t 2)+E ∂boxProbability a b) = _
  rw [integral_add
    (f := fun t : BoxPoint => A*(1/t 2)+B*(t 0/t 2)+C*(t 1/t 2))
    (g := fun _ : BoxPoint => E)
    (((hi.const_mul A).add (hx.const_mul B)).add (hy.const_mul C))
    (integrable_const E),
    integral_add
      (f := fun t : BoxPoint => A*(1/t 2)+B*(t 0/t 2))
      (g := fun t : BoxPoint => C*(t 1/t 2))
      ((hi.const_mul A).add (hx.const_mul B)) (hy.const_mul C),
    integral_add
      (f := fun t : BoxPoint => A*(1/t 2))
      (g := fun t : BoxPoint => B*(t 0/t 2))
      (hi.const_mul A) (hx.const_mul B)]
  simp only [integral_const_mul, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  have hm := boxProbability_moments a b ha hab
  rw [hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2]
  ring

/-- Ordinary full-cell geometry makes the closed rectangle itself a genuine
subset of compactRegion. No symmetric-half shortcut occurs in this theorem. -/
theorem ordinary_full_box_subset_compact (a b : BoxPoint)
    (ha : ∀i,0<a i) (hcut : (1:ℝ)/100≤a 2)
    (hyx : b 1≤a 0) (hzy : b 2≤a 1) (hrho : b 0≤thirdPrefixRho)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta) : Icc a b ⊆ compactRegion := by
  intro t ht
  have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
  have hzy' : t 2≤t 1 := (ht.2 2).trans (hzy.trans (ht.1 1))
  have hyx' : t 1≤t 0 := (ht.2 1).trans (hyx.trans (ht.1 0))
  have hx : t 0≤thirdPrefixRho := (ht.2 0).trans hrho
  have hc : t 0+t 1+3*t 2≤thirdPrefixTheta := by
    linarith [ht.2 0, ht.2 1, ht.2 2]
  exact ⟨⟨⟨hz, hzy'.trans (hyx'.trans hx), hzy', hyx', hx⟩,
    by
      change t 0+t 1+3*t 2≤thirdPrefixTheta-2*0
      simpa only [mul_zero, sub_zero] using hc⟩, hcut.trans (ht.1 2)⟩

/-- Concrete Jensen endpoint for the original full-box new argument.
The only range premise is the generator's full raw-domain corner inequality;
all probability, support, continuity, integrability and mean facts are supplied. -/
theorem ordinary_full_box_new_Jensen (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta) :
    (∫ t, actualExtendedThirdLowerFactor
      (affineArgument thirdPrefixTheta (-1) (-1) (-1) t) ∂boxProbability a b) ≤
    actualExtendedThirdLowerFactor
      ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1) := by
  let : IsProbabilityMeasure (boxProbability a b) :=
    boxProbability_isProbability a b ha hab
  have hc := continuousOn_affineArgument a b ha thirdPrefixTheta (-1) (-1) (-1)
  have hq : ∀ᵐ t ∂boxProbability a b,
      2≤affineArgument thirdPrefixTheta (-1) (-1) (-1) t := by
    filter_upwards [boxProbability_ae_mem a b] with t ht
    have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
    have hcube : t 0+t 1+3*t 2≤thirdPrefixTheta := by
      linarith [ht.2 0, ht.2 1, ht.2 2]
    have hd : 3≤(thirdPrefixTheta-t 0-t 1)/t 2 :=
      (le_div_iff₀ hz).2 (by linarith)
    simpa only [affineArgument, neg_one_mul, ← sub_eq_add_neg] using
      (show 2≤(thirdPrefixTheta-t 0-t 1)/t 2-1 by linarith)
  have hi := integrable_boxProbability_of_continuousOn a b ha hab hc
  have hfi := integrable_boxProbability_of_continuousOn a b ha hab
    (continuous_actualExtendedThirdLowerFactor.comp_continuousOn hc)
  have hJ := actual_lower_Jensen_probability (boxProbability a b)
    (affineArgument thirdPrefixTheta (-1) (-1) (-1)) hq hi hfi
  rw [boxProbability_affine_mean a b ha hab] at hJ
  simpa only [neg_one_mul, ← sub_eq_add_neg] using hJ

/-- The literal factor4 in the original box mass is retained. -/
theorem original_full_box_mass (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) :
    (∫ t in Icc a b, 4/(t 0*t 1*(t 2)^2)) =
      Real.log (b 0/a 0)*Real.log (b 1/a 1)*
        (4*(b 2-a 2)/(a 2*b 2)) := by
  have heq : (fun t : BoxPoint => 4/(t 0*t 1*(t 2)^2)) =
      (fun t => 4*boxWeight t) := by
    funext t
    simp only [boxWeight, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, integral_const_mul, integral_boxWeight a b ha (fun i => (hab i).le)]
  unfold boxMass zMass
  ring

end
end ImbalancedChen.OriginalThirdBoxMomentsSourceOnly