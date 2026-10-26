import ImbalancedChen.Part3RealOrderIGrowthExclusion
import ImbalancedChen.Part3ActualComplexKIBasis
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual I/K independence at every nonnegative real order, including zero,
and classification of native modified-Bessel solutions on q>Q>=0.
The initial-value coefficients are explicit two-by-two determinants.
Abel differentiation and Mathlib's connected-open-set mean-value theorem
prove constancy and uniqueness; no spanning or ODE-uniqueness hypothesis
is supplied. L2 on a logarithmic right tail then selects the actual K.

For a cusp eigenfunction, deriving this native ODE from its Fourier
coefficient and transporting its L2 norm are separate caller obligations.
The spectral relation for this real-order leaf is lambda=1/4-nu^2.
Pure imaginary order lambda=1/4+tau^2 is not asserted here.
-/

namespace ImbalancedChen.Part3.RealBesselTailKSelection20261026a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexBesselAbelBasis ActualComplexKIBasis
open GeneralComplexISeriesSourceOnly GeneralIRealPositiveEndpoint20261025a
open ComplexOrderKBridgeSourceOnly ComplexOrderKRadialRegularitySourceOnly
open GeneralKRightEndpoint20261025a RealOrderIGrowthExclusion20261026a

theorem actualRealK_ne_zero (nu : ℝ) {q : ℝ} (hq : 0 < q) :
    complexOrderK (nu : ℂ) q ≠ 0 := by
  rw [complexOrderK_real]
  exact Complex.ofReal_ne_zero.mpr (actualRealOrderK_pos nu hq).ne'

/-- Actual I/K independence includes nu=0. A zero determinant would make
I/K constant; actual K is L2 and actual I is not, giving a contradiction. -/
theorem actualRealIK_weightedWronskian_ne_zero {nu a : ℝ}
    (hnu : 0 ≤ nu) (ha : 0 < a) :
    weightedWronskian (generalI (nu : ℂ)) (complexOrderK (nu : ℂ)) a ≠ 0 := by
  intro hzero
  let f : ℝ → ℂ := generalI (nu : ℂ)
  let g : ℝ → ℂ := complexOrderK (nu : ℂ)
  have hf : PositiveBesselSolution (nu : ℂ) f :=
    actualI_positiveBesselSolution (by simp only [Complex.ofReal_re]; linarith)
  have hg : PositiveBesselSolution (nu : ℂ) g := actualK_positiveBesselSolution _
  have hW (q : ℝ) (hq : 0 < q) : weightedWronskian f g q = 0 :=
    (weightedWronskian_eq hf hg hq ha).trans hzero
  have hratio (q : ℝ) (hq : 0 < q) :
      HasDerivAt (fun x : ℝ => f x / g x) 0 q := by
    have hgq : g q ≠ 0 := actualRealK_ne_zero nu hq
    have hw := hW q hq
    have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    have hdet : f q * deriv g q - deriv f q * g q = 0 :=
      (mul_eq_zero.mp hw).resolve_left hqC
    have hnum : deriv f q * g q - f q * deriv g q = 0 := by
      linear_combination -hdet
    simpa only [hnum, zero_div] using ((hf q hq).1.div (hg q hq).1 hgq)
  have hconst (q : ℝ) (hq : 0 < q) : f q / g q = f a / g a := by
    apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    · intro x hx
      exact (hratio x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hratio x hx).deriv
    · exact hq
    · exact ha
  have hrep (q : ℝ) (hq : 0 < q) : f q = (f a / g a) * g q :=
    (div_eq_iff (actualRealK_ne_zero nu hq)).mp (hconst q hq)
  have heq : realILogMode nu = fun r : ℝ => (f a / g a) * radialK (nu : ℂ) r := by
    funext r
    exact hrep (Real.exp r) (Real.exp_pos r)
  have hL2 : MemLp (realILogMode nu) 2 (volume.restrict (Ioi (0 : ℝ))) := by
    rw [heq]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (radialK_memLp_two_Ioi (nu : ℂ)).const_smul (f a / g a)
  exact realILogMode_not_memLp_two_Ioi hnu 0 hL2

/-- Native first and second derivatives, with the actual Bessel equation,
at one point. This is the ODE datum, not a solution representation. -/
def BesselJet (nu : ℂ) (f : ℝ → ℂ) (q : ℝ) : Prop :=
  HasDerivAt f (deriv f q) q ∧
  HasDerivAt (deriv f) (deriv (deriv f) q) q ∧
  (q : ℂ)^2 * deriv (deriv f) q + (q : ℂ) * deriv f q -
    ((q : ℂ)^2 + nu^2) * f q = 0

def TailBesselSolution (nu : ℂ) (Q : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ q : ℝ, Q < q → BesselJet nu f q

private theorem wronskian_deriv_zero_of_jets {nu : ℂ} {f g : ℝ → ℂ}
    {q : ℝ} (hq : 0 < q) (hf : BesselJet nu f q) (hg : BesselJet nu g q) :
    HasDerivAt (weightedWronskian f g) 0 q := by
  obtain ⟨hf1, hf2, hfODE⟩ := hf
  obtain ⟨hg1, hg2, hgODE⟩ := hg
  have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 q := by
    simpa only [Complex.ofReal_one] using (hasDerivAt_id q).ofReal_comp
  let D : ℂ := f q * deriv g q - deriv f q * g q +
    (q : ℂ) * (f q * deriv (deriv g) q - deriv (deriv f) q * g q)
  have hd : HasDerivAt (weightedWronskian f g) D q := by
    convert hid.mul ((hf1.mul hg2).sub (hf2.mul hg1)) using 1 <;>
      dsimp [weightedWronskian, D] <;> ring
  have hqD : (q : ℂ) * D = 0 := by
    dsimp [D]
    linear_combination (f q) * hgODE - (g q) * hfODE
  have hD : D = 0 := (mul_eq_zero.mp hqD).resolve_left
    (Complex.ofReal_ne_zero.mpr hq.ne')
  simpa only [hD] using hd

/-- The determinant is constant on the genuine cusp tail, without an
extension of its solution through the omitted compact interval. -/
theorem tail_weightedWronskian_eq {nu : ℂ} {Q a q : ℝ} (hQ : 0 ≤ Q)
    {f g : ℝ → ℂ} (hf : TailBesselSolution nu Q f)
    (hg : TailBesselSolution nu Q g) (ha : Q < a) (hq : Q < q) :
    weightedWronskian f g a = weightedWronskian f g q := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
  · intro x hx
    exact (wronskian_deriv_zero_of_jets (hQ.trans_lt hx) (hf x hx) (hg x hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (wronskian_deriv_zero_of_jets (hQ.trans_lt hx) (hf x hx) (hg x hx)).deriv
  · exact ha
  · exact hq

def realTailICoefficient (nu a : ℝ) (f : ℝ → ℂ) : ℂ :=
  weightedWronskian f (complexOrderK (nu : ℂ)) a /
    weightedWronskian (generalI (nu : ℂ)) (complexOrderK (nu : ℂ)) a

def realTailKCoefficient (nu a : ℝ) (f : ℝ → ℂ) : ℂ :=
  weightedWronskian (generalI (nu : ℂ)) f a /
    weightedWronskian (generalI (nu : ℂ)) (complexOrderK (nu : ℂ)) a

/-- Actual I and K span every genuine native tail solution, with explicit
initial-value coefficients. The determinant is proved nonzero above. -/
theorem real_tail_solution_eq_IK {nu Q a q : ℝ} (hnu : 0 ≤ nu) (hQ : 0 ≤ Q)
    {f : ℝ → ℂ} (hf : TailBesselSolution (nu : ℂ) Q f) (ha : Q < a) (hq : Q < q) :
    f q = realTailICoefficient nu a f * generalI (nu : ℂ) q +
      realTailKCoefficient nu a f * complexOrderK (nu : ℂ) q := by
  have hI : TailBesselSolution (nu : ℂ) Q (generalI (nu : ℂ)) := fun x hx =>
    actualI_positiveBesselSolution (by simp only [Complex.ofReal_re]; linarith)
      x (hQ.trans_lt hx)
  have hK : TailBesselSolution (nu : ℂ) Q (complexOrderK (nu : ℂ)) := fun x hx =>
    actualK_positiveBesselSolution _ x (hQ.trans_lt hx)
  have hIK := tail_weightedWronskian_eq hQ hI hK ha hq
  have hfK := tail_weightedWronskian_eq hQ hf hK ha hq
  have hIf := tail_weightedWronskian_eq hQ hI hf ha hq
  have hW := actualRealIK_weightedWronskian_ne_zero hnu (hQ.trans_lt ha)
  unfold realTailICoefficient realTailKCoefficient
  field_simp [hW]
  rw [hIK, hfK, hIf]
  unfold weightedWronskian
  ring

/-- Native initial-value uniqueness on the cusp tail, deduced from the
proved actual basis, rather than supplied as an assumption. -/
theorem real_tail_initial_value_unique {nu Q a : ℝ} (hnu : 0 ≤ nu) (hQ : 0 ≤ Q)
    {f g : ℝ → ℂ} (hf : TailBesselSolution (nu : ℂ) Q f)
    (hg : TailBesselSolution (nu : ℂ) Q g) (ha : Q < a)
    (hvalue : f a = g a) (hderiv : deriv f a = deriv g a) :
    EqOn f g (Ioi Q) := by
  intro q hq
  rw [real_tail_solution_eq_IK hnu hQ hf ha hq,
    real_tail_solution_eq_IK hnu hQ hg ha hq]
  simp only [realTailICoefficient, realTailKCoefficient, weightedWronskian, hvalue, hderiv]

/-- A genuine ODE solution square integrable on one logarithmic right
tail is the actual single K solution throughout its entire ODE domain.
The geometric condition Q<=exp R ensures that the L2 tail is inside it. -/
theorem real_tail_L2_solution_eq_K {nu Q a R : ℝ} (hnu : 0 ≤ nu) (hQ : 0 ≤ Q)
    {f : ℝ → ℂ} (hf : TailBesselSolution (nu : ℂ) Q f) (ha : Q < a)
    (hQR : Q ≤ Real.exp R)
    (hL2 : MemLp (fun r : ℝ => f (Real.exp r)) 2 (volume.restrict (Ioi R))) :
    ∀ q : ℝ, Q < q → f q = realTailKCoefficient nu a f * complexOrderK (nu : ℂ) q := by
  have heq : (fun r : ℝ => f (Real.exp r)) =ᵐ[volume.restrict (Ioi R)]
      (fun r : ℝ => realTailICoefficient nu a f * realILogMode nu r +
        realTailKCoefficient nu a f * radialK (nu : ℂ) r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact real_tail_solution_eq_IK hnu hQ hf ha
      (hQR.trans_lt (Real.exp_lt_exp.mpr hr))
  have hcomb := (memLp_congr_ae heq).mp hL2
  have hA := real_IK_combination_L2_I_coefficient_zero hnu
    (realTailICoefficient nu a f) (realTailKCoefficient nu a f) R hcomb
  intro q hq
  simpa only [hA, zero_mul, zero_add] using real_tail_solution_eq_IK hnu hQ hf ha hq

end
end ImbalancedChen.Part3.RealBesselTailKSelection20261026a
