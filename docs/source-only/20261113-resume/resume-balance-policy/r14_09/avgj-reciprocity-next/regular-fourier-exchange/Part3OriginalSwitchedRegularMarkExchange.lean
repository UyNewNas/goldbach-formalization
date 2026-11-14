import ImbalancedChen.Part3OriginalSwitchedRegularFourierBudget

/-! The four-dimensional Fourier series commutes with every
principal-series slot and the full incoming-cusp continuous measure. -/
namespace ImbalancedChen.Part3.OriginalSwitchedRegularMarkExchange20261113
noncomputable section
open Finset Complex MeasureTheory
open scoped BigOperators Classical
open OriginalSwitchedRegularFourierBudget20261113 (scaled term tested uniform_majorant)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalSameInfinityScalarPrices20261113 (cubic_prices covariance_meas)
open OriginalSameInfinityTensorSpectrum20261113 (disc cont)
open ActualMarkedCubicPrice20261112 (linePrice linePrice_pos slotPrice slotPrice_nn)
open ActualUnitBandSpectralMass20261112 (exceptional height)
open ActualPositiveNativeDiagonal20261112 (nativeWeight)
open ActualFullCuspEigenbasis20261026b
open ActualPrescribedPositiveJ20261112 (positiveWeight regular_transform weightSchwartz)
open OriginalSwitchedCutoffModes20261113 (mode)
open OriginalSwitchedSeparatedTransforms20261113 (factor)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open private rectangle from ImbalancedChen.Part3OriginalSwitchedMaassExchange

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def principal (q m n : ℕ+) (Φ : ℝ→ℂ) :=
  ∑' i : actualCuspBasisIndex q.val (NeZero.pos q.val),
    if exceptional q.val i then 0 else nativeWeight q.val Φ i*disc q m n i

def incoming (q m n : ℕ+) (Φ : ℝ→ℂ) :=
  ∫ t : ℝ,scaled Φ t*cont q m n t

def discreteMode (q m n : ℕ+) (j : ℕ) (Y Q : ℝ) (k : D4→ℤ) (i : actualCuspBasisIndex q.val (NeZero.pos q.val)) :=
  if exceptional q.val i then 0 else term q j Y Q m.val n.val k (height q.val i)*disc q m n i

def incomingMode (q m n : ℕ+) (j : ℕ) (Y Q : ℝ) (k : D4→ℤ) (t : ℝ) :=
  term q j Y Q m.val n.val k t*cont q m n t

theorem discrete_exchange (q m n : ℕ+) {j : ℕ} (hm : m.val∈dyadicWindow j) (hn : n.val∈dyadicWindow j)
    {Y Q : ℝ} (y1 : 1≤Y) (qp : 0<Q) :
    let F := discreteMode q m n j Y Q
    Summable (fun z : (D4→ℤ)×actualCuspBasisIndex q.val (NeZero.pos q.val) => ‖F z.1 z.2‖) ∧
    HasSum (fun k => ∑' i,F k i) (principal q m n (switchedTest Y ((q.val:ℝ)*Q) m.val n.val)) := by
  let F := discreteMode q m n j Y Q
  let Idx := actualCuspBasisIndex q.val (NeZero.pos q.val)
  let f := switchedTest Y ((q.val:ℝ)*Q) m.val n.val
  let G := fun i : Idx => if exceptional q.val i then 0 else nativeWeight q.val f i*disc q m n i
  obtain ⟨A,an,sa,H⟩ := uniform_majorant
  let a := fun k : D4→ℤ => A k*(1+Real.log (2*Y)^2)
  let b := fun i : Idx => slotPrice q.val i*‖disc q m n i‖
  have ap (k : D4→ℤ) : 0≤a k := mul_nonneg (an _) (by positivity)
  have bp (i : Idx) : 0≤b i := mul_nonneg (slotPrice_nn _ _) (norm_nonneg _)
  have big : Summable (fun z : (D4→ℤ)×Idx => a z.1*b z.2) :=
    rectangle (sa.mul_right (1+Real.log (2*Y)^2)) (cubic_prices q m n).1 ap bp
  have sf : Summable (fun z : (D4→ℤ)×Idx => ‖F z.1 z.2‖) := by
    apply big.of_nonneg_of_le (fun z => norm_nonneg _)
    rintro ⟨k,i⟩
    by_cases e : exceptional q.val i
    · change ‖F k i‖≤a k*b i
      simpa only [F,discreteMode,if_pos e,norm_zero] using mul_nonneg (ap k) (bp i)
    · change ‖F k i‖≤a k*b i
      simp only [F,discreteMode,if_neg e,norm_mul]
      apply (mul_le_mul_of_nonneg_right (H Y y1 q j m.val n.val Q k (height q.val i)) (norm_nonneg _)).trans_eq
      simp only [b,slotPrice,if_neg e,a];ring
  have s : Summable (Function.uncurry F) := Summable.of_norm sf
  have point (i : Idx) : (∑' k,F k i)=G i := by
    by_cases e : exceptional q.val i
    · simp [F,discreteMode,G,e]
    · exact (show HasSum (fun k => F k i) (G i) from by
        simpa only [F,discreteMode,G,nativeWeight,if_neg e,scaled,f] using
          (tested q hm hn (zero_lt_one.trans_le y1) qp (height q.val i)).mul_right (disc q m n i)).tsum_eq
  have val : (∑' k,∑' i,F k i)=principal q m n f := calc
    _ = ∑' i,∑' k,F k i := s.tsum_comm.symm
    _ = ∑' i,G i := by simp_rw [point]
    _ = _ := rfl
  refine ⟨sf,?_⟩
  change HasSum (fun k => ∑' i,F k i) (principal q m n f)
  rw [←val]
  exact s.prod.hasSum

theorem continuous_exchange (q m n : ℕ+) {j : ℕ} (hm : m.val∈dyadicWindow j) (hn : n.val∈dyadicWindow j)
    {Y Q : ℝ} (y1 : 1≤Y) (qp : 0<Q) :
    let F := incomingMode q m n j Y Q
    (∀ k,Integrable (F k)) ∧ Summable (fun k => ∫ t : ℝ,‖F k t‖) ∧
    HasSum (fun k => ∫ t : ℝ,F k t) (incoming q m n (switchedTest Y ((q.val:ℝ)*Q) m.val n.val)) := by
  let F := incomingMode q m n j Y Q
  let f := switchedTest Y ((q.val:ℝ)*Q) m.val n.val
  obtain ⟨A,an,sa,H⟩ := uniform_majorant
  let a := fun k : D4→ℤ => A k*(1+Real.log (2*Y)^2)
  let b := fun t : ℝ => linePrice t*‖cont q m n t‖
  have sb : Integrable b := (cubic_prices q m n).2
  have vp := inv_pos.mpr (zero_lt_one.trans_le y1)
  have dom (k : D4→ℤ) (t : ℝ) : ‖F k t‖≤a k*b t := by
    rw [show ‖F k t‖=‖term q j Y Q m.val n.val k t‖*‖cont q m n t‖ from norm_mul _ _]
    exact (mul_le_mul_of_nonneg_right (H Y y1 q j m.val n.val Q k t) (norm_nonneg _)).trans_eq
      (by dsimp only [a,b];ring)
  have fi (k : D4→ℤ) : Integrable (F k) := by
    have sw : Continuous (fun t => scaled (spectralTest (mode (k 0)) Y⁻¹) t) := by
      simp only [scaled]
      simp_rw [show ∀ t,positiveWeight (spectralTest (mode (k 0)) Y⁻¹) t=weightSchwartz (mode (k 0)) vp t from
        fun t => (regular_transform _ vp t).2]
      exact (weightSchwartz _ _).continuous.div (by fun_prop)
        (fun t => Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
    exact (sb.const_mul (a k)).mono'
      ((aestronglyMeasurable_const.mul sw.aestronglyMeasurable).mul (covariance_meas q m n)) (ae_of_all _ (dom k))
  have sg : Summable (fun k => ∫ t : ℝ,‖F k t‖) := by
    apply ((sa.mul_right (1+Real.log (2*Y)^2)).mul_right (∫ t,b t)).of_nonneg_of_le
      (fun k => integral_nonneg (fun t => norm_nonneg _))
    intro k
    simpa only [integral_const_mul] using integral_mono (fi k).norm (sb.const_mul (a k)) (dom k)
  have point (t : ℝ) : (∑' k,F k t)=scaled f t*cont q m n t :=
    ((tested q hm hn (zero_lt_one.trans_le y1) qp t).mul_right (cont q m n t)).tsum_eq
  have out := hasSum_integral_of_summable_integral_norm fi sg
  simp_rw [point] at out
  exact ⟨fi,sg,out⟩

end
end ImbalancedChen.Part3.OriginalSwitchedRegularMarkExchange20261113
