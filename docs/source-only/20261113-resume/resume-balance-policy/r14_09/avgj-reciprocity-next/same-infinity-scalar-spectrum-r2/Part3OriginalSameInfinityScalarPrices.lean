import ImbalancedChen.Part3OriginalSameInfinityTensorSpectrum
import ImbalancedChen.Part3OriginalMarkedPacketLimits

/-! Measurability and a cubic majorant of the same-infinity native
covariance at two arbitrary positive marks of the identical level. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityScalarPrices20261113
noncomputable section
open Set Filter MeasureTheory Complex Finset
open scoped Topology BigOperators MatrixGroups
open OriginalSameInfinityTensorSpectrum20261113 OriginalSameInfinityCompactTrace20261113
open ActualCuspDenominatorClasses20261110 OriginalContinuousCuspGram20261110
open ActualContinuousClassFourier20261110
open ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110
open ActualCriticalCuspEvaluation20261110 ActualUnitBandMellinProbe20261112 ActualUnitBandHeightSeeds20261112
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualSingleModeSpectralEnergy20261112 ActualMarkedCubicPrice20261112
open private cross_re from ImbalancedChen.Part3OriginalSameInfinityProbeEnergy
open private product_le from ImbalancedChen.Part3ActualMarkedSpectralMajorants

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

theorem covariance_meas (q m n : ℕ+) : AEStronglyMeasurable (cont q m n) volume := by
  let f := fun k : ℕ => seed (rate 1) 1 k
  let b := fun k t => radialProbe 1 (f k).toFun t
  let v := fun t : ℝ => 2*probeIntegral 1 ((t:ℂ)*I)
  let p := fun t : ℝ => ‖v t‖^2
  have MF (k : ℕ) : AEStronglyMeasurable (fun t => (star (b k t)*b k t)*cont q m n t) volume := by
    let ξ := (f k).toHeightSeed
    obtain ⟨_,H⟩ := same_infinity_compact_trace n m ξ ξ
    apply (H q).2.1.aestronglyMeasurable.congr
    apply ae_of_all
    intro t
    simp only [eisenstein,cont,nativeProduct,Finset.mul_sum,star_mul',ξ,b]
    apply sum_congr rfl
    intro a _
    ring
  have lim (t : ℝ) : Tendsto (fun k => b k t) atTop (𝓝 (v t)) := by
    change Tendsto (fun k => orderProbe 1 (f k).toFun (criticalPoint t-1/2)) atTop _
    rw [show criticalPoint t-1/2=(t:ℂ)*I by unfold criticalPoint; ring]
    exact cutoff_limit 1 (by norm_num) 1 (by simp [Complex.mul_re])
  have M : AEStronglyMeasurable (fun t => (p t:ℂ)*cont q m n t) volume := by
    apply aestronglyMeasurable_of_tendsto_ae atTop MF
    exact ae_of_all _ fun t => by
      have sq : star (v t)*v t=(p t:ℂ) := by
        rw [mul_comm,Complex.star_def,Complex.mul_conj'] <;> norm_cast
      simpa only [sq] using ((lim t).star.mul (lim t)).mul_const (cont q m n t)
  have eq (t : ℝ) : p t=4*((Real.pi^3/4)*Real.sinh Real.pi/
      (Real.cosh Real.pi+Real.cosh (Real.pi*t))^2) := by
    dsimp only [p,v]
    rw [norm_mul,mul_pow,gamma_norm 1 t (by norm_num)]
    norm_num
  have h : Continuous p := by rw [funext eq]; fun_prop (disch:=positivity)
  have nz (t : ℝ) : (p t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by rw [eq]; positivity)
  apply (M.div (Complex.continuous_ofReal.comp h).aestronglyMeasurable).congr
  exact ae_of_all _ fun t => by change (p t:ℂ)*cont q m n t/(p t:ℂ)=_; field_simp [nz t]

theorem cubic_prices (q m n : ℕ+) :
    Summable (fun i => slotPrice q.val i*‖disc q m n i‖) ∧
      Integrable (fun t => linePrice t*‖cont q m n t‖) := by
  have mz : (m.val:ℤ)≠0 := by exact_mod_cast m.property.ne'
  have nz : (n.val:ℤ)≠0 := by exact_mod_cast n.property.ne'
  constructor
  · apply ((discrete_mode q.val 1 _ mz).add (discrete_mode q.val 1 _ nz)).of_nonneg_of_le
      (fun i => mul_nonneg (slotPrice_nn _ _) (norm_nonneg _))
    intro i
    simp only [disc,norm_mul,norm_star,←mul_add]
    exact mul_le_mul_of_nonneg_left (product_le _ _) (slotPrice_nn _ _)
  · have pm : Continuous linePrice := by unfold linePrice cubic; fun_prop (disch:=positivity)
    apply ((continuous_mode q.val false _ mz).add (continuous_mode q.val false _ nz)).mono'
      (pm.aestronglyMeasurable.mul (covariance_meas q m n).norm)
    apply ae_of_all
    intro t
    rw [Real.norm_of_nonneg (mul_nonneg (linePrice_pos _).le (norm_nonneg _)),←mul_add]
    apply mul_le_mul_of_nonneg_left _ (linePrice_pos _).le
    simpa only [cont,nativeMass,←Finset.sum_div,continuousMass,div_eq_inv_mul] using
      cross_re q (fun a => nativeR a false (m.val:ℤ) t) (fun a => nativeR a false (n.val:ℤ) t)

end
end ImbalancedChen.Part3.OriginalSameInfinityScalarPrices20261113
