import ImbalancedChen.P2FiniteMarkedGamma5SeedOrdinaryPrice
import ImbalancedChen.SingularProductIdentity
import ImbalancedChen.CurrentChenTrueLiNormalization
import ImbalancedChen.P2MarkedThetaLiNormalization
import ImbalancedChen.PowerErrorBudget

namespace ImbalancedChen.P2FiniteMarkedGamma5SeedConversionFloor
noncomputable section
open Finset Filter Real
open MathlibNt.SieveTheory.SingularSeries
  (liuSingularSeries liuSingularSeries_source_formula liuBaseDeviation
    liuCorrection liuCorrectionFactor liuUniversalProduct liuUniversalProduct_nonneg
    liuCorrectionFactor_pos one_le_liuCorrectionFactor)
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418 (logarithmicIntegral)
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open Wu2008DoubleSieve (wuSingularSeries wuSingularSeries_eq_liu)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2MarkedThetaLiNormalization (trueLi_eq_literalLi_add)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SeedHistoryMass
open P2EnhancedBadGamma5ArithmeticGeometry (ordinaryBad)
open P2FiniteMarkedGamma5SeedOrdinaryPrice (seedMass)
open P2FiniteMarkedGamma5NativeSeedSum (seed_marked_sum_eq_selected_coordinates)
open scoped Classical Topology BigOperators

private theorem original_eq_liu (N : ℕ) : singularSeries N=liuSingularSeries N := by
  rw [singularSeries_eq_natProduct,liuSingularSeries_source_formula]
  rfl

/-- All odd-prime factors of N still divide dN. The source conventions
have identical Euler products, with no factor of two at this interface. -/
theorem original_le_wu_product {d N : ℕ} (hd : 0<d) (hN : 0<N) :
    singularSeries N ≤ wuSingularSeries (d*N) := by
  rw [original_eq_liu,wuSingularSeries_eq_liu _ (Nat.mul_pos hd hN)]
  unfold liuSingularSeries
  apply mul_le_mul_of_nonneg_right _ liuUniversalProduct_nonneg
  unfold liuCorrection
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    obtain ⟨hm,hodd⟩ := mem_filter.mp hp
    obtain ⟨hp',hdvd,_⟩ := Nat.mem_primeFactors.mp hm
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr
      ⟨hp',dvd_mul_of_dvd_right hdvd d,(Nat.mul_pos hd hN).ne'⟩,hodd⟩
  · intro p hp
    exact (liuCorrectionFactor_pos (mem_filter.mp hp).2).le
  · intro p hp _
    exact one_le_liuCorrectionFactor (mem_filter.mp hp).2

/-- The additive normalization constant in true Li is removed before
using the specific literal logarithmic integral in thetaConversion. -/
theorem literal_li_normalized :
    Tendsto (fun N : ℕ => logarithmicIntegral N * log (N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ => log (N:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one,Real.rpow_one] using
      tendsto_nat_log_pow_div_rpow 1 (by norm_num : (0:ℝ)<1)
  have H : Tendsto (fun N : ℕ => trueLogarithmicIntegral N*log (N:ℝ)/(N:ℝ)-
      (2/log 2)*(log (N:ℝ)/(N:ℝ))) atTop (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using
      tendsto_currentChen_trueLi_normalized.sub (hz.const_mul (2/log 2))
  convert H using 1
  funext N
  rw [trueLi_eq_literalLi_add]
  ring

/-- One threshold precedes every old modulus. This is a lower bound on
the literal conversion, not a uniform approximation of a moving d by 1. -/
theorem conversion_floor {epsilon : ℝ} (he : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, 0<d →
      (1-epsilon)*singularSeries N/log (N:ℝ) ≤ thetaConversion N d/4 := by
  have H := literal_li_normalized
  filter_upwards [eventually_ge_atTop (2:ℕ),
    H.eventually (gt_mem_nhds (by linarith : 1-epsilon<1)),
    H.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with N hN hlow hpos
  intro d hd
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hLn : 0<log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  have hphi : (0:ℝ)<Nat.totient d := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)
  have hsc : singularSeries N ≤ d*wuSingularSeries (d*N)/(Nat.totient d:ℝ) := by
    apply (le_div_iff₀ hphi).mpr
    calc
      singularSeries N*(Nat.totient d:ℝ) ≤ singularSeries N*(d:ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.totient_le d) (singularSeries_pos N).le
      _ ≤ wuSingularSeries (d*N)*(d:ℝ) :=
        mul_le_mul_of_nonneg_right (original_le_wu_product hd (by omega)) (Nat.cast_nonneg _)
      _ = _ := mul_comm _ _
  have hli : (1-epsilon)/log (N:ℝ) ≤ logarithmicIntegral N/(N:ℝ) := by
    apply (div_le_iff₀ hLn).mpr
    simpa only [div_mul_eq_mul_div] using hlow.le
  have hli0 : 0 ≤ logarithmicIntegral N/(N:ℝ) := by
    have hpos' : 0 < logarithmicIntegral N/(N:ℝ)*log (N:ℝ) := by
      simpa only [div_mul_eq_mul_div] using hpos
    exact (pos_of_mul_pos_left hpos' hLn.le).le
  calc
    _ = ((1-epsilon)/log (N:ℝ))*singularSeries N := by ring
    _ ≤ (logarithmicIntegral N/(N:ℝ))*singularSeries N :=
      mul_le_mul_of_nonneg_right hli (singularSeries_pos N).le
    _ ≤ (logarithmicIntegral N/(N:ℝ))*(d*wuSingularSeries (d*N)/(Nat.totient d:ℝ)) :=
      mul_le_mul_of_nonneg_left hsc hli0
    _ = _ := by unfold thetaConversion; field_simp [hNr.ne',hphi.ne'] <;> ring

/-- The same target density unit is absorbed at each original modulus,
then summed on the fixed positive seed carrier. Multiplication by K
gives exactly the coefficient K/4 of the converted Gamma5 component. -/
theorem same_seed_density_unit {epsilon : ℝ} (he : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (k : Root) (t : ℝ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 →
      let Q := rootQ N n k t
      ((1-epsilon)*singularSeries N/log (N:ℝ))*
        seedMass N n k t (fun p w => ordinaryBad N (Q p) w.prod) ≤
        (1/4:ℝ)*seedMass N n k t
          (fun p w => thetaConversion N w.prod*ordinaryBad N (Q p) w.prod) := by
  filter_upwards [conversion_floor he,eventually_ge_atTop (2:ℕ)] with N H hN
  intro n k t ht ht' hn
  dsimp only
  have eqM (F : ℕ → List ℕ → ℝ) := seed_marked_sum_eq_selected_coordinates N n k t hN ht ht' hn F
  simp only [seedMass,← eqM,mul_sum]
  apply sum_le_sum
  intro p hp
  apply sum_le_sum
  intro l _
  have hpos : 0 ≤ ordinaryBad N (rootQ N n k t p) (wordProduct l) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hw := mul_nonneg (mark_pos (levelOccurrence l)).le hpos
  have h := mul_le_mul_of_nonneg_right
    (H _ (scale_and_alpha hN ht ht' hn hp l).1) hw
  simpa only [div_eq_mul_inv,one_mul,mul_assoc,mul_left_comm,mul_comm] using h

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedConversionFloor
