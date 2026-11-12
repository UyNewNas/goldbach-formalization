import ImbalancedChen.Part3ActualPositiveHolomorphicWeights

/-! The identity cell contributed by all even weights. In the Petersson
expansion this scalar is multiplied by the actual equal-cusp/equal-index
indicator. -/
namespace ImbalancedChen.Part3.ActualPositiveHolomorphicDiagonal20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)
open OriginalFullModulusTestJets20261102 ActualPositiveHolomorphicWeights20261112

def diagonalMoment (n : ℕ) (Φ : ℝ → ℂ) : ℂ :=
  ∫ q in Ioi (0:ℝ), intJ n q*Φ q

private theorem raw_integrable (n : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Integrable (fun q => intJ n q*spectralTest ell Y q) (volume.restrict (Ioi 0)) := by
  have hc : HasCompactSupport (spectralTest ell Y) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (Y/16) (16*Y)))
      (fun q h => ⟨(spectralTest_tsupport_strict ell hY (subset_tsupport _ h)).1.le,
        (spectralTest_tsupport_strict ell hY (subset_tsupport _ h)).2.le⟩)
  exact (((intJ_continuous n).mul (spectralTest_contDiff ell Y).continuous).integrable_of_hasCompactSupport hc.mul_left).integrableOn

private theorem diagonalSummable (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun n : ℕ => ‖diagonalMoment n (spectralTest ell Y)‖) := by
  let a := ∫ q in Ioi (0:ℝ),‖spectralTest ell Y q‖
  have h := ((spectralTest_integrable ell hY).norm).integrableOn (s:=Ioi (0:ℝ))
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((Real.summable_pow_div_factorial (8*Y)).mul_left (expMass (16*Y)*a))
  intro n
  let d := ((16*Y/2)^n/(n.factorial:ℝ))*expMass (16*Y)
  calc
    ‖diagonalMoment n (spectralTest ell Y)‖ ≤ ∫ q in Ioi (0:ℝ),d*‖spectralTest ell Y q‖ := by
      apply norm_integral_le_of_norm_le (h.const_mul d)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      by_cases hq0 : spectralTest ell Y q=0
      · simp [hq0]
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (intJ_bound n hq.le
          (spectralTest_tsupport_strict ell hY (subset_tsupport _ hq0)).2.le) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; dsimp [a,d]; rw [show 16*Y/2=8*Y by ring]; ring

private theorem weightedMoment (j : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    ((2*j+1:ℕ):ℂ)*moment (2*j+1) (spectralTest ell Y)=
      (diagonalMoment (2*j) (spectralTest ell Y)+diagonalMoment (2*j+2) (spectralTest ell Y))/2 := by
  rw [moment,← integral_const_mul,diagonalMoment,diagonalMoment,
    ← integral_add (raw_integrable _ ell hY) (raw_integrable _ ell hY),div_eq_mul_inv,← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have H := intJ_three_term (2*j) q
  push_cast at H ⊢
  field_simp [Complex.ofReal_ne_zero.mpr hq.ne'] at H ⊢
  linear_combination (spectralTest ell Y q)*H

private theorem unitPhase (j : ℕ) : I^(2*(j+1))=(-1:ℂ)^(j+1) := by
  rw [pow_mul,Complex.I_sq]

private theorem cell_term (j : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    ((2*j+1:ℕ):ℂ)*holWeight j (spectralTest ell Y)=
      (-(2:ℂ)*(-1:ℂ)^j)*diagonalMoment (2*j) (spectralTest ell Y) -
      (-(2:ℂ)*(-1:ℂ)^(j+1))*diagonalMoment (2*(j+1)) (spectralTest ell Y) := by
  rw [holWeight,unitPhase,show 2*(j+1)=2*j+2 by omega]
  linear_combination 4*(-1:ℂ)^(j+1)*weightedMoment j ell hY <;> ring_nf

/-- All moments here are the two actual integrals against the original
test. The surviving order zero uses dq, without the factor 1/q. -/
theorem positive_holomorphic_diagonal (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    HasSum (fun j : ℕ => ((2*j+1:ℕ):ℂ)*holWeight j (spectralTest ell Y))
      (-2*diagonalMoment 0 (spectralTest ell Y)) := by
  let Φ := spectralTest ell Y
  let b := fun j : ℕ => (-(2:ℂ)*(-1:ℂ)^j)*diagonalMoment (2*j) Φ
  have inj : Function.Injective (fun j : ℕ => 2*j) := fun u v h => by omega
  have S := (diagonalSummable ell hY).comp_injective inj
  have Sb : Summable (fun j => ‖b j‖) := by
    simpa only [b,norm_mul,norm_neg,norm_pow,norm_one,one_pow,mul_one,Complex.norm_ofNat,Function.comp_apply]
      using S.mul_left 2
  have s : Summable b := Sb.of_norm
  have hs : HasSum (fun j => b j-b (j+1)) (b 0) := by
    have tail := (summable_nat_add_iff 1).mpr s
    have H := s.hasSum.sub tail.hasSum
    have E := s.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at E
    convert H using 1 <;> linear_combination E
  simpa only [cell_term _ ell hY,b,pow_zero,mul_one,Nat.mul_zero] using hs

end
end ImbalancedChen.Part3.ActualPositiveHolomorphicDiagonal20261112

