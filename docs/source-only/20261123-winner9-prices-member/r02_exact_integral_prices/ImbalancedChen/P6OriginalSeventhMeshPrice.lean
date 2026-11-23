import ImbalancedChen.P6OriginalLiteralMeshPrices
import ImbalancedChen.P6OriginalSeventhCorrectionIdentity
import ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral
import ImbalancedChen.P5U7OriginalRationalCoverConvergence

/-! The extra term in the original U7 triangle is integrated using two
primitives. Their chain-rule terms cancel on the moving boundary. This
evaluates the exact Fubini correction used in the numerical appendix. -/
namespace ImbalancedChen.P6OriginalSeventhMeshPrice

noncomputable section
open MeasureTheory Set
open P6OriginalLiteralMeshPrices P6OriginalLiteralLogIntegralPrices P6OriginalSeventhCorrectionIdentity

/-- Split the actual Buchstab kernel at its original seam. The ordered
branch is zero above the seam. Both positive denominators are the originals. -/
private theorem kernel_split {t u : ℝ} (hs : p5U7OmegaClosedSupport t u) :
    p5U7OmegaKernel 1 t u = 1/(t*u*(1-t-u)) + f (v t u)/(t*u^2) := by
  rw [kernel_branch hs.1 hs.2.1 hs.2.2]
  by_cases hc : u < (1-t)/3
  · rw [branchKernel,if_pos hc, (p5U7Omega_kernel_second 1 hs hc).2]
    unfold p5U7OmegaSecondKernel
    ring
  · rw [branchKernel,if_neg hc, p5U7Omega_kernel_first 1 hs (le_of_not_gt hc)]
    simp only [p5U7OmegaFirstKernel,add_zero]

private theorem original_row_split {t : ℝ} (ht : t ∈ Icc delta (1/3:ℝ)) :
    p5U7OmegaRow 1 t = Real.log ((1-2*t)/t)/(t*(1-t))+row t := by
  have ht0 := (show 0<delta by norm_num [delta]).trans_le ht.1
  have ht1 : t<1 := by linarith [ht.2]
  have hcap : t≤(1-t)/2 := by linarith [ht.2]
  have hc : ContinuousOn (fun u : ℝ => 1/(t*u*(1-t-u))) (Icc t ((1-t)/2)) := by
    apply continuousOn_const.div ((continuousOn_const.mul continuousOn_id).mul (continuousOn_const.sub continuousOn_id))
    intro u hu
    exact (mul_pos (mul_pos ht0 (ht0.trans_le hu.1)) (show 0<1-t-u by linarith [hu.2])).ne'
  have hi : (∫ u in t..((1-t)/2),1/(t*u*(1-t-u))) = Real.log ((1-2*t)/t)/(t*(1-t)) := by
    rw [intervalIntegral.integral_of_le hcap, ← integral_Ico_eq_integral_Ioc]
    simpa only [show 1-t-t=1-2*t by ring] using currentChenUpsilon9Harmonic_inner_integral ht0 ht1 ht0 hcap
  calc
    p5U7OmegaRow 1 t = ∫ u in t..((1-t)/2), 1/(t*u*(1-t-u)) + f (v t u)/(t*u^2) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hcap] at hu
      exact kernel_split ⟨ht.1,hu.1,hu.2⟩
    _ = (∫ u in t..((1-t)/2), 1/(t*u*(1-t-u))) + row t :=
      intervalIntegral.integral_add (hc.intervalIntegrable_of_Icc hcap)
        ((row_kernel_continuous ht0).intervalIntegrable_of_Icc hcap)
    _ = _ := by rw [hi]

theorem full_original_seventh_dictionary :
    p5U7OriginalOmegaIntegral 1 =
      (∫ t in (59/250:ℝ)..(1/3:ℝ), Real.log ((1-2*t)/t)/(t*(1-t))) +
      ∫ t in (2:ℝ)..(132/59:ℝ),
        (Real.log (t-1)/t)*Real.log ((1-59/250)/((59/250)*(t+1))) := by
  have hle : delta≤1/3 := by norm_num [delta]
  have hp : ContinuousOn (fun t : ℝ => Real.log ((1-2*t)/t)/(t*(1-t))) (Icc delta (1/3:ℝ)) := by
    have hO : ContinuousOn (fun t => p5U7OmegaRow 1 t-row t) (Icc delta (1/3:ℝ)) :=
      (p5U7Omega_row_continuousOn 1).sub row_continuous
    apply hO.congr
    intro t ht
    have h := original_row_split ht
    linarith only [h]
  rw [← correction_identity]
  calc
    _ = ∫ t in delta..(1/3:ℝ), Real.log ((1-2*t)/t)/(t*(1-t))+row t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact original_row_split (uIcc_of_le hle ▸ ht)
    _ = _ := intervalIntegral.integral_add (hp.intervalIntegrable_of_Icc hle)
      (row_continuous.intervalIntegrable_of_Icc hle)

theorem actual_seventh_integral :
    p5U7OriginalOmegaIntegral 1 ≤ (2042785889856317+3133582170107)/10000000000000000 := by
  rw [full_original_seventh_dictionary]
  linarith only [seventhPrime_literal_integral,correction_literal_integral]

theorem seventh_mesh_passes :
    P5U7OriginalRationalCoverCertificate.rationalUpper 32 1000000000000000000 ≤
      (1672464594622060236183097/1208925819614629174706176:ℚ)/(67619/10000) := by
  have hgap := (P5U7OriginalRationalCoverConvergence.rational_gap_le_totalRate 32 1000000000000000000 (by decide)).2
  have hLOW := P5U7OriginalRationalCoverCertificate.rationalLower_le_actual_integral 32 1000000000000000000 (by decide)
  have hsmall : ((2042785889856317+3133582170107)/10000000000000000:ℚ)+
      P5U7OriginalRationalCoverConvergence.totalRate 32 1000000000000000000 ≤
      (1672464594622060236183097/1208925819614629174706176:ℚ)/(67619/10000) := by
    change _ + rate7 ≤ price7
    exact seventh_budget.le
  have hgapR : (P5U7OriginalRationalCoverCertificate.rationalUpper 32 1000000000000000000:ℝ) -
      (P5U7OriginalRationalCoverCertificate.rationalLower 32 1000000000000000000:ℝ) ≤
      (P5U7OriginalRationalCoverConvergence.totalRate 32 1000000000000000000:ℝ) := by
    simpa only [Rat.cast_sub] using (Rat.cast_le (K:=ℝ)).mpr hgap
  have hc : (P5U7OriginalRationalCoverCertificate.rationalUpper 32 1000000000000000000:ℝ) ≤
      (2042785889856317+3133582170107)/10000000000000000+
        (P5U7OriginalRationalCoverConvergence.totalRate 32 1000000000000000000:ℝ) := by
    linarith only [hgapR,hLOW,actual_seventh_integral]
  apply (Rat.cast_le (K:=ℝ)).mp
  have hsR := (Rat.cast_le (K:=ℝ)).mpr hsmall
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_add] at hsR ⊢
  exact hc.trans hsR

end
end ImbalancedChen.P6OriginalSeventhMeshPrice
