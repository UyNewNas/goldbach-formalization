import ImbalancedChen.P1OriginalSingletonFixedRectangleScale
import ImbalancedChen.P5ActualHBRoughBrunRates

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The scale remains the product of ALL original block lower endpoints.
The actual singleton roughness cutoff and prime alphabet are unchanged.
Its argument is 2^(6*K+2)*(2*R), and the genuine chart comparison is
R <= 128*X0, never the unrelated old pair bound R <= 16*X0.

K is fixed BEFORE this physical-N threshold. The threshold may depend on
K, the small parameters and the requested positive support exponent.
The profile order B is uniform here; a final caller may choose B, then K,
then this N threshold. No uniform-in-K roughness conclusion is asserted.

Four original short positions give M <= R^(12*zeta). The strict 28*zeta
gap pays the fixed factor 128^(12*zeta); the separate 1-3*zeta gap pays
the factor 2*128^(3*zeta) for every short block. The original real-x Brun
supplier is used at eps/2 with exactly halfOrder X0, without changing the
cutoff, the growing order, the selected i,k or the short carrier.
-/

namespace ImbalancedChen.P1OriginalSingletonFixedScaleTransport
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile scalarProfile_eq_ambient)
open P5Z.ActualLabelledPrimeSmoothCharts (profile_nonzero_support)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (actual_chi_one actual_chi_zero)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow)
open P5Z.ExactOriginalSmoothDyadicPartition (R_pos scales beforeHBCutoff tupleProfile)
open P5Z.OriginalChartRoughCutoff (roughF roughF_mono roughF_upper)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale)
open Part3.ActualRoughContourParameters20261026b (roughZ)
open P5Z.ActualHBRoughBrunRates
  (halfOrder nextOrder supportSize eventually_support_le_power)
open P1OriginalSingletonFixedRectangleScale
  (eventually_actual_singleton_fixed_rectangle_level)

/-- The SAME actual scalar profile supplies the original smooth chart
window through the existing labelled-profile support theorem. -/
theorem scalarProfile_chart_window (kap kap0 : ℝ) (B N cj n : ℕ)
    (hactive : scalarProfile kap B N cj kap0 n ≠ 0) :
    P5Z.ExactOriginalSmoothDyadicPartition.R cj / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P5Z.ExactOriginalSmoothDyadicPartition.R cj := by
  rw [scalarProfile_eq_ambient] at hactive
  have hpsi : P5Z.ActualEtaPsiOccurrenceBudget.psi ((n : ℝ) / P5Z.ExactOriginalSmoothDyadicPartition.R cj) ≠ 0 :=
    (mul_ne_zero_iff.mp hactive).2
  have htuple : tupleProfile P5Z.ActualEtaPsiOccurrenceBudget.chi [cj] [n] ≠ 0 := by
    simpa only [tupleProfile, P5Z.ExactOriginalSmoothDyadicPartition.psi,
      P5Z.ExactOriginalSmoothDyadicPartition.bump,
      P5Z.ActualEtaPsiOccurrenceBudget.psi, mul_one] using
      (Complex.ofReal_ne_zero.mpr hpsi)
  have hwindow := profile_nonzero_support P5Z.ActualEtaPsiOccurrenceBudget.chi
    (fun _ h => actual_chi_one h) (fun _ h => actual_chi_zero h) [cj] [n] htuple
  cases hwindow with
  | cons hhead _ => exact hhead.2

/-- Scalar constant absorption at fixed K. This helper keeps every
geometric premise visible; the actual theorem below proves them from the
original profile, rectangle and short-position output of the dictionary. -/
theorem eventually_fixed_scalar_transport (K : ℕ) (eps : ℝ) (heps : 0 < eps)
    {zeta : ℝ} (hzeta : 0 < zeta) (hsmall : zeta ≤ 1 / 400) :
    ∀ᶠ x : ℝ in atTop, ∀ R M : ℝ,
      0 < R → R ≤ 128*x → x ≤ 2*R → M ≤ R^(12*zeta) →
      let Z := roughF ((2 : ℝ)^(6*K+2)*(2*R))
      1 < x ∧ M ≤ x^(40*zeta) ∧
        (∀ U : ℝ, U ≤ R^(3*zeta) → 2*U ≤ x) ∧
        roughZ x ≤ Z ∧ Z ≤ (roughZ x)^2 ∧ 1 ≤ Z ∧
        Z^(2*halfOrder x+1) ≤ x^eps := by
  let C : ℝ := (2 : ℝ)^(6*K+2)
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num)
  filter_upwards [eventually_support_le_power (eps/2) (half_pos heps),
    eventually_ge_atTop (Real.exp (Real.exp 3)),
    eventually_ge_atTop (256*C),
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 28*zeta)).eventually
      (eventually_ge_atTop ((128 : ℝ)^(12*zeta))),
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-3*zeta)).eventually
      (eventually_ge_atTop (2*(128 : ℝ)^(3*zeta)))]
    with x hsupport hlarge hconstant hMconstant hUconstant
  intro R M hR hRx hxR hM
  let Z := roughF (C*(2*R))
  have hx : 1 < x := hsupport.1
  have hxp : 0 < x := zero_lt_one.trans hx
  have hMx : M ≤ x^(40*zeta) := by
    calc
      M ≤ R^(12*zeta) := hM
      _ ≤ (128*x)^(12*zeta) := Real.rpow_le_rpow hR.le hRx (by linarith)
      _ = (128 : ℝ)^(12*zeta)*x^(12*zeta) :=
        Real.mul_rpow (by norm_num) hxp.le
      _ ≤ x^(28*zeta)*x^(12*zeta) :=
        mul_le_mul_of_nonneg_right hMconstant (Real.rpow_nonneg hxp.le _)
      _ = x^(40*zeta) := by rw [← Real.rpow_add hxp]; congr 1; ring
  have hUx (U : ℝ) (hU : U ≤ R^(3*zeta)) : 2*U ≤ x := by
    have H := Real.rpow_le_rpow hR.le hRx (show 0 ≤ 3*zeta by linarith)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) hxp.le] at H
    have J := mul_le_mul_of_nonneg_right hUconstant (Real.rpow_nonneg hxp.le (3*zeta))
    rw [← Real.rpow_add hxp, show (1-3*zeta)+3*zeta=1 by ring, Real.rpow_one] at J
    nlinarith only [hU, H, J]
  have hxv : x ≤ C*(2*R) := hxR.trans (by nlinarith only [hC, hR])
  have hvx : C*(2*R) ≤ x^2 := by
    have H := mul_le_mul_of_nonneg_left hRx (show 0 ≤ 2*C by linarith)
    have J := mul_le_mul_of_nonneg_right hconstant hxp.le
    nlinarith only [H, J]
  have hlog : Real.exp 3 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hlarge
  have hloglog : 3 ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le (Real.log_pos hx)).mpr hlog
  have hlow : roughZ x ≤ Z := roughF_mono hx hloglog hxv
  have hupper := roughF_upper hx hloglog hxv hvx
  have hsq : x^(2/(Real.log (Real.log x))^3) = (roughZ x)^2 := by
    rw [← Real.rpow_natCast (roughZ x) 2]
    unfold roughZ
    rw [← Real.rpow_mul hxp.le]
    congr 1
    ring
  have hupperZ : Z ≤ (roughZ x)^2 := hupper.trans_eq hsq
  have hZ : 1 ≤ Z := hsupport.2.1.trans hlow
  refine ⟨hx, hMx, hUx, hlow, hupperZ, hZ, ?_⟩
  calc
    Z^(2*halfOrder x+1) ≤ ((roughZ x)^2)^(2*halfOrder x+1) :=
      pow_le_pow_left₀ (zero_le_one.trans hZ) hupperZ _
    _ = (supportSize x)^2 := by
      simp only [supportSize, nextOrder, ← pow_mul]
      congr 1
      omega
    _ ≤ (x^(eps/2))^2 :=
      pow_le_pow_left₀ (by unfold supportSize; exact pow_nonneg (zero_le_one.trans hsupport.2.1) _) hsupport.2.2 2
    _ = x^eps := by rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]; congr 1; ring

/-- The actual fixed rectangle pays the constant-128 chart transport.
The original two indices and their original short-position condition are
inputs from the already proved dictionary, not a desired M or support
bound. No activity of the whole rectangle or aggregate is required.

K and eps precede the physical-N threshold; every chart, row, tuple and
selected index follows it. Thus the same bound is available for all m,q,
rho and xi in the unchanged finite dictionary. -/
theorem eventually_actual_singleton_fixed_scale_transport (K : ℕ)
    (eps : ℝ) (heps : 0 < eps) {kappa kap0 zeta : ℝ}
    (hkappa : 0 < kappa) (hsmall : kappa ≤ zeta / 10000)
    (hzeta : zeta ≤ 1 / 400) (htrim : kap0 < kappa / (4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (B cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap B N cj kap0 (completeProduct ns) ≠ 0 →
      (∀ a : ShortPositions i k,
        (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) →
      let X0 : ℝ := shortScale bs
      let M := shortScale (fun a : ShortPositions i k => bs a.val)
      let Z := beforeHBCutoff K [cj]
      1 < X0 ∧ X0 = (M : ℝ)*(lower (bs i) : ℝ)*(lower (bs k) : ℝ) ∧
        P5Z.ExactOriginalSmoothDyadicPartition.R cj ≤ 128*X0 ∧ X0 ≤ 2*P5Z.ExactOriginalSmoothDyadicPartition.R cj ∧ (M : ℝ) ≤ X0^(40*zeta) ∧
        (∀ a : ShortPositions i k, 2*(lower (bs a.val) : ℝ) ≤ X0) ∧
        roughZ X0 ≤ Z ∧ Z ≤ (roughZ X0)^2 ∧ 1 ≤ Z ∧
        Z^(2*halfOrder X0+1) ≤ X0^eps := by
  have hzeta0 : 0 < zeta := by linarith only [hkappa, hsmall]
  have hkap0 : kap0 < 1 := by
    have H := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_fixed_scalar_transport K eps heps hzeta0 hzeta)
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(1-kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kap0)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_singleton_fixed_rectangle_level hkappa hsmall hzeta htrim,
    hgrowth.eventually (eventually_ge_atTop (64*T))] with N hrectangle hlarge
  intro kap hkap B cj j bs ns i k hj hik hns hactive hshort
  let X0 : ℝ := shortScale bs
  let M := shortScale (fun a : ShortPositions i k => bs a.val)
  obtain ⟨_, hfour, hscale, htrimX, _, hx, _, _, hwindow, _, _⟩ :=
    hrectangle kap hkap B cj j bs ns i k hj hik hns hactive
  have hTX : T ≤ X0 := by linarith only [hlarge, htrimX]
  obtain ⟨hnlow, hnhigh⟩ := scalarProfile_chart_window kap kap0 B N cj (completeProduct ns) hactive
  have hpoint := hwindow ns hns
  have hRX : P5Z.ExactOriginalSmoothDyadicPartition.R cj ≤ 128*X0 := by linarith only [hnlow, hpoint.2]
  have hXR : X0 ≤ 2*P5Z.ExactOriginalSmoothDyadicPartition.R cj := hpoint.1.trans hnhigh
  have hRone : (1 : ℝ) ≤ P5Z.ExactOriginalSmoothDyadicPartition.R cj := one_le_pow₀ (by norm_num)
  have hAone : 1 ≤ (P5Z.ExactOriginalSmoothDyadicPartition.R cj)^(3*zeta) := Real.one_le_rpow hRone (by linarith)
  have hslots (a : ShortPositions i k) : (lower (bs a.val) : ℝ) ≤ (P5Z.ExactOriginalSmoothDyadicPartition.R cj)^(3*zeta) := by
    simpa only [originalMediumLow, scales, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] using (hshort a).le
  have hM : (M : ℝ) ≤ (P5Z.ExactOriginalSmoothDyadicPartition.R cj)^(12*zeta) := by
    calc
      (M : ℝ) = ∏ a : ShortPositions i k, (lower (bs a.val) : ℝ) := by simp [M, shortScale]
      _ ≤ ∏ _a : ShortPositions i k, (P5Z.ExactOriginalSmoothDyadicPartition.R cj)^(3*zeta) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun a _ => hslots a)
      _ = ((P5Z.ExactOriginalSmoothDyadicPartition.R cj)^(3*zeta))^Fintype.card (ShortPositions i k) := by simp
      _ ≤ ((P5Z.ExactOriginalSmoothDyadicPartition.R cj)^(3*zeta))^4 := pow_le_pow_right₀ hAone hfour
      _ = (P5Z.ExactOriginalSmoothDyadicPartition.R cj)^(12*zeta) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (R_pos cj).le]
        congr 1
        ring
  have hZ : beforeHBCutoff K [cj] = roughF ((2 : ℝ)^(6*K+2)*(2*P5Z.ExactOriginalSmoothDyadicPartition.R cj)) := by
    simp only [beforeHBCutoff, scales, P5Z.OriginalChartRoughCutoff.chartCutoff,
      P5Z.OriginalChartRoughCutoff.argument, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil, List.prod_cons, List.prod_nil, pow_one, mul_one]
  obtain ⟨_, hMpay, hUpay, hzlow, hzhigh, hz1, hsupport⟩ :=
    hT X0 hTX (P5Z.ExactOriginalSmoothDyadicPartition.R cj) (M : ℝ) (R_pos cj) hRX hXR hM
  refine ⟨hx, hscale, hRX, hXR, hMpay, fun a => hUpay _ (hslots a), ?_⟩
  simpa only [hZ] using And.intro hzlow (And.intro hzhigh (And.intro hz1 hsupport))

end
end ImbalancedChen.P1OriginalSingletonFixedScaleTransport
