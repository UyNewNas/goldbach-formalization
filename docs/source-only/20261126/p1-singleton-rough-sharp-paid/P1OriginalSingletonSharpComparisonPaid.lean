import ImbalancedChen.P1OriginalHistoricalTwoLongSharpComparison
import ImbalancedChen.P1OriginalSingletonRoughSmoothPaid

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

Local payment of the original historical singleton sharp-to-smooth
endpoint difference. The finite strip invoice is combined with the
existing P1 dominant and bare secondary payments and the original
inverse-log lemma. The P4 x^(1/3) endpoint terminal is not invoked.

The leading strip bill is C*x*delta*log(x)^26. Thus the fixed choice
stripSmoothingOrder A = A+30 leaves the required inverse-log margin
without a smoothing-order-dependent loss in that leading term. All
derivative losses are assigned to the existing P1 power reserves.

The same physical-N threshold precedes every original active singleton,
HB row, two long positions and signed historical coefficient. No rate,
P2, mass, mean or target-error hypothesis is added. This file stops at
the local endpoint difference; native-mode/Fourier/outer HB attachment
and the existing import-closure obligations remain outside its claim.
-/

namespace ImbalancedChen.P1OriginalSingletonSharpComparisonPaid
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile rowRoles)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualHBRoughBrunRates (halfOrder)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale shortSupport shortSequence)
open Part3.TwoLongHBMellinBrunProfiles (pairCost pairCost_nonneg)
open Part3.TwoLongTransitionMellinN2 (profile)
open Part3.TwoLongMellinLogBudget (eventually_schedule)
open P4BOriginalNoMediumPairRows (longPositions)
open P4BOriginalSharpLongProfiles (sharpProfile stripPrice)
open P4BOriginalSharpEndpointPrices (sizeConstant sizeConstant_nonneg eventually_inverse_log)
open P1OriginalHistoricalTwoLongRoughComparison (historicalRoughSum)
open P1OriginalHistoricalTwoLongSharpComparison
  (endpointFourTermBudget historical_shortSequence_endpoint_four_terms)
open P1OriginalSingletonRoughComparison (eventually_actual_singleton_rough_comparison_gates)
open P1OriginalSingletonFixedRectangleScale (eventually_actual_singleton_fixed_rectangle_level)
open P1OriginalSingletonTwoLongPowerPayment (eventually_actual_singleton_twoLong_power_payment)
open P1OriginalSingletonTwoLongSecondaryPowerPayment
  (eventually_actual_singleton_twoLong_secondary_power_payment)

/-- Chosen from the P1 strip integral loss 26, after the requested accuracy. -/
def stripSmoothingOrder (accuracy : ℕ) : ℕ := accuracy+30

theorem eventually_actual_singleton_sharp_comparison_paid
    (accuracy cutoffOrder : ℕ)
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 400)
    (htrim : kap0 < kappa / (4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (Bprofile cj j : ℕ) (bs : Fin (2*(j+1)) → Block)
        (ns : Fin (2*(j+1)) → ℕ) (i k : Fin (2*(j+1))),
      j ∈ Finset.range 3 → i ≠ k → ns ∈ rectangle bs →
      scalarProfile kap Bprofile N cj kap0 (completeProduct ns) ≠ 0 →
      (∀ a : ShortPositions i k,
        (lower (bs a.val) : ℝ) < originalMediumLow zeta [cj]) →
      longPositions (originalMediumHigh zeta [cj]) bs = {i,k} →
      ∀ (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ)
        (w z L t₁ t₂ : ℝ) (log₁ log₂ : Bool)
        (xi : Fin (2*(j+1)) → ℝ),
      let X0 : ℝ := shortScale bs
      let U : ℝ := lower (bs i)
      let V : ℝ := lower (bs k)
      let Z := beforeHBCutoff cutoffOrder [cj]
      let delta := ((Real.log X0)^(stripSmoothingOrder accuracy))⁻¹
      let shortBlocks := fun a : ShortPositions i k => bs a.val
      let shortCutoffs := fun _ : ShortPositions i k => hbCutoff cj
      let shortFrequencies := fun a : ShortPositions i k => xi a.val
      let shortRoles := fun a : ShortPositions i k => rowRoles j a.val
      let alpha := shortSequence shortBlocks Z shortCutoffs shortFrequencies shortRoles
      ‖historicalRoughSum levelB old fresh N cap w z L
          (sharpProfile log₁ U t₁) (sharpProfile log₂ V t₂)
          U V Z (shortSupport shortBlocks) alpha -
        historicalRoughSum levelB old fresh N cap w z L
          (profile false log₁ delta U t₁) (profile false log₂ delta V t₂)
          U V Z (shortSupport shortBlocks) alpha‖ ≤ X0/(Real.log X0)^accuracy := by
  let B := stripSmoothingOrder accuracy
  let E := 26+4*B
  let Cp : ℝ := 256*8^16*sizeConstant
  let C₀ : ℝ := 262144*8^16*sizeConstant
  let C₁ : ℝ := 4096*8^16*sizeConstant*stripPrice
  let C₂ : ℝ := 256*8^16*sizeConstant*stripPrice^2
  have hB : 1 ≤ B := by dsimp only [B, stripSmoothingOrder]; omega
  have hC₀ : 0 ≤ C₀ := by
    have H := sizeConstant_nonneg
    dsimp only [C₀]
    positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((eventually_schedule B hB).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (max 4 (max Cp (max C₁ C₂))))).and
      (eventually_inverse_log C₀ hC₀ 26 (accuracy+1) B
        (by dsimp only [B, stripSmoothingOrder]; omega)))
  have hkap0 : kap0 < 1 := by
    have H := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(1-kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kap0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_singleton_rough_comparison_gates cutoffOrder
      hkappa hsmall hzeta htrim,
    eventually_actual_singleton_twoLong_power_payment (accuracy+1) B 0 25 cutoffOrder
      hkappa hsmall hzeta htrim,
    eventually_actual_singleton_twoLong_secondary_power_payment (accuracy+1) B 0 E cutoffOrder
      hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall hzeta htrim,
    hgrowth.eventually (eventually_ge_atTop (64*T))]
      with N hgates hpower hsecondary hrectangle hlarge
  intro kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
    levelB old fresh cap w z L t₁ t₂ log₁ log₂ xi
  let X0 : ℝ := shortScale bs
  let bS := fun a : ShortPositions i k => bs a.val
  let ys := fun _ : ShortPositions i k => hbCutoff cj
  let xis := fun a : ShortPositions i k => xi a.val
  let rs := fun a : ShortPositions i k => rowRoles j a.val
  let M : ℝ := shortScale bS
  let U : ℝ := lower (bs i)
  let V : ℝ := lower (bs k)
  let Z := beforeHBCutoff cutoffOrder [cj]
  let J := halfOrder X0
  let Y := Z^(2*J+1)
  let D : ℕ := Nat.floor (X0^(1199/2000 : ℝ))
  let ell := Real.log X0
  let delta := (ell^B)⁻¹
  obtain ⟨_, hcard, hscale, htrimX, _, hx, _, _, _, _, _⟩ :=
    hrectangle kap hkap Bprofile cj j bs ns i k hj hik hns hactive
  have hTX : T ≤ X0 := by linarith only [hlarge, htrimX]
  obtain ⟨⟨⟨hlog, hd, hs⟩, hconstant⟩, hleading⟩ := hT X0 hTX
  have hfour : (4 : ℝ) ≤ ell := (le_max_left 4 _).trans hconstant
  have hCp : Cp ≤ ell := (le_max_left Cp _).trans ((le_max_right 4 _).trans hconstant)
  have hC₁ : C₁ ≤ ell := (le_max_left C₁ C₂).trans
    ((le_max_right Cp _).trans ((le_max_right 4 _).trans hconstant))
  have hC₂ : C₂ ≤ ell := (le_max_right C₁ C₂).trans
    ((le_max_right Cp _).trans ((le_max_right 4 _).trans hconstant))
  have hell0 : 0 < ell := zero_lt_one.trans_le hlog
  have hx0 : 0 < X0 := zero_lt_one.trans hx
  obtain ⟨_, hZ, hy, _, hcap, hlevel⟩ :=
    hgates kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨_, hD, _, hpowerBound⟩ :=
    hpower kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨_, _, _, _, _, hcrossBound, hsquareBound⟩ :=
    hsecondary kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
  have hMnat : 0 < shortScale bS := Finset.prod_pos (fun a _ => lower_pos (bs a.val))
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.succ_le_of_lt hMnat
  have hU : (1 : ℝ) ≤ U := by exact_mod_cast Nat.succ_le_of_lt (lower_pos (bs i))
  have hV : (1 : ℝ) ≤ V := by exact_mod_cast Nat.succ_le_of_lt (lower_pos (bs k))
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hMU : (1 : ℝ) ≤ M*U := by
    simpa only [one_mul] using mul_le_mul hM hU (by norm_num : (0 : ℝ) ≤ 1) hM0
  have hMV : (1 : ℝ) ≤ M*V := by
    simpa only [one_mul] using mul_le_mul hM hV (by norm_num : (0 : ℝ) ≤ 1) hM0
  have hUx : U ≤ 4*X0 := by
    have H : U ≤ X0 := calc
      U ≤ U*(M*V) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hMV hU0
      _ = X0 := by rw [hscale]; ring
    linarith
  have hVx : V ≤ 4*X0 := by
    have H : V ≤ X0 := calc
      V ≤ (M*U)*V := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hMU hV0
      _ = X0 := hscale.symm
    linarith
  have hDx : (D : ℝ) ≤ X0 := by
    calc
      (D : ℝ) ≤ X0^(1199/2000 : ℝ) := Nat.floor_le (Real.rpow_nonneg hx0.le _)
      _ ≤ X0 := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le
          (by norm_num : (1199/2000 : ℝ) ≤ 1)
  have hY : 0 ≤ Y := pow_nonneg (zero_le_one.trans hZ) _
  have hfinite := historical_shortSequence_endpoint_four_terms
    levelB old fresh N cap D w z L (fun q hq => hlevel levelB old fresh cap w z q hq)
    B log₁ log₂ hx hlog hU hV hUx hVx hZ hD hDx hd hs t₁ t₂ J hy
    bS ys xis rs (by omega) hcap hscale.symm
  have hcoefficient {C : ℝ} (hC : C ≤ ell) (e : ℕ) : C*ell^e ≤ ell^(e+1) := by
    calc
      _ ≤ ell*ell^e := mul_le_mul_of_nonneg_right hC (pow_nonneg hell0.le _)
      _ = _ := by rw [pow_succ]; ring
  have hdominant : pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^25 ≤
      X0/ell^(accuracy+1) := by simpa only [pow_zero] using hpowerBound
  have hpolyPaid : Cp*pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^24 ≤
      X0/ell^(accuracy+1) := by
    calc
      _ = (pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ)))*(Cp*ell^24) := by ring
      _ ≤ (pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ)))*ell^25 :=
        mul_le_mul_of_nonneg_left (hcoefficient hCp 24)
          (mul_nonneg (pairCost_nonneg _ _ _ _) (by positivity))
      _ ≤ _ := hdominant
  have hleadingPaid : C₀*X0*delta*ell^26 ≤ X0/ell^(accuracy+1) := by
    have H := mul_le_mul_of_nonneg_right hleading hx0.le
    calc
      _ = (C₀*ell^26*delta)*X0 := by ring
      _ ≤ (1/ell^(accuracy+1))*X0 := H
      _ = _ := by ring
  have hcrossPaid : C₁*(M*(U+V)*Y)*ell^(25+2*B) ≤ X0/ell^(accuracy+1) := by
    have H : C₁*ell^(25+2*B) ≤ ell^E := (hcoefficient hC₁ (25+2*B)).trans
      (pow_le_pow_right₀ hlog (by dsimp only [E]; omega))
    calc
      _ = (M*(U+V)*Y)*(C₁*ell^(25+2*B)) := by ring
      _ ≤ (M*(U+V)*Y)*ell^E := mul_le_mul_of_nonneg_left H (by positivity)
      _ ≤ _ := hcrossBound
  have hsquarePaid : C₂*(M*Y^2)*ell^(24+4*B) ≤ X0/ell^(accuracy+1) := by
    have H : C₂*ell^(24+4*B) ≤ ell^E := (hcoefficient hC₂ (24+4*B)).trans
      (pow_le_pow_right₀ hlog (by dsimp only [E]; omega))
    calc
      _ = (M*Y^2)*(C₂*ell^(24+4*B)) := by ring
      _ ≤ (M*Y^2)*ell^E := mul_le_mul_of_nonneg_left H (by positivity)
      _ ≤ _ := hsquareBound
  have hbudget : endpointFourTermBudget B X0 U V Y M D ≤ 4*X0/ell^(accuracy+1) := by
    exact (add_le_add (add_le_add (add_le_add hpolyPaid hleadingPaid) hcrossPaid) hsquarePaid).trans_eq
      (by ring)
  calc
    _ ≤ 4*X0/ell^(accuracy+1) := hfinite.trans hbudget
    _ = (4/ell)*(X0/ell^accuracy) := by rw [pow_succ]; field_simp [hell0.ne']; ring
    _ ≤ 1*(X0/ell^accuracy) := mul_le_mul_of_nonneg_right
      ((div_le_one hell0).mpr hfour) (by positivity)
    _ = _ := one_mul _

end
end ImbalancedChen.P1OriginalSingletonSharpComparisonPaid
