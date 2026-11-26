import ImbalancedChen.P1OriginalSingletonRoughComparison
import ImbalancedChen.P1OriginalSingletonTwoLongSecondaryPowerPayment
import ImbalancedChen.P4BOriginalE3LogPrices
import ImbalancedChen.Part3TwoLongActualLowerCorePayment

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The frozen 1106 two-rough-error is paid at one physical-N threshold for
the original singleton rectangle. The existing finite historical rough
comparison, original envelope/mean/moment prices, and all four scalar
payments are invoked. No Brun, P2, E1, fourth-moment or asymptotic rate
proof is replaced here.

The exact identity X0=M*U*V is retained. In particular the factorial
epsilon term is multiplied only by fixed logarithmic factors; the bound
M <= X0^(40*zeta) is not substituted into that term. The short mass keeps
its factor M until after the exact complete-scale identity is available.

Only rough-minus-upper for smooth profiles is asserted. The two actual
long positions are the existing dictionary positions. Sharp strips,
Fourier reconstruction, outer HB/selector summation and the full P1.5
terminal remain outside this source. Imports retain their existing
source-availability and unique-owner obligations.
-/

namespace ImbalancedChen.P1OriginalSingletonRoughComparisonPaid
noncomputable section
open Classical Filter
open scoped BigOperators SchwartzMap
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile rowRoles)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualHBRoughBrunRates (halfOrder)
open P5Z.ActualHBRoughBrunFinite (gapDensity chartPrimes)
open OriginalOneLongE5FiniteBudget (brunEpsilon)
open Part3.RoughSlotCharacterLift20261026b (smallPrimes)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale shortSupport shortSequence)
open Part3.TwoLongHBMellinBrunProfiles (leftMellin rightMellin pairCost pairCost_nonneg)
open Part3.TwoLongMellinLogBudget (eventually_schedule)
open Part3.TwoLongActualLowerCorePayment (moment_log_budget short_log_budget)
open P4BOriginalNoMediumPairRows (longPositions)
open P4BOriginalPositiveLongEnvelope (envelopeSchwartz meanPrice meanPrice_nonneg)
open P4BOriginalEnvelopePolynomialPayment (p2Price p2Price_nonneg)
open P4BOriginalPairMeanNorm (densityLog densityLog_one_le)
open P4BOriginalBrunCoprimeE1 (gap_density_B2)
open P4BOriginalE3LogPrices
  (envelope_price_pair meanLogConstant meanLogConstant_nonneg meanPrice_log)
open P1OriginalHistoricalTwoLongP2 (historicalRowCore momentBudget momentBudget_nonneg)
open P1OriginalHistoricalTwoLongRoughComparison
  (historicalRoughSum reciprocalMoment reciprocalMoment_nonneg)
open P1OriginalSingletonRoughComparison
  (eventually_actual_singleton_rough_comparison
    eventually_actual_singleton_rough_comparison_gates)
open P1OriginalSingletonFixedRectangleScale
  (eventually_actual_singleton_fixed_rectangle_level)
open P1OriginalSingletonTwoLongPowerPayment
  (eventually_actual_singleton_twoLong_power_payment)
open P1OriginalSingletonTwoLongSecondaryPowerPayment
  (eventually_actual_singleton_twoLong_secondary_power_payment)
open P1OriginalSingletonActualBrunDensity
  (eventually_actual_singleton_twoLong_density_payment)

/-- Only finite multiplication and regrouping of the already proved
prices. The short logarithmic price is the existing six-slot bound;
the actual singleton later supplies s <= 4. Epsilon stays literal. -/
private theorem rough_budget_le_four_terms
    (smoothOrder s : ℕ) (D : ℕ) {x U V Y epsilon M : ℝ}
    (hsCard : s ≤ 6) (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUx : U ≤ 4*x) (hVx : V ≤ 4*x)
    (hD : 1 ≤ D) (hDx : (D : ℝ) ≤ x)
    (hY : 0 ≤ Y) (hepsilon : 0 ≤ epsilon) (hM : 0 ≤ M)
    (hd : 0 < ((Real.log x)^smoothOrder)⁻¹)
    (hs : ((Real.log x)^smoothOrder)⁻¹ ≤ 1/4) :
    let delta := ((Real.log x)^smoothOrder)⁻¹
    let E := envelopeSchwartz hd hs U
    let J := envelopeSchwartz hd hs V
    let mu := M*(1+Real.log x)^s
    2*p2Price E J*Y^2*mu*momentBudget D +
      2*mu*meanPrice delta U*meanPrice delta V*reciprocalMoment D*
        (2*U*V*epsilon*densityLog x+2*densityLog x*(U+V)*Y+2*Y^2) ≤
    (2304*8^16 : ℝ)*pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*
        (Real.log x)^22 +
      (2048*8^16*meanLogConstant)*(Real.log x)^(25+4*smoothOrder)*
        (M*U*V*epsilon+M*(U+V)*Y+M*Y^2) := by
  let delta := ((Real.log x)^smoothOrder)⁻¹
  let E := envelopeSchwartz hd hs U
  let J := envelopeSchwartz hd hs V
  let mu := M*(1+Real.log x)^s
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog0 : 0 ≤ Real.log x := zero_le_one.trans hlog
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hmu : 0 ≤ mu := by dsimp only [mu]; positivity
  have hmuBound : mu ≤ 64*M*(Real.log x)^6 :=
    (mul_le_mul_of_nonneg_left (short_log_budget hsCard hlog) hM).trans_eq (by ring)
  have hpolyPrice : p2Price E J ≤ 9*pairCost delta U V 1 :=
    envelope_price_pair hd hs (by norm_num)
  have hmeanPrice := meanPrice_log smoothOrder hx0 hlog hU hV hUx hVx
  have hmoment : momentBudget D ≤
      (2*8^16 : ℝ)*(D : ℝ)^(3/2 : ℝ)*(Real.log x)^16 :=
    moment_log_budget hD hlog hDx
  have hreciprocal : reciprocalMoment D ≤ 8^16*(Real.log x)^16 :=
    P4BOriginalE3LogPrices.reciprocalMoment_log hD hlog hDx
  have hp0 := p2Price_nonneg E J
  have hpc0 := pairCost_nonneg delta U V 1
  have hm0 := momentBudget_nonneg D
  have hr0 := reciprocalMoment_nonneg D
  have hpu0 := meanPrice_nonneg delta U
  have hpv0 := meanPrice_nonneg delta V
  have hmc0 := meanLogConstant_nonneg
  have hdl0 : 0 ≤ densityLog x := zero_le_one.trans (densityLog_one_le hx.le)
  have hdl : densityLog x ≤ 8*Real.log x := by
    unfold densityLog
    linarith
  have hpoly : 2*p2Price E J*Y^2*mu*momentBudget D ≤
      (2304*8^16 : ℝ)*pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*
        (Real.log x)^22 := by
    calc
      _ ≤ 2*(9*pairCost delta U V 1)*Y^2*(64*M*(Real.log x)^6)*
          ((2*8^16 : ℝ)*(D : ℝ)^(3/2 : ℝ)*(Real.log x)^16) := by
        gcongr <;> first
          | exact hpolyPrice
          | exact hmuBound
          | exact hmoment
          | positivity
      _ = _ := by ring
  have hbracket :
      2*U*V*epsilon*densityLog x+2*densityLog x*(U+V)*Y+2*Y^2 ≤
        16*Real.log x*(U*V*epsilon+(U+V)*Y+Y^2) := by
    calc
      _ ≤ 2*U*V*epsilon*(8*Real.log x)+2*(8*Real.log x)*(U+V)*Y+2*Y^2 := by
        gcongr <;> first
          | exact hdl
          | positivity
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right
          (show (2 : ℝ) ≤ 16*Real.log x by linarith) (sq_nonneg Y)
        nlinarith only [hh]
  have hb0 : 0 ≤
      2*U*V*epsilon*densityLog x+2*densityLog x*(U+V)*Y+2*Y^2 := by positivity
  have hmean :
      2*mu*meanPrice delta U*meanPrice delta V*reciprocalMoment D*
        (2*U*V*epsilon*densityLog x+2*densityLog x*(U+V)*Y+2*Y^2) ≤
      (2048*8^16*meanLogConstant)*(Real.log x)^(25+4*smoothOrder)*
        (M*U*V*epsilon+M*(U+V)*Y+M*Y^2) := by
    calc
      _ = 2*mu*(meanPrice delta U*meanPrice delta V)*reciprocalMoment D*
          (2*U*V*epsilon*densityLog x+2*densityLog x*(U+V)*Y+2*Y^2) := by ring
      _ ≤ 2*(64*M*(Real.log x)^6)*
          (meanLogConstant*(Real.log x)^(2+4*smoothOrder))*
          (8^16*(Real.log x)^16)*
          (16*Real.log x*(U*V*epsilon+(U+V)*Y+Y^2)) := by
        gcongr <;> first
          | exact hmuBound
          | exact hmeanPrice
          | exact hreciprocal
          | exact hbracket
          | positivity
      _ = _ := by simp only [pow_add, pow_mul]; ring
  exact add_le_add hpoly hmean

/-- The actual singleton rough-minus-upper comparison is paid at one
physical-N threshold. All requested accuracies, smoothing orders and
cutoff orders precede that threshold. The given active tuple, original
profile order, chart, HB row, long positions, signed historical policies,
profile/log labels and real Mellin frequencies all follow it.

The two-long dictionary supplies hshort and the exact longPositions
identity. There is no mass, price, error, gap-density or rate premise.
No frequency bound is needed for this difference: both positive-gap
polynomial payments use the existing positive envelopes. -/
theorem eventually_actual_singleton_rough_comparison_paid
    (accuracy smoothOrder cutoffOrder : ℕ) (hSmooth : 1 ≤ smoothOrder)
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
        (w z L t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
        (xi : Fin (2*(j+1)) → ℝ),
      let X0 : ℝ := shortScale bs
      let U : ℝ := lower (bs i)
      let V : ℝ := lower (bs k)
      let Z := beforeHBCutoff cutoffOrder [cj]
      let J := halfOrder X0
      let delta := ((Real.log X0)^smoothOrder)⁻¹
      let shortBlocks := fun a : ShortPositions i k => bs a.val
      let shortCutoffs := fun _ : ShortPositions i k => hbCutoff cj
      let shortFrequencies := fun a : ShortPositions i k => xi a.val
      let shortRoles := fun a : ShortPositions i k => rowRoles j a.val
      let alpha := shortSequence shortBlocks Z shortCutoffs shortFrequencies shortRoles
      ‖historicalRoughSum levelB old fresh N cap w z L
          (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂)
          U V Z (shortSupport shortBlocks) alpha -
        historicalRowCore levelB old fresh N cap w z L Z J false false
          delta U V t₁ t₂ label log₁ log₂
          shortBlocks shortCutoffs shortFrequencies shortRoles‖ ≤
        X0/(Real.log X0)^accuracy := by
  let Cp : ℝ := 2304*8^16
  let Cm : ℝ := 2048*8^16*meanLogConstant
  let e : ℕ := 25+4*smoothOrder
  have hCm : 0 ≤ Cm := by
    have hm := meanLogConstant_nonneg
    dsimp only [Cm]
    positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_schedule smoothOrder hSmooth).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (max 4 (max Cp Cm))))
  have hkap0 : kap0 < 1 := by
    have hh := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(1-kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kap0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_singleton_rough_comparison cutoffOrder
      hkappa hsmall hzeta htrim,
    eventually_actual_singleton_rough_comparison_gates cutoffOrder
      hkappa hsmall hzeta htrim,
    eventually_actual_singleton_twoLong_power_payment (accuracy+1) smoothOrder 0 23
      cutoffOrder hkappa hsmall hzeta htrim,
    eventually_actual_singleton_twoLong_secondary_power_payment (accuracy+1) smoothOrder 0 (e+1)
      cutoffOrder hkappa hsmall hzeta htrim,
    eventually_actual_singleton_twoLong_density_payment cutoffOrder e (accuracy+1)
      Cm 1 hCm (by norm_num) hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall hzeta htrim,
    hgrowth.eventually (eventually_ge_atTop (64*T))]
      with N hrough hgates hpower hsecondary hdensity hrectangle hlarge
  intro kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
    levelB old fresh cap w z L t₁ t₂ label log₁ log₂ xi
  let X0 : ℝ := shortScale bs
  let bS := fun a : ShortPositions i k => bs a.val
  let M : ℝ := shortScale bS
  let U : ℝ := lower (bs i)
  let V : ℝ := lower (bs k)
  let Z := beforeHBCutoff cutoffOrder [cj]
  let J := halfOrder X0
  let Y := Z^(2*J+1)
  let D : ℕ := Nat.floor (X0^(1199/2000 : ℝ))
  let epsilon := brunEpsilon J (smallPrimes Z)
  let delta := ((Real.log X0)^smoothOrder)⁻¹
  let ell := Real.log X0
  obtain ⟨_, hcard, hscale, htrimX, _, hx, _, _, _, _, _⟩ :=
    hrectangle kap hkap Bprofile cj j bs ns i k hj hik hns hactive
  have hTX : T ≤ X0 := by linarith only [hlarge, htrimX]
  obtain ⟨⟨hlog, hd, hs⟩, hconstant⟩ := hT X0 hTX
  have hCpLog : Cp ≤ ell :=
    (le_max_left Cp Cm).trans ((le_max_right 4 (max Cp Cm)).trans hconstant)
  have hCmLog : Cm ≤ ell :=
    (le_max_right Cp Cm).trans ((le_max_right 4 (max Cp Cm)).trans hconstant)
  have hfourLog : (4 : ℝ) ≤ ell := (le_max_left 4 (max Cp Cm)).trans hconstant
  have hell0 : 0 < ell := zero_lt_one.trans_le hlog
  have hx0 : 0 < X0 := zero_lt_one.trans hx
  obtain ⟨_, hZ, _, _, _, _⟩ :=
    hgates kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨_, hD, _, hpowerBound⟩ :=
    hpower kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨_, _, _, _, _, hcrossBound, hsquareBound⟩ :=
    hsecondary kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
  obtain ⟨_, _, hdensityBound⟩ :=
    hdensity kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
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
  have hUx : U ≤ X0 := by
    calc
      U ≤ U*(M*V) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hMV hU0
      _ = X0 := by rw [hscale]; ring
  have hVx : V ≤ X0 := by
    calc
      V ≤ (M*U)*V := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hMU hV0
      _ = X0 := hscale.symm
  have hUx4 : U ≤ 4*X0 := hUx.trans (by linarith)
  have hVx4 : V ≤ 4*X0 := hVx.trans (by linarith)
  have hDx : (D : ℝ) ≤ X0 := by
    calc
      (D : ℝ) ≤ X0^(1199/2000 : ℝ) := Nat.floor_le (Real.rpow_nonneg hx0.le _)
      _ ≤ X0 := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le
          (by norm_num : (1199/2000 : ℝ) ≤ 1)
  have hY : 0 ≤ Y := pow_nonneg (zero_le_one.trans hZ) _
  have hepsilon : 0 ≤ epsilon := (norm_nonneg _).trans (gap_density_B2 Z J 1 1)
  have hfinite := hrough kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
    levelB old fresh cap w z L delta t₁ t₂ label log₁ log₂ xi hd hs
  have hprices := rough_budget_le_four_terms smoothOrder
    (Fintype.card (ShortPositions i k)) D (x := X0) (U := U) (V := V)
    (Y := Y) (epsilon := epsilon) (M := M) (by omega) hx hlog hU hV hUx4 hVx4
    hD hDx hY hepsilon hM0 hd hs
  have hdominant : pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^23 ≤
      X0/ell^(accuracy+1) := by
    simpa only [pow_zero] using hpowerBound
  have hpolyPaid : Cp*pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^22 ≤
      X0/ell^(accuracy+1) := by
    have hnon : 0 ≤ pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ)) :=
      mul_nonneg (pairCost_nonneg _ _ _ _) (by positivity)
    calc
      _ = (pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ)))*(Cp*ell^22) := by ring
      _ ≤ (pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ)))*(ell*ell^22) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCpLog (pow_nonneg hell0.le _)) hnon
      _ = pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^23 := by ring
      _ ≤ _ := hdominant
  have hepsilonDictionary : gapDensity Z J = epsilon := by
    simp only [epsilon, gapDensity, chartPrimes, smallPrimes]
  have hdensityPaid : Cm*ell^e*(M*U*V*epsilon) ≤ X0/ell^(accuracy+1) := by
    calc
      _ = Cm*(M*U*V)*gapDensity Z J*ell^e := by rw [hepsilonDictionary]; ring
      _ ≤ _ := by simpa only [one_mul] using hdensityBound
  have hmeanCoefficient : Cm*ell^e ≤ ell^(e+1) := by
    calc
      _ ≤ ell*ell^e := mul_le_mul_of_nonneg_right hCmLog (pow_nonneg hell0.le _)
      _ = _ := by rw [pow_succ]; ring
  have hcrossPaid : Cm*ell^e*(M*(U+V)*Y) ≤ X0/ell^(accuracy+1) := by
    calc
      _ ≤ ell^(e+1)*(M*(U+V)*Y) :=
        mul_le_mul_of_nonneg_right hmeanCoefficient (by positivity)
      _ = (M*(U+V)*Y)*ell^(e+1) := mul_comm _ _
      _ ≤ _ := hcrossBound
  have hsquarePaid : Cm*ell^e*(M*Y^2) ≤ X0/ell^(accuracy+1) := by
    calc
      _ ≤ ell^(e+1)*(M*Y^2) :=
        mul_le_mul_of_nonneg_right hmeanCoefficient (by positivity)
      _ = (M*Y^2)*ell^(e+1) := mul_comm _ _
      _ ≤ _ := hsquareBound
  have hsum :
      Cp*pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^22 +
        Cm*ell^e*(M*U*V*epsilon+M*(U+V)*Y+M*Y^2) ≤
      4*X0/ell^(accuracy+1) := by
    calc
      _ = Cp*pairCost delta U V 1*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^22 +
          Cm*ell^e*(M*U*V*epsilon)+Cm*ell^e*(M*(U+V)*Y)+Cm*ell^e*(M*Y^2) := by ring
      _ ≤ X0/ell^(accuracy+1)+X0/ell^(accuracy+1)+
          X0/ell^(accuracy+1)+X0/ell^(accuracy+1) :=
        add_le_add (add_le_add (add_le_add hpolyPaid hdensityPaid) hcrossPaid) hsquarePaid
      _ = _ := by ring
  calc
    _ ≤ 4*X0/ell^(accuracy+1) := hfinite.trans (hprices.trans hsum)
    _ = (4/ell)*(X0/ell^accuracy) := by rw [pow_succ]; field_simp [hell0.ne']; ring
    _ ≤ 1*(X0/ell^accuracy) := mul_le_mul_of_nonneg_right
      ((div_le_one hell0).mpr hfourLog) (by positivity)
    _ = _ := one_mul _

end
end ImbalancedChen.P1OriginalSingletonRoughComparisonPaid
