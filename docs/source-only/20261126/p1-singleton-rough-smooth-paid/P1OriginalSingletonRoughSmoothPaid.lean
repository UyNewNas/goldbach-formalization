import ImbalancedChen.P1OriginalSingletonRoughComparisonPaid

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The already paid historical rough-minus-upper comparison is combined
with the original historical upper-core P2 bound. The existing fixed
moment and short-log prices feed the existing actual dominant-power
payment. No scalar rate, P2, rough comparison or coefficient-mass proof
is repeated, and none of those bounds is a premise.

All fixed accuracy, smoothing, frequency and cutoff orders precede one
physical-N threshold. The original signed historical coefficient and
actual shortSequence remain unchanged. Only the two long frequencies
are restricted by the stated logarithmic band.

This is the complete smooth rough arithmetic norm, still on the existing
wideWindow profiles. It does not identify those profiles with the sharp
block rectangle, restore Fourier tails, sum the outer HB atlas, or close
P1.5. The inherited missing-source and unique-owner boundaries remain.
-/

namespace ImbalancedChen.P1OriginalSingletonRoughSmoothPaid
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
open Part3.TwoLongHBMellinBrunProfiles (leftMellin rightMellin pairCost pairCost_nonneg)
open Part3.TwoLongMellinLogBudget (eventually_schedule)
open Part3.TwoLongActualLowerCorePayment (moment_log_budget short_log_budget)
open P4BOriginalNoMediumPairRows (longPositions)
open P1OriginalHistoricalTwoLongP2
  (historicalRowCore historical_rowCore_bound momentBudget momentBudget_nonneg)
open P1OriginalHistoricalTwoLongRoughComparison (historicalRoughSum)
open P1OriginalSingletonRoughComparison (eventually_actual_singleton_rough_comparison_gates)
open P1OriginalSingletonRoughComparisonPaid (eventually_actual_singleton_rough_comparison_paid)
open P1OriginalSingletonFixedRectangleScale (eventually_actual_singleton_fixed_rectangle_level)
open P1OriginalSingletonTwoLongPowerPayment (eventually_actual_singleton_twoLong_power_payment)

/-- The original singleton two-long smooth rough sum, including its
unchanged exact coprime mean, is paid at the complete block scale.
The same two positions, profile/log labels and signed HB pushforward
remain in the conclusion. No P2, error, mass or payment hypothesis is
assumed; hshort and the longPositions identity are the original dictionary
conditions for the actual two-long branch. -/
theorem eventually_actual_singleton_rough_smooth_paid
    (accuracy smoothOrder frequencyOrder cutoffOrder : ℕ)
    (hSmooth : 1 ≤ smoothOrder)
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
      |t₁| ≤ (Real.log (shortScale bs : ℝ))^frequencyOrder →
      |t₂| ≤ (Real.log (shortScale bs : ℝ))^frequencyOrder →
      let X0 : ℝ := shortScale bs
      let U : ℝ := lower (bs i)
      let V : ℝ := lower (bs k)
      let Z := beforeHBCutoff cutoffOrder [cj]
      let delta := ((Real.log X0)^smoothOrder)⁻¹
      let shortBlocks := fun a : ShortPositions i k => bs a.val
      let shortCutoffs := fun _ : ShortPositions i k => hbCutoff cj
      let shortFrequencies := fun a : ShortPositions i k => xi a.val
      let shortRoles := fun a : ShortPositions i k => rowRoles j a.val
      let alpha := shortSequence shortBlocks Z shortCutoffs shortFrequencies shortRoles
      ‖historicalRoughSum levelB old fresh N cap w z L
          (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂)
          U V Z (shortSupport shortBlocks) alpha‖ ≤
        X0/(Real.log X0)^accuracy := by
  let C : ℝ := 128*8^16
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_schedule smoothOrder hSmooth).and
      (Real.tendsto_log_atTop.eventually_ge_atTop C))
  have hkap0 : kap0 < 1 := by
    have hh := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(1-kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kap0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_singleton_rough_comparison_paid
      (accuracy+1) smoothOrder cutoffOrder hSmooth hkappa hsmall hzeta htrim,
    eventually_actual_singleton_rough_comparison_gates cutoffOrder
      hkappa hsmall hzeta htrim,
    eventually_actual_singleton_twoLong_power_payment (accuracy+1) smoothOrder
      frequencyOrder 23 cutoffOrder hkappa hsmall hzeta htrim,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall hzeta htrim,
    hgrowth.eventually (eventually_ge_atTop (64*T))]
      with N hcomparison hgates hpower hrectangle hlarge
  intro kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
    levelB old fresh cap w z L t₁ t₂ label log₁ log₂ xi ht₁ ht₂
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
  let delta := (ell^smoothOrder)⁻¹
  let H := ell^frequencyOrder
  let alpha := shortSequence bS Z ys xis rs
  let rough := historicalRoughSum levelB old fresh N cap w z L
    (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂)
    U V Z (shortSupport bS) alpha
  let core := historicalRowCore levelB old fresh N cap w z L Z J false false
    delta U V t₁ t₂ label log₁ log₂ bS ys xis rs
  obtain ⟨_, hcard, _, htrimX, _, _, _, _, _, _, _⟩ :=
    hrectangle kap hkap Bprofile cj j bs ns i k hj hik hns hactive
  have hTX : T ≤ X0 := by linarith only [hlarge, htrimX]
  obtain ⟨⟨hlog, hd, hs⟩, hconstant⟩ := hT X0 hTX
  have hell0 : 0 < ell := zero_lt_one.trans_le hlog
  have htwoLog : (2 : ℝ) ≤ ell := (show (2 : ℝ) ≤ C by norm_num [C]).trans hconstant
  obtain ⟨hx, hZ, _, _, hcap, hlevel⟩ :=
    hgates kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  obtain ⟨_, hD, _, hpowerBound⟩ :=
    hpower kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort
  have hx0 : 0 < X0 := zero_lt_one.trans hx
  have hU : 0 < U := by exact_mod_cast lower_pos (bs i)
  have hV : 0 < V := by exact_mod_cast lower_pos (bs k)
  have hH : 0 ≤ H := pow_nonneg hell0.le _
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hY : 0 ≤ Y := pow_nonneg (zero_le_one.trans hZ) _
  have hcost := pairCost_nonneg delta U V H
  have hmoment0 := momentBudget_nonneg D
  have hDx : (D : ℝ) ≤ X0 := by
    calc
      (D : ℝ) ≤ X0^(1199/2000 : ℝ) := Nat.floor_le (Real.rpow_nonneg hx0.le _)
      _ ≤ X0 := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le
          (by norm_num : (1199/2000 : ℝ) ≤ 1)
  have hmoment : momentBudget D ≤ (2*8^16 : ℝ)*(D : ℝ)^(3/2 : ℝ)*ell^16 :=
    moment_log_budget hD hlog hDx
  have hshortLog : (1+ell)^Fintype.card (ShortPositions i k) ≤ 64*ell^6 :=
    short_log_budget (by omega) hlog
  have hcore := historical_rowCore_bound levelB old fresh N cap D w z L
    (fun q hq => hlevel levelB old fresh cap w z q hq)
    hZ hx.le hd hs hU hV hH ht₁ ht₂ J false false label log₁ log₂ bS ys xis rs hcap
  have hcorePaid : ‖core‖ ≤ X0/ell^(accuracy+1) := by
    calc
      _ ≤ pairCost delta U V H*(M*Y^2)*
          ((2*8^16 : ℝ)*(D : ℝ)^(3/2 : ℝ)*ell^16)*(64*ell^6) := by
        apply hcore.trans
        gcongr <;> first
          | exact hmoment
          | exact hshortLog
          | positivity
      _ = pairCost delta U V H*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*(C*ell^22) := by
        dsimp only [C]
        ring
      _ ≤ pairCost delta U V H*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*(ell*ell^22) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hconstant (pow_nonneg hell0.le _))
          (mul_nonneg hcost (by positivity))
      _ = pairCost delta U V H*(M*Y^2*(D : ℝ)^(3/2 : ℝ))*ell^23 := by ring
      _ ≤ _ := hpowerBound
  have hdiff : ‖rough-core‖ ≤ X0/ell^(accuracy+1) :=
    hcomparison kap hkap Bprofile cj j bs ns i k hj hik hns hactive hshort hpair
      levelB old fresh cap w z L t₁ t₂ label log₁ log₂ xi
  have htriangle : ‖rough‖ ≤ ‖rough-core‖+‖core‖ := by
    simpa only [sub_add_cancel] using norm_add_le (rough-core) core
  calc
    _ ≤ ‖rough-core‖+‖core‖ := htriangle
    _ ≤ X0/ell^(accuracy+1)+X0/ell^(accuracy+1) := add_le_add hdiff hcorePaid
    _ = 2*X0/ell^(accuracy+1) := by ring
    _ = (2/ell)*(X0/ell^accuracy) := by rw [pow_succ]; field_simp [hell0.ne']; ring
    _ ≤ 1*(X0/ell^accuracy) := mul_le_mul_of_nonneg_right
      ((div_le_one hell0).mpr htwoLog) (by positivity)
    _ = _ := one_mul _

end
end ImbalancedChen.P1OriginalSingletonRoughSmoothPaid
