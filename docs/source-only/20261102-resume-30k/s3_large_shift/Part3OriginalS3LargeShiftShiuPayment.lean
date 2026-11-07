import ImbalancedChen.Part3OriginalS3LargeShiftProductMoment
import ImbalancedChen.Part3OriginalS2OtherRoughLogPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Reuse the exact existing primitive Shiu boundary at order 12 and the
already proved signed translated-window theorem, now at modulus one.
The mixed seventh moment needs no order-14 external input: for b>=1,
a*b^7 <= a^3+b^12.  Original kappa<=sigma/100 implies the weak kappa<=1
gate used for polynomial location; no extra kappa cap is introduced.
-/
namespace ImbalancedChen.Part3.OriginalS3LargeShiftShiuPayment20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3LargeShiftLocalization20261102 OriginalS3LargeShiftProductMoment20261102
open OriginalS3ClosePairPayment20261102 MediumActualDiagonalDivisorPayment20261028
open MediumActualRestorationPayment20261028 MediumGlobalDyadicOwnership20261028
open OriginalSamePsiS1OwnedAtlas OriginalMediumS1SeparatedDivisorMean
open ImbalancedChen.Part3OriginalS2ShiftedTwelve
open ImbalancedChen.Part3OriginalS2OtherRoughLogPayment
open ImbalancedChen.Part3OriginalS2OtherRoughCounting
open ImbalancedChen.Part3OriginalS2OtherRoughSource
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open MediumSignedShiftGCD20261028 MediumPrimitiveShiuWindow20261028
open MediumPrimitiveShiuSigned20261028 MediumPrimitiveShiuEuler20261028
open MediumPrimitiveShiuTwoSigns20261028
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def shiftedTwelfthMoment (atom : MediumAtom) : ℝ :=
  ∑ v ∈ productSource atom, tauR (productShift atom v) ^ 12

/-- A fixed polynomial domination permits the EXISTING order-12
Shiu boundary. The cutoff exponent and requested precision do not
change this moment order. -/
theorem mixed_seventh_le_cube_add_twelfth {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) :
    a * b ^ 7 ≤ a ^ 3 + b ^ 12 := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  by_cases hab : a ≤ b ^ 4
  · have hpow : b ^ 11 ≤ b ^ 12 := pow_le_pow_right₀ hb (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hab (pow_nonneg hb0 7)
    have hmul' : a * b ^ 7 ≤ b ^ 11 := by convert hmul using 1 <;> ring
    linarith [pow_nonneg ha 3]
  · have hpow : b ^ 7 ≤ b ^ 8 := pow_le_pow_right₀ hb (by norm_num)
    have hsq : b ^ 8 ≤ a ^ 2 := by
      have hh := pow_le_pow_left₀ (pow_nonneg hb0 4) (le_of_not_ge hab) 2
      simpa only [← pow_mul] using hh
    have hh := mul_le_mul_of_nonneg_left (hpow.trans hsq) ha
    have hh' : a * b ^ 7 ≤ a ^ 3 := by convert hh using 1 <;> ring
    linarith [pow_nonneg hb0 12]

theorem ordinary_tauR_cube_mean {X : ℝ} (hX : 1 ≤ X) :
    (∑ v ∈ Icc 1 (Nat.floor X), tauR v ^ 3) ≤ X * (1 + Real.log X) ^ 7 := by
  have hI : Icc 1 (Nat.floor X) = Ioc 0 (Nat.floor X) := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hI]
  have hh := sum_fouvryTau_pow_le_real (k := 2) (r := 3) (by norm_num) hX
  rw [fouvryTau_two] at hh
  simpa only [tauR, show (2 : ℕ) ^ 3 - 1 = 7 by norm_num] using hh

theorem shiftedSeventhMoment_le_cube_and_twelfth
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) :
    shiftedSeventhMoment atom ≤
      5 * atom.scale * (1 + Real.log (5 * atom.scale)) ^ 7 + shiftedTwelfthMoment atom := by
  have hx : 1 ≤ atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  have hmean : (∑ v ∈ productSource atom, tauR v ^ 3) ≤
      5 * atom.scale * (1 + Real.log (5 * atom.scale)) ^ 7 := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun _ _ _ => by dsimp [tauR]; positivity))
    exact ordinary_tauR_cube_mean (by linarith)
  apply (shiftedSeventhMoment_le_collapsed hA).trans
  calc
    _ ≤ (∑ v ∈ productSource atom, tauR v ^ 3) + shiftedTwelfthMoment atom := by
      unfold collapsedSeventhMoment shiftedTwelfthMoment
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro v hv
      have hshift : productShift atom v ≠ 0 :=
        Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr (mem_filter.mp hv).2)
      have hcard : 0 < (productShift atom v).divisors.card :=
        card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hshift⟩⟩
      apply mixed_seventh_le_cube_add_twelfth (by dsimp [tauR]; positivity)
      exact_mod_cast hcard
    _ ≤ _ := add_le_add_right hmean _

/-- The q=1 original translated moment. The residue remains signed,
and both endpoints come from the actual product cap. No prime-p or
occupied-key hypothesis is needed at modulus one. -/
theorem shiftedTwelfthMoment_le (hShiu : S2PrimitiveShiu)
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (hκ : κ ≤ 1)
    (hx : shiuThreshold hShiu ≤ atom.scale) :
    shiftedTwelfthMoment atom ≤ 5 * atom.scale * shiftedLogBudget hShiu atom.scale := by
  have hlarge := shiuThreshold_large hShiu hx
  have hx8 : 8 ≤ atom.scale :=
    (by norm_num : (8 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ)).trans hlarge
  have hxone : 1 ≤ atom.scale := by linarith
  have hxpos : 0 < atom.scale := by linarith
  have hroot := shiuThreshold_root hShiu hx
  have hroot32 : 32 ≤ atom.scale ^ ((1 : ℝ) / 80) := by linarith [hShiu.X0_lower]
  have hpow (t : ℝ) (ht : (1 : ℝ) / 80 ≤ t) :
      atom.scale ^ ((1 : ℝ) / 80) ≤ atom.scale ^ t :=
    Real.rpow_le_rpow_of_exponent_le hxone ht
  have h3 : 3 ≤ atom.scale ^ ((1 : ℝ) / 5) :=
    (by linarith : (3 : ℝ) ≤ atom.scale ^ ((1 : ℝ) / 80)).trans (hpow _ (by norm_num))
  have h16 : 16 < atom.scale ^ (7 * ((1 : ℝ) / 5) / 16) :=
    (by linarith : (16 : ℝ) < atom.scale ^ ((1 : ℝ) / 80)).trans_le (hpow _ (by norm_num))
  have h2 : 2 ≤ atom.scale ^ (((1 : ℝ) / 5) / 4) :=
    (by linarith : (2 : ℝ) ≤ atom.scale ^ ((1 : ℝ) / 80)).trans (hpow _ (by norm_num))
  have hf : (1 : ℝ) ≤ (5 * atom.scale) * atom.scale ^ (-((1 : ℝ) / 5)) := by
    calc
      _ ≤ atom.scale ^ ((4 : ℝ) / 5) := Real.one_le_rpow hxone (by norm_num)
      _ ≤ 5 * atom.scale ^ ((4 : ℝ) / 5) := by
        nlinarith [Real.rpow_nonneg hxpos.le ((4 : ℝ) / 5)]
      _ = _ := by
        conv_rhs => rw [← Real.rpow_one atom.scale]
        rw [mul_assoc, ← Real.rpow_add hxpos]
        norm_num
  have hg := shifted_original_geometry hA hκ hx8
  have hq1 : (1 : ℝ) ≤ reducedModulus 1 (naturalResidue (-atom.residue) 1) := by
    exact_mod_cast (show 1 ≤ reducedModulus 1 (naturalResidue (-atom.residue) 1) from
      reducedModulus_pos (r := naturalResidue (-atom.residue) 1) (by norm_num))
  have hX0 : hShiu.X0 ≤
      (reducedModulus 1 (naturalResidue (-atom.residue) 1) : ℝ) *
        atom.scale ^ (((1 : ℝ) / 5) / 2) / 2 := by
    have hroot' := hpow (((1 : ℝ) / 5) / 2) (by norm_num)
    have hnonneg := Real.rpow_nonneg hxpos.le (((1 : ℝ) / 5) / 2)
    nlinarith [mul_le_mul_of_nonneg_right hq1 hnonneg]
  have hraw := original_signed_shifted_sum_compact_budget 12
    (L := shiftedLow atom) (U := shiftedHigh atom)
    (f := 1) (r := naturalResidue (-atom.residue) 1)
    (x := atom.scale) (δ := 1 / 5) (K := 3) (M := 5 * atom.scale) hShiu
    (by norm_num) hg.1 hx8 (by norm_num) (by norm_num) (by norm_num)
    hf hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2 h3 h16 h2 hX0
  have hsource := actual_shifted_moment_le_signed atom 1 12 (by norm_num)
  have heq : productMultiples atom 1 = productSource atom := by
    ext v
    simp [productMultiples, productSource]
  rw [heq] at hsource
  have hsource' : shiftedTwelfthMoment atom ≤
      ∑ w ∈ signedShiftProgression (shiftedLow atom) (shiftedHigh atom) 1
        (naturalResidue (-atom.residue) 1), (w.natAbs.divisors.card : ℝ) ^ 12 := by
    simpa only [shiftedTwelfthMoment, productShift, tauR,
      ImbalancedChen.Part3OriginalS2OtherRoughSource.shiftAbs,
      ImbalancedChen.Part3OriginalS2OtherRoughSource.tau] using hsource
  exact hsource'.trans (by simpa only [Nat.divisors_one, card_singleton,
    Nat.cast_one, one_pow, div_one, mul_one, shiftedLogBudget] using hraw)

def momentLogOrder : ℕ := 2 ^ 12
def momentConstant (hShiu : S2PrimitiveShiu) : ℝ :=
  5 * logMultiplier ^ 7 + 5 * (smallLogConstant + 2 * largeLogConstant hShiu)

theorem momentConstant_pos (hShiu : S2PrimitiveShiu) : 0 < momentConstant hShiu := by
  have hD := logMultiplier_pos
  have hS := smallLogConstant_pos
  have hL := largeLogConstant_pos hShiu
  unfold momentConstant
  positivity

theorem shiftedSeventhMoment_polylog (hShiu : S2PrimitiveShiu)
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (hκ : κ ≤ 1)
    (hx : shiuThreshold hShiu ≤ atom.scale) (hL : 1 ≤ Real.log atom.scale) :
    shiftedSeventhMoment atom ≤
      momentConstant hShiu * atom.scale * Real.log atom.scale ^ momentLogOrder := by
  have hx1 : 1 ≤ atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  have hx0 : 0 < atom.scale := zero_lt_one.trans_le hx1
  have hD := logMultiplier_pos
  have hS := smallLogConstant_pos
  have hC := largeLogConstant_pos hShiu
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have h5base : 1 + Real.log (5 * atom.scale) ≤ logMultiplier * Real.log atom.scale := by
    have hh := Real.log_le_log (by positivity : 0 < 5 * atom.scale)
      (show 5 * atom.scale ≤ 8 * atom.scale by linarith)
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hx0.ne'] at hh
    unfold logMultiplier
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) hlog8]
  have h5nonneg : 0 ≤ 1 + Real.log (5 * atom.scale) := by
    linarith [Real.log_nonneg (show 1 ≤ 5 * atom.scale by linarith)]
  have h57 := pow_le_pow_left₀ h5nonneg h5base 7
  rw [mul_pow] at h57
  have h7E : Real.log atom.scale ^ (7 : ℕ) ≤ Real.log atom.scale ^ momentLogOrder :=
    pow_le_pow_right₀ hL (by norm_num [momentLogOrder])
  have h1E : 1 ≤ Real.log atom.scale ^ momentLogOrder := one_le_pow₀ hL
  have hF : shiftedLogBudget hShiu atom.scale ≤
      (smallLogConstant + 2 * largeLogConstant hShiu) * Real.log atom.scale ^ momentLogOrder := by
    unfold shiftedLogBudget
    rw [largeLogFactor_eq]
    change smallLogConstant + 2 * (largeLogConstant hShiu *
      Real.log atom.scale ^ momentLogOrder) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left h1E hS.le]
  have hfirst : 5 * atom.scale * (1 + Real.log (5 * atom.scale)) ^ 7 ≤
      5 * atom.scale * logMultiplier ^ 7 * Real.log atom.scale ^ momentLogOrder := by
    have hh := h57.trans (mul_le_mul_of_nonneg_left h7E (pow_nonneg hD.le 7))
    convert mul_le_mul_of_nonneg_left hh (show 0 ≤ 5 * atom.scale by positivity) using 1 <;> ring
  have hsecond := mul_le_mul_of_nonneg_left hF (show 0 ≤ 5 * atom.scale by positivity)
  have hraw := shiftedSeventhMoment_le_cube_and_twelfth hA
  have h12 := shiftedTwelfthMoment_le hShiu hA hκ hx
  unfold momentConstant
  nlinarith

/-- The manuscript chooses Ccut AFTER its fixed moment order and the
desired local precision. This is that original logarithmic cutoff. -/
def cutoffOrder (A : ℝ) : ℝ := A + (momentLogOrder : ℝ)

theorem exists_original_largeShiftMass_payment (hShiu : S2PrimitiveShiu)
    (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) (hκ : κ ≤ σ / 100) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
      ∀ (z y : ℝ) (k : Key),
        k ∈ keyBank atom z (roughY atom.scale) →
        largeShiftMass atom z y k (shiftCutoff atom (cutoffOrder A)) ≤
          6 * momentConstant hShiu * actualVScale atom k / Real.log atom.scale ^ A := by
  obtain ⟨xg, hxg, hgeom⟩ := exists_original_occupied_key_geometry σ hσ hσsmall
  refine ⟨max xg (max (shiuThreshold hShiu) (Real.exp 1)),
    hxg.trans_le (le_max_left _ _), ?_⟩
  intro B c0 atom hA hc0 hx z y k hk
  have hxg' := (le_max_left xg _).trans hx
  have htail := (le_max_right xg _).trans hx
  have hxS := (le_max_left (shiuThreshold hShiu) _).trans htail
  have hxE := (le_max_right (shiuThreshold hShiu) _).trans htail
  have hL : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxE
  have hL0 : 0 < Real.log atom.scale := zero_lt_one.trans_le hL
  have hx1 : 1 ≤ atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  have hx0 : 0 < atom.scale := zero_lt_one.trans_le hx1
  have hκone : κ ≤ 1 := by linarith
  have hVbig : atom.scale ≤ actualVScale atom k := by
    calc
      _ = atom.scale ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ atom.scale ^ (1 + σ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ ≤ _ := diagonal_scale_ge_power hA (σ / 2) k
        (hgeom B κ c0 atom hA hc0 hxg' z k hk).1
  have hY := keyY_positive hA k
  have hC := momentConstant_pos hShiu
  have hmoment := shiftedSeventhMoment_polylog hShiu hA hκone hxS hL
  have hcut : 0 < shiftCutoff atom (cutoffOrder A) := by
    unfold shiftCutoff
    exact Real.rpow_pos_of_pos hL0 _
  have hratio : Real.log atom.scale ^ momentLogOrder /
      shiftCutoff atom (cutoffOrder A) = 1 / Real.log atom.scale ^ A := by
    unfold shiftCutoff cutoffOrder
    rw [Real.rpow_add hL0, Real.rpow_natCast]
    field_simp [(Real.rpow_pos_of_pos hL0 A).ne', pow_ne_zero momentLogOrder hL0.ne'] <;> ring
  calc
    _ ≤ 2 * (2 * atom.U / keyY atom k + 1) * shiftedSeventhMoment atom /
        shiftCutoff atom (cutoffOrder A) := largeShiftMass_le_seventh hA z y k hcut
    _ ≤ 2 * (2 * atom.U / keyY atom k + 1) *
        (momentConstant hShiu * atom.scale * Real.log atom.scale ^ momentLogOrder) /
          shiftCutoff atom (cutoffOrder A) := by
      apply div_le_div_of_nonneg_right _ hcut.le
      apply mul_le_mul_of_nonneg_left hmoment
      have hU := hA.1
      positivity
    _ = momentConstant hShiu * (4 * actualVScale atom k + 2 * atom.scale) /
        Real.log atom.scale ^ A := by
      rw [show 2 * (2 * atom.U / keyY atom k + 1) *
          (momentConstant hShiu * atom.scale * Real.log atom.scale ^ momentLogOrder) /
            shiftCutoff atom (cutoffOrder A) =
          (2 * (2 * atom.U / keyY atom k + 1) * momentConstant hShiu * atom.scale) *
            (Real.log atom.scale ^ momentLogOrder / shiftCutoff atom (cutoffOrder A)) by ring,
        hratio]
      unfold actualVScale MediumAtom.scale
      field_simp [hY.ne', (Real.rpow_pos_of_pos hL0 A).ne'] <;> ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hL0.le A)
      nlinarith [mul_le_mul_of_nonneg_left hVbig hC.le]

end
end ImbalancedChen.Part3.OriginalS3LargeShiftShiuPayment20261102
