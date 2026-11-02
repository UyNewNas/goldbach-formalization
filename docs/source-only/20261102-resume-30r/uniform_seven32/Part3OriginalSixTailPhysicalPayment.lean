import ImbalancedChen.Part3OriginalSixTailBinding
import ImbalancedChen.Part3OriginalActualPoissonTightH
import ImbalancedChen.Part3OriginalOwnedS1PolynomialCaps
import ImbalancedChen.Part3ActualOriginalSpectralScales
import ImbalancedChen.Part3ActualPhysicalRawLabelPolynomial
import ImbalancedChen.Part3ActualPhysicalHardEpsilonSelection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Uniform Schwartz-tail payment for the actual tight Poisson atlas inside
O/Q OriginalData.  The literal source and all six physical pieces are
unchanged.  A deliberately coarse polynomial bound suffices for this
tail only; it is not used as a bound for the main spectral quadratic form.

The tail order and its constant precede b, sigma, kappa, c0, atom, key,
rectangle, polarization, both smooth labels and the earlier s frequency.
The last theorem supplies one common threshold and uses the original
globalCutoff with exponent eta/2.  It does not pay y=0 or m=0.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalActualPoissonTightH20261028
open ImbalancedChen.Part3.OriginalOwnedS1PolynomialCaps
open ImbalancedChen.Part3.ActualOriginalSpectralScales20261028
open ImbalancedChen.Part3.ActualFixedFeatureCountGeometrySourceOnly
open ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly
open ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b
open ImbalancedChen.Part3.ActualPhysicalRawLabelPolynomialSourceOnly
open ImbalancedChen.Part3.ActualPhysicalHardEpsilonSelectionSourceOnly
open ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalSixTailBinding20261102

namespace ImbalancedChen.Part3.OriginalSixTailPhysicalPayment20261102

attribute [local instance] Classical.propDecidable

/-- This is the existing tight atlas block in the existing OriginalData
record, with all originally independent choices still present. -/
def tightOriginalData {b : ℕ} {sigma kappa c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b sigma kappa c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (rectangle : Rectangle) (st st' : ℕ × ℕ) (polarS polarR polarN : Fin 4) : OriginalData where
  block := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
  atom := atom
  roughCutoff := z
  key := k
  small := small
  rectangle := rectangle
  smoothLeft := st
  smoothRight := st'
  polarS := polarS
  polarR := polarR
  polarN := polarN

/-- The O source's s carrier has its actual half-open dyadic support.
This uses its source-membership theorem, not the old chart carrier. -/
theorem original_sCarrier_card_le (D : OriginalData) :
    (D.sCarrier.card : ℝ) ≤ 2 * scaleS D.key := by
  have hsub : D.sCarrier ⊆ Ioc 0 (Nat.floor (2 * scaleS D.key)) := by
    intro s hs
    exact mem_Ioc.mpr ⟨D.sCarrier_positive hs,
      (mem_Icc.mp (D.sCarrier_subset_factorCarrier hs)).2⟩
  calc
    _ ≤ ((Ioc 0 (Nat.floor (2 * scaleS D.key))).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ = (Nat.floor (2 * scaleS D.key) : ℝ) := by
      simp only [Nat.card_Ioc, Nat.sub_zero]
    _ ≤ _ := Nat.floor_le (by have := scaleS_pos D.key; positivity)

/-- A coarse polynomial cap for the actual keyRealH, uniform in kappa.
The existing occupied-key bounds supply D and the total rough length. -/
theorem occupied_keyRealH_le_power {b : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible b sigma kappa c0 atom)
    (hsigma : 0 ≤ sigma) {z y : ℝ} {k : Key} (hk : k ∈ keyBank atom z y) :
    0 ≤ keyRealH atom k ∧ keyRealH atom k ≤ 64 * atom.scale ^ 12 := by
  obtain ⟨hx, hU, hQ1, hQ2, hQ3⟩ := actual_admissible_geometry hA hsigma
  have hx0 : 0 < atom.scale := zero_lt_one.trans_le hx
  have hlog0 : 0 ≤ Real.log atom.scale := Real.log_nonneg hx
  have hlog : Real.log atom.scale ≤ atom.scale :=
    (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hV : 1 ≤ atom.V := hA.2.1
  have hV0 : 0 < atom.V := zero_lt_one.trans_le hV
  have hQ0 : 0 ≤ atom.Q1 := zero_le_one.trans hA.2.2.1
  obtain ⟨hD, hR⟩ := occupied_key_scales_le_physical_cap hk
  have hcap := physical_cap_le_four_scale_sq hA hsigma
  have hD' := hD.trans hcap
  have hR' := hR.trans hcap
  have hD0 : 0 ≤ keyD k := by unfold keyD; positivity
  have hR0 : 0 ≤ keyR k := by unfold keyR; positivity
  have hnum0 : 0 ≤ atom.Q1 * keyD k * keyR k ^ 2 * Real.log atom.scale ^ 5 := by
    positivity
  have hnum : atom.Q1 * keyD k * keyR k ^ 2 * Real.log atom.scale ^ 5 ≤
      64 * atom.scale ^ 12 := by
    calc
      _ ≤ atom.scale * (4 * atom.scale ^ 2) *
          (4 * atom.scale ^ 2) ^ 2 * atom.scale ^ 5 := by gcongr
      _ = _ := by ring
  constructor
  · unfold keyRealH
    positivity
  · unfold keyRealH
    apply le_trans _ hnum
    apply (div_le_iff₀ hV0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hV hnum0]

/-- Actual OriginalData source mass, including every signed f and both
ordered h/s labels.  No norm or polynomial-cost hypothesis is assumed. -/
theorem tight_original_physical_tail_cost {b : ℕ} {sigma kappa c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b sigma kappa c0 atom) (hsigma : 0 ≤ sigma)
    (hk : k ∈ keyBank atom z y) (Csep : ℕ) (j : Fin 3)
    (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (rectangle : Rectangle) (st st' : ℕ × ℕ) (polarS polarR polarN : Fin 4) :
    let D := tightOriginalData atom z y k hA Csep j small hd negative
      rectangle st st' polarS polarR polarN
    D.cScale ^ 2 * rawLabelBudget D.sCarrier D.hBound D.fScale ≤
      21632000 * atom.scale ^ 33 := by
  let D := tightOriginalData atom z y k hA Csep j small hd negative
    rectangle st st' polarS polarR polarN
  change D.cScale ^ 2 * rawLabelBudget D.sCarrier D.hBound D.fScale ≤ _
  obtain ⟨hx, hU, hQ1, hQ2, hQ3⟩ := actual_admissible_geometry hA hsigma
  have hx0 : 0 ≤ atom.scale := zero_le_one.trans hx
  obtain ⟨hR, hS, hRS⟩ := actual_rough_owner_geometry hA z y k hk
  have hRx : scaleR D.key ≤ 2 * atom.scale :=
    hR.trans (mul_le_mul_of_nonneg_left hQ3 (by norm_num))
  have hSx : scaleS D.key ≤ 2 * atom.scale :=
    hS.trans (mul_le_mul_of_nonneg_left hQ2 (by norm_num))
  have hR0 := (scaleR_pos D.key).le
  have hS0 := (scaleS_pos D.key).le
  have hU0 : 0 ≤ atom.U := zero_le_one.trans hA.1
  have hC : D.cScale ≤ 4 * atom.scale ^ 3 := by
    change atom.U * scaleR k * scaleS k ≤ _
    calc
      _ ≤ atom.scale * (2 * atom.scale) * (2 * atom.scale) := by gcongr
      _ = _ := by ring
  have hC2 : D.cScale ^ 2 ≤ 16 * atom.scale ^ 6 := by
    calc
      _ ≤ (4 * atom.scale ^ 3) ^ 2 := pow_le_pow_left₀ D.cScale_pos.le hC 2
      _ = _ := by ring
  have hT : (D.sCarrier.card : ℝ) ≤ 4 * atom.scale :=
    (original_sCarrier_card_le D).trans (by linarith)
  have hHid : D.block.H = keyRealH atom k := rfl
  obtain ⟨hH0, hH⟩ := occupied_keyRealH_le_power hA hsigma hk
  have hHceil : (D.hBound : ℝ) ≤ 65 * atom.scale ^ 12 := by
    have hh := (Nat.ceil_lt_add_one hH0).le
    have hp : 1 ≤ atom.scale ^ 12 := one_le_pow₀ hx
    change (Nat.ceil D.block.H : ℝ) ≤ _
    rw [hHid]
    linarith
  have hFreq : ((poissonNonzeroFrequencyWindow D.hBound).card : ℝ) ≤
      130 * atom.scale ^ 12 := by
    have hh : ((poissonNonzeroFrequencyWindow D.hBound).card : ℝ) ≤
        2 * D.hBound := by exact_mod_cast frequency_card_le D.hBound
    linarith
  have hF : D.fScale ≤ 2 * atom.scale := by
    have hQ : 1 ≤ atom.Q1 := hA.2.2.1
    have hQp : 0 < atom.Q1 := zero_lt_one.trans_le hQ
    change 2 * atom.U / atom.Q1 ≤ _
    apply (div_le_iff₀ hQp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * atom.scale by positivity)]
  have hFc : ((Icc (Int.ceil (-D.fScale)) (Int.floor D.fScale)).card : ℝ) ≤
      5 * atom.scale := by
    have hh := full_signed_f_card_le D.fScale_pos.le
    linarith
  have hProd : (D.sCarrier.card : ℝ) *
      ((poissonNonzeroFrequencyWindow D.hBound).card : ℝ) ≤ 520 * atom.scale ^ 13 := by
    calc
      _ ≤ (4 * atom.scale) * (130 * atom.scale ^ 12) :=
        mul_le_mul hT hFreq (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hMass : rawLabelBudget D.sCarrier D.hBound D.fScale ≤
      1352000 * atom.scale ^ 27 := by
    unfold rawLabelBudget
    calc
      _ ≤ (5 * atom.scale) * (520 * atom.scale ^ 13) ^ 2 :=
        mul_le_mul hFc (pow_le_pow_left₀ (by positivity) hProd 2)
          (sq_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (16 * atom.scale ^ 6) * (1352000 * atom.scale ^ 27) :=
      mul_le_mul hC2 hMass (by unfold rawLabelBudget; positivity) (by positivity)
    _ = _ := by ring

/-- The already proved degree-23 rate and order selection are reused;
only the ten additional powers in this actual source cap are transported. -/
private theorem rate33 {x eps A : ℝ} (hx : 1 ≤ x) (heps : 0 < eps)
    (hA : 0 ≤ A) {dord : ℕ} (hdord : 2 ≤ dord)
    (hrate : 33 + A ≤ eps * ((dord - 1 : ℕ) : ℝ)) :
    x ^ (33 : ℕ) / (x ^ eps) ^ (dord - 1) ≤ x ^ (-A) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hbase := hard_rate_absorption hx heps (show 0 ≤ A + 10 by linarith)
    hdord (show 23 + (A + 10) ≤ eps * ((dord - 1 : ℕ) : ℝ) by linarith)
  calc
    _ = x ^ (10 : ℕ) * (x ^ (23 : ℕ) / (x ^ eps) ^ (dord - 1)) := by ring
    _ ≤ x ^ (10 : ℕ) * x ^ (-(A + 10)) :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg hx0.le _)
    _ = x ^ (-A) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
      congr 1
      norm_num <;> ring

/-- An actual uniform payment for Q's nonzero-y six-tail at the literal
eta/2 cutoff.  The order and threshold are selected before every moving
source parameter.  The zero-y and m=0 terms remain in sixZeros. -/
theorem exists_tight_original_sixTail_threshold (A eta : ℝ)
    (hA : 0 ≤ A) (heta : 0 < eta) :
    ∃ dord : ℕ, 2 ≤ dord ∧
      34 + A ≤ (eta / 2) * ((dord - 1 : ℕ) : ℝ) ∧
      ∃ X : ℝ, 1 ≤ X ∧
      ∀ (b : ℕ) (sigma kappa c0 : ℝ) (atom : MediumAtom)
        (hAdm : MediumAdmissible b sigma kappa c0 atom),
        0 ≤ sigma → X ≤ atom.scale →
        ∀ (z y : ℝ) (k : Key), k ∈ keyBank atom z y →
        ∀ (Csep : ℕ) (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k)
          (negative : Bool) (rectangle : Rectangle) (st st' : ℕ × ℕ)
          (polarS polarR polarN : Fin 4),
        let D := tightOriginalData atom z y k hAdm Csep j small hd negative
          rectangle st st' polarS polarR polarN
        ∀ r : ZMod (prefixPeriod D.key),
          ‖sixTail D r (globalCutoff D atom.scale (eta / 2))‖ ≤ atom.scale ^ (-A) := by
  have heps : 0 < eta / 2 := by positivity
  obtain ⟨dord, hdord, horder⟩ := exists_hard_order (A + 11) (eta / 2) heps
  obtain ⟨K, hK, htail⟩ := original_sixTail_raw_bound dord hdord
  refine ⟨dord, hdord, by linarith, max 1 (21632000 * K), le_max_left _ _, ?_⟩
  intro b sigma kappa c0 atom hAdm hsigma hx z y k hk
    Csep j small hd negative rectangle st st' polarS polarR polarN
  let D := tightOriginalData atom z y k hAdm Csep j small hd negative
    rectangle st st' polarS polarR polarN
  change ∀ r : ZMod (prefixPeriod D.key), _
  intro r
  have hx1 : 1 ≤ atom.scale := (le_max_left _ _).trans hx
  have hx0 : 0 < atom.scale := zero_lt_one.trans_le hx1
  have hKx : 21632000 * K ≤ atom.scale := (le_max_right _ _).trans hx
  have hcost := tight_original_physical_tail_cost atom z y k hAdm hsigma hk
    Csep j small hd negative rectangle st st' polarS polarR polarN
  have hraw := htail b sigma kappa c0 D hAdm r atom.scale (eta / 2) hx0
  have hrate := rate33 hx1 heps (show 0 ≤ A + 1 by linarith) hdord
    (show 33 + (A + 1) ≤ (eta / 2) * ((dord - 1 : ℕ) : ℝ) by linarith)
  calc
    _ ≤ K * (D.cScale ^ 2 * rawLabelBudget D.sCarrier D.hBound D.fScale) /
        (atom.scale ^ (eta / 2)) ^ (dord - 1) := hraw
    _ ≤ K * (21632000 * atom.scale ^ (33 : ℕ)) /
        (atom.scale ^ (eta / 2)) ^ (dord - 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcost hK.le
    _ = (21632000 * K) *
        (atom.scale ^ (33 : ℕ) / (atom.scale ^ (eta / 2)) ^ (dord - 1)) := by ring
    _ ≤ (21632000 * K) * atom.scale ^ (-(A + 1)) :=
      mul_le_mul_of_nonneg_left hrate (by positivity)
    _ ≤ atom.scale * atom.scale ^ (-(A + 1)) :=
      mul_le_mul_of_nonneg_right hKx (Real.rpow_nonneg hx0.le _)
    _ = atom.scale ^ (-A) := by
      nth_rw 1 [← Real.rpow_one atom.scale]
      rw [← Real.rpow_add hx0]
      congr 1
      ring

end ImbalancedChen.Part3.OriginalSixTailPhysicalPayment20261102
end
