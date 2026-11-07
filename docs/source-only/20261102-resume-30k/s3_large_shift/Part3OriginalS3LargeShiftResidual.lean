import ImbalancedChen.Part3OriginalS3LargeShiftShiuPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual signed-source and all-key consumer.  Reinstatement is performed on
the deleted (nonzero-shift) source, before later single-zero restoration.
Both old single zeros remain explicit in the full cutoff complement and
are paid by H's existing component theorem.  No final medium or clean-E2
estimate is supplied as a premise.
-/
namespace ImbalancedChen.Part3.OriginalS3LargeShiftResidual20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3LargeShiftLocalization20261102 OriginalS3LargeShiftShiuPayment20261102
open OriginalS3ClosePairCount20261102 OriginalS3ClosePairPayment20261102
open OriginalS3ClosePairResidual20261102 OriginalS3RoughPairGcd20261102
open OriginalS3RoughPairGcdResidual20261102
open MediumLiteralS3Stages20261028 MediumActualDiagonalDivisorPayment20261028
open MediumActualRestorationPayment20261028 MediumOriginalRestorationLogPayment20261102
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open MediumActualS3ZeroCentering20261028 OriginalSamePsiS1OwnedAtlas
open OriginalS1KeyMultiplicityPayment OriginalS1OuterCauchy20261028
open OriginalS1OuterScalePayment20261028 ActualMediumVarianceAtomBindingSourceOnly
open ActualOuterPrincipalScalePayment20261028 OriginalPrincipalVarianceInOuterCauchy20261028
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028 OriginalCompleteS123Ledger20261028
open ActualRoughContourParameters20261026b
open ImbalancedChen.Part3OriginalActualSingleZeroSource
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2ActualCenteringLedger
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2ShiftedTwelve

/-- Only r/s coprimality and the ORIGINAL close width are imposed.
The cutoff is gone; exact-product shifts are still deleted. -/
def uncutCoprimeFarDeleted (atom : MediumAtom) (z y : ℝ) (k : Key) (T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ¬Close T t ∧ t.2.1.1.Coprime t.2.2.1 then S3DeletedTerm atom z y k t else 0

def coprimeFarReinstatement (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ¬Close T t ∧ t.2.1.1.Coprime t.2.2.1 ∧ ¬ShiftCut atom H t then
      S3DeletedTerm atom z y k t else 0

theorem uncutCoprimeFarDeleted_eq_cut_add_reinstatement (atom : MediumAtom)
    (z y : ℝ) (k : Key) (H T : ℝ) :
    uncutCoprimeFarDeleted atom z y k T =
      coprimeFarFull atom z y k H T + coprimeFarReinstatement atom z y k H T := by
  unfold uncutCoprimeFarDeleted coprimeFarFull coprimeFarReinstatement
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t
  · have he := fullTerm_eq_deleted_of_shiftCut atom z y k H t hs
    by_cases hc : Close T t <;> by_cases hg : t.2.1.1.Coprime t.2.2.1 <;>
      simp [hs, hc, hg, he]
  · by_cases hc : Close T t <;> by_cases hg : t.2.1.1.Coprime t.2.2.1 <;>
      simp [hs, hc, hg]

theorem coprimeFarReinstatement_norm_le_mass (atom : MediumAtom)
    (z y : ℝ) (k : Key) (H T : ℝ) :
    ‖coprimeFarReinstatement atom z y k H T‖ ≤ largeShiftMass atom z y k H := by
  unfold coprimeFarReinstatement largeShiftMass
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro t ht
  by_cases hs : ShiftCut atom H t <;> by_cases hc : Close T t <;>
    by_cases hg : t.2.1.1.Coprime t.2.2.1 <;> simp [hs, hc, hg, norm_nonneg]

/-- Exact signs: the two zeros in largeShiftFull cancel their two
negative occurrences in restorationCorrection, leaving the genuine
deleted diagonal. No double-zero diagonal is ever added. -/
theorem primitiveS3_eq_uncut_deleted_with_signed_cutoff
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    (primitiveS3 atom z y k : ℂ) =
      uncutCoprimeFarDeleted atom z y k T + badPairDeleted atom z y k H T +
        closeDeleted atom z y k H T + actualDiagonal atom z y k +
        (largeShiftDeleted atom z y k H - coprimeFarReinstatement atom z y k H T) := by
  have hp := primitiveS3_eq_cut_coprime_bad_close_restoration hA z y k H T
  rw [largeShiftFull_eq_deleted_add_singleZeros hA z y k H] at hp
  have hr := uncutCoprimeFarDeleted_eq_cut_add_reinstatement atom z y k H T
  unfold restorationCorrection at hp
  linear_combination hp - hr

theorem largeShiftFull_norm_le_mass_and_zeros
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H : ℝ) :
    ‖largeShiftFull atom z y k H‖ ≤ largeShiftMass atom z y k H +
      ‖actualFirstZero atom z y k‖ + ‖actualSecondZero atom z y k‖ := by
  have hd : ‖largeShiftDeleted atom z y k H‖ ≤ largeShiftMass atom z y k H := by
    unfold largeShiftDeleted largeShiftMass
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro t ht
    split_ifs <;> simp
  rw [largeShiftFull_eq_deleted_add_singleZeros hA z y k H]
  exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
    (add_le_add_right (add_le_add_right hd _) _)

/-- Literal original L1 receiver after outer Cauchy; both owner-bank
multiplicities and betaL2 remain outside the source norm. -/
def allKeyL1 (atom : MediumAtom) (z : ℝ) (F : Key → ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k * F k

/-- Algebraic normalization lemma, immediately instantiated below by
the PROVED cutoff and single-zero bounds. No estimate is postulated in
the final source theorem. -/
theorem allKeyL1_le_from_local {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (hσ : 0 ≤ σ)
    (z A L : ℝ) (hL : 0 ≤ L) (hlog : 1 ≤ Real.log atom.scale)
    (F : Key → ℝ) (hF0 : ∀ k ∈ originalNumericKeys atom z, 0 ≤ F k)
    (hF : ∀ k ∈ originalNumericKeys atom z,
      F k ≤ L * actualVScale atom k / Real.log atom.scale ^ (outerPrecision B A)) :
    allKeyL1 atom z F ≤
      (12 * L * betaLogConstant ^ betaMomentOrder B * (2 * keyLogConstant) ^ 12) *
        atom.scale ^ 2 / Real.log atom.scale ^ A := by
  let p : ℕ := betaMomentOrder B
  let D : ℝ := outerPrecision B A
  let t := Real.log atom.scale
  let K := originalNumericKeys atom z
  have ht : 0 < t := by dsimp [t]; linarith
  have hV : 0 ≤ atom.V := zero_le_one.trans hA.2.1
  have hbeta0 := betaL2_nonneg atom
  have hbeta := actual_betaL2_le_scale_log atom hA hlog
  have hcard := originalNumericKeys_card_sq_le_scale_log hA hσ z hlog
  have hkeyC := keyLogConstant_pos
  have hbetaC := betaLogConstant_pos
  let E : ℝ := 6 * L * betaL2 atom * atom.V * atom.U ^ 2 / t ^ D
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hterm : ∀ k ∈ K, outerL2 atom k * F k ≤ E := by
    intro k hk
    have hY := keyY_positive hA k
    have hlocal : F k ≤ L * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D) := by
      convert hF k hk using 1 <;> simp only [actualVScale, t, D, div_eq_mul_inv, mul_inv_rev] <;> ring
    calc
      _ ≤ (6 * keyY atom k * betaL2 atom) *
          (L * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D)) :=
        mul_le_mul (outerL2_le_actual_Y_betaL2 atom k hA) hlocal (hF0 k hk) (by positivity)
      _ = E := by dsimp [E]; field_simp [hY.ne', (Real.rpow_pos_of_pos ht D).ne'] <;> ring
  calc
    _ ≤ (K.card : ℝ) ^ 2 * E := by
      unfold allKeyL1
      change (K.card : ℝ) * (∑ k ∈ K, _) ≤ _
      calc
        _ ≤ (K.card : ℝ) * (∑ _k ∈ K, E) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)
        _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((2 * keyLogConstant) ^ 12 * t ^ 12) *
        (6 * L * (2 * atom.V * betaLogConstant ^ p * t ^ p) * atom.V * atom.U ^ 2 / t ^ D) := by
      have hEup : E ≤ 6 * L * (2 * atom.V * betaLogConstant ^ p * t ^ p) *
          atom.V * atom.U ^ 2 / t ^ D := by
        dsimp [E]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg ht.le D)
        have hh := mul_le_mul_of_nonneg_left hbeta
          (show 0 ≤ 6 * L * atom.V * atom.U ^ 2 by positivity)
        convert hh using 1 <;> ring
      exact mul_le_mul hcard hEup hE (by positivity)
    _ = _ := by
      change ((2 * keyLogConstant) ^ 12 * t ^ 12) *
        (6 * L * (2 * atom.V * betaLogConstant ^ p * t ^ p) * atom.V * atom.U ^ 2 / t ^ D) =
          (12 * L * betaLogConstant ^ p * (2 * keyLogConstant) ^ 12) * atom.scale ^ 2 / t ^ A
      dsimp only [D, outerPrecision]
      rw [Real.rpow_add ht A ((p + 12 : ℕ) : ℝ), Real.rpow_natCast, pow_add]
      unfold MediumAtom.scale
      field_simp [ht.ne', (Real.rpow_pos_of_pos ht A).ne', pow_ne_zero p ht.ne'] <;> ring

def actualCutoffOrder (B : ℕ) (A : ℝ) : ℝ := cutoffOrder (outerPrecision B A)

def actualCutoffCorrection (B : ℕ) (atom : MediumAtom) (z A : ℝ) : ℝ :=
  allKeyL1 atom z (fun k =>
    2 * largeShiftMass atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
      (shiftCutoff atom (actualCutoffOrder B A)) +
    ‖actualFirstZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
    ‖actualSecondZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖)

theorem exists_actualCutoffCorrection_payment (hShiu : S2PrimitiveShiu)
    (B : ℕ) (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) (hκ : κ ≤ σ / 100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ (c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale → ∀ z : ℝ, 0 ≤ z →
      actualCutoffCorrection B atom z A ≤ C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  let D := outerPrecision B A
  obtain ⟨xm, hxm, hmass⟩ := exists_original_largeShiftMass_payment hShiu σ κ D hσ hσsmall hκ
  obtain ⟨xz, hxz, hzero⟩ := exists_original_S3_restoration_component_payments σ κ D hσ hσsmall
  let L : ℝ := 12 * momentConstant hShiu + 2
  let C : ℝ := 12 * L * betaLogConstant ^ betaMomentOrder B * (2 * keyLogConstant) ^ 12
  have hL : 0 < L := by dsimp [L]; linarith [momentConstant_pos hShiu]
  have hC : 0 < C := by
    have := betaLogConstant_pos
    have := keyLogConstant_pos
    dsimp [C]; positivity
  refine ⟨C, hC, max xm (max xz (Real.exp 1)), hxm.trans_le (le_max_left _ _), ?_⟩
  intro c0 atom hA hc0 hx z hz
  have hxm' := (le_max_left xm _).trans hx
  have htail := (le_max_right xm _).trans hx
  have hxz' := (le_max_left xz _).trans htail
  have hxE := (le_max_right xz _).trans htail
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxE
  unfold actualCutoffCorrection
  apply allKeyL1_le_from_local hA hσ.le z A L hL.le hlog
  · intro k hk
    unfold largeShiftMass
    positivity
  · intro k hk
    have hk' : k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) := by
      simpa only [originalNumericKeys, originalSmoothTrim, roughY] using hk
    have hm := hmass B c0 atom hA hc0 hxm' (strictReceiverCutoff z) (originalSmoothTrim atom) k hk'
    have hz0 := (hzero B c0 atom hA hc0 hxz' z k hz hk').2
    change 2 * largeShiftMass atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
      (shiftCutoff atom (cutoffOrder D)) + _ + _ ≤ _
    have hz1 : ‖actualFirstZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
        ‖actualSecondZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ ≤
          2 * actualVScale atom k / Real.log atom.scale ^ D := by
      simpa only [originalSmoothTrim, roughY] using hz0
    dsimp [L, D] at *
    linarith

/-- Existing J ledger with only its cutoff removed. All other original
Fourier, zero, rough and four S2 corrections retain their literal costs. -/
def unpaidOriginalCutoffFreeLedger (B : ℕ) (atom : MediumAtom) (z A : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      (‖uncutCoprimeFarDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (closeWidth atom (actualCutoffOrder B A) (outerPrecision B A)) -
          genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
          offDiagonalOmitted atom z (originalSmoothTrim atom) k +
          diagonalRetained atom z (originalSmoothTrim atom) k‖ +
        ‖offDiagonalOmitted atom z (originalSmoothTrim atom) k‖ +
        ‖diagonalRetained atom z (originalSmoothTrim atom) k‖ +
        ‖roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
        ‖genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
        2 * (‖actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖))

theorem unpaidGcdLedger_le_cutoffFree_and_correction
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z A : ℝ) :
    unpaidOriginalGcdLedger B atom z (actualCutoffOrder B A) A ≤
      unpaidOriginalCutoffFreeLedger B atom z A + actualCutoffCorrection B atom z A := by
  unfold unpaidOriginalGcdLedger unpaidOriginalCutoffFreeLedger actualCutoffCorrection allKeyL1
  rw [← mul_add, ← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
  let H := shiftCutoff atom (actualCutoffOrder B A)
  let T := closeWidth atom (actualCutoffOrder B A) (outerPrecision B A)
  let u := uncutCoprimeFarDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k T
  let r := coprimeFarReinstatement atom (strictReceiverCutoff z) (originalSmoothTrim atom) k H T
  let v := genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k +
    offDiagonalOmitted atom z (originalSmoothTrim atom) k - diagonalRetained atom z (originalSmoothTrim atom) k
  have he : coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k H T = u - r := by
    have hh := uncutCoprimeFarDeleted_eq_cut_add_reinstatement atom
      (strictReceiverCutoff z) (originalSmoothTrim atom) k H T
    dsimp [u, r]
    linear_combination -hh
  have hn : ‖coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k H T - v‖ ≤
      ‖u - v‖ + largeShiftMass atom (strictReceiverCutoff z) (originalSmoothTrim atom) k H := by
    rw [he, show u - r - v = (u - v) - r by ring]
    exact (norm_sub_le _ _).trans (add_le_add_left
      (coprimeFarReinstatement_norm_le_mass atom (strictReceiverCutoff z) (originalSmoothTrim atom) k H T) _)
  have hf := largeShiftFull_norm_le_mass_and_zeros hA (strictReceiverCutoff z) (originalSmoothTrim atom) k H
  have ecut : coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k H T - v =
      coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k H T -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
        offDiagonalOmitted atom z (originalSmoothTrim atom) k + diagonalRetained atom z (originalSmoothTrim atom) k := by
    dsimp [v]
    ring
  have euncut : u - v =
      uncutCoprimeFarDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k T -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
        offDiagonalOmitted atom z (originalSmoothTrim atom) k + diagonalRetained atom z (originalSmoothTrim atom) k := by
    dsimp [u, v]
    ring
  rw [ecut, euncut] at hn
  dsimp [H, T] at hn hf
  linarith

/-- Final actual consumer: the earliest cutoff and its reinstatement
are paid at the original full residual. The final medium estimate and
the remaining unpaid ledger are not hypotheses. -/
theorem exists_actualResidualFunctional_cutoff_paid (hShiu : S2PrimitiveShiu)
    (B : ℕ) (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) (hκ : κ ≤ σ / 100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ (c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
      ∀ z : ℝ, roughZ atom.scale ≤ z →
      actualResidualFunctional atom z ≤ unpaidOriginalCutoffFreeLedger B atom z A +
        C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨Cg, hCg, xg, hxg, hg⟩ := exists_actualResidualFunctional_gcd_paid
    B σ κ (actualCutoffOrder B A) A hσ hσsmall
  obtain ⟨Cc, hCc, xc, hxc, hc⟩ := exists_actualCutoffCorrection_payment hShiu B σ κ A hσ hσsmall hκ
  refine ⟨Cg + Cc, add_pos hCg hCc, max xg xc, hxg.trans_le (le_max_left _ _), ?_⟩
  intro c0 atom hA hc0 hx z hzr
  have hx0 : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  have hz : 0 ≤ z := ((Real.rpow_pos_of_pos hx0 _).trans_le hzr).le
  have h1 := hg c0 atom hA hc0 ((le_max_left _ _).trans hx) z hzr
  have h2 := hc c0 atom hA hc0 ((le_max_right _ _).trans hx) z hz
  have h3 := unpaidGcdLedger_le_cutoffFree_and_correction hA z A
  calc
    _ ≤ unpaidOriginalGcdLedger B atom z (actualCutoffOrder B A) A +
        Cg * atom.scale ^ 2 / Real.log atom.scale ^ A := h1
    _ ≤ unpaidOriginalCutoffFreeLedger B atom z A +
        Cc * atom.scale ^ 2 / Real.log atom.scale ^ A +
        Cg * atom.scale ^ 2 / Real.log atom.scale ^ A := by linarith
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalS3LargeShiftResidual20261102
