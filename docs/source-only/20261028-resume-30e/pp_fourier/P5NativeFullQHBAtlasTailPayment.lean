import ImbalancedChen.P5ActualHBAtlasScalarInventory

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One cutoff for the actual original dyadic/rank/HB inventory, after the
full native q-sum and all fixed losses have been paid. The original
modulus mark sum is inside nativeRho, so no marked-prime mass is assumed
or counted twice. The geometric source cap is ceil(Family.upper*T).
This is an actual Fourier tail theorem. It does not assert the retained
arithmetic modes or the final original prime-product identity.
-/
namespace ImbalancedChen.P5Z.NativeFullQHBAtlasTailPayment
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open AdmissibleAllRankIntegerGeometricFamily ActualAllRankOccurrenceFourierBridge
open ActualHBPostModulusLogCutoff CompleteProductTailDivisorBudgets
open NativeFullQActualHBTail ActualHBAtlasScalarInventory
open HBRightClosedDyadicRoles ExactOriginalSmoothDyadicPartition

theorem paymentExponent_mono {m n : ℕ} (hmn : m ≤ n) (J : ℕ) :
    paymentExponent m J ≤ paymentExponent n J := by
  have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hmn
  have hp2 := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
    (Nat.mul_le_mul_left 2 hmn)
  unfold paymentExponent
  omega

def atlasCutoff (kStar : ℕ) (X : ℝ) (accuracy derivativeOrder : ℕ) : ℝ :=
  selectedCutoff X (accuracy + 7 * kStar) derivativeOrder (paymentExponent (6 * kStar) 0)

theorem atlasCutoff_one_le (kStar : ℕ) {X : ℝ} (hX : 1 ≤ X) (accuracy E : ℕ) :
    1 ≤ atlasCutoff kStar X accuracy E := selectedCutoff_one_le hX _ _ _

/-- Raise the requested accuracy by the fixed difference of moment
orders. Thus every dimension, including zero, uses exactly ONE H. -/
theorem exists_native_common_cutoff_tail {kStar : ℕ} (A : Family kStar) :
    ∃ CD CC : ℝ, ∃ E : ℕ, 0 ≤ CD ∧ 0 < CC ∧
      ∀ (precision T : ℕ) (eta : ℚ) (mask : ℕ × ℕ → Prop)
        (k : Fin (kStar + 1)) (m : ℕ) (owner : Fin m → Fin k.val)
        (blocks : Fin m → Block) (R : Fin k.val → ℝ) (κ₀ Z : ℝ)
        (y : Fin m → ℝ) (roles : Fin m → ActualRoughHeathBrownWords.Role)
        (cap : ℕ) (X : ℝ) (accuracy : ℕ),
        1 < T → 0 < eta → m ≤ 6 * kStar → (∀ i, 0 < R i) →
        1 ≤ X → (T : ℝ) ≤ X → (cap : ℝ) ≤ 6 * X →
        ‖actualNativeTail A precision T eta mask k owner blocks R κ₀ Z y roles cap
          (atlasCutoff kStar X accuracy E)‖ ≤
          (6 * kStar : ℕ) * CD * (massConstant 0 + CC) * X /
            logScale X ^ (accuracy + 7 * kStar + 3) := by
  obtain ⟨CD, CC, E, hCD, hCC, htail⟩ := exists_native_actual_role_tail A
  refine ⟨CD, CC, E, hCD, hCC, ?_⟩
  intro precision T eta mask k m owner blocks R κ₀ Z y roles cap X accuracy hT heta hm hR hX hTX hcap
  let extra := paymentExponent (6 * kStar) 0 - paymentExponent m 0
  have hpay := paymentExponent_mono hm 0
  have hH : selectedCutoff X (accuracy + 7 * kStar + extra) E (paymentExponent m 0) =
      atlasCutoff kStar X accuracy E := by
    unfold atlasCutoff selectedCutoff
    congr 1
    dsimp [extra]
    omega
  have ht := htail precision T eta mask k m owner blocks R κ₀ Z y roles cap X
    (accuracy + 7 * kStar + extra) hT heta hm hR hX hTX hcap
  change ‖actualNativeTail A precision T eta mask k owner blocks R κ₀ Z y roles cap
    (selectedCutoff X (accuracy + 7 * kStar + extra) E (paymentExponent m 0))‖ ≤ _ at ht
  rw [hH] at ht
  have hL : 0 < logScale X := lt_of_lt_of_le zero_lt_one (logScale_one_le hX)
  apply ht.trans
  apply div_le_div_of_nonneg_left
  · have := hCD
    have := hCC.le
    dsimp [massConstant]
    positivity
  · positivity
  · exact pow_le_pow_right₀ (logScale_one_le hX) (by omega)

/-- Totalized only outside the actual bank. On every actual piece the
length proof is supplied by hbBank_spec, not a proposed Family cover. -/
def pieceError {kStar : ℕ} (A : Family kStar) (precision T : ℕ)
    (eta : ℚ) (mask : ℕ × ℕ → Prop) (k : Fin (kStar + 1))
    (js : List ℕ) (cs : List Choice) (κ₀ Z : ℝ) (cap : ℕ) (H : ℝ) : ℂ :=
  if hlen : cs.length = k.val then
    actualNativeTail A precision T eta mask k (rankOwner hlen) (pieceBlocks cs)
      (originalR js k.val) κ₀ Z (occurrenceCutoff hlen js) (pieceRoles cs) cap H
  else 0

def atlasTail {kStar : ℕ} (A : Family kStar) (precision T : ℕ)
    (eta : ℚ) (mask : ℕ × ℕ → Prop) (κ₀ Z : ℝ) (cap : ℕ) (H : ℝ) : ℂ :=
  ∑ k : Fin (kStar + 1), ∑ js ∈ chartBank cap k.val, ∑ cs ∈ hbBank cap k.val,
    hbScalar cs * pieceError A precision T eta mask k js cs κ₀ Z cap H

/-- Derived full native tail after the actual signed HB scalars, all
unit/nonunit dyadic occurrences, original dyadic chart labels and ranks.
No arbitrary H, rhoMass, scalar mass, or desired tail bound is a premise. -/
theorem exists_native_atlas_tail {kStar : ℕ} (A : Family kStar) :
    ∃ CD CC : ℝ, ∃ E : ℕ, 0 ≤ CD ∧ 0 < CC ∧
      ∀ (precision T : ℕ) (eta : ℚ) (mask : ℕ × ℕ → Prop)
        (κ₀ Z : ℝ) (cap : ℕ) (X : ℝ) (accuracy : ℕ),
        1 < T → 0 < eta → 1 ≤ X → (T : ℝ) ≤ X → (cap : ℝ) ≤ 6 * X →
        ‖atlasTail A precision T eta mask κ₀ Z cap (atlasCutoff kStar X accuracy E)‖ ≤
          inventoryConstant kStar * ((6 * kStar : ℕ) * CD * (massConstant 0 + CC)) * X /
            logScale X ^ (accuracy + 3) := by
  obtain ⟨CD, CC, E, hCD, hCC, htail⟩ := exists_native_common_cutoff_tail A
  refine ⟨CD, CC, E, hCD, hCC, ?_⟩
  intro precision T eta mask κ₀ Z cap X accuracy hT heta hX hTX hcap
  let H := atlasCutoff kStar X accuracy E
  let Cerror : ℝ := (6 * kStar : ℕ) * CD * (massConstant 0 + CC)
  have hCerror : 0 ≤ Cerror := by dsimp [Cerror, massConstant]; positivity
  have hpiece (k : Fin (kStar + 1)) (js : List ℕ) (cs : List Choice)
      (hcs : cs ∈ hbBank cap k.val) :
      ‖pieceError A precision T eta mask k js cs κ₀ Z cap H‖ ≤
        Cerror * X / logScale X ^ (accuracy + 7 * kStar + 3) := by
    obtain ⟨hlen, hroles, hdim⟩ := hbBank_spec cap k.val cs hcs
    have hm : dimension cs ≤ 6 * kStar := hdim.trans (Nat.mul_le_mul_left 6 (by omega))
    simp only [pieceError, dif_pos hlen]
    exact htail precision T eta mask k (dimension cs) (rankOwner hlen) (pieceBlocks cs)
      (originalR js k.val) κ₀ Z (occurrenceCutoff hlen js) (pieceRoles cs) cap X accuracy
      hT heta hm (originalR_pos js k.val) hX hTX hcap
  have hL : 0 < logScale X := lt_of_lt_of_le zero_lt_one (logScale_one_le hX)
  unfold atlasTail
  calc
    _ ≤ ∑ k : Fin (kStar + 1), ∑ js ∈ chartBank cap k.val, ∑ cs ∈ hbBank cap k.val,
        ‖hbScalar cs‖ * ‖pieceError A precision T eta mask k js cs κ₀ Z cap H‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro js hjs
      simpa only [norm_mul] using norm_sum_le (hbBank cap k.val)
        (fun cs => hbScalar cs * pieceError A precision T eta mask k js cs κ₀ Z cap H)
    _ ≤ ∑ k : Fin (kStar + 1), ∑ _js ∈ chartBank cap k.val, ∑ cs ∈ hbBank cap k.val,
        ‖hbScalar cs‖ * (Cerror * X / logScale X ^ (accuracy + 7 * kStar + 3)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro js hjs
      apply Finset.sum_le_sum
      intro cs hcs
      exact mul_le_mul_of_nonneg_left (hpiece k js cs hcs) (norm_nonneg _)
    _ = (∑ k : Fin (kStar + 1), ∑ _js ∈ chartBank cap k.val,
          ∑ cs ∈ hbBank cap k.val, ‖hbScalar cs‖) *
        (Cerror * X / logScale X ^ (accuracy + 7 * kStar + 3)) := by
      simp_rw [← Finset.sum_mul]
    _ ≤ (inventoryConstant kStar * logScale X ^ (7 * kStar)) *
        (Cerror * X / logScale X ^ (accuracy + 7 * kStar + 3)) :=
      mul_le_mul_of_nonneg_right (complete_inventory_mass_le kStar cap hX hcap) (by positivity)
    _ = inventoryConstant kStar * Cerror * X / logScale X ^ (accuracy + 3) := by
      rw [show accuracy + 7 * kStar + 3 = (accuracy + 3) + 7 * kStar by omega, pow_add]
      field_simp [hL.ne']
      ring

def sourceCap {kStar : ℕ} (A : Family kStar) (T : ℕ) : ℕ := Nat.ceil (A.upper * (T : ℝ))

def scaleFactor {kStar : ℕ} (A : Family kStar) : ℝ := max 1 A.upper + 1

def completeScale {kStar : ℕ} (A : Family kStar) (T : ℕ) : ℝ := scaleFactor A * T

theorem actual_source_geometry {kStar : ℕ} (A : Family kStar) {T : ℕ} (hT : 1 < T) :
    1 ≤ completeScale A T ∧ (T : ℝ) ≤ completeScale A T ∧
      (sourceCap A T : ℝ) ≤ 6 * completeScale A T := by
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hS : 1 ≤ scaleFactor A := by unfold scaleFactor; linarith [le_max_left 1 A.upper]
  have hTX : (T : ℝ) ≤ completeScale A T := by
    unfold completeScale
    exact le_mul_of_one_le_left (by positivity) hS
  have hceil : (sourceCap A T : ℝ) ≤ A.upper * (T : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg A.upper_pos.le (Nat.cast_nonneg T))).le
  have hupper : A.upper ≤ max 1 A.upper := le_max_right _ _
  have hcap : (sourceCap A T : ℝ) ≤ completeScale A T := by
    unfold completeScale scaleFactor
    nlinarith
  exact ⟨hTR.trans hTX, hTX, by linarith⟩

/-- The source cap is fixed by the original Family. Its entire genuine
HB/dyadic/rank tail is O_A(T/log^accuracy T), with one fixed exponent E
chosen before accuracy and before any target, mask or native precision.
All original native modulus marks are included inside the same rho. -/
theorem exists_native_source_atlas_tail {kStar : ℕ} (A : Family kStar) :
    ∃ C : ℝ, ∃ E : ℕ, 0 ≤ C ∧
      ∀ (accuracy precision T : ℕ) (eta : ℚ) (mask : ℕ × ℕ → Prop) (κ₀ Z : ℝ),
        1 < T → 0 < eta →
        ‖atlasTail A precision T eta mask κ₀ Z (sourceCap A T)
          (atlasCutoff kStar (completeScale A T) accuracy E)‖ ≤
          C * (T : ℝ) / logScale (T : ℝ) ^ (accuracy + 3) := by
  obtain ⟨CD, CC, E, hCD, hCC, htail⟩ := exists_native_atlas_tail A
  let Cbase : ℝ := inventoryConstant kStar * ((6 * kStar : ℕ) * CD * (massConstant 0 + CC))
  have hCbase : 0 ≤ Cbase := by
    have := inventoryConstant_nonneg kStar
    dsimp [Cbase, massConstant]
    positivity
  have hS : 0 ≤ scaleFactor A := by unfold scaleFactor; linarith [le_max_left 1 A.upper]
  refine ⟨Cbase * scaleFactor A, E, mul_nonneg hCbase hS, ?_⟩
  intro accuracy precision T eta mask κ₀ Z hT heta
  obtain ⟨hX, hTX, hcap⟩ := actual_source_geometry A hT
  have ht := htail precision T eta mask κ₀ Z (sourceCap A T) (completeScale A T)
    accuracy hT heta hX hTX hcap
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hL : 0 < logScale (T : ℝ) := lt_of_lt_of_le zero_lt_one (logScale_one_le hTR)
  have hlog : logScale (T : ℝ) ≤ logScale (completeScale A T) := by
    unfold logScale
    exact add_le_add_left (Real.log_le_log (by positivity) (by linarith)) _
  apply ht.trans
  change Cbase * completeScale A T / _ ≤ _
  rw [completeScale, ← mul_assoc]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ (zero_le_one.trans (logScale_one_le hTR)) hlog _)

end
end ImbalancedChen.P5Z.NativeFullQHBAtlasTailPayment
