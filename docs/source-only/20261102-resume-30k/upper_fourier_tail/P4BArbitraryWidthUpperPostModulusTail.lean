import ImbalancedChen.P4BArbitraryWidthUpperBlockGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Post-COMPLETE-modulus Fourier payment for the same physical upper rho
and every legal width. The upper profile, derivative cost, full rectangle
scale, HB slot norms and divisor moments are proved, not caller inputs.
Only the original active physical support gate remains explicit.
-/
namespace ImbalancedChen.P4BArbitraryWidthUpperPostModulusTail
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open P4BOuterRampRoughness P4BArbitraryWidthUpperBlockGeometry
open P5Z.HBRightClosedDyadicRoles P5Z.ActualRoughHeathBrownWords
open P5Z.ActualHBPostModulusLogCutoff P5Z.ActualCompleteModulusFourierTail
open P5Z.CompleteProductTailDivisorBudgets P5Z.ActualEuclideanPhysicalFourier
open P5Z.ActualAllRankOccurrenceFourierBridge
open ImbalancedChen.PrimeProducts

variable {m : ℕ}

def upperRho (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N : ℕ) : ℕ → ℂ :=
  fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)

/-- Enumeration caps may include zero coefficients. Removing only those
rows is an exact equality, and does not change either count or exact mean. -/
def activeQ (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (attachedUpperModuli nu r epsilon retain cap N).filter
    (fun q => attachedUpperCoefficient nu r epsilon retain cap N q ≠ 0)

theorem upperRho_norm (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N q : ℕ) : ‖upperRho nu r epsilon retain cap N q‖ ≤ 1 := by
  simpa only [upperRho, attachedUpperCoefficient, Complex.norm_real, Real.norm_eq_abs] using
    actualSmallRoughRho_abs_le_one (retain N) N (cap N)
      ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
      ((N : ℝ) ^ (nu * epsilon)) q

theorem activeQ_squarefree (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N : ℕ) {q : ℕ} (hq : q ∈ activeQ nu r epsilon retain cap N) :
    Squarefree q :=
  actualSmallRoughModuli_squarefree (retain N) N (cap N) _ _ (Finset.mem_filter.mp hq).1

theorem discrepancy_activeQ {ι : Type*} (s : Finset ι) (product : ι → ℕ)
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N : ℕ) (w : ι → ℂ) :
    MellinInsertion20261028.exactDiscrepancy s
      (attachedUpperModuli nu r epsilon retain cap N) (upperRho nu r epsilon retain cap N)
      product N w =
    MellinInsertion20261028.exactDiscrepancy s
      (activeQ nu r epsilon retain cap N) (upperRho nu r epsilon retain cap N)
      product N w := by
  unfold MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  rw [activeQ, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : attachedUpperCoefficient nu r epsilon retain cap N q = 0
  · simp [h, upperRho]
  · simp [h]

/-- This is a support condition on the actual coefficient, not on the
larger enumeration set and not a tail, mass or distribution estimate. -/
def Supported (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N D : ℕ) : Prop :=
  ∀ q ∈ attachedUpperModuli nu r epsilon retain cap N,
    attachedUpperCoefficient nu r epsilon retain cap N q ≠ 0 → q ≤ D

theorem activeQ_subset (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N D : ℕ) (hSupport : Supported nu r epsilon retain cap N D) :
    effectiveModuli (activeQ nu r epsilon retain cap N) ⊆ Finset.Icc 1 D := by
  intro q hq
  have ha := Finset.mem_of_mem_erase hq
  have hs := activeQ_squarefree nu r epsilon retain cap N ha
  have hf := Finset.mem_filter.mp ha
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hs.ne_zero, hSupport q hf.1 hf.2⟩

def originalAtom (b kappa width : ℝ) (N : ℕ) (owner : Fin m → Fin 2)
    (bs : Fin m → Block) (R : Fin 2 → ℝ) (kappa0 Z : ℝ)
    (y : Fin m → ℝ) (rs : Fin m → Role) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (rectangle bs)
    (attachedUpperModuli nu r epsilon retain cap N) (upperRho nu r epsilon retain cap N)
    completeProduct N (fun n => hbSlots Z y rs n *
      (integerProfile b kappa width N owner R kappa0 n : ℂ))

def retainedAtom (b kappa width : ℝ) (N : ℕ) (owner : Fin m → Fin 2)
    (bs : Fin m → Block) (R : Fin 2 → ℝ) (kappa0 Z : ℝ)
    (y : Fin m → ℝ) (rs : Fin m → Role) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (H : ℝ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (rectangle bs)
    (attachedUpperModuli nu r epsilon retain cap N) (upperRho nu r epsilon retain cap N)
    completeProduct N (fun n => hbSlots Z y rs n *
      truncatedPhysical m (blockChart b kappa width N owner bs R kappa0) H
        (WithLp.toLp 2 (logOccurrence (scales bs) n)))

/-- The true full-Q mass is bounded BEFORE Fourier truncation. Both
original-group logs stay in integerProfile, never in rho or hbSlots. -/
theorem actual_upper_mass {b kappa nu r width : ℝ} {N : ℕ}
    (hb : 0 < b) (hkappa : 0 < kappa) (hnu : 0 < nu) (hr : 0 < r)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - nu * r)
    (owner : Fin m → Fin 2) (bs : Fin m → Block) (R : Fin 2 → ℝ) (kappa0 : ℝ)
    (hm : m ≤ 12) (hN : 0 < N) (hMeet : Meets b kappa width N owner bs R kappa0)
    (Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role) (epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (D : ℕ)
    (hD : 1 ≤ D) (hDX : (D : ℝ) ≤ 6 * countingScale N)
    (hSupport : Supported nu r epsilon retain cap N D) :
    fullTailMass (rectangle bs) (hbSlots Z y rs) completeProduct
      (activeQ nu r epsilon retain cap N) (upperRho nu r epsilon retain cap N) N 0 1 ≤
      (massConstant 0 * countingScale N + (D : ℝ) * tau N ^ m) *
        logScale (countingScale N) ^ paymentExponent m 0 := by
  have h := actual_hb_mass_polylog (rectangle bs) Z y rs
    (countingScale_one_le hN) N D 0 hN (target_le_countingScale N) hD hDX
    (fun n hn => by
      obtain ⟨hp, hbnd⟩ := rectangle_counting_scale hb hkappa hnu hr hwidth hgap
        owner bs R kappa0 hm hMeet hn
      refine ⟨hp, hbnd.trans ?_⟩
      nlinarith [countingScale_one_le hN])
    (activeQ nu r epsilon retain cap N) (upperRho nu r epsilon retain cap N)
    (activeQ_subset nu r epsilon retain cap N D hSupport)
    (fun q hq => activeQ_squarefree nu r epsilon retain cap N (Finset.mem_of_mem_erase hq))
    1 (by norm_num)
    (fun q hq => by simpa only [pow_zero, mul_one] using upperRho_norm nu r epsilon retain cap N q)
  simpa only [one_mul] using h

/-- This fixed logarithmic cutoff depends only on rank, requested
accuracy and target. Width remains an explicit constant at each precision. -/
def cutoff (N m accuracy : ℕ) : ℝ :=
  selectedCutoff (countingScale N) accuracy 0 (paymentExponent m 0)

theorem exists_actual_upper_postmodulus_tail :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      0 < b → b ≤ 1 → 0 < kappa → 0 < nu → 0 < r → 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ (N m : ℕ) (owner : Fin m → Fin 2) (bs : Fin m → Block)
        (R : Fin 2 → ℝ) (kappa0 Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role)
        (epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (D accuracy : ℕ),
      0 < N → (∀ i, 0 < R i) → m ≤ 12 → Meets b kappa width N owner bs R kappa0 →
      1 ≤ D → (D : ℝ) ≤ 6 * countingScale N → Supported nu r epsilon retain cap N D →
      ‖originalAtom b kappa width N owner bs R kappa0 Z y rs nu r epsilon retain cap -
        retainedAtom b kappa width N owner bs R kappa0 Z y rs nu r epsilon retain cap
          (cutoff N m accuracy)‖ ≤
        ((m : ℝ) * C / width^24) *
          (massConstant 0 * countingScale N + (D : ℝ) * tau N ^ m) /
            logScale (countingScale N) ^ (accuracy+3) := by
  obtain ⟨C, hC, htail⟩ := exists_actual_upper_cube_tail
  refine ⟨C, hC, ?_⟩
  intro b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
    N m owner bs R kappa0 Z y rs epsilon retain cap D accuracy hN hR hm hMeet hD hDX hSupport
  let X := countingScale N
  let H := cutoff N m accuracy
  have hX : 1 ≤ X := countingScale_one_le hN
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (selectedCutoff_one_le hX accuracy 0 _)
  have herr : ∀ n ∈ rectangle bs,
      ‖(integerProfile b kappa width N owner R kappa0 n : ℂ) -
        truncatedPhysical m (blockChart b kappa width N owner bs R kappa0) H
          (WithLp.toLp 2 (logOccurrence (scales bs) n))‖ ≤
        ((m : ℝ) * C / width^24) / H := by
    intro n hn
    rw [← blockChart_integer b kappa width N owner bs R kappa0 hn]
    have ht := htail b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
      N m owner bs R kappa0 H hN hR hm hH (WithLp.toLp 2 (logOccurrence (scales bs) n))
    simpa only [mul_div_assoc] using ht
  have hd := discrepancy_tail_le (rectangle bs) (hbSlots Z y rs) completeProduct
    (activeQ nu r epsilon retain cap N) (upperRho nu r epsilon retain cap N) N 0 1
    (((m : ℝ)*C/width^24)/H) (by norm_num) (by positivity)
    (fun q hq => by simpa only [pow_zero, mul_one] using upperRho_norm nu r epsilon retain cap N q)
    (fun n => (integerProfile b kappa width N owner R kappa0 n : ℂ))
    (fun n => truncatedPhysical m (blockChart b kappa width N owner bs R kappa0) H
      (WithLp.toLp 2 (logOccurrence (scales bs) n))) herr
  have hmass := actual_upper_mass hb hkappa hnu hr hwidth hgap owner bs R kappa0
    hm hN hMeet Z y rs epsilon retain cap D hD hDX hSupport
  unfold originalAtom retainedAtom
  rw [discrepancy_activeQ, discrepancy_activeQ]
  apply hd.trans
  calc
    _ ≤ (((m : ℝ)*C/width^24)/H) *
        ((massConstant 0*X + (D : ℝ)*tau N^m)*logScale X^(paymentExponent m 0)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (massConstant 0*X + (D : ℝ)*tau N^m) *
        ((((m : ℝ)*C/width^24)*logScale X^0/
          selectedCutoff X accuracy 0 (paymentExponent m 0))*logScale X^(paymentExponent m 0)) := by
      dsimp [H, cutoff, X]
      ring
    _ = _ := by rw [selected_cutoff_payment hX]; ring

/-- The original subunit physical support pays the complete-product=N
collision. No tau(0), residual-only modulus, or cap cost for the mean. -/
theorem exists_actual_upper_log_saving (theta : ℝ) (htheta : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      0 < b → b ≤ 1 → 0 < kappa → 0 < nu → 0 < r → 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ (N m : ℕ) (owner : Fin m → Fin 2) (bs : Fin m → Block)
        (R : Fin 2 → ℝ) (kappa0 Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role)
        (epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (D accuracy : ℕ),
      0 < N → (∀ i, 0 < R i) → m ≤ 12 → Meets b kappa width N owner bs R kappa0 →
      1 ≤ D → (D : ℝ) ≤ (N : ℝ)^theta → Supported nu r epsilon retain cap N D →
      ‖originalAtom b kappa width N owner bs R kappa0 Z y rs nu r epsilon retain cap -
        retainedAtom b kappa width N owner bs R kappa0 Z y rs nu r epsilon retain cap
          (cutoff N m accuracy)‖ ≤
        (C / width^24) * (N : ℝ) / logScale (countingScale N) ^ (accuracy+3) := by
  obtain ⟨CD, hCD, htail⟩ := exists_actual_upper_postmodulus_tail
  obtain ⟨CC, hCC, hcollision⟩ := exists_uniform_exact_product_payment 2 theta htheta
  let C := 12*CD*(scaleFactor*massConstant 0+CC)
  refine ⟨C, by dsimp [C, scaleFactor, massConstant]; positivity, ?_⟩
  intro b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
    N m owner bs R kappa0 Z y rs epsilon retain cap D accuracy hN hR hm hMeet hD hDtheta hSupport
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hDN : (D : ℝ) ≤ N := hDtheta.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNR htheta.le)
  have hDX : (D : ℝ) ≤ 6*countingScale N := by
    nlinarith [target_le_countingScale N, countingScale_one_le hN]
  have ht := htail b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
    N m owner bs R kappa0 Z y rs epsilon retain cap D accuracy hN hR hm hMeet hD hDX hSupport
  have hc := hcollision m N D (by simpa using hm) hN hDtheta
  have hmR : (m : ℝ) ≤ 12 := by exact_mod_cast hm
  have hlog : 0 < logScale (countingScale N) :=
    lt_of_lt_of_le zero_lt_one (logScale_one_le (countingScale_one_le hN))
  have hmass : massConstant 0*countingScale N + (D : ℝ)*tau N^m ≤
      (scaleFactor*massConstant 0+CC)*(N : ℝ) := by
    dsimp [countingScale]
    nlinarith
  apply ht.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ((m : ℝ)*CD/width^24)*((scaleFactor*massConstant 0+CC)*(N : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (12*CD/width^24)*((scaleFactor*massConstant 0+CC)*(N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmR hCD) (by positivity))
      dsimp [scaleFactor, massConstant]
      positivity
    _ = (C/width^24)*(N : ℝ) := by dsimp [C]; ring

/-- An inactive full rectangle has exactly zero ORIGINAL discrepancy.
Only entire zero rows are omitted; no product wall cuts a Fourier carrier. -/
theorem originalAtom_zero_of_not_meets
    (b kappa width : ℝ) (N : ℕ) (owner : Fin m → Fin 2)
    (bs : Fin m → Block) (R : Fin 2 → ℝ) (kappa0 Z : ℝ)
    (y : Fin m → ℝ) (rs : Fin m → Role) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (h : ¬ Meets b kappa width N owner bs R kappa0) :
    originalAtom b kappa width N owner bs R kappa0 Z y rs nu r epsilon retain cap = 0 := by
  unfold originalAtom MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
  apply Finset.sum_eq_zero
  intro n hn
  have hz : integerProfile b kappa width N owner R kappa0 n = 0 := by
    by_contra hnz
    exact h ⟨n, hn, hnz⟩
  simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul]

/-- All ordered row labels are retained as labels. Inactive rows have
zero synthesis, and active rows use the SAME full rectangle transform. -/
def retainedActiveAtom (b kappa width : ℝ) (N : ℕ) (owner : Fin m → Fin 2)
    (bs : Fin m → Block) (R : Fin 2 → ℝ) (kappa0 Z : ℝ)
    (y : Fin m → ℝ) (rs : Fin m → Role) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (H : ℝ) : ℂ :=
  if Meets b kappa width N owner bs R kappa0 then
    retainedAtom b kappa width N owner bs R kappa0 Z y rs nu r epsilon retain cap H
  else 0

/-- The every-row form has no Meets/profile/tail premise. It keeps every
original label and derives the inactive case from the original source. -/
theorem exists_every_row_upper_log_saving (theta : ℝ) (htheta : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      0 < b → b ≤ 1 → 0 < kappa → 0 < nu → 0 < r → 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ (N m : ℕ) (owner : Fin m → Fin 2) (bs : Fin m → Block)
        (R : Fin 2 → ℝ) (kappa0 Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role)
        (epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (D accuracy : ℕ),
      0 < N → (∀ i, 0 < R i) → m ≤ 12 →
      1 ≤ D → (D : ℝ) ≤ (N : ℝ)^theta → Supported nu r epsilon retain cap N D →
      ‖originalAtom b kappa width N owner bs R kappa0 Z y rs nu r epsilon retain cap -
        retainedActiveAtom b kappa width N owner bs R kappa0 Z y rs nu r epsilon retain cap
          (cutoff N m accuracy)‖ ≤
        (C / width^24) * (N : ℝ) / logScale (countingScale N) ^ (accuracy+3) := by
  obtain ⟨C, hC, htail⟩ := exists_actual_upper_log_saving theta htheta
  refine ⟨C, hC, ?_⟩
  intro b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
    N m owner bs R kappa0 Z y rs epsilon retain cap D accuracy hN hR hm hD hDtheta hSupport
  by_cases hMeet : Meets b kappa width N owner bs R kappa0
  · rw [retainedActiveAtom, if_pos hMeet]
    exact htail b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
      N m owner bs R kappa0 Z y rs epsilon retain cap D accuracy
      hN hR hm hMeet hD hDtheta hSupport
  · rw [retainedActiveAtom, if_neg hMeet,
      originalAtom_zero_of_not_meets b kappa width N owner bs R kappa0 Z y rs
        nu r epsilon retain cap hMeet, sub_self, norm_zero]
    have hlog : 0 < logScale (countingScale N) :=
      lt_of_lt_of_le zero_lt_one (logScale_one_le (countingScale_one_le hN))
    positivity

end
end ImbalancedChen.P4BArbitraryWidthUpperPostModulusTail
