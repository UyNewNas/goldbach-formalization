import ImbalancedChen.P5CompleteProductTailDivisorBudgets
import ImbalancedChen.P5ActualRoughHeathBrownWords
import ImbalancedChen.Part3PolynomialResidueDivisorBound

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual ordered HB tuple fibres, complete-modulus mass and a preselected
polylogarithmic Fourier cutoff. The cutoff exponent is chosen from fixed
orders and requested accuracy, never from a finite target's total mass.
-/
namespace ImbalancedChen.P5Z.ActualHBPostModulusLogCutoff
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open ActualCompleteModulusFourierTail CompleteProductTailDivisorBudgets
open AllRankCoordinateFourierIBP AllRankMixedOperatorBudget
open AdmissibleAllRankIntegerGeometricFamily ActualEuclideanPhysicalFourier
open ActualAllRankOccurrenceFourierBridge
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {m : ℕ}

def completeProduct (n : Fin m → ℕ) : ℕ := ∏ a, n a

/-- This uses the actual ordered tuple carrier. Repeated numerical
factors and repeated complete products keep their separate positions. -/
theorem hb_fibre_card_le (s : Finset (Fin m → ℕ)) (b : ℕ) (hb : 0 < b) :
    (s.filter (fun n => completeProduct n = b)).card ≤ b.divisors.card ^ m := by
  have hsub : s.filter (fun n => completeProduct n = b) ⊆
      Fintype.piFinset (fun _ : Fin m => b.divisors) := by
    intro n hn
    apply Fintype.mem_piFinset.mpr
    intro a
    have hd : n a ∣ completeProduct n := Finset.dvd_prod_of_mem n (Finset.mem_univ a)
    exact Nat.mem_divisors.mpr ⟨by simpa only [(Finset.mem_filter.mp hn).2] using hd, hb.ne'⟩
  exact (Finset.card_le_card hsub).trans_eq (by simp)

theorem hb_fibreMass_le (s : Finset (Fin m → ℕ)) (β : (Fin m → ℕ) → ℂ)
    (Bβ : ℝ) (hBβ : 0 ≤ Bβ) (hβ : ∀ n ∈ s, ‖β n‖ ≤ Bβ)
    (b : ℕ) (hb : 0 < b) :
    fibreMass s β completeProduct b ≤ Bβ * tau b ^ m := by
  calc
    fibreMass s β completeProduct b ≤ ∑ n ∈ s with completeProduct n = b, Bβ :=
      Finset.sum_le_sum (fun n hn => hβ n (Finset.mem_filter.mp hn).1)
    _ = ((s.filter (fun n => completeProduct n = b)).card : ℝ) * Bβ := by simp
    _ ≤ (b.divisors.card : ℝ) ^ m * Bβ := by
      apply mul_le_mul_of_nonneg_right _ hBβ
      exact_mod_cast hb_fibre_card_le s b hb
    _ = Bβ * tau b ^ m := by unfold tau; ring

theorem tupleMass_eq_fibres (s : Finset (Fin m → ℕ)) (β : (Fin m → ℕ) → ℂ) :
    tupleMass s β = ∑ b ∈ s.image completeProduct, fibreMass s β completeProduct b := by
  exact (Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image completeProduct)
    (g := completeProduct) (fun n hn => Finset.mem_image_of_mem completeProduct hn)
    (fun n => ‖β n‖)).symm

/-- All the actual tuple multiplicity is collapsed to the COMPLETE b
before the elementary moment is used. There is no sharp long-slot cut. -/
theorem hb_nonzeroMoment_le (s : Finset (Fin m → ℕ)) (β : (Fin m → ℕ) → ℂ)
    (Bβ : ℝ) (hBβ : 0 ≤ Bβ) (hβ : ∀ n ∈ s, ‖β n‖ ≤ Bβ)
    {X : ℝ} (hX : 1 ≤ X) (T S : ℕ) (hS : 1 ≤ S) (hT : (T : ℝ) ≤ X)
    (hs : ∀ n ∈ s, 1 ≤ completeProduct n ∧ (completeProduct n : ℝ) ≤ 6 * X) :
    nonzeroMoment s β completeProduct T S ≤
      Bβ * ((3 + 13 * (2 ^ (2 * S) : ℕ) : ℝ) * X *
        logScale X ^ (2 ^ (2 * m) + 2 ^ (2 * S))) := by
  rw [nonzeroMoment_eq_fibres]
  have hsub : (s.image completeProduct).filter (fun b => b ≠ T) ⊆ completeNonzero X T := by
    intro b hb
    obtain ⟨⟨n, hn, rfl⟩, hbne⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(hs n hn).1, Nat.le_floor (hs n hn).2⟩, hbne⟩
  calc
    (∑ b ∈ s.image completeProduct with b ≠ T,
        fibreMass s β completeProduct b * tau (P5OriginalPrimeEndpoint.distance T b) ^ S) ≤
      Bβ * ∑ b ∈ s.image completeProduct with b ≠ T,
        tau b ^ m * tau (P5OriginalPrimeEndpoint.distance T b) ^ S := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨n, hn, hnb⟩ := (Finset.mem_image.mp (Finset.mem_filter.mp hb).1)
      have hbpos : 0 < b := by rw [← hnb]; exact (hs n hn).1
      have hh := mul_le_mul_of_nonneg_right (hb_fibreMass_le s β Bβ hBβ hβ b hbpos)
        (show 0 ≤ tau (P5OriginalPrimeEndpoint.distance T b) ^ S by positivity)
      simpa only [mul_assoc] using hh
    _ ≤ Bβ * ∑ b ∈ completeNonzero X T,
        tau b ^ m * tau (P5OriginalPrimeEndpoint.distance T b) ^ S := by
      apply mul_le_mul_of_nonneg_left _ hBβ
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b hb hnot => by positivity)
    _ ≤ Bβ * ((3 + 13 * (2 ^ (2 * S) : ℕ) : ℝ) * X *
        logScale X ^ (2 ^ (2 * m) + 2 ^ (2 * S))) :=
      mul_le_mul_of_nonneg_left (complete_mixed_moment_le m S hS hX T hT) hBβ

theorem hb_tupleMass_le (s : Finset (Fin m → ℕ)) (β : (Fin m → ℕ) → ℂ)
    (Bβ : ℝ) (hBβ : 0 ≤ Bβ) (hβ : ∀ n ∈ s, ‖β n‖ ≤ Bβ)
    {X : ℝ} (hX : 1 ≤ X)
    (hs : ∀ n ∈ s, 1 ≤ completeProduct n ∧ (completeProduct n : ℝ) ≤ 6 * X) :
    tupleMass s β ≤ Bβ * (6 * X * logScale X ^ (2 ^ m - 1)) := by
  rw [tupleMass_eq_fibres]
  have hsub : s.image completeProduct ⊆ Finset.Icc 1 ⌊6 * X⌋₊ := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_Icc.mpr ⟨(hs n hn).1, Nat.le_floor (hs n hn).2⟩
  calc
    (∑ b ∈ s.image completeProduct, fibreMass s β completeProduct b) ≤
        Bβ * ∑ b ∈ s.image completeProduct, tau b ^ m := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨n, hn, hnb⟩ := Finset.mem_image.mp hb
      apply hb_fibreMass_le s β Bβ hBβ hβ
      rw [← hnb]
      exact (hs n hn).1
    _ ≤ Bβ * ∑ b ∈ Finset.Icc 1 ⌊6 * X⌋₊, tau b ^ m :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun b hb hnot => by positivity)) hBβ
    _ ≤ Bβ * (6 * X * logScale X ^ (2 ^ m - 1)) :=
      mul_le_mul_of_nonneg_left (sum_tau_pow_Icc_le m hX) hBβ

/-- The exceptional product T pays the actual supported modulus mass.
The reciprocal-totient budget is kept separate for the exact mean. -/
theorem hb_fullTailMass_le (s : Finset (Fin m → ℕ)) (β : (Fin m → ℕ) → ℂ)
    (Bβ : ℝ) (hBβ : 0 ≤ Bβ) (hβ : ∀ n ∈ s, ‖β n‖ ≤ Bβ)
    {X : ℝ} (hX : 1 ≤ X) (T D J : ℕ) (hTpos : 0 < T) (hT : (T : ℝ) ≤ X)
    (hs : ∀ n ∈ s, 1 ≤ completeProduct n ∧ (completeProduct n : ℝ) ≤ 6 * X)
    (Q : Finset ℕ) (rho : ℕ → ℂ)
    (hQ : effectiveModuli Q ⊆ Finset.Icc 1 D)
    (hsq : ∀ q ∈ effectiveModuli Q, Squarefree q)
    (Cρ : ℝ) (hCρ : 0 ≤ Cρ)
    (hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J) :
    fullTailMass s β completeProduct Q rho T J Cρ ≤
      Cρ * Bβ * ((3 + 13 * (2 ^ (2 * (J + 1)) : ℕ) : ℝ) * X *
        logScale X ^ (2 ^ (2 * m) + 2 ^ (2 * (J + 1)))) +
      Bβ * tau T ^ m * rhoMass Q rho +
      Bβ * (6 * X * logScale X ^ (2 ^ m - 1)) *
        (Cρ * (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ (2 ^ J)) := by
  have hn := hb_nonzeroMoment_le s β Bβ hBβ hβ hX T (J + 1) (by omega) hT hs
  have he := hb_fibreMass_le s β Bβ hBβ hβ T hTpos
  have hu := hb_tupleMass_le s β Bβ hBβ hβ hX hs
  have hm := actual_rho_mean_budget Q rho D J hQ hsq Cρ hCρ hrho
  unfold fullTailMass
  exact add_le_add (add_le_add
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn hCρ)
    (mul_le_mul_of_nonneg_right he (rhoMass_nonneg Q rho)))
    (mul_le_mul hu hm (rhoMeanMass_nonneg Q rho) (by positivity))

/-- Every divisor order, dimension and finite restoring loss fixes its
own nonnegative exponent BEFORE accuracy and target are chosen. -/
def paymentExponent (m J : ℕ) : ℕ :=
  m + (2 ^ (2 * m) + 2 ^ (2 * (J + 1))) + (2 ^ m - 1) + 2 ^ J

/-- A concrete polylog cutoff. It is never selected from the finite
source mass at the current target. -/
def selectedCutoff (X : ℝ) (accuracy derivativeOrder paymentOrder : ℕ) : ℝ :=
  logScale X ^ (accuracy + derivativeOrder + paymentOrder + 3)

theorem selectedCutoff_one_le {X : ℝ} (hX : 1 ≤ X) (A E F : ℕ) :
    1 ≤ selectedCutoff X A E F := one_le_pow₀ (logScale_one_le hX)

/-- Exact exponent payment for the selected cutoff. All parameters A/E/F
are fixed before X grows. This is the algebra used by the actual error
and its derived complete-modulus mass, with no arbitrary H premise. -/
theorem selected_cutoff_payment {X : ℝ} (hX : 1 ≤ X) (A E F : ℕ) (C : ℝ) :
    (C * logScale X ^ E / selectedCutoff X A E F) * logScale X ^ F =
      C / logScale X ^ (A + 3) := by
  have hL : logScale X ≠ 0 := (lt_of_lt_of_le zero_lt_one (logScale_one_le hX)).ne'
  unfold selectedCutoff
  rw [show A + E + F + 3 = (A + 3) + (E + F) by omega,
    pow_add, pow_add]
  field_simp [hL]
  ring

/-- The source-to-truncated discrepancy is evaluated for this actual
Euclidean occurrence chart, after its COMPLETE modulus mass has been
formed. A concrete selectedCutoff is substituted, not left arbitrary. -/
theorem actual_selected_cutoff_tail {kStar : ℕ}
    (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
    (s : Finset (Fin m → ℕ)) (β : (Fin m → ℕ) → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (J : ℕ) (Cρ : ℝ) (hCρ : 0 ≤ Cρ)
    (hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J)
    (hU : ∀ a, 0 < U a)
    (hlo : ∀ n ∈ s, ∀ a, U a < (n a : ℝ))
    (hhi : ∀ n ∈ s, ∀ a, (n a : ℝ) ≤ 2 * U a)
    {X : ℝ} (hX : 1 ≤ X) (accuracy derivativeOrder paymentOrder : ℕ) :
    ‖MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
        (fun n => β n * (integerChartWeight A T k owner R κ₀ n : ℂ)) -
      MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
        (fun n => β n * truncatedPhysical m (actualEuclideanChart A T k owner U R κ₀)
          (selectedCutoff X accuracy derivativeOrder paymentOrder)
          (WithLp.toLp 2 (logOccurrence U n)))‖ ≤
      ((m : ℝ) * mixedD m (actualEuclideanChart A T k owner U R κ₀) /
        selectedCutoff X accuracy derivativeOrder paymentOrder) *
        fullTailMass s β completeProduct Q rho T J Cρ := by
  have hH : 0 < selectedCutoff X accuracy derivativeOrder paymentOrder :=
    lt_of_lt_of_le zero_lt_one (selectedCutoff_one_le hX _ _ _)
  apply discrepancy_tail_le s β completeProduct Q rho T J Cρ _ hCρ
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (mixedD_nonneg m _)) hH.le) hrho
  intro n hn
  rw [← actualEuclideanChart_integer_atom A T k owner U R κ₀ n hU (hlo n hn) (hhi n hn)]
  exact actual_uniform_truncation_error m _
    (actualEuclideanChart_smooth A T k owner U R κ₀)
    (actualEuclideanChart_compact A T k owner U R κ₀) _ hH _

/-- Literal native rough HB occurrences, allowing a separate real cutoff
y_a for each original group. Signed truncated Moebius and every log slot
remain exactly those of the original order-three expansion. -/
def hbSlots (Z : ℝ) (y : Fin m → ℝ)
    (roles : Fin m → ActualRoughHeathBrownWords.Role) (n : Fin m → ℕ) : ℂ :=
  ∏ a, ActualRoughHeathBrownWords.actual Z (y a) (roles a) (n a)

theorem hbSlots_norm_le {X : ℝ} (hX : 1 ≤ X) (Z : ℝ) (y : Fin m → ℝ)
    (roles : Fin m → ActualRoughHeathBrownWords.Role) (n : Fin m → ℕ)
    (hn : ∀ a, 0 < n a) (hp : (completeProduct n : ℝ) ≤ 6 * X) :
    ‖hbSlots Z y roles n‖ ≤ logScale X ^ m := by
  have hprodpos : 0 < completeProduct n := Finset.prod_pos (fun a ha => hn a)
  have hL := logScale_one_le hX
  have heach (a : Fin m) :
      ‖ActualRoughHeathBrownWords.actual Z (y a) (roles a) (n a)‖ ≤ logScale X := by
    have hadiv : n a ∣ completeProduct n := Finset.dvd_prod_of_mem n (Finset.mem_univ a)
    have hale : (n a : ℝ) ≤ 6 * X := (by exact_mod_cast Nat.le_of_dvd hprodpos hadiv).trans hp
    have hna : (0 : ℝ) < n a := by exact_mod_cast hn a
    have hn1 : (1 : ℝ) ≤ n a := by exact_mod_cast hn a
    cases hr : roles a with
    | mobius =>
        exact (ActualRoughHeathBrownWords.roughMuTrunc_norm_le Z (y a) (n a)).trans hL
    | one => exact (ImbalancedChen.Part3.roughOneSlot_norm_le Z (n a)).trans hL
    | logarithm =>
        have hlog0 := Real.log_nonneg hn1
        have hlog := Real.log_le_log hna (show (n a : ℝ) ≤ 7 * X by linarith)
        change ‖ActualRoughHeathBrownWords.roughLog Z (n a)‖ ≤ logScale X
        calc
          ‖ActualRoughHeathBrownWords.roughLog Z (n a)‖ =
              Real.log (n a : ℝ) * ‖ImbalancedChen.Part3.roughOneSlot Z (n a)‖ := by
            simp [ActualRoughHeathBrownWords.roughLog, norm_mul, abs_of_nonneg hlog0]
          _ ≤ Real.log (n a : ℝ) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left
              (ImbalancedChen.Part3.roughOneSlot_norm_le Z (n a)) hlog0
          _ ≤ logScale X := by unfold logScale; linarith
  rw [hbSlots, norm_prod]
  exact (Finset.prod_le_prod (fun a ha => norm_nonneg _)
    (fun a ha => heach a)).trans_eq (by simp)

def massConstant (J : ℕ) : ℝ :=
  (3 + 13 * (2 ^ (2 * (J + 1)) : ℕ)) + 6 * (4 : ℝ) ^ (2 ^ J)

/-- A complete structural mass bound for the actual native HB role
product. It is DERIVED from the preceding fibre/moment/totient proofs;
it is not a Fourier-tail or a final-discrepancy hypothesis. -/
theorem actual_hb_mass_polylog (s : Finset (Fin m → ℕ))
    (Z : ℝ) (y : Fin m → ℝ) (roles : Fin m → ActualRoughHeathBrownWords.Role)
    {X : ℝ} (hX : 1 ≤ X) (T D J : ℕ) (hTpos : 0 < T) (hT : (T : ℝ) ≤ X)
    (hD : 1 ≤ D) (hDX : (D : ℝ) ≤ 6 * X)
    (hs : ∀ n ∈ s, (∀ a, 0 < n a) ∧ (completeProduct n : ℝ) ≤ 6 * X)
    (Q : Finset ℕ) (rho : ℕ → ℂ)
    (hQ : effectiveModuli Q ⊆ Finset.Icc 1 D)
    (hsq : ∀ q ∈ effectiveModuli Q, Squarefree q)
    (Cρ : ℝ) (hCρ : 0 ≤ Cρ)
    (hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J) :
    fullTailMass s (hbSlots Z y roles) completeProduct Q rho T J Cρ ≤
      Cρ * (massConstant J * X + (D : ℝ) * tau T ^ m) *
        logScale X ^ paymentExponent m J := by
  let L := logScale X
  let F := paymentExponent m J
  let E₁ := 2 ^ (2 * m) + 2 ^ (2 * (J + 1))
  let E₂ := 2 ^ m - 1
  let K := 2 ^ J
  let C₁ : ℝ := (3 + 13 * (2 ^ (2 * (J + 1)) : ℕ))
  have hL : 1 ≤ L := logScale_one_le hX
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hβ : ∀ n ∈ s, ‖hbSlots Z y roles n‖ ≤ L ^ m :=
    fun n hn => hbSlots_norm_le hX Z y roles n (hs n hn).1 (hs n hn).2
  have hprod : ∀ n ∈ s, 1 ≤ completeProduct n ∧ (completeProduct n : ℝ) ≤ 6 * X := by
    intro n hn
    exact ⟨Finset.prod_pos (fun a ha => (hs n hn).1 a), (hs n hn).2⟩
  have hraw := hb_fullTailMass_le s (hbSlots Z y roles) (L ^ m) (pow_nonneg hL0 m)
    hβ hX T D J hTpos hT hprod Q rho hQ hsq Cρ hCρ hrho
  have hqmass := actual_rho_total_budget Q rho D J hD hQ Cρ hCρ hrho
  have hlogD : 1 + Real.log (D : ℝ) ≤ L := by
    unfold L logScale
    exact add_le_add_left (Real.log_le_log (by exact_mod_cast hD) (by linarith)) 1
  have hmax : max 1 (D : ℝ) = (D : ℝ) := max_eq_right (by exact_mod_cast hD)
  have hq : rhoMass Q rho ≤ Cρ * (D : ℝ) * L ^ (K - 1) := by
    apply hqmass.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg (by exact_mod_cast hD : (1 : ℝ) ≤ D)])
        hlogD _) (mul_nonneg hCρ (Nat.cast_nonneg D))
  have hp₁ : L ^ (m + E₁) ≤ L ^ F := pow_le_pow_right₀ hL (by dsimp [F, paymentExponent, E₁]; omega)
  have hp₂ : L ^ (m + E₂ + K) ≤ L ^ F := pow_le_pow_right₀ hL (by dsimp [F, paymentExponent, E₂, K]; omega)
  have hp₃ : L ^ (m + (K - 1)) ≤ L ^ F := pow_le_pow_right₀ hL (by dsimp [F, paymentExponent, K]; omega)
  have ha : Cρ * L ^ m * (C₁ * X * L ^ E₁) ≤ Cρ * C₁ * X * L ^ F := by
    calc
      _ = (Cρ * C₁ * X) * L ^ (m + E₁) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₁ (by dsimp [C₁]; positivity)
  have hb : L ^ m * tau T ^ m * rhoMass Q rho ≤ Cρ * (D : ℝ) * tau T ^ m * L ^ F := by
    calc
      _ ≤ L ^ m * tau T ^ m * (Cρ * (D : ℝ) * L ^ (K - 1)) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (Cρ * (D : ℝ) * tau T ^ m) * L ^ (m + (K - 1)) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₃ (by positivity)
  have hc : L ^ m * (6 * X * L ^ E₂) *
      (Cρ * (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ K) ≤
      Cρ * (6 * 4 ^ K) * X * L ^ F := by
    calc
      _ ≤ L ^ m * (6 * X * L ^ E₂) * (Cρ * (4 * L) ^ K) := by
        rw [hmax]
        gcongr
      _ = (Cρ * (6 * 4 ^ K) * X) * L ^ (m + E₂ + K) := by
        rw [mul_pow, pow_add, pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₂ (by positivity)
  apply hraw.trans
  change Cρ * L ^ m * (C₁ * X * L ^ E₁) + L ^ m * tau T ^ m * rhoMass Q rho +
      L ^ m * (6 * X * L ^ E₂) * (Cρ * (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ K) ≤ _
  calc
    _ ≤ Cρ * C₁ * X * L ^ F + Cρ * (D : ℝ) * tau T ^ m * L ^ F +
        Cρ * (6 * 4 ^ K) * X * L ^ F := add_le_add (add_le_add ha hb) hc
    _ = _ := by dsimp [massConstant, C₁, L, F, K]; ring

/-- The selected logarithmic H is now fully paid against the DERIVED
actual native-HB complete-modulus mass. The exact product T retains its
separate D*tau(T)^m first moment and never enters the mixed moment. -/
theorem paid_actual_role_tail {kStar : ℕ}
    (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
    (s : Finset (Fin m → ℕ)) (Z : ℝ) (y : Fin m → ℝ)
    (roles : Fin m → ActualRoughHeathBrownWords.Role)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (D J : ℕ)
    (Cρ CD : ℝ) (hCρ : 0 ≤ Cρ) (hCD : 0 ≤ CD)
    (hQ : effectiveModuli Q ⊆ Finset.Icc 1 D)
    (hsq : ∀ q ∈ effectiveModuli Q, Squarefree q)
    (hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J)
    (hU : ∀ a, 0 < U a) (hTpos : 0 < T)
    (hlo : ∀ n ∈ s, ∀ a, U a < (n a : ℝ))
    (hhi : ∀ n ∈ s, ∀ a, (n a : ℝ) ≤ 2 * U a)
    {X : ℝ} (hX : 1 ≤ X) (hT : (T : ℝ) ≤ X) (hD : 1 ≤ D) (hDX : (D : ℝ) ≤ 6 * X)
    (hproducts : ∀ n ∈ s, (completeProduct n : ℝ) ≤ 6 * X)
    (accuracy derivativeOrder : ℕ)
    (hder : mixedD m (actualEuclideanChart A T k owner U R κ₀) ≤
      CD * logScale X ^ derivativeOrder) :
    ‖MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
        (fun n => hbSlots Z y roles n * (integerChartWeight A T k owner R κ₀ n : ℂ)) -
      MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
        (fun n => hbSlots Z y roles n *
          truncatedPhysical m (actualEuclideanChart A T k owner U R κ₀)
            (selectedCutoff X accuracy derivativeOrder (paymentExponent m J))
            (WithLp.toLp 2 (logOccurrence U n)))‖ ≤
      (m : ℝ) * CD * Cρ * (massConstant J * X + (D : ℝ) * tau T ^ m) /
        logScale X ^ (accuracy + 3) := by
  have hH : 0 < selectedCutoff X accuracy derivativeOrder (paymentExponent m J) :=
    lt_of_lt_of_le zero_lt_one (selectedCutoff_one_le hX _ _ _)
  have hslotpos : ∀ n ∈ s, ∀ a, 0 < n a := by
    intro n hn a
    exact_mod_cast (hU a).trans (hlo n hn a)
  have hmass := actual_hb_mass_polylog s Z y roles hX T D J hTpos hT hD hDX
    (fun n hn => ⟨hslotpos n hn, hproducts n hn⟩) Q rho hQ hsq Cρ hCρ hrho
  have herr := actual_selected_cutoff_tail A T k owner U R κ₀ s (hbSlots Z y roles)
    Q rho J Cρ hCρ hrho hU hlo hhi hX accuracy derivativeOrder (paymentExponent m J)
  have hδ := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hder (Nat.cast_nonneg m)) hH.le
  have hmass0 : 0 ≤ fullTailMass s (hbSlots Z y roles) completeProduct Q rho T J Cρ := by
    unfold fullTailMass nonzeroMoment fibreMass tupleMass rhoMass rhoMeanMass
    positivity
  have hnewδ : 0 ≤ (m : ℝ) * (CD * logScale X ^ derivativeOrder) /
      selectedCutoff X accuracy derivativeOrder (paymentExponent m J) := by positivity
  apply herr.trans
  calc
    _ ≤ ((m : ℝ) * (CD * logScale X ^ derivativeOrder) /
          selectedCutoff X accuracy derivativeOrder (paymentExponent m J)) *
        (Cρ * (massConstant J * X + (D : ℝ) * tau T ^ m) *
          logScale X ^ paymentExponent m J) :=
      mul_le_mul hδ hmass hmass0 hnewδ
    _ = (Cρ * (massConstant J * X + (D : ℝ) * tau T ^ m)) *
        (((m : ℝ) * CD * logScale X ^ derivativeOrder /
          selectedCutoff X accuracy derivativeOrder (paymentExponent m J)) *
            logScale X ^ paymentExponent m J) := by ring
    _ = _ := by rw [selected_cutoff_payment hX]; ring

/-- Eliminate the derivative-envelope premise using the actual all-rank
chart theorem. The same CD/E are selected before every target, original
rank, HB dimension, role pattern, modulus atom and requested accuracy. -/
theorem exists_paid_actual_role_tail (A : Family kStar) :
    ∃ CD : ℝ, ∃ E : ℕ, 0 ≤ CD ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (m : ℕ)
        (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
        (s : Finset (Fin m → ℕ)) (Z : ℝ) (y : Fin m → ℝ)
        (roles : Fin m → ActualRoughHeathBrownWords.Role)
        (Q : Finset ℕ) (rho : ℕ → ℂ) (D J : ℕ) (Cρ : ℝ) (X : ℝ) (accuracy : ℕ),
        0 < T → m ≤ 6 * kStar → (∀ a, 0 < U a) → (∀ i, 0 < R i) →
        1 ≤ X → (T : ℝ) ≤ X → 1 ≤ D → (D : ℝ) ≤ 6 * X → 0 ≤ Cρ →
        effectiveModuli Q ⊆ Finset.Icc 1 D →
        (∀ q ∈ effectiveModuli Q, Squarefree q) →
        (∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J) →
        (∀ n ∈ s, ∀ a, U a < (n a : ℝ)) →
        (∀ n ∈ s, ∀ a, (n a : ℝ) ≤ 2 * U a) →
        (∀ n ∈ s, (completeProduct n : ℝ) ≤ 6 * X) →
        ‖MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
          (fun n => hbSlots Z y roles n * (integerChartWeight A T k owner R κ₀ n : ℂ)) -
         MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
          (fun n => hbSlots Z y roles n *
            truncatedPhysical m (actualEuclideanChart A T k owner U R κ₀)
              (selectedCutoff X accuracy E (paymentExponent m J))
              (WithLp.toLp 2 (logOccurrence U n)))‖ ≤
          (m : ℝ) * CD * Cρ * (massConstant J * X + (D : ℝ) * tau T ^ m) /
            logScale X ^ (accuracy + 3) := by
  obtain ⟨CD, E, hCD, hbudget⟩ := exists_actual_mixedD_budget A
  refine ⟨CD, E, hCD, ?_⟩
  intro T k m owner U R κ₀ s Z y roles Q rho D J Cρ X accuracy hT hm hU hR
    hX hTX hD hDX hCρ hQ hsq hrho hlo hhi hproducts
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hder := hbudget T k m owner U R κ₀ hTR hU hR hm
  have hlogT : Real.log ((T : ℝ) + 2) ≤ logScale X := by
    unfold logScale
    have harg : (T : ℝ) + 2 ≤ 7 * X := by linarith
    exact (Real.log_le_log (by positivity) harg).trans (by linarith)
  have hder' : mixedD m (actualEuclideanChart A T k owner U R κ₀) ≤
      CD * logScale X ^ E := hder.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlogT E) hCD)
  exact paid_actual_role_tail A T k owner U R κ₀ s Z y roles Q rho D J Cρ CD hCρ hCD
    hQ hsq hrho hU hT hlo hhi hX hTX hD hDX hproducts accuracy E hder'

/-- The exact b=T term is genuinely paid using the original subunit
physical exponent, not merely D<=6X. This uses the existing proved native
tau subpower theorem, with epsilon=(1-theta)/2 fixed before all targets. -/
theorem exists_exact_product_payment (r : ℕ) (θ : ℝ) (hθ : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T D : ℕ), 0 < T → (D : ℝ) ≤ (T : ℝ) ^ θ →
      (D : ℝ) * tau T ^ r ≤ C * (T : ℝ) ^ ((1 + θ) / 2) := by
  let ε := (1 - θ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hb⟩ := ImbalancedChen.Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2 ^ r) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))) hε
  refine ⟨C, hC, ?_⟩
  intro T D hT hD
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have htau : tau T ^ r ≤ C * (T : ℝ) ^ ε :=
    (tau_pow_le_native r hT.ne').trans (hb T hT)
  calc
    (D : ℝ) * tau T ^ r ≤ (T : ℝ) ^ θ * (C * (T : ℝ) ^ ε) :=
      mul_le_mul hD htau (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg T) θ)
    _ = C * (T : ℝ) ^ (θ + ε) := by rw [Real.rpow_add hTR]; ring
    _ = C * (T : ℝ) ^ ((1 + θ) / 2) := by congr 2; dsimp [ε]; ring

theorem exists_uniform_exact_product_payment (kStar : ℕ) (θ : ℝ) (hθ : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m T D : ℕ), m ≤ 6 * kStar → 0 < T →
      (D : ℝ) ≤ (T : ℝ) ^ θ → (D : ℝ) * tau T ^ m ≤ C * (T : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_exact_product_payment (6 * kStar) θ hθ
  refine ⟨C, hC, ?_⟩
  intro m T D hm hT hD
  have hτ : 1 ≤ tau T := by
    have hc : 0 < T.divisors.card := Finset.card_pos.mpr
      ⟨1, Nat.mem_divisors.mpr ⟨one_dvd T, hT.ne'⟩⟩
    exact_mod_cast hc
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  calc
    (D : ℝ) * tau T ^ m ≤ (D : ℝ) * tau T ^ (6 * kStar) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hτ hm) (Nat.cast_nonneg D)
    _ ≤ C * (T : ℝ) ^ ((1 + θ) / 2) := hb T D hT hD
    _ ≤ C * (T : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      have h := Real.rpow_le_rpow_of_exponent_le hTR
        (show (1 + θ) / 2 ≤ 1 by linarith)
      simpa only [Real.rpow_one] using h

/-- The nonzero, exact-product and exact-mean tails now all have a
logarithmic saving for actual HB slots and actual chart derivatives.
The same CD/E and collision constant precede target and requested accuracy. -/
theorem exists_log_saving_actual_role_tail (A : Family kStar) (θ : ℝ) (hθ : θ < 1) :
    ∃ CD Ccollision : ℝ, ∃ E : ℕ, 0 ≤ CD ∧ 0 < Ccollision ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (m : ℕ)
        (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
        (s : Finset (Fin m → ℕ)) (Z : ℝ) (y : Fin m → ℝ)
        (roles : Fin m → ActualRoughHeathBrownWords.Role)
        (Q : Finset ℕ) (rho : ℕ → ℂ) (D J : ℕ) (Cρ X : ℝ) (accuracy : ℕ),
        0 < T → m ≤ 6 * kStar → (∀ a, 0 < U a) → (∀ i, 0 < R i) →
        1 ≤ X → (T : ℝ) ≤ X → 1 ≤ D → (D : ℝ) ≤ 6 * X →
        (D : ℝ) ≤ (T : ℝ) ^ θ → 0 ≤ Cρ →
        effectiveModuli Q ⊆ Finset.Icc 1 D →
        (∀ q ∈ effectiveModuli Q, Squarefree q) →
        (∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J) →
        (∀ n ∈ s, ∀ a, U a < (n a : ℝ)) →
        (∀ n ∈ s, ∀ a, (n a : ℝ) ≤ 2 * U a) →
        (∀ n ∈ s, (completeProduct n : ℝ) ≤ 6 * X) →
        ‖MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
          (fun n => hbSlots Z y roles n * (integerChartWeight A T k owner R κ₀ n : ℂ)) -
         MellinInsertion20261028.exactDiscrepancy s Q rho completeProduct T
          (fun n => hbSlots Z y roles n *
            truncatedPhysical m (actualEuclideanChart A T k owner U R κ₀)
              (selectedCutoff X accuracy E (paymentExponent m J))
              (WithLp.toLp 2 (logOccurrence U n)))‖ ≤
          (6 * kStar : ℕ) * CD * Cρ * (massConstant J + Ccollision) * X /
            logScale X ^ (accuracy + 3) := by
  obtain ⟨CD, E, hCD, htail⟩ := exists_paid_actual_role_tail A
  obtain ⟨CC, hCC, hcollision⟩ := exists_uniform_exact_product_payment kStar θ hθ
  refine ⟨CD, CC, E, hCD, hCC, ?_⟩
  intro T k m owner U R κ₀ s Z y roles Q rho D J Cρ X accuracy hT hm hU hR hX hTX
    hD hDX hDθ hCρ hQ hsq hrho hlo hhi hproducts
  have ht := htail T k m owner U R κ₀ s Z y roles Q rho D J Cρ X accuracy hT hm hU hR
    hX hTX hD hDX hCρ hQ hsq hrho hlo hhi hproducts
  have hcol : (D : ℝ) * tau T ^ m ≤ CC * X :=
    (hcollision m T D hm hT hDθ).trans (mul_le_mul_of_nonneg_left hTX hCC.le)
  have hmR : (m : ℝ) ≤ (6 * kStar : ℕ) := by exact_mod_cast hm
  apply ht.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hmass : massConstant J * X + (D : ℝ) * tau T ^ m ≤
      (massConstant J + CC) * X := by nlinarith
  calc
    (m : ℝ) * CD * Cρ * (massConstant J * X + (D : ℝ) * tau T ^ m) ≤
        (m : ℝ) * CD * Cρ * ((massConstant J + CC) * X) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (6 * kStar : ℕ) * CD * Cρ * ((massConstant J + CC) * X) := by
      have hcoef : 0 ≤ CD * Cρ * ((massConstant J + CC) * X) := by
        dsimp [massConstant]
        positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hmR hcoef
    _ = _ := by ring

/-- Finite restoration of dyadic/rank/marked-slot pieces. The signed
restoring scalars stay unchanged; their total norm is charged once. A
fixed logarithmic scalar loss Jpiece is paid by requesting that many more
powers before the common target varies. -/
theorem finite_piece_restoration {ι : Type*} (pieces : Finset ι)
    (scalar error : ι → ℂ) {X : ℝ} (hX : 1 ≤ X) (A Jpiece : ℕ)
    (Cpiece Cerror : ℝ) (hCpiece : 0 ≤ Cpiece) (hCerror : 0 ≤ Cerror)
    (hscalar : (∑ p ∈ pieces, ‖scalar p‖) ≤ Cpiece * logScale X ^ Jpiece)
    (herr : ∀ p ∈ pieces, ‖error p‖ ≤ Cerror * X /
      logScale X ^ (A + Jpiece + 3)) :
    ‖∑ p ∈ pieces, scalar p * error p‖ ≤ Cpiece * Cerror * X /
      logScale X ^ (A + 3) := by
  have hL : 0 < logScale X := lt_of_lt_of_le zero_lt_one (logScale_one_le hX)
  calc
    ‖∑ p ∈ pieces, scalar p * error p‖ ≤ ∑ p ∈ pieces, ‖scalar p‖ * ‖error p‖ := by
      simpa only [norm_mul] using norm_sum_le pieces (fun p => scalar p*error p)
    _ ≤ ∑ p ∈ pieces, ‖scalar p‖ * (Cerror * X /
        logScale X ^ (A + Jpiece + 3)) :=
      Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (herr p hp) (norm_nonneg _))
    _ = (∑ p ∈ pieces, ‖scalar p‖) * (Cerror * X / logScale X ^ (A + Jpiece + 3)) := by
      rw [Finset.sum_mul]
    _ ≤ (Cpiece * logScale X ^ Jpiece) *
        (Cerror * X / logScale X ^ (A + Jpiece + 3)) :=
      mul_le_mul_of_nonneg_right hscalar (by positivity)
    _ = Cpiece * Cerror * X / logScale X ^ (A + 3) := by
      rw [show A + Jpiece + 3 = (A + 3) + Jpiece by omega, pow_add]
      field_simp [hL.ne']
      ring

end
end ImbalancedChen.P5Z.ActualHBPostModulusLogCutoff
