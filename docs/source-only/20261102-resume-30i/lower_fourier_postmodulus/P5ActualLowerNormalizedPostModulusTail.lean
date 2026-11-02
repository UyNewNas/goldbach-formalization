import ImbalancedChen.P5ActualLowerNormalizedBlockGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The H genuine normalized lower-singleton chart, literal HB role factors,
and actual full small/rough lower rho are inserted into the independently
proved complete-product divisor accounting BEFORE a cutoff is selected.
No Family, derivative envelope, Fourier-tail estimate, or final arithmetic
mode estimate is a premise. Full atlas reindex/restoration is separate.
-/
namespace ImbalancedChen.P5Z.ActualLowerNormalizedPostModulusTail
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open ActualLowerNormalizedBlockGeometry ActualLowerNormalizedHBSource
open ActualCompleteModulusFourierTail CompleteProductTailDivisorBudgets
open ActualHBPostModulusLogCutoff ActualEuclideanPhysicalFourier
open AllRankCoordinateFourierIBP AllRankMixedOperatorBudget
open ActualAllRankOccurrenceFourierBridge OccurrenceEuclideanMixedIntegral
open HBRightClosedDyadicRoles PerGroupIntegerHBAtlasPushforward
open ActualRoughHeathBrownWords
open ImbalancedChen.PrimeProducts

variable {m : ℕ}

def lowerQ (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :=
  actualLowerSmallRoughModuli retainEven N cap w z

def lowerRho (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : ℕ → ℂ :=
  fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)

theorem lowerRho_norm (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (q : ℕ) : ‖lowerRho retainEven N cap w z L q‖ ≤ 1 := by
  simpa only [lowerRho, Complex.norm_real, Real.norm_eq_abs] using
    actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q

theorem lowerQ_squarefree (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {q : ℕ} (hq : q ∈ effectiveModuli (lowerQ retainEven N cap w z)) :
    Squarefree q :=
  actualLowerSmallRoughModuli_squarefree retainEven N cap w z (Finset.mem_of_mem_erase hq)

/-- This is a global COMPLETE-product scale for absolute tail counting.
Retained arithmetic modes still use their own original local scale. -/
def countingScale (N : ℕ) : ℝ := 128 * (N : ℝ)

theorem countingScale_one_le {N : ℕ} (hN : 0 < N) : 1 ≤ countingScale N := by
  have h : (1 : ℝ) ≤ N := by exact_mod_cast hN
  dsimp [countingScale]
  linarith

theorem target_le_countingScale (N : ℕ) : (N : ℝ) ≤ countingScale N := by
  dsimp [countingScale]
  nlinarith [Nat.cast_nonneg N]

/-- A real arithmetic atom on the FULL block rectangle. The list of
roles below may be specialized to the literal +3, -3, +1 HB rows; no
coefficient bounds are supplied by the caller. -/
def originalAtom (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (bs : Fin m → Block) (Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (rectangle bs)
    (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L)
    completeProduct N (fun n => hbSlots Z y rs n *
      (integerProfile kappa B N cj kappa0 n : ℂ))

def retainedAtom (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (bs : Fin m → Block) (Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L H : ℝ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (rectangle bs)
    (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L)
    completeProduct N (fun n => hbSlots Z y rs n *
      truncatedPhysical m (blockChart kappa B N cj kappa0 bs) H
        (WithLp.toLp 2 (logOccurrence (scales bs) n)))

/-- Actual complete-modulus mass. Fibre multiplicities, nonzero shifted
divisor moment, exact b=N collision, and reciprocal-totient mean are
already bounded in D's source proof. Here every gate is discharged from
the genuine rectangle and actual lower coefficient, apart from the
explicit original physical support level. -/
theorem actual_lower_mass (kappa : ℝ) (hkappa : kappa < 1)
    (B N cj : ℕ) (kappa0 : ℝ) (bs : Fin m → Block) (hm : m ≤ 6)
    (hN : 0 < N) (hMeet : Meets kappa B N cj kappa0 bs)
    (Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role)
    (retainEven : List ℕ → Bool) (cap D : ℕ) (w z L : ℝ)
    (hD : 1 ≤ D) (hDX : (D : ℝ) ≤ 6 * countingScale N)
    (hQ : lowerQ retainEven N cap w z ⊆ Finset.Icc 1 D) :
    fullTailMass (rectangle bs) (hbSlots Z y rs) completeProduct
        (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) N 0 1 ≤
      (massConstant 0 * countingScale N + (D : ℝ) * tau N ^ m) *
        logScale (countingScale N) ^ paymentExponent m 0 := by
  have h := actual_hb_mass_polylog (rectangle bs) Z y rs
    (countingScale_one_le hN) N D 0 hN (target_le_countingScale N) hD hDX
    (fun n hn => by
      obtain ⟨hpos, hbound⟩ := rectangle_counting_scale kappa hkappa B N cj kappa0 bs hm hMeet hn
      refine ⟨hpos, hbound.trans ?_⟩
      change countingScale N ≤ 6 * countingScale N
      nlinarith [countingScale_one_le hN])
    (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L)
    (fun q hq => hQ (Finset.mem_of_mem_erase hq))
    (fun q hq => lowerQ_squarefree retainEven N cap w z hq)
    1 (by norm_num)
    (fun q hq => by simpa only [pow_zero, mul_one] using lowerRho_norm retainEven N cap w z L q)
  simpa only [one_mul] using h

/-- Fixed logarithmic cube cutoff, selected from the actual collar
derivative order, the genuine HB dimension and requested accuracy. -/
def cutoff (B N m accuracy : ℕ) : ℝ :=
  selectedCutoff (countingScale N) accuracy (B*12) (paymentExponent m 0)

/-- Concrete post-full-Q payment for the SAME normalized extension.
The constant precedes every target, policy, block, role cutoff, and A.
The exact-product contribution remains visible at this intermediate step. -/
theorem exists_actual_lower_postmodulus_tail (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N cj kappa0 m (bs : Fin m → Block)
      (Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role)
      (retainEven : List ℕ → Bool) (cap D : ℕ) (w z L : ℝ) (accuracy : ℕ),
      kappa < 1 → 0 < N → m ≤ 6 → Meets kappa B N cj kappa0 bs →
      1 ≤ D → (D : ℝ) ≤ 6 * countingScale N →
      lowerQ retainEven N cap w z ⊆ Finset.Icc 1 D →
      ‖originalAtom kappa B N cj kappa0 bs Z y rs retainEven cap w z L -
        retainedAtom kappa B N cj kappa0 bs Z y rs retainEven cap w z L
          (cutoff B N m accuracy)‖ ≤
        (m : ℝ) * C * (massConstant 0 * countingScale N + (D : ℝ) * tau N ^ m) /
          logScale (countingScale N) ^ (accuracy+3) := by
  obtain ⟨C, hC, htail⟩ := actual_normalized_cube_tail B
  refine ⟨C, hC, ?_⟩
  intro kappa N cj kappa0 m bs Z y rs retainEven cap D w z L accuracy
    hkappa hN hm hMeet hD hDX hQ
  let X := countingScale N
  let E := B*12
  let F := paymentExponent m 0
  let H := cutoff B N m accuracy
  have hX : 1 ≤ X := countingScale_one_le hN
  have hL : 0 < logScale X := lt_of_lt_of_le zero_lt_one (logScale_one_le hX)
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (selectedCutoff_one_le hX accuracy E F)
  have hlog : Real.log ((N : ℝ)+2) ≤ logScale X := by
    have hNX : (N : ℝ) ≤ X := target_le_countingScale N
    exact (Real.log_le_log (by positivity) (by linarith : (N : ℝ)+2 ≤ 7*X)).trans
      (by dsimp [logScale]; linarith)
  have hlog0 : 0 ≤ Real.log ((N : ℝ)+2) := Real.log_nonneg (by positivity)
  have herr : ∀ n ∈ rectangle bs,
      ‖(integerProfile kappa B N cj kappa0 n : ℂ) -
        truncatedPhysical m (blockChart kappa B N cj kappa0 bs) H
          (WithLp.toLp 2 (logOccurrence (scales bs) n))‖ ≤
        (m : ℝ) * C * logScale X^E / H := by
    intro n hn
    rw [← blockChart_integer kappa B N cj kappa0 bs hn]
    have ht := htail kappa N m (singletonOwner m) (scales bs)
      (fun _ => ExactOriginalSmoothDyadicPartition.R cj) kappa0
      (by exact_mod_cast hN) (scales_pos bs)
      (fun _ => ExactOriginalSmoothDyadicPartition.R_pos cj) hm H hH
      (WithLp.toLp 2 (logOccurrence (scales bs) n))
    apply ht.trans
    apply div_le_div_of_nonneg_right _ hH.le
    calc
      _ ≤ (m : ℝ) * (C * logScale X^E) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog E) hC) (Nat.cast_nonneg m)
      _ = _ := by ring
  have hmass := actual_lower_mass kappa hkappa B N cj kappa0 bs hm hN hMeet
    Z y rs retainEven cap D w z L hD hDX hQ
  have hd := discrepancy_tail_le (rectangle bs) (hbSlots Z y rs) completeProduct
    (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) N 0 1
    ((m : ℝ)*C*logScale X^E/H) (by norm_num) (by positivity)
    (fun q hq => by simpa only [pow_zero, mul_one] using lowerRho_norm retainEven N cap w z L q)
    (fun n => (integerProfile kappa B N cj kappa0 n : ℂ))
    (fun n => truncatedPhysical m (blockChart kappa B N cj kappa0 bs) H
      (WithLp.toLp 2 (logOccurrence (scales bs) n))) herr
  change ‖originalAtom kappa B N cj kappa0 bs Z y rs retainEven cap w z L -
      retainedAtom kappa B N cj kappa0 bs Z y rs retainEven cap w z L H‖ ≤ _ at hd
  apply hd.trans
  calc
    _ ≤ ((m : ℝ)*C*logScale X^E/H) *
        ((massConstant 0*X + (D : ℝ)*tau N^m)*logScale X^F) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (massConstant 0*X + (D : ℝ)*tau N^m) *
        (((m : ℝ)*C*logScale X^E/selectedCutoff X accuracy E F)*logScale X^F) := by
      dsimp [H, cutoff, X, E, F]
      ring
    _ = _ := by rw [selected_cutoff_payment hX]; ring

/-- The actual original subunit full-modulus exponent pays the b=N
collision. There is no tau(0), no cap charge on the exact mean, and no
replacement of the full small/rough modulus by a residual quotient. -/
theorem exists_actual_lower_log_saving (B : ℕ) (theta : ℝ) (htheta : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N cj kappa0 m (bs : Fin m → Block)
      (Z : ℝ) (y : Fin m → ℝ) (rs : Fin m → Role)
      (retainEven : List ℕ → Bool) (cap D : ℕ) (w z L : ℝ) (accuracy : ℕ),
      kappa < 1 → 0 < N → m ≤ 6 → Meets kappa B N cj kappa0 bs →
      1 ≤ D → (D : ℝ) ≤ (N : ℝ)^theta →
      lowerQ retainEven N cap w z ⊆ Finset.Icc 1 D →
      ‖originalAtom kappa B N cj kappa0 bs Z y rs retainEven cap w z L -
        retainedAtom kappa B N cj kappa0 bs Z y rs retainEven cap w z L
          (cutoff B N m accuracy)‖ ≤
        C * (N : ℝ) / logScale (countingScale N) ^ (accuracy+3) := by
  obtain ⟨CD, hCD, htail⟩ := exists_actual_lower_postmodulus_tail B
  obtain ⟨CC, hCC, hcollision⟩ := exists_uniform_exact_product_payment 1 theta htheta
  let C := 6*CD*(128*massConstant 0+CC)
  refine ⟨C, by dsimp [C, massConstant]; positivity, ?_⟩
  intro kappa N cj kappa0 m bs Z y rs retainEven cap D w z L accuracy
    hkappa hN hm hMeet hD hDtheta hQ
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hDN : (D : ℝ) ≤ N := hDtheta.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNR htheta.le)
  have hDX : (D : ℝ) ≤ 6*countingScale N := by
    dsimp [countingScale]
    nlinarith
  have ht := htail kappa N cj kappa0 m bs Z y rs retainEven cap D w z L accuracy
    hkappa hN hm hMeet hD hDX hQ
  have hc := hcollision m N D (by simpa using hm) hN hDtheta
  have hmR : (m : ℝ) ≤ 6 := by exact_mod_cast hm
  have hlog : 0 < logScale (countingScale N) :=
    lt_of_lt_of_le zero_lt_one (logScale_one_le (countingScale_one_le hN))
  apply ht.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hmass : massConstant 0*countingScale N + (D : ℝ)*tau N^m ≤
      (128*massConstant 0+CC)*(N : ℝ) := by
    dsimp [countingScale]
    nlinarith
  calc
    _ ≤ (m : ℝ)*CD*((128*massConstant 0+CC)*(N : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ 6*CD*((128*massConstant 0+CC)*(N : ℝ)) := by
      have hnonneg : 0 ≤ CD*((128*massConstant 0+CC)*(N : ℝ)) := by
        dsimp [massConstant]
        positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hmR hnonneg
    _ = C*(N : ℝ) := by dsimp [C]; ring

end
end ImbalancedChen.P5Z.ActualLowerNormalizedPostModulusTail
