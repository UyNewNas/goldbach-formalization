import ImbalancedChen.P1OriginalHistoricalTwoLongP2
import ImbalancedChen.P5ActualLowerNormalizedPostModulusTail
import ImbalancedChen.P5NativeFullQHBAtlasTailPayment

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original normalized singleton blockChart is used at collar order 6.
Its existing integer identity includes unit blocks, the group logarithm,
the complete-product trim and original psi. This file only specializes
the original Fourier and complete-modulus suppliers to historical Q/rho.

The retained integral has the actual normalized amplitude, whose L1 cost
is log(N+2)^72/2^m. The omitted modes are paid separately, after the full
historical modulus sum, by the original mixed divisor moment, reciprocal
totient mean and exact-product collision suppliers. No mode estimate is
used outside a retained band, and no mass or derivative bound is assumed.

The cutoff uses the fixed maximum dimension six for every HB order.
This does not bind the outer remainingTypeI selector to a rectangle sum
or close P1.5. The inherited source-only and missing-owner boundaries remain.
-/

namespace ImbalancedChen.P1OriginalHistoricalSingletonFourier
noncomputable section
open Classical Filter MeasureTheory Set
open scoped BigOperators
open PrimeProducts
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.ActualLowerNormalizedBlockGeometry
  (rectangle scales scales_pos singletonOwner integerProfile blockChart
    blockChart_integer Meets rectangle_counting_scale)
open P5Z.ActualLowerNormalizedHBSource
  (chart_smooth chart_compact actual_fourier_l1_budget actual_normalized_cube_tail)
open P5Z.OccurrenceEuclideanMixedIntegral (euclideanLift_smooth euclideanLift_compact)
open P5Z.ActualAllRankOccurrenceFourierBridge
  (logOccurrence occurrenceMode physicalPhase_occurrenceMode)
open P5Z.ActualEuclideanPhysicalFourier
open P5Z.AllRankCauchyCubeTail (outsideCube measurableSet_outsideCube)
open P5Z.ActualCompleteModulusFourierTail
  (effectiveModuli tau fullTailMass discrepancy_tail_le)
open P5Z.ActualHBPostModulusLogCutoff
  (hbSlots completeProduct massConstant paymentExponent actual_hb_mass_polylog
    selectedCutoff selectedCutoff_one_le selected_cutoff_payment
    exists_uniform_exact_product_payment)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P5Z.ActualLowerNormalizedPostModulusTail
  (countingScale countingScale_one_le target_le_countingScale cutoff)
open P5Z.NativeFullQHBAtlasTailPayment (paymentExponent_mono)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos)
open P1OriginalHistoricalTwoLongP2
  (historicalModuli historicalRho historical_modulus_class historical_modulus_floor)

variable {m : ℕ}

/-- The original normalized physical amplitude, specialized only to B=6. -/
def amplitude (kap : ℝ) (N cj : ℕ) (kap0 : ℝ) (bs : Fin m → Block)
    (xi : Fin m → ℝ) : ℂ :=
  (frequencyScale^m)⁻¹ • physicalFourier m (blockChart kap 6 N cj kap0 bs) xi

theorem amplitude_integrable (kap : ℝ) (N cj : ℕ) (kap0 : ℝ)
    (bs : Fin m → Block) : Integrable (amplitude kap N cj kap0 bs) :=
  (physicalFourier_integrable m _
    (euclideanLift_smooth m _ (chart_smooth kap 6 N (singletonOwner m)
      (scales bs) (fun _ => R cj) kap0))
    (euclideanLift_compact m _ (chart_compact kap 6 N (singletonOwner m)
      (scales bs) (fun _ => R cj) kap0))).const_smul _

/-- The existing singleton derivative budget gives one constant before
all charts and blocks; no abstract Family or L1 premise is introduced. -/
theorem exists_amplitude_l1_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kap : ℝ) (N cj : ℕ) (kap0 : ℝ)
      (m : ℕ) (bs : Fin m → Block), 0 < N → m ≤ 6 →
      (∫ xi, ‖amplitude kap N cj kap0 bs xi‖) ≤
        C * Real.log ((N : ℝ)+2)^72 / 2^m := by
  obtain ⟨C, hC, HC⟩ := actual_fourier_l1_budget 6
  refine ⟨C, hC, ?_⟩
  intro kap N cj kap0 m bs hN hm
  have heq : (∫ xi, ‖amplitude kap N cj kap0 bs xi‖) =
      (∫ xi, ‖physicalFourier m (blockChart kap 6 N cj kap0 bs) xi‖) /
        frequencyScale^m := by
    simp only [amplitude, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg frequencyScale_pos.le _))]
    rw [integral_const_mul]
    ring
  rw [heq]
  exact HC kap N m (singletonOwner m) (scales bs) (fun _ => R cj) kap0
    (by exact_mod_cast hN) (scales_pos bs) (fun _ => R_pos cj) hm

private theorem amplitude_mode_integrable (kap : ℝ) (N cj : ℕ) (kap0 : ℝ)
    (bs : Fin m → Block) (n : Fin m → ℕ) :
    Integrable (fun xi => amplitude kap N cj kap0 bs xi * occurrenceMode (scales bs) n xi) := by
  let p := WithLp.toLp 2 (logOccurrence (scales bs) n)
  have ha := amplitude_integrable kap N cj kap0 bs
  have h : Integrable (fun xi => amplitude kap N cj kap0 bs xi * physicalPhase m p xi) := by
    apply ha.norm.mono'
      (ha.aestronglyMeasurable.mul (physicalPhase_continuous m p).aestronglyMeasurable)
    exact Eventually.of_forall (fun xi => by rw [norm_mul, physicalPhase_norm, mul_one])
  simpa only [p, physicalPhase_occurrenceMode] using h

def originalAtom (kap : ℝ) (N cj : ℕ) (kap0 : ℝ) (bs : Fin m → Block)
    (Z : ℝ) (ys : Fin m → ℝ) (rs : Fin m → Role)
    (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (rectangle bs)
    (historicalModuli levelB old fresh N cap w z) (historicalRho old fresh N cap w z L)
    completeProduct N (fun n => hbSlots Z ys rs n * (integerProfile kap 6 N cj kap0 n : ℂ))

def retainedAtom (kap : ℝ) (N cj : ℕ) (kap0 : ℝ) (bs : Fin m → Block)
    (Z : ℝ) (ys : Fin m → ℝ) (rs : Fin m → Role)
    (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z L H : ℝ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (rectangle bs)
    (historicalModuli levelB old fresh N cap w z) (historicalRho old fresh N cap w z L)
    completeProduct N (fun n => hbSlots Z ys rs n *
      truncatedPhysical m (blockChart kap 6 N cj kap0 bs) H
        (WithLp.toLp 2 (logOccurrence (scales bs) n)))

/-- Only the existing finite functional/integral interchange is applied.
The modulus sum is already complete inside the integrand. -/
theorem retained_eq_band (kap : ℝ) (N cj : ℕ) (kap0 : ℝ) (bs : Fin m → Block)
    (Z : ℝ) (ys : Fin m → ℝ) (rs : Fin m → Role)
    (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z L H : ℝ) :
    retainedAtom kap N cj kap0 bs Z ys rs levelB old fresh cap w z L H =
      ∫ xi in (outsideCube m H)ᶜ, amplitude kap N cj kap0 bs xi *
        MellinInsertion20261028.exactDiscrepancy (rectangle bs)
          (historicalModuli levelB old fresh N cap w z)
          (historicalRho old fresh N cap w z L) completeProduct N
          (fun n => hbSlots Z ys rs n * occurrenceMode (scales bs) n xi) := by
  let kernel := fun n : Fin m → ℕ => ∑ q ∈ historicalModuli levelB old fresh N cap w z,
    historicalRho old fresh N cap w z L q * MellinInsertion20261028.residueKernel q N (completeProduct n)
  have hint (n : Fin m → ℕ) : Integrable (fun xi => amplitude kap N cj kap0 bs xi *
      (hbSlots Z ys rs n * occurrenceMode (scales bs) n xi)) := by
    have h := (amplitude_mode_integrable kap N cj kap0 bs n).const_mul (hbSlots Z ys rs n)
    exact h.congr (Eventually.of_forall (fun xi => by ring))
  have rep (n : Fin m → ℕ) : hbSlots Z ys rs n *
      truncatedPhysical m (blockChart kap 6 N cj kap0 bs) H
        (WithLp.toLp 2 (logOccurrence (scales bs) n)) =
      ∫ xi in (outsideCube m H)ᶜ, amplitude kap N cj kap0 bs xi *
        (hbSlots Z ys rs n * occurrenceMode (scales bs) n xi) := by
    unfold truncatedPhysical
    rw [← integral_smul, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun xi => by
      rw [physicalPhase_occurrenceMode]
      simp only [amplitude, Complex.real_smul, smul_eq_mul]
      ring)
  change MellinInsertion20261028.functional (rectangle bs) kernel _ = _
  simp_rw [rep]
  rw [MellinInsertion20261028.functional_integral (rectangle bs) kernel _
    (fun n _ => (hint n).integrableOn)]
  simp_rw [MellinInsertion20261028.functional_mul]
  rfl

/-- The old complete-product mass proof is instantiated at the historical
squarefree carrier. Its exact-product collision is paid by theta=599/1000;
neither a mass bound nor a coefficient norm is a premise. -/
theorem exists_historical_full_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kap : ℝ) (N cj : ℕ) (kap0 : ℝ)
      (m : ℕ) (bs : Fin m → Block), kap < 1 → 0 < N → m ≤ 6 →
      Meets kap 6 N cj kap0 bs →
      ∀ (Z : ℝ) (ys : Fin m → ℝ) (rs : Fin m → Role)
        (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      fullTailMass (rectangle bs) (hbSlots Z ys rs) completeProduct
        (historicalModuli levelB old fresh N cap w z) (historicalRho old fresh N cap w z L)
        N 0 1 ≤ C * (N : ℝ) * logScale (countingScale N)^paymentExponent m 0 := by
  obtain ⟨CC, hCC, hcollision⟩ :=
    exists_uniform_exact_product_payment 1 (599/1000) (by norm_num)
  refine ⟨128*massConstant 0+CC, by dsimp [massConstant]; positivity, ?_⟩
  intro kap N cj kap0 m bs hkap hN hm hMeet Z ys rs levelB old fresh cap w z L
  let X := countingScale N
  let D := Nat.floor ((N : ℝ)^(599/1000 : ℝ))
  let Q := historicalModuli levelB old fresh N cap w z
  let rho := historicalRho old fresh N cap w z L
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : 1 ≤ D := Nat.le_floor (Real.one_le_rpow hNR (by norm_num))
  have hDpower : (D : ℝ) ≤ (N : ℝ)^(599/1000 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hDN : (D : ℝ) ≤ N := hDpower.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNR
      (by norm_num : (599/1000 : ℝ) ≤ 1))
  have hDX : (D : ℝ) ≤ 6*X := by
    have hNX := target_le_countingScale N
    have hX := countingScale_one_le hN
    dsimp only [X]
    linarith
  have hQ : effectiveModuli Q ⊆ Finset.Icc 1 D := by
    intro q hq
    have hqQ := Finset.mem_of_mem_erase hq
    exact Finset.mem_Icc.mpr
      ⟨(historical_modulus_class levelB old fresh N cap w z L hqQ).1,
        historical_modulus_floor levelB old fresh N cap w z hqQ⟩
  have hsq : ∀ q ∈ effectiveModuli Q, Squarefree q := fun q hq =>
    (historical_modulus_class levelB old fresh N cap w z L
      (Finset.mem_of_mem_erase hq)).2.2.1
  have hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ (1 : ℝ)*tau q^0 := by
    intro q hq
    simpa only [one_mul, pow_zero] using
      (historical_modulus_class levelB old fresh N cap w z L
        (Finset.mem_of_mem_erase hq)).2.2.2
  have hs : ∀ n ∈ rectangle bs,
      (∀ a, 0 < n a) ∧ (completeProduct n : ℝ) ≤ 6*X := by
    intro n hn
    obtain ⟨hpos, hprod⟩ := rectangle_counting_scale kap hkap 6 N cj kap0 bs hm hMeet hn
    refine ⟨hpos, ?_⟩
    change (completeProduct n : ℝ) ≤ 6*countingScale N
    dsimp only [countingScale] at *
    nlinarith [Nat.cast_nonneg N]
  have hmass := actual_hb_mass_polylog (rectangle bs) Z ys rs
    (countingScale_one_le hN) N D 0 hN (target_le_countingScale N) hD hDX hs
    Q rho hQ hsq 1 (by norm_num) hrho
  have hc := hcollision m N D (by simpa using hm) hN hDpower
  have htop : massConstant 0*X+(D : ℝ)*tau N^m ≤
      (128*massConstant 0+CC)*(N : ℝ) := by
    dsimp only [X, countingScale]
    nlinarith only [hc]
  calc
    _ ≤ (massConstant 0*X+(D : ℝ)*tau N^m)*logScale X^paymentExponent m 0 := by
      simpa only [one_mul] using hmass
    _ ≤ _ := mul_le_mul_of_nonneg_right htop
      (pow_nonneg (zero_le_one.trans (logScale_one_le (countingScale_one_le hN))) _)

/-- Uniform Fourier omission for the original historical coefficient.
The chosen H is the original normalized singleton cutoff with B=6 and
the fixed maximum dimension six, common to all original HB orders.
This is an actual arithmetic tail payment, independent of any retained
mode estimate, including at completeProduct n = N. -/
theorem exists_historical_tail_paid :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kap : ℝ) (N cj : ℕ) (kap0 : ℝ)
      (m : ℕ) (bs : Fin m → Block), kap < 1 → 0 < N → m ≤ 6 →
      Meets kap 6 N cj kap0 bs →
      ∀ (Z : ℝ) (ys : Fin m → ℝ) (rs : Fin m → Role)
        (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) (accuracy : ℕ),
      ‖originalAtom kap N cj kap0 bs Z ys rs levelB old fresh cap w z L -
        retainedAtom kap N cj kap0 bs Z ys rs levelB old fresh cap w z L
          (cutoff 6 N 6 accuracy)‖ ≤
        C*(N : ℝ)/logScale (countingScale N)^(accuracy+3) := by
  obtain ⟨CD, hCD, htail⟩ := actual_normalized_cube_tail 6
  obtain ⟨CM, hCM, hmass⟩ := exists_historical_full_mass
  refine ⟨6*CD*CM, by positivity, ?_⟩
  intro kap N cj kap0 m bs hkap hN hm hMeet Z ys rs levelB old fresh cap w z L accuracy
  let X := countingScale N
  let H := cutoff 6 N 6 accuracy
  let F := paymentExponent 6 0
  have hX : 1 ≤ X := countingScale_one_le hN
  have hH : 0 < H := zero_lt_one.trans_le (selectedCutoff_one_le hX accuracy 72 F)
  have hlog : Real.log ((N : ℝ)+2) ≤ logScale X := by
    have hNX := target_le_countingScale N
    exact (Real.log_le_log (by positivity) (by linarith : (N : ℝ)+2 ≤ 7*X)).trans
      (by dsimp [logScale]; linarith)
  have hlog0 : 0 ≤ Real.log ((N : ℝ)+2) := Real.log_nonneg (by
    have hN0 := Nat.cast_nonneg (R := ℝ) N
    linarith)
  have herr (n : Fin m → ℕ) (hn : n ∈ rectangle bs) :
      ‖(integerProfile kap 6 N cj kap0 n : ℂ) -
        truncatedPhysical m (blockChart kap 6 N cj kap0 bs) H
          (WithLp.toLp 2 (logOccurrence (scales bs) n))‖ ≤
        (m : ℝ)*CD*logScale X^72/H := by
    rw [← blockChart_integer kap 6 N cj kap0 bs hn]
    have ht := htail kap N m (singletonOwner m) (scales bs) (fun _ => R cj) kap0
      (by exact_mod_cast hN) (scales_pos bs) (fun _ => R_pos cj) hm H hH
      (WithLp.toLp 2 (logOccurrence (scales bs) n))
    apply ht.trans
    apply div_le_div_of_nonneg_right _ hH.le
    calc
      _ ≤ (m : ℝ)*(CD*logScale X^72) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 72) hCD) (Nat.cast_nonneg m)
      _ = _ := by ring
  have hrho : ∀ q ∈ effectiveModuli (historicalModuli levelB old fresh N cap w z),
      ‖historicalRho old fresh N cap w z L q‖ ≤ (1 : ℝ)*tau q^0 := by
    intro q hq
    simpa only [one_mul, pow_zero] using
      (historical_modulus_class levelB old fresh N cap w z L
        (Finset.mem_of_mem_erase hq)).2.2.2
  have hd := discrepancy_tail_le (rectangle bs) (hbSlots Z ys rs) completeProduct
    (historicalModuli levelB old fresh N cap w z) (historicalRho old fresh N cap w z L)
    N 0 1 ((m : ℝ)*CD*logScale X^72/H) (by norm_num)
    (by have hLX := logScale_one_le hX; positivity) hrho
    (fun n => (integerProfile kap 6 N cj kap0 n : ℂ))
    (fun n => truncatedPhysical m (blockChart kap 6 N cj kap0 bs) H
      (WithLp.toLp 2 (logOccurrence (scales bs) n))) herr
  have hmassBound :=
    hmass kap N cj kap0 m bs hkap hN hm hMeet Z ys rs levelB old fresh cap w z L
  have hlogPow : logScale X^paymentExponent m 0 ≤ logScale X^F :=
    pow_le_pow_right₀ (logScale_one_le hX) (paymentExponent_mono hm 0)
  apply hd.trans
  calc
    _ ≤ ((m : ℝ)*CD*logScale X^72/H)*((CM*(N : ℝ))*logScale X^F) :=
      mul_le_mul_of_nonneg_left
        (hmassBound.trans (mul_le_mul_of_nonneg_left hlogPow (mul_nonneg hCM (Nat.cast_nonneg N))))
        (by have hLX := logScale_one_le hX; positivity)
    _ = (CM*(N : ℝ))*(((m : ℝ)*CD*logScale X^72/
        selectedCutoff X accuracy 72 F)*logScale X^F) := by
      dsimp only [H, cutoff, X, F]
      ring
    _ = ((m : ℝ)*CD*CM)*(N : ℝ)/logScale X^(accuracy+3) := by
      rw [selected_cutoff_payment hX]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _
        (pow_nonneg (zero_le_one.trans (logScale_one_le hX)) _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hm : (m : ℝ) ≤ 6)
          (mul_nonneg hCD hCM)) (Nat.cast_nonneg N)

end
end ImbalancedChen.P1OriginalHistoricalSingletonFourier
