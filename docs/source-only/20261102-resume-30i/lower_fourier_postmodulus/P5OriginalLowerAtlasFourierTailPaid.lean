import ImbalancedChen.P5ActualLowerRetainedCubeModes
import ImbalancedChen.P5ActualLowerNormalizedAtlasOccurrence
import ImbalancedChen.P5ActualHBAtlasScalarInventory

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual original lower-source attachment. The finite scalar inventory is
derived for its real chart-dependent HB caps and filtered block banks.
The extra seven logarithmic powers are selected BEFORE N. All five source
reserves and all retained arithmetic cube modes remain explicit.
-/
namespace ImbalancedChen.P5Z.OriginalLowerAtlasFourierTailPaid
noncomputable section
open Classical
open scoped BigOperators
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open PerGroupIntegerHBAtlasPushforward ExactOriginalSmoothDyadicPartition
open ActualLowerNormalizedPostModulusTail ActualLowerRetainedCubeModes
open ActualHBAtlasScalarInventory CompleteProductTailDivisorBudgets
open OriginalPrimeAllGroupHBDiscrepancy
open P5CanonicalTentNarrowSingletonTransfer

def blockMap (j : ℕ) (bs : List Block) : Fin (2*(j+1)) → Block :=
  OrderedFactorTupleRectangleReindex.blockVector (2*(j+1)) bs

/-- Independent definitions agree, not an equality supplied by the caller. -/
theorem occurrenceAtom_eq_originalAtom (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (j : ℕ) (bs : List Block) (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) :
    ActualLowerNormalizedAtlasOccurrence.occurrenceAtom
        kappa B N cj kappa0 j bs retainEven cap w z L =
      originalAtom kappa B N cj kappa0 (blockMap j bs) (beforeHBCutoff 1 [cj])
        (fun _ => hbCutoff cj) (rowRoles j) retainEven cap w z L := by
  rfl

theorem actual_meets (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) (j : ℕ)
    {bs : List Block}
    (hbs : bs ∈ ActualLowerNormalizedAtlasOccurrence.activeBlocks kappa B N cj kappa0 j) :
    ActualLowerNormalizedBlockGeometry.Meets kappa B N cj kappa0 (blockMap j bs) := by
  exact (Finset.mem_filter.mp hbs).2

/-- The source chart labels imply their actual HB bank caps are <=8N.
This concerns the WHOLE original group; no residual scale enters. -/
theorem actual_hbCap_le {N : ℕ} (hN : 0 < N) {js : List ℕ}
    (hjs : js ∈ chartBank (2*N) 1) : hbCap (js.getD 0 0) ≤ 8*N := by
  have hspec := words_spec (Finset.range (cutoffIndex (2*N)+1)) 1 js hjs
  have hj : js.getD 0 0 ≤ Nat.log2 (2*N)+1 := by
    cases js with
    | nil => simp at hspec
    | cons cj tail =>
      have hh := Finset.mem_range.mp (hspec.2 cj (by simp))
      change cj ≤ Nat.log2 (2*N)+1
      change cj < (Nat.log2 (2*N)+1)+1 at hh
      omega
  have hpow : (2 : ℕ)^Nat.log2 (2*N) ≤ 2*N := Nat.log2_self_le (by omega)
  calc
    hbCap (js.getD 0 0) = 2^(js.getD 0 0+1) := rfl
    _ ≤ 2^(Nat.log2 (2*N)+2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4 * 2^Nat.log2 (2*N) := by rw [pow_add]; ring
    _ ≤ 4*(2*N) := Nat.mul_le_mul_left 4 hpow
    _ = 8*N := by ring

def chartScalarMass (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 3, ‖SmoothChartHBDyadicPartition.scalar j‖ *
    ((ActualLowerNormalizedAtlasOccurrence.activeBlocks kappa B N cj kappa0 j).card : ℝ)

/-- The actual active bank is a filter of the true HB bank. Its scalar
mass is bounded from the exact +3, -3, +1 inventory, not postulated. -/
theorem chartScalarMass_le (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) :
    chartScalarMass kappa B N cj kappa0 ≤
      7 * ((Nat.log2 (hbCap cj-1)+2 : ℕ) : ℝ)^6 := by
  calc
    _ ≤ ∑ j ∈ Finset.range 3, ‖SmoothChartHBDyadicPartition.scalar j‖ *
        ((blockWords (hbCap cj) (2*(j+1))).card : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hsub : ActualLowerNormalizedAtlasOccurrence.activeBlocks kappa B N cj kappa0 j ⊆
          blockWords (hbCap cj) (2*(j+1)) := by
        intro bs hbs
        exact (Finset.mem_filter.mp hbs).1
      exact_mod_cast Finset.card_le_card hsub
    _ = ∑ c ∈ singleBank (hbCap cj), ‖hbSign c.1‖ := by
      rw [singleBank, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.sum_const, nsmul_eq_mul]
      change ‖hbSign j‖ * _ = _ * ‖hbSign j‖
      exact mul_comm _ _
    _ ≤ _ := singleBank_scalar_mass_le (hbCap cj)

def sourceScalarMass (kappa : ℝ) (B N : ℕ) (kappa0 : ℝ) : ℝ :=
  ∑ js ∈ chartBank (2*N) 1, chartScalarMass kappa B N (js.getD 0 0) kappa0

/-- Literal original chart inventory, now with chart-dependent hbCap
and actual retained block filter. The logarithmic exponent is seven. -/
theorem sourceScalarMass_le (kappa : ℝ) (B N : ℕ) (kappa0 : ℝ) (hN : 0 < N) :
    sourceScalarMass kappa B N kappa0 ≤
      (7*dyadicConstant^7) * logScale (countingScale N)^7 := by
  let X := countingScale N
  let L := dyadicConstant*logScale X
  have hX : 1 ≤ X := countingScale_one_le hN
  have hL0 : 0 ≤ L := mul_nonneg dyadicConstant_pos.le (zero_le_one.trans (logScale_one_le hX))
  have hcap : ((2*N : ℕ) : ℝ) ≤ 6*X := by
    dsimp [X, countingScale]
    push_cast
    nlinarith [Nat.cast_nonneg N]
  have hchart := log2_count_le hX (2*N) hcap
  have hblocks (js : List ℕ) (hjs : js ∈ chartBank (2*N) 1) :
      chartScalarMass kappa B N (js.getD 0 0) kappa0 ≤ 7*L^6 := by
    have hhb : ((hbCap (js.getD 0 0)-1 : ℕ) : ℝ) ≤ 6*X := by
      have hh := actual_hbCap_le hN hjs
      have hs : hbCap (js.getD 0 0)-1 ≤ 8*N := (Nat.sub_le _ _).trans hh
      have hsR : ((hbCap (js.getD 0 0)-1 : ℕ) : ℝ) ≤ 8*(N : ℝ) := by exact_mod_cast hs
      dsimp [X, countingScale]
      nlinarith [Nat.cast_nonneg N]
    exact (chartScalarMass_le kappa B N _ kappa0).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (log2_count_le hX _ hhb) 6) (by norm_num))
  calc
    sourceScalarMass kappa B N kappa0 ≤ ∑ _js ∈ chartBank (2*N) 1, 7*L^6 :=
      Finset.sum_le_sum hblocks
    _ = ((Nat.log2 (2*N)+2 : ℕ) : ℝ)*(7*L^6) := by
      rw [Finset.sum_const, nsmul_eq_mul, OriginalDyadicRankUnion.actual_chartBank_card]
      simp only [pow_one, cutoffIndex, Nat.add_assoc]
    _ ≤ L*(7*L^6) := mul_le_mul_of_nonneg_right hchart (by positivity)
    _ = (7*dyadicConstant^7)*logScale (countingScale N)^7 := by
      dsimp [L, X]
      ring

def retainedChart (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) (accuracy : ℕ) : ℂ :=
  ∑ j ∈ Finset.range 3, SmoothChartHBDyadicPartition.scalar j *
    ∑ bs ∈ ActualLowerNormalizedAtlasOccurrence.activeBlocks kappa B N cj kappa0 j,
      retainedAtom kappa B N cj kappa0 (blockMap j bs) (beforeHBCutoff 1 [cj])
        (fun _ => hbCutoff cj) (rowRoles j) retainEven cap w z L
        (cutoff B N (2*(j+1)) (accuracy+7))

def retainedLowerAtlas (kappa : ℝ) (B N : ℕ) (kappa0 : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) (accuracy : ℕ) : ℂ :=
  trimReserve (actualLicence kappa B N) (2*N) N kappa0
      (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) +
    ∑ js ∈ chartBank (2*N) 1,
      (retainedChart kappa B N (js.getD 0 0) kappa0 retainEven cap w z L accuracy -
        properPowerReserve (actualLicence kappa B N) 1 (2*N) N kappa0
          (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) js +
        roughPrimeReserve (actualLicence kappa B N) 1 (2*N) N kappa0
          (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) js)

theorem exists_original_atlas_tail_paid (B : ℕ) (theta : ℝ) (htheta : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N kappa0
      (retainEven : List ℕ → Bool) (cap D : ℕ) (w z L : ℝ) (accuracy : ℕ),
      kappa < 1 → 0 < N → 1 ≤ D → (D : ℝ) ≤ (N : ℝ)^theta →
      lowerQ retainEven N cap w z ⊆ Finset.Icc 1 D →
      ‖ActualLowerNormalizedAtlasOccurrence.lowerOccurrenceAtlas kappa B N kappa0 retainEven cap w z L -
        retainedLowerAtlas kappa B N kappa0 retainEven cap w z L accuracy‖ ≤
        C*(N : ℝ)/logScale (countingScale N)^(accuracy+3) := by
  obtain ⟨C0, hC0, hrow⟩ := exists_actual_lower_log_saving B theta htheta
  have hdc : 0 < dyadicConstant := dyadicConstant_pos
  refine ⟨(7*dyadicConstant^7)*C0, by positivity, ?_⟩
  intro kappa N kappa0 retainEven cap D w z L accuracy hkappa hN hD hDtheta hQ
  let ell := logScale (countingScale N)
  let E := C0*(N : ℝ)/ell^(accuracy+7+3)
  have hell : 0 < ell := lt_of_lt_of_le zero_lt_one (logScale_one_le (countingScale_one_le hN))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hchart (cj : ℕ) :
      ‖ActualLowerNormalizedAtlasOccurrence.occurrenceChart kappa B N cj kappa0 retainEven cap w z L -
        retainedChart kappa B N cj kappa0 retainEven cap w z L accuracy‖ ≤
        chartScalarMass kappa B N cj kappa0 * E := by
    unfold ActualLowerNormalizedAtlasOccurrence.occurrenceChart retainedChart
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ Finset.range 3, ‖SmoothChartHBDyadicPartition.scalar j *
          (∑ bs ∈ ActualLowerNormalizedAtlasOccurrence.activeBlocks kappa B N cj kappa0 j,
            ActualLowerNormalizedAtlasOccurrence.occurrenceAtom kappa B N cj kappa0 j bs retainEven cap w z L -
              retainedAtom kappa B N cj kappa0 (blockMap j bs) (beforeHBCutoff 1 [cj])
                (fun _ => hbCutoff cj) (rowRoles j) retainEven cap w z L
                (cutoff B N (2*(j+1)) (accuracy+7)))‖ := by
        simp_rw [← mul_sub, ← Finset.sum_sub_distrib]
        exact norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range 3, ‖SmoothChartHBDyadicPartition.scalar j‖ *
          (((ActualLowerNormalizedAtlasOccurrence.activeBlocks kappa B N cj kappa0 j).card : ℝ)*E) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ _bs ∈ ActualLowerNormalizedAtlasOccurrence.activeBlocks kappa B N cj kappa0 j, E := by
            apply Finset.sum_le_sum
            intro bs hbs
            rw [occurrenceAtom_eq_originalAtom]
            exact hrow kappa N cj kappa0 (2*(j+1)) (blockMap j bs) (beforeHBCutoff 1 [cj])
              (fun _ => hbCutoff cj) (rowRoles j) retainEven cap D w z L (accuracy+7)
              hkappa hN (by have := Finset.mem_range.mp hj; omega)
              (actual_meets kappa B N cj kappa0 j hbs) hD hDtheta hQ
          _ = _ := by simp
      _ = chartScalarMass kappa B N cj kappa0 * E := by
        rw [chartScalarMass, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have heq : ActualLowerNormalizedAtlasOccurrence.lowerOccurrenceAtlas kappa B N kappa0 retainEven cap w z L -
      retainedLowerAtlas kappa B N kappa0 retainEven cap w z L accuracy =
        ∑ js ∈ chartBank (2*N) 1,
          (ActualLowerNormalizedAtlasOccurrence.occurrenceChart kappa B N (js.getD 0 0) kappa0 retainEven cap w z L -
            retainedChart kappa B N (js.getD 0 0) kappa0 retainEven cap w z L accuracy) := by
    unfold ActualLowerNormalizedAtlasOccurrence.lowerOccurrenceAtlas retainedLowerAtlas
      ActualLowerNormalizedAtlasOccurrence.lowerQ ActualLowerNormalizedAtlasOccurrence.lowerRho lowerQ lowerRho
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro js hjs
    ring
  rw [heq]
  calc
    _ ≤ ∑ js ∈ chartBank (2*N) 1,
        ‖ActualLowerNormalizedAtlasOccurrence.occurrenceChart kappa B N (js.getD 0 0) kappa0 retainEven cap w z L -
          retainedChart kappa B N (js.getD 0 0) kappa0 retainEven cap w z L accuracy‖ := norm_sum_le _ _
    _ ≤ ∑ js ∈ chartBank (2*N) 1, chartScalarMass kappa B N (js.getD 0 0) kappa0 * E :=
      Finset.sum_le_sum (fun js hjs => hchart _)
    _ = sourceScalarMass kappa B N kappa0 * E := by rw [← Finset.sum_mul]; rfl
    _ ≤ ((7*dyadicConstant^7)*ell^7)*E :=
      mul_le_mul_of_nonneg_right (sourceScalarMass_le kappa B N kappa0 hN) hE
    _ = ((7*dyadicConstant^7)*C0)*(N : ℝ)/logScale (countingScale N)^(accuracy+3) := by
      dsimp [E]
      rw [show accuracy+7+3 = (accuracy+3)+7 by omega, pow_add]
      change _ = ((7*dyadicConstant^7)*C0)*(N : ℝ)/ell^(accuracy+3)
      field_simp [hell.ne']
      ring

/-- The independently defined ORIGINAL sharp prime-product receiver.
Only its Fourier tail is paid: the five original reserves stay literally
in the retained atlas and the two smoothing summands. -/
theorem exists_original_source_fourier_tail_paid (B : ℕ) (theta : ℝ) (htheta : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N kappa0
      (retainEven : List ℕ → Bool) (cap D : ℕ) (w z L : ℝ) (accuracy : ℕ),
      kappa < 1 → 0 < N → 1 ≤ D → (D : ℝ) ≤ (N : ℝ)^theta →
      lowerQ retainEven N cap w z ⊆ Finset.Icc 1 D →
      ‖(Part3.primeProductSignedError 1 N N
          (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L)
          (P5S1SingletonPP.singletonWeight N (fun _ => 1)) : ℂ) -
        (retainedLowerAtlas kappa B N kappa0 retainEven cap w z L accuracy +
          (lowerReserve kappa B N (lowerQ retainEven N cap w z)
            (actualLowerSmallRoughRho retainEven N cap w z L) : ℂ) +
          (upperReserve kappa B N (lowerQ retainEven N cap w z)
            (actualLowerSmallRoughRho retainEven N cap w z L) : ℂ))‖ ≤
        C*(N : ℝ)/logScale (countingScale N)^(accuracy+3) := by
  obtain ⟨C, hC, htail⟩ := exists_original_atlas_tail_paid B theta htheta
  refine ⟨C, hC, ?_⟩
  intro kappa N kappa0 retainEven cap D w z L accuracy hkappa hN hD hDtheta hQ
  rw [ActualLowerNormalizedAtlasOccurrence.original_lower_source_occurrences kappa hkappa]
  simpa only [lowerQ, add_sub_add_right_eq_sub] using
    htail kappa N kappa0 retainEven cap D w z L accuracy hkappa hN hD hDtheta hQ

end
end ImbalancedChen.P5Z.OriginalLowerAtlasFourierTailPaid
