import ImbalancedChen.P4BArbitraryWidthUpperPairOccurrence
import ImbalancedChen.P5ActualHBPostModulusLogCutoff
import ImbalancedChen.P5ActualHBDyadicProductWindow

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual arbitrary-width upper profile on full original HB rectangles.
The complete counting scale is derived from one nonzero source atom;
no coupled product cut is inserted in the rectangle. Units are retained.
-/
namespace ImbalancedChen.P4BArbitraryWidthUpperBlockGeometry
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open P4BOuterRampRoughness P4BArbitraryWidthUpperPairProfile
open P4BArbitraryWidthUpperPairHBNormalization P4BArbitraryWidthUpperPairOccurrence
open P5Z.HBRightClosedDyadicRoles P5Z.ActualHBDyadicProductWindow
open P5Z.ActualHBPostModulusLogCutoff P5Z.ActualAllRankOccurrenceFourierBridge
open P5Z.ActualOccurrencePlateauWordBudget P5Z.OccurrenceEuclideanMixedIntegral
open P5Z.ActualEtaPsiOccurrenceBudget P5Z.ActualEuclideanPhysicalFourier
open P5Z.AllRankCoordinateFourierIBP P5Z.AllRankMixedOperatorBudget

variable {m : ℕ}

def blockIntegers : Block → Finset ℕ
  | .unit => {1}
  | .dyadic j => Finset.Ioc (2^j) (2^(j+1))

def rectangle (bs : Fin m → Block) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun a => blockIntegers (bs a))

def scales (bs : Fin m → Block) : Fin m → ℝ := fun a => (lower (bs a) : ℝ)

theorem scales_pos (bs : Fin m → Block) (a : Fin m) : 0 < scales bs a := by
  exact_mod_cast lower_pos (bs a)

theorem rectangle_owns (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) (a : Fin m) : Owns (bs a) (n a) := by
  have h := Fintype.mem_piFinset.mp hn a
  cases hba : bs a <;> simpa [blockIntegers, hba, Owns] using h

theorem rectangle_bounds (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) (a : Fin m) :
    0 < n a ∧ scales bs a ≤ (n a : ℝ) ∧ (n a : ℝ) ≤ 2 * scales bs a := by
  have h := owns_bounds (rectangle_owns bs hn a)
  refine ⟨(lower_pos (bs a)).trans_le h.1, ?_, ?_⟩
  · exact_mod_cast h.1
  · exact_mod_cast h.2

theorem rectangle_plateau (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) : plateau m (logOccurrence (scales bs) n) = 1 := by
  unfold plateau
  apply Finset.prod_eq_one
  intro a ha
  obtain ⟨hnpos, hlo, hhi⟩ := rectangle_bounds bs hn a
  apply c_eq_one
  constructor
  · apply Real.log_nonneg
    exact (le_div_iff₀ (scales_pos bs a)).mpr (by simpa using hlo)
  · apply Real.log_le_log (div_pos (by exact_mod_cast hnpos) (scales_pos bs a))
    exact (div_le_iff₀ (scales_pos bs a)).mpr hhi

/-- Both ORIGINAL group logarithms remain in this integer value via
J's exact groupChart_nat, including totalized unit cases. -/
def integerProfile (b kappa width : ℝ) (N : ℕ) (owner : Fin m → Fin 2)
    (R : Fin 2 → ℝ) (kappa0 : ℝ) (n : Fin m → ℕ) : ℝ :=
  groupChart b kappa width N kappa0 R
    (fun i => (integerGroupProduct owner n i : ℝ))

def blockChart (b kappa width : ℝ) (N : ℕ) (owner : Fin m → Fin 2)
    (bs : Fin m → Block) (R : Fin 2 → ℝ) (kappa0 : ℝ) : V m → ℂ :=
  euclideanChart b kappa width N owner (scales bs) R kappa0

/-- Exact source evaluation at every original rectangle point, including
unit blocks (whose log-coordinate is zero). No strict-left unit fiction. -/
theorem blockChart_integer (b kappa width : ℝ) (N : ℕ)
    (owner : Fin m → Fin 2) (bs : Fin m → Block) (R : Fin 2 → ℝ) (kappa0 : ℝ)
    {n : Fin m → ℕ} (hn : n ∈ rectangle bs) :
    blockChart b kappa width N owner bs R kappa0
      (WithLp.toLp 2 (logOccurrence (scales bs) n)) =
        (integerProfile b kappa width N owner R kappa0 n : ℂ) := by
  have hpos : ∀ a, 0 < n a := fun a => (rectangle_bounds bs hn a).1
  rw [blockChart, euclideanChart, euclideanLift_toLp,
    occurrenceChart_eq_groupChart, rectangle_plateau bs hn, mul_one]
  simp_rw [groupProduct_logOccurrence owner (scales bs) n (scales_pos bs) hpos]
  rfl

theorem integerProfile_original_logs {b kappa nu r width : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    (N : ℕ) (owner : Fin m → Fin 2) (R : Fin 2 → ℝ) (kappa0 : ℝ)
    (n : Fin m → ℕ) :
    integerProfile b kappa width N owner R kappa0 n =
      P5Z.LicensedOriginalIntegerProfile.chartAmbient
        (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N)
        chi eta (N : ℝ) kappa0 R
        (fun i => (integerGroupProduct owner n i : ℝ)) /
          ∏ i, Real.log (integerGroupProduct owner n i : ℝ) :=
  groupChart_nat hb hnu hr hwidth hgap N kappa0 R (integerGroupProduct owner n)

def Meets (b kappa width : ℝ) (N : ℕ) (owner : Fin m → Fin 2)
    (bs : Fin m → Block) (R : Fin 2 → ℝ) (kappa0 : ℝ) : Prop :=
  ∃ n ∈ rectangle bs, integerProfile b kappa width N owner R kappa0 n ≠ 0

theorem integerProfile_support {b kappa nu r width : ℝ} {N : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    (owner : Fin m → Fin 2) (R : Fin 2 → ℝ) (kappa0 : ℝ) {n : Fin m → ℕ}
    (hn : integerProfile b kappa width N owner R kappa0 n ≠ 0) :
    (completeProduct n : ℝ) < Real.exp width * (N : ℝ) := by
  have hnrm : normalizedProfile b kappa width N
      (fun i => (integerGroupProduct owner n i : ℝ)) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  have hs := (normalized_support hb hnu hr hwidth hgap hnrm).2.2.2.2
  have hg : (integerGroupProduct owner n 0 : ℝ) * integerGroupProduct owner n 1 =
      (completeProduct n : ℝ) := by
    have h := congrArg (fun t : ℕ => (t : ℝ)) (complete_product_grouped owner n)
    simpa only [Fin.prod_univ_two, Nat.cast_mul, Nat.cast_prod, completeProduct] using h
  rwa [hg] at hs

theorem rectangle_product_lower (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) : (∏ a, scales bs a) ≤ (completeProduct n : ℝ) := by
  rw [completeProduct, Nat.cast_prod]
  exact Finset.prod_le_prod (fun a ha => (scales_pos bs a).le)
    (fun a ha => (rectangle_bounds bs hn a).2.1)

theorem rectangle_product_upper (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) :
    (completeProduct n : ℝ) ≤ (2 : ℝ)^m * ∏ a, scales bs a := by
  rw [completeProduct, Nat.cast_prod]
  calc
    _ ≤ ∏ a : Fin m, 2 * scales bs a := Finset.prod_le_prod
      (fun a ha => Nat.cast_nonneg _) (fun a ha => (rectangle_bounds bs hn a).2.2)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- One global scale for absolute tail counting, uniform over ALL legal
widths. Retained arithmetic modes retain their own original local scale. -/
def scaleFactor : ℝ := 4096 * Real.exp 1
def countingScale (N : ℕ) : ℝ := scaleFactor * (N : ℝ)

theorem scaleFactor_one_le : 1 ≤ scaleFactor := by
  have h : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  dsimp [scaleFactor]
  linarith

theorem target_le_countingScale (N : ℕ) : (N : ℝ) ≤ countingScale N := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right scaleFactor_one_le (Nat.cast_nonneg N)

theorem countingScale_one_le {N : ℕ} (hN : 0 < N) : 1 ≤ countingScale N :=
  (by exact_mod_cast hN : (1 : ℝ) ≤ N).trans (target_le_countingScale N)

/-- One actual nonzero integer source point bounds the whole full
rectangle by 2^12 times exp(1)N, independently of width and of rho. -/
theorem rectangle_counting_scale {b kappa nu r width : ℝ} {N : ℕ}
    (hb : 0 < b) (hkappa : 0 < kappa) (hnu : 0 < nu) (hr : 0 < r)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - nu * r)
    (owner : Fin m → Fin 2) (bs : Fin m → Block) (R : Fin 2 → ℝ) (kappa0 : ℝ)
    (hm : m ≤ 12) (hMeet : Meets b kappa width N owner bs R kappa0)
    {n : Fin m → ℕ} (hn : n ∈ rectangle bs) :
    (∀ a, 0 < n a) ∧ (completeProduct n : ℝ) ≤ countingScale N := by
  obtain ⟨v, hv, hvnz⟩ := hMeet
  have hlo := (rectangle_product_lower bs hv).trans
    (integerProfile_support hb hnu hr hwidth hgap owner R kappa0 hvnz).le
  have hw := legal_width_le_one hb hkappa hnu hr hgap
  have hexp : Real.exp width * (N : ℝ) ≤ Real.exp 1 * (N : ℝ) :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hw) (Nat.cast_nonneg N)
  have hpow : (2 : ℝ)^m ≤ 4096 := by
    calc
      _ ≤ (2 : ℝ)^12 := pow_le_pow_right₀ (by norm_num) hm
      _ = 4096 := by norm_num
  refine ⟨fun a => (rectangle_bounds bs hn a).1, ?_⟩
  calc
    _ ≤ (2 : ℝ)^m * ∏ a, scales bs a := rectangle_product_upper bs hn
    _ ≤ 4096 * (Real.exp 1 * (N : ℝ)) := mul_le_mul hpow (hlo.trans hexp)
      (Finset.prod_nonneg (fun a ha => (scales_pos bs a).le)) (by norm_num)
    _ = countingScale N := by dsimp [countingScale, scaleFactor]; ring

/-- Native inverse-Fourier cube tail from J's proved mixed jets. The
constant precedes every legal width; the width^(-24) cost is explicit. -/
theorem exists_actual_upper_cube_tail :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      0 < b → b ≤ 1 → 0 < kappa → 0 < nu → 0 < r → 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ (N m : ℕ) (owner : Fin m → Fin 2) (bs : Fin m → Block)
        (R : Fin 2 → ℝ) (kappa0 H : ℝ),
      0 < N → (∀ i, 0 < R i) → m ≤ 12 → 0 < H → ∀ z : V m,
        ‖blockChart b kappa width N owner bs R kappa0 z -
          truncatedPhysical m (blockChart b kappa width N owner bs R kappa0) H z‖ ≤
            (m : ℝ) * (C / width^24) / H := by
  obtain ⟨C, hC, hbudget⟩ := exists_actual_mixedD_width_budget
  refine ⟨C, hC, ?_⟩
  intro b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
    N m owner bs R kappa0 H hN hR hm hH z
  have hs := occurrenceChart_smooth hb hnu hr hwidth hgap N owner (scales bs) R kappa0
  have hc := occurrenceChart_compact b kappa width N owner (scales bs) R kappa0
  exact (actual_uniform_truncation_error m _
    (euclideanLift_smooth m _ hs) (euclideanLift_compact m _ hc) H hH z).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (hbudget b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
            N m owner (scales bs) R kappa0 (by exact_mod_cast hN) (scales_pos bs) hR hm)
          (Nat.cast_nonneg m)) hH.le)

end
end ImbalancedChen.P4BArbitraryWidthUpperBlockGeometry
