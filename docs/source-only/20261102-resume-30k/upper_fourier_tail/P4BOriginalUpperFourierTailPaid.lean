import ImbalancedChen.P4BArbitraryWidthUpperPostModulusTail
import ImbalancedChen.P4BUpperPairOrderedRowModes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual arbitrary-width upper source with its original two-group
chart/HB inventory. Fourteen logarithmic powers pay the actual finite
scalar mass. The three original reserves remain literally unchanged.
-/
namespace ImbalancedChen.P4BOriginalUpperFourierTailPaid
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOuterRampRoughness P4BArbitraryWidthUpperPairProfile
open P4BArbitraryWidthUpperBlockGeometry P4BArbitraryWidthUpperPostModulusTail
open P4BUpperPairOrderedRowGeometry P4BUpperPairOrderedRowModes
open P5Z.ActualHBPostModulusLogCutoff P5Z.ActualCompleteModulusFourierTail
open P5Z.CompleteProductTailDivisorBudgets
open P5Z.ActualHBDyadicOccurrenceFamily P5Z.HBRightClosedDyadicRoles
open P5Z.PerGroupIntegerHBAtlasPushforward P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.OriginalPrimeAllGroupHBDiscrepancy P5Z.OrderedFactorTupleRectangleReindex
open P5Z.ActualRoughHeathBrownWords

def dyadicConstant : ℝ := 2 + 1 / Real.log 2

theorem dyadicConstant_pos : 0 < dyadicConstant := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold dyadicConstant
  positivity

/-- Elementary count for the actual dyadic labels; no atlas or Family
estimate is imported to obtain the two-group scalar inventory below. -/
theorem log2_count_le {X : ℝ} (hX : 1 ≤ X) (n : ℕ) (hn : (n : ℝ) ≤ 6 * X) :
    ((Nat.log2 n + 2 : ℕ) : ℝ) ≤ dyadicConstant * logScale X := by
  have hL : 1 ≤ logScale X := logScale_one_le hX
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hz : n = 0
  · subst n
    simp only [Nat.log2_zero, Nat.zero_add, Nat.cast_ofNat]
    have hC : 2 ≤ dyadicConstant := by
      unfold dyadicConstant
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) h2.le]
    exact hC.trans (le_mul_of_one_le_right dyadicConstant_pos.le hL)
  · have hp : (2 : ℕ) ^ Nat.log2 n ≤ n := (Nat.le_log2 hz).mp le_rfl
    have hpR : (2 : ℝ) ^ Nat.log2 n ≤ 7 * X :=
      (show (2 : ℝ) ^ Nat.log2 n ≤ (n : ℝ) by exact_mod_cast hp).trans (by linarith)
    have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpR
    rw [Real.log_pow] at hl
    have hj : (Nat.log2 n : ℝ) ≤ Real.log (7 * X) / Real.log 2 :=
      (le_div_iff₀ h2).mpr (by simpa only [mul_comm] using hl)
    simp only [Nat.cast_add, Nat.cast_ofNat]
    unfold dyadicConstant logScale at *
    have hxlog : 0 ≤ Real.log (7 * X) := Real.log_nonneg (by linarith)
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) h2.le]

def groupScalarMass (cj : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 3, ‖P5Z.SmoothChartHBDyadicPartition.scalar j‖ *
    ((blockWords (hbCap cj) (2*(j+1))).card : ℝ)

theorem groupScalarMass_nonneg (cj : ℕ) : 0 ≤ groupScalarMass cj :=
  Finset.sum_nonneg (fun j hj => mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

theorem groupScalarMass_le (cj : ℕ) :
    groupScalarMass cj ≤ 7 * ((Nat.log2 (hbCap cj-1)+2 : ℕ) : ℝ)^6 := by
  let B : ℝ := (Nat.log2 (hbCap cj-1)+2 : ℕ)
  have hB : 1 ≤ B := by dsimp [B]; norm_cast; omega
  have h2 : B^2 ≤ B^6 := pow_le_pow_right₀ hB (by omega)
  have h4 : B^4 ≤ B^6 := pow_le_pow_right₀ hB (by omega)
  have heq : groupScalarMass cj = 3*B^2+3*B^4+B^6 := by
    unfold groupScalarMass
    simp only [blockWords_card]
    norm_num [Finset.sum_range_succ, P5Z.SmoothChartHBDyadicPartition.scalar,
      Complex.norm_real, Real.norm_eq_abs, B]
  rw [heq]
  change _ ≤ 7*B^6
  linarith

/-- Source membership fixes each original group cap, independently of
the physical modulus cap and without replacing N by a residual quotient. -/
theorem actual_hbCap_le {N : ℕ} (hN : 0 < N) {js : List ℕ}
    (hjs : js ∈ chartBank N 2) {cj : ℕ} (hcj : cj ∈ js) : hbCap cj ≤ 4*N := by
  have hspec := words_spec (Finset.range (cutoffIndex N+1)) 2 js hjs
  have hj := Finset.mem_range.mp (hspec.2 cj hcj)
  have hj' : cj ≤ Nat.log2 N+1 := by
    change cj < (Nat.log2 N+1)+1 at hj
    omega
  have hpow : (2 : ℕ)^Nat.log2 N ≤ N := Nat.log2_self_le hN.ne'
  calc
    hbCap cj = 2^(cj+1) := rfl
    _ ≤ 2^(Nat.log2 N+2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4 * 2^Nat.log2 N := by rw [pow_add]; ring
    _ ≤ 4*N := Nat.mul_le_mul_left 4 hpow

def sourceScalarMass (N : ℕ) : ℝ :=
  ∑ js ∈ chartBank N 2, groupScalarMass (js.getD 0 0) * groupScalarMass (js.getD 1 0)

/-- Two original smooth chart coordinates and at most twelve individual
HB coordinates cost exactly a fixed exponent 14 in the literal inventory. -/
theorem sourceScalarMass_le {N : ℕ} (hN : 0 < N) :
    sourceScalarMass N ≤
      (49*dyadicConstant^14) * logScale (countingScale N)^14 := by
  let X := countingScale N
  let L := dyadicConstant*logScale X
  have hX : 1 ≤ X := countingScale_one_le hN
  have hL0 : 0 ≤ L := mul_nonneg dyadicConstant_pos.le (zero_le_one.trans (logScale_one_le hX))
  have hNX : (N : ℝ) ≤ X := target_le_countingScale N
  have hchart := log2_count_le hX N (by linarith : (N : ℝ) ≤ 6*X)
  have hgroup (js : List ℕ) (hjs : js ∈ chartBank N 2) (cj : ℕ) (hcj : cj ∈ js) :
      groupScalarMass cj ≤ 7*L^6 := by
    have hh := actual_hbCap_le hN hjs hcj
    have hs : hbCap cj-1 ≤ 4*N := (Nat.sub_le _ _).trans hh
    have hsR : ((hbCap cj-1 : ℕ) : ℝ) ≤ 4*(N : ℝ) := by exact_mod_cast hs
    have hhb : ((hbCap cj-1 : ℕ) : ℝ) ≤ 6*X := by linarith
    exact (groupScalarMass_le cj).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (log2_count_le hX _ hhb) 6) (by norm_num))
  have hp (js : List ℕ) (hjs : js ∈ chartBank N 2) :
      groupScalarMass (js.getD 0 0)*groupScalarMass (js.getD 1 0) ≤ 49*L^12 := by
    have hlen := (words_spec _ _ _ hjs).1
    obtain ⟨cj, ck, rfl⟩ : ∃ cj ck, js = [cj,ck] := by
      cases js with
      | nil => simp at hlen
      | cons cj tail =>
        cases tail with
        | nil => simp at hlen
        | cons ck rest =>
          have he : rest = [] := List.length_eq_zero.mp (by simpa using hlen)
          subst rest
          exact ⟨cj,ck,rfl⟩
    have h1 := hgroup [cj,ck] hjs cj (by simp)
    have h2 := hgroup [cj,ck] hjs ck (by simp)
    change groupScalarMass cj*groupScalarMass ck ≤ 49*L^12
    exact (mul_le_mul h1 h2 (groupScalarMass_nonneg ck) (by positivity)).trans_eq
      (by ring : (7*L^6)*(7*L^6) = 49*L^12)
  calc
    sourceScalarMass N ≤ ∑ _js ∈ chartBank N 2, 49*L^12 := Finset.sum_le_sum hp
    _ = ((Nat.log2 N+2 : ℕ) : ℝ)^2*(49*L^12) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [chartBank, words_card, Finset.card_range, Nat.cast_pow, cutoffIndex, Nat.add_assoc]
    _ ≤ L^2*(49*L^12) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hchart 2) (by positivity)
    _ = (49*dyadicConstant^14)*logScale (countingScale N)^14 := by
      dsimp [L, X]
      ring

def groupEval (cj : ℕ) (F : ℕ → List Block → ℂ) : ℂ :=
  ∑ j ∈ Finset.range 3, P5Z.SmoothChartHBDyadicPartition.scalar j *
    ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)), F j bs

theorem groupEval_sub_le (cj : ℕ) (F G : ℕ → List Block → ℂ) (E : ℝ)
    (herr : ∀ j ∈ Finset.range 3, ∀ bs ∈ blockWords (hbCap cj) (2*(j+1)),
      ‖F j bs-G j bs‖ ≤ E) :
    ‖groupEval cj F-groupEval cj G‖ ≤ groupScalarMass cj*E := by
  unfold groupEval
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range 3, ‖P5Z.SmoothChartHBDyadicPartition.scalar j *
        ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)), (F j bs-G j bs)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range 3, ‖P5Z.SmoothChartHBDyadicPartition.scalar j‖ *
        (((blockWords (hbCap cj) (2*(j+1))).card : ℝ)*E) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _bs ∈ blockWords (hbCap cj) (2*(j+1)), E :=
          Finset.sum_le_sum (fun bs hbs => herr j hj bs hbs)
        _ = _ := by simp
    _ = _ := by
      rw [groupScalarMass, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

def retainedRowBank (b kappa width : ℝ) (N K cj ck : ℕ) (kappa0 : ℝ)
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (accuracy : ℕ) : ℂ :=
  groupEval cj (fun j bs => groupEval ck (fun l cs =>
    retainedActiveAtom b kappa width N (pairOwner (2*(j+1)) (2*(l+1)))
      (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
      (![R cj,R ck]) kappa0 (beforeHBCutoff K [cj,ck])
      (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l)) nu r epsilon retain cap
      (cutoff N (2*(j+1)+2*(l+1)) (accuracy+14))))

/-- This adapter identifies independent upper definitions; it is not a
source-equality premise. Both rectangles retain ordered multiplicity. -/
theorem rowAtom_eq_originalAtom {a d : ℕ} (b kappa width : ℝ) (N : ℕ)
    (kappa0 : ℝ) (cj ck : ℕ) (bs : Fin (a+d) → Block) (Z : ℝ)
    (ys : Fin (a+d) → ℝ) (rs : Fin (a+d) → Role) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    rowAtom b kappa width N kappa0 cj ck bs Z ys rs
      (attachedUpperModuli nu r epsilon retain cap N)
      (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) =
    originalAtom b kappa width N (pairOwner a d) bs (![R cj,R ck]) kappa0 Z ys rs
      nu r epsilon retain cap := rfl

section Source
variable {b kappa nu r width : ℝ}
variable (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hw : 0 < width)
variable (hgap : 2*width ≤ baseline b kappa - nu*r)

/-- Same actual trim, subtractive proper-power and additive rough-prime
reserves as the independent raw source identity; none is dropped or paid. -/
def retainedUpperAtlas (N K : ℕ) (kappa0 epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (accuracy : ℕ) : ℂ :=
  trimReserve (licence hb hnu hr hw hgap N) N N kappa0
      (attachedUpperModuli nu r epsilon retain cap N)
      (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) +
    ∑ js ∈ chartBank N 2,
      (retainedRowBank b kappa width N K (js.getD 0 0) (js.getD 1 0) kappa0
          nu r epsilon retain cap accuracy -
        properPowerReserve (licence hb hnu hr hw hgap N) K N N kappa0
          (attachedUpperModuli nu r epsilon retain cap N)
          (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) js +
        roughPrimeReserve (licence hb hnu hr hw hgap N) K N N kappa0
          (attachedUpperModuli nu r epsilon retain cap N)
          (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) js)

end Source

theorem exists_actual_upper_atlas_tail_paid (theta : ℝ) (htheta : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      ∀ hb : 0 < b, b ≤ 1 → 0 < kappa → ∀ hnu : 0 < nu, ∀ hr : 0 < r,
      ∀ hw : 0 < width, ∀ hgap : 2*width ≤ baseline b kappa-nu*r,
      ∀ (N K D accuracy : ℕ) (kappa0 epsilon : ℝ)
        (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      0 < N → 1 ≤ D → (D : ℝ) ≤ (N : ℝ)^theta → Supported nu r epsilon retain cap N D →
      ‖restoredRows hb hnu hr hw hgap N K kappa0
          (attachedUpperModuli nu r epsilon retain cap N)
          (attachedUpperCoefficient nu r epsilon retain cap N) -
        retainedUpperAtlas hb hnu hr hw hgap N K kappa0 epsilon retain cap accuracy‖ ≤
        (C/width^24)*(N : ℝ)/logScale (countingScale N)^(accuracy+3) := by
  obtain ⟨C0, hC0, hrow⟩ := exists_every_row_upper_log_saving theta htheta
  have hdc : 0 < dyadicConstant := dyadicConstant_pos
  refine ⟨(49*dyadicConstant^14)*C0, by positivity, ?_⟩
  intro b kappa nu r width hb hbOne hkappa hnu hr hw hgap
    N K D accuracy kappa0 epsilon retain cap hN hD hDtheta hSupport
  let ell := logScale (countingScale N)
  let E := (C0/width^24)*(N : ℝ)/ell^(accuracy+14+3)
  have hell : 0 < ell := lt_of_lt_of_le zero_lt_one (logScale_one_le (countingScale_one_le hN))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hchart (cj ck : ℕ) :
      ‖rowBank b kappa width N K cj ck kappa0
          (attachedUpperModuli nu r epsilon retain cap N)
          (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) -
        retainedRowBank b kappa width N K cj ck kappa0 nu r epsilon retain cap accuracy‖ ≤
      (groupScalarMass cj*groupScalarMass ck)*E := by
    change ‖groupEval cj _-groupEval cj _‖ ≤ _
    rw [mul_assoc]
    apply groupEval_sub_le
    intro j hj bs hbs
    apply groupEval_sub_le
    intro l hl cs hcs
    rw [rowAtom_eq_originalAtom]
    exact hrow b kappa nu r width hb hbOne hkappa hnu hr hw hgap
      N (2*(j+1)+2*(l+1)) (pairOwner (2*(j+1)) (2*(l+1)))
      (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
      (![R cj,R ck]) kappa0 (beforeHBCutoff K [cj,ck])
      (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l)) epsilon retain cap D (accuracy+14)
      hN (by intro i; fin_cases i <;> exact R_pos _)
      (by have hj' := Finset.mem_range.mp hj; have hl' := Finset.mem_range.mp hl; omega)
      hD hDtheta hSupport
  have heq : restoredRows hb hnu hr hw hgap N K kappa0
      (attachedUpperModuli nu r epsilon retain cap N) (attachedUpperCoefficient nu r epsilon retain cap N) -
      retainedUpperAtlas hb hnu hr hw hgap N K kappa0 epsilon retain cap accuracy =
      ∑ js ∈ chartBank N 2,
        (rowBank b kappa width N K (js.getD 0 0) (js.getD 1 0) kappa0
          (attachedUpperModuli nu r epsilon retain cap N)
          (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) -
        retainedRowBank b kappa width N K (js.getD 0 0) (js.getD 1 0) kappa0
          nu r epsilon retain cap accuracy) := by
    unfold restoredRows retainedUpperAtlas
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro js hjs
    ring
  rw [heq]
  calc
    _ ≤ ∑ js ∈ chartBank N 2, ‖rowBank b kappa width N K (js.getD 0 0) (js.getD 1 0) kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (fun q => (attachedUpperCoefficient nu r epsilon retain cap N q : ℂ)) -
        retainedRowBank b kappa width N K (js.getD 0 0) (js.getD 1 0) kappa0
          nu r epsilon retain cap accuracy‖ := norm_sum_le _ _
    _ ≤ ∑ js ∈ chartBank N 2,
        (groupScalarMass (js.getD 0 0)*groupScalarMass (js.getD 1 0))*E :=
      Finset.sum_le_sum (fun js hjs => hchart _ _)
    _ = sourceScalarMass N*E := by rw [← Finset.sum_mul]; rfl
    _ ≤ ((49*dyadicConstant^14)*ell^14)*E :=
      mul_le_mul_of_nonneg_right (sourceScalarMass_le hN) hE
    _ = (((49*dyadicConstant^14)*C0)/width^24)*(N : ℝ)/
        logScale (countingScale N)^(accuracy+3) := by
      dsimp [E]
      rw [show accuracy+14+3 = (accuracy+3)+14 by omega, pow_add]
      change _ = (((49*dyadicConstant^14)*C0)/width^24)*(N : ℝ)/ell^(accuracy+3)
      field_simp [hell.ne', hw.ne']
      ring

/-- Actual hUniformPP source, with one threshold BEFORE every legal
width. Only the Fourier tail is paid; actual retained modes and all three
source reserves remain in retainedUpperAtlas. -/
theorem exists_eventual_original_upper_fourier_tail_paid (theta : ℝ) (htheta : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r : ℝ,
      ∀ hb : 0 < b, b ≤ 1 → 0 < kappa → ∀ hnu : 0 < nu, ∀ hr : 0 < r,
      ∀ᶠ N : ℕ in atTop, ∀ width : ℝ, ∀ hw : 0 < width,
      ∀ hgap : 2*width ≤ baseline b kappa-nu*r,
      ∀ (K D accuracy : ℕ) (kappa0 epsilon : ℝ)
        (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      1 ≤ D → (D : ℝ) ≤ (N : ℝ)^theta → Supported nu r epsilon retain cap N D →
      ‖(Part3.primeProductSignedError 2 N N
          (attachedUpperModuli nu r epsilon retain cap N)
          (attachedUpperCoefficient nu r epsilon retain cap N)
          (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) : ℂ) -
        retainedUpperAtlas hb hnu hr hw hgap N K kappa0 epsilon retain cap accuracy‖ ≤
        (C/width^24)*(N : ℝ)/logScale (countingScale N)^(accuracy+3) := by
  obtain ⟨C, hC, htail⟩ := exists_actual_upper_atlas_tail_paid theta htheta
  refine ⟨C, hC, ?_⟩
  intro b kappa nu r hb hbOne hkappa hnu hr
  filter_upwards [eventually_attachedUpper_source_rows hb hnu hr,
    eventually_ge_atTop (1 : ℕ)] with N hs hN
  intro width hw hgap K D accuracy kappa0 epsilon retain cap hD hDtheta hSupport
  rw [hs width hw hgap K kappa0 epsilon retain cap]
  exact htail b kappa nu r width hb hbOne hkappa hnu hr hw hgap
    N K D accuracy kappa0 epsilon retain cap hN hD hDtheta hSupport

end
end ImbalancedChen.P4BOriginalUpperFourierTailPaid
