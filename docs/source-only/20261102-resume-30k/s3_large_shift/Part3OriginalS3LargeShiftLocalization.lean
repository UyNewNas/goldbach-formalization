import ImbalancedChen.Part3OriginalS3RoughPairGcdResidual
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original medium completion 169--181.  Orient the ACTUAL physical deleted
pair by its larger shifted divisor count, without imposing a new cutoff.
All q,d,r,s labels and both actual Lambda factors are paid inside a fixed
seventh shifted moment.  The result controls the absolute correction mass,
so it also applies when the original cutoff is reinstated after additional
gcd or separation filters.  No moment estimate or largeShift estimate is
a premise.  The arbitrary-logarithmic Shiu payment is still separate.
-/
namespace ImbalancedChen.Part3.OriginalS3LargeShiftLocalization20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3ClosePairCount20261102 OriginalS3ClosePairResidual20261102
open MediumLiteralS3Stages20261028 MediumLiteralS3Deleted20261028
open MediumDeletedIndicatorShift20261028 MediumActualPreliminaryCauchy20261028
open MediumActualPsiPreliminaryDispersion20261028 MediumPrimitivePsiSource20261028
open MediumGlobalDyadicOwnership20261028 MediumActualDiagonalDivisorPayment20261028
open MediumNativePrincipalSource20261028 OriginalSamePsiS1OwnedAtlas
open OriginalMediumS1SeparatedDivisorMean OriginalGevreyFinalPsi20261028
open OriginalGevreyPoissonPacket20261028 OriginalGevreySharedRowDictionary20261028
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ElementaryTauTruncation.IntervalPayment

def pairFlip (t : PairIndex) : PairIndex := (t.1, t.2.2, t.2.1)

@[simp] theorem pairFlip_involutive (t : PairIndex) : pairFlip (pairFlip t) = t := rfl

theorem pairFlip_mem_offDiagonal {atom : MediumAtom} {k : Key} {t : PairIndex}
    (ht : t ∈ offDiagonalCarrier atom k) : pairFlip t ∈ offDiagonalCarrier atom k := by
  obtain ⟨ht, hne⟩ := mem_filter.mp ht
  obtain ⟨ho, hi⟩ := mem_product.mp ht
  obtain ⟨hl, hr⟩ := mem_product.mp hi
  exact mem_filter.mpr ⟨mem_product.mpr ⟨ho, mem_product.mpr ⟨hr, hl⟩⟩,
    by simpa only [oldIndex, pairFlip, ne_eq, eq_comm] using hne⟩

/-- This symmetry is used only for norms of the original physical pair.
It makes no Hermitian assertion about the later independently polarized
E3 source. -/
theorem pairFlip_term_norm (atom : MediumAtom) (z y : ℝ) (k : Key) (t : PairIndex) :
    ‖S3DeletedTerm atom z y k (pairFlip t)‖ = ‖S3DeletedTerm atom z y k t‖ := by
  simp only [S3DeletedTerm, pairCoefficient, pairFlip, firstDeleted, secondDeleted,
    oldIndex, norm_mul, norm_star]
  ring

theorem deletedTerm_nonzero_shifts {atom : MediumAtom} {z y : ℝ} {k : Key}
    {t : PairIndex} (hne : S3DeletedTerm atom z y k t ≠ 0) :
    shiftAbs atom (firstMN t) ≠ 0 ∧ shiftAbs atom (secondMN t) ≠ 0 := by
  have h1 : firstDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro hz
    exact hne (by simp [S3DeletedTerm, hz])
  have h2 : secondDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro hz
    exact hne (by simp [S3DeletedTerm, hz])
  exact ⟨Int.natAbs_ne_zero.mpr (deletedIndicator_nonzero_data h1).1,
    Int.natAbs_ne_zero.mpr (deletedIndicator_nonzero_data h2).1⟩

/-- The threshold on the right is the actual larger value, not a
strengthened logarithmic cutoff. Ties may belong to both orientations;
the final factor two explicitly pays that harmless overlap. -/
def dominantLarge (atom : MediumAtom) (z y : ℝ) (k : Key) (H : ℝ) : Finset PairIndex :=
  (offDiagonalCarrier atom k).filter (fun t =>
    ShiftCut atom (tauR (shiftAbs atom (firstMN t))) t ∧
    H < tauR (shiftAbs atom (firstMN t)) ∧ S3DeletedTerm atom z y k t ≠ 0)

theorem dominantLarge_as_activeClose {atom : MediumAtom} {z y H : ℝ} {k : Key}
    {t : PairIndex} (ht : t ∈ dominantLarge atom z y k H) :
    t ∈ activeClose atom z y k (tauR (shiftAbs atom (firstMN t)))
      (|(t.2.1.2 : ℝ) - t.2.2.2| + 1) := by
  obtain ⟨hoff, hcut, hlarge, hne⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨hoff, hcut, by unfold Close; linarith, hne⟩

/-- The receiver needed by cutoff deletion and by later reinstatement
is a sum of norms. A signed largeShift bound alone would not control
arbitrary further arithmetic masks. -/
def largeShiftMass (atom : MediumAtom) (z y : ℝ) (k : Key) (H : ℝ) : ℝ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ¬ShiftCut atom H t then ‖S3DeletedTerm atom z y k t‖ else 0

theorem largeShiftMass_le_two_dominant (atom : MediumAtom) (z y : ℝ)
    (k : Key) (H : ℝ) :
    largeShiftMass atom z y k H ≤
      2 * ∑ t ∈ dominantLarge atom z y k H, ‖S3DeletedTerm atom z y k t‖ := by
  let F : PairIndex → ℝ := fun t =>
    if t ∈ dominantLarge atom z y k H then ‖S3DeletedTerm atom z y k t‖ else 0
  have hpoint (t : PairIndex) (ht : t ∈ offDiagonalCarrier atom k) :
      (if ¬ShiftCut atom H t then ‖S3DeletedTerm atom z y k t‖ else 0) ≤
        F t + F (pairFlip t) := by
    have hF (u : PairIndex) : 0 ≤ F u := by dsimp [F]; split_ifs <;> positivity
    by_cases hcut : ShiftCut atom H t
    · simpa only [hcut, not_true_eq_false, if_false] using add_nonneg (hF t) (hF (pairFlip t))
    by_cases hne : S3DeletedTerm atom z y k t = 0
    · simp only [hcut, not_false_eq_true, if_true, hne, norm_zero]
      exact add_nonneg (hF t) (hF (pairFlip t))
    obtain ⟨h1, h2⟩ := deletedTerm_nonzero_shifts hne
    by_cases hdom : tauR (shiftAbs atom (secondMN t)) ≤ tauR (shiftAbs atom (firstMN t))
    · have hlarge : H < tauR (shiftAbs atom (firstMN t)) := by
        by_contra! hsmall
        exact hcut ⟨h1, h2, hsmall, hdom.trans hsmall⟩
      have hmem : t ∈ dominantLarge atom z y k H :=
        mem_filter.mpr ⟨ht, ⟨h1, h2, le_rfl, hdom⟩, hlarge, hne⟩
      simp only [hcut, not_false_eq_true, if_true]
      have hFt : F t = ‖S3DeletedTerm atom z y k t‖ := by simp only [F, if_pos hmem]
      rw [hFt]
      exact le_add_of_nonneg_right (hF (pairFlip t))
    · have hdom' := (lt_of_not_ge hdom).le
      have hlarge : H < tauR (shiftAbs atom (secondMN t)) := by
        by_contra! hsmall
        exact hcut ⟨h1, h2, hdom'.trans hsmall, hsmall⟩
      have hflipne : S3DeletedTerm atom z y k (pairFlip t) ≠ 0 := by
        intro hz
        have hh := pairFlip_term_norm atom z y k t
        rw [hz, norm_zero] at hh
        exact hne (norm_eq_zero.mp hh.symm)
      have hmem : pairFlip t ∈ dominantLarge atom z y k H := by
        apply mem_filter.mpr
        refine ⟨pairFlip_mem_offDiagonal ht, ?_, ?_, hflipne⟩
        · exact ⟨h2, h1, le_rfl, hdom'⟩
        · exact hlarge
      simp only [hcut, not_false_eq_true, if_true]
      have hFt : F (pairFlip t) = ‖S3DeletedTerm atom z y k t‖ := by
        simp only [F, if_pos hmem, pairFlip_term_norm]
      rw [hFt]
      exact le_add_of_nonneg_left (hF t)
  have hflip : (∑ t ∈ offDiagonalCarrier atom k, F (pairFlip t)) =
      ∑ t ∈ offDiagonalCarrier atom k, F t := by
    refine sum_bij (fun t _ => pairFlip t) ?_ ?_ ?_ ?_
    · intro t ht; exact pairFlip_mem_offDiagonal ht
    · intro t ht u hu he
      simpa only [pairFlip_involutive] using congrArg pairFlip he
    · intro u hu
      exact ⟨pairFlip u, pairFlip_mem_offDiagonal hu, pairFlip_involutive u⟩
    · intro t ht; rfl
  have hsum : (∑ t ∈ offDiagonalCarrier atom k, F t) =
      ∑ t ∈ dominantLarge atom z y k H, ‖S3DeletedTerm atom z y k t‖ := by
    calc
      _ = ∑ t ∈ dominantLarge atom z y k H, F t := by
        symm
        apply sum_subset (filter_subset _ _)
        intro t ht hnot
        simp only [F, if_neg hnot]
      _ = _ := sum_congr rfl (fun t ht => by simp only [F, if_pos ht])
  calc
    _ ≤ ∑ t ∈ offDiagonalCarrier atom k, (F t + F (pairFlip t)) := sum_le_sum hpoint
    _ = 2 * ∑ t ∈ dominantLarge atom z y k H, ‖S3DeletedTerm atom z y k t‖ := by
      rw [sum_add_distrib, hflip, hsum]
      ring

def largeFirstPairs (atom : MediumAtom) (H : ℝ) : Finset (ℕ × ℕ) :=
  (actualMN atom).filter (fun p => shiftAbs atom p ≠ 0 ∧ H < tauR (shiftAbs atom p))

def dominantSeconds (atom : MediumAtom) (p qd : ℕ × ℕ) : Finset ℕ :=
  atom.alphaCarrier.filter (fun n =>
    Int.ModEq ((qd.1 * qd.2 : ℕ) : ℤ) (n : ℤ) (p.2 : ℤ) ∧
      shiftAbs atom (p.1, n) ≠ 0 ∧
      tauR (shiftAbs atom (p.1, n)) ≤ tauR (shiftAbs atom p))

/-- Reuse I's explicit decoder: no q,d,r,s occurrence is quotiented away. -/
def dominantCodeCarrier (atom : MediumAtom) (k : Key) (H : ℝ) : Finset CloseCode :=
  (largeFirstPairs atom H).sigma (fun p => (divisorQD atom k p).sigma (fun qd =>
    (dominantSeconds atom p qd).sigma (fun n =>
      (shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1, n)).divisors)))

theorem dominantLarge_maps_to_code {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H : ℝ)
    {t : PairIndex} (ht : t ∈ dominantLarge atom z y k H) :
    closeCode t ∈ dominantCodeCarrier atom k H := by
  have htC := dominantLarge_as_activeClose ht
  obtain ⟨hmn1, hmn2, hqd, hL, hR, hprog⟩ := activeClose_data hA z y k _ _ htC
  obtain ⟨_, hcut, hlarge, _⟩ := mem_filter.mp ht
  have hq : t.1.1 ∣ shiftAbs atom (firstMN t) :=
    dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hL)
  have hd : t.1.2.1 ∣ shiftAbs atom (firstMN t) :=
    dvd_trans (dvd_mul_left _ _) (dvd_trans (dvd_mul_right _ _) hL)
  have hr : t.2.1.1 ∣ shiftAbs atom (firstMN t) := dvd_trans (dvd_mul_left _ _) hL
  have hs : t.2.2.1 ∣ shiftAbs atom (secondMN t) := dvd_trans (dvd_mul_left _ _) hR
  apply mem_sigma.mpr
  refine ⟨mem_filter.mpr ⟨hmn1, hcut.1, hlarge⟩, mem_sigma.mpr ⟨?_, mem_sigma.mpr ⟨?_, ?_⟩⟩⟩
  · exact mem_filter.mpr ⟨mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hq, hcut.1⟩,
      Nat.mem_divisors.mpr ⟨hd, hcut.1⟩⟩, hqd⟩
  · exact mem_filter.mpr ⟨(mem_product.mp hmn2).2, hprog, hcut.2.1, hcut.2.2.2⟩
  · exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hr, hcut.1⟩,
      Nat.mem_divisors.mpr ⟨hs, hcut.2.1⟩⟩

/-- The literal [U,2U] alpha support and primitive ell=qd give the
original U/Y+1 occupancy, including its endpoint one. -/
theorem dominantSeconds_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (k : Key) (p qd : ℕ × ℕ)
    (hqd : qd ∈ nativeQD atom k) :
    ((dominantSeconds atom p qd).card : ℝ) ≤ 2 * atom.U / keyY atom k + 1 := by
  obtain ⟨hell, hlevel, _⟩ := nativeQD_positive_level hA k qd hqd
  have hY := keyY_positive hA k
  have hlevel' : keyY atom k / 2 ≤ ((qd.1 * qd.2 : ℕ) : ℝ) := by
    simpa only [singleZeroY, keyY, keyD, Nat.cast_pow, Nat.cast_ofNat] using hlevel
  have hc := card_real_supported_modEq_dvd_le_lcm (dominantSeconds atom p qd)
    (a := atom.U) (b := 2 * atom.U) (q := qd.1 * qd.2) (d := 1) (r := p.2)
    (by linarith [hA.1]) hell (by norm_num)
    (fun n hn => by
      have hi := mem_Icc.mp (mem_filter.mp (mem_filter.mp hn).1).1
      exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hi.1),
        (show (n : ℝ) ≤ (Nat.floor (2 * atom.U) : ℝ) by exact_mod_cast hi.2).trans
          (Nat.floor_le (by linarith [hA.1]))⟩)
    (fun n hn => (mem_filter.mp hn).2.1) (fun n hn => one_dvd _)
  have hc' : ((dominantSeconds atom p qd).card : ℝ) ≤
      atom.U / ((qd.1 * qd.2 : ℕ) : ℝ) + 1 := by
    simpa only [Nat.lcm_one_left, show 2 * atom.U - atom.U = atom.U by ring] using hc
  apply hc'.trans
  apply add_le_add_right
  apply (div_le_div_iff₀ (by exact_mod_cast hell : (0 : ℝ) < (qd.1 * qd.2 : ℕ)) hY).mpr
  have hh := mul_le_mul_of_nonneg_left hlevel' (show 0 ≤ 2 * atom.U by linarith [hA.1])
  nlinarith

/-- Four divisor multiplicities plus two Lambda norms give order six.
No supremum bound on the other shift is inserted. -/
theorem dominantCode_weight_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (k : Key) (H : ℝ) :
    (∑ v ∈ dominantCodeCarrier atom k H, tauR (shiftAbs atom v.1) ^ 2) ≤
      (2 * atom.U / keyY atom k + 1) *
        ∑ p ∈ largeFirstPairs atom H, tauR (shiftAbs atom p) ^ 6 := by
  let Occ : ℝ := 2 * atom.U / keyY atom k + 1
  have hOcc : 0 ≤ Occ := by have hY := keyY_positive hA k; have hU := hA.1; dsimp [Occ]; positivity
  rw [dominantCodeCarrier, sum_sigma, mul_sum]
  apply sum_le_sum
  intro p hp
  let W : ℝ := tauR (shiftAbs atom p)
  have hW : 0 ≤ W := by dsimp [W, tauR]; positivity
  have hQD : ((divisorQD atom k p).card : ℝ) ≤ W ^ 2 := by
    have hh := card_le_card (filter_subset (fun qd => qd ∈ nativeQD atom k)
      ((shiftAbs atom p).divisors ×ˢ (shiftAbs atom p).divisors))
    simpa only [card_product, Nat.cast_mul, W, tauR, pow_two] using (Nat.cast_le.mpr hh :
      ((divisorQD atom k p).card : ℝ) ≤ _)
  simp only [sum_sigma]
  change (∑ qd ∈ divisorQD atom k p, ∑ n ∈ dominantSeconds atom p qd,
    ∑ _rs ∈ (shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1,n)).divisors, W ^ 2) ≤ Occ * W ^ 6
  calc
    _ ≤ ∑ _qd ∈ divisorQD atom k p, Occ * W ^ 4 := by
      apply sum_le_sum
      intro qd hqd
      calc
        _ ≤ ∑ _n ∈ dominantSeconds atom p qd, W ^ 4 := by
          apply sum_le_sum
          intro n hn
          have hτ := (mem_filter.mp hn).2.2.2
          simp only [sum_const, nsmul_eq_mul, card_product, Nat.cast_mul]
          change W * tauR (shiftAbs atom (p.1,n)) * W ^ 2 ≤ W ^ 4
          calc
            _ ≤ W * W * W ^ 2 := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hτ hW) (sq_nonneg W)
            _ = _ := by ring
        _ = ((dominantSeconds atom p qd).card : ℝ) * W ^ 4 := by simp
        _ ≤ Occ * W ^ 4 := mul_le_mul_of_nonneg_right
          (dominantSeconds_card_le hA k p qd (mem_filter.mp hqd).2) (by positivity)
    _ = ((divisorQD atom k p).card : ℝ) * (Occ * W ^ 4) := by simp
    _ ≤ W ^ 2 * (Occ * W ^ 4) := mul_le_mul_of_nonneg_right hQD (by positivity)
    _ = _ := by ring

theorem dominantLarge_norm_sum_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H : ℝ) :
    (∑ t ∈ dominantLarge atom z y k H, ‖S3DeletedTerm atom z y k t‖) ≤
      (2 * atom.U / keyY atom k + 1) *
        ∑ p ∈ largeFirstPairs atom H, tauR (shiftAbs atom p) ^ 6 := by
  have hinj : Set.InjOn closeCode (dominantLarge atom z y k H) :=
    fun t ht u hu he => closeCode_injective he
  have hsub : (dominantLarge atom z y k H).image closeCode ⊆ dominantCodeCarrier atom k H := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hv
    exact dominantLarge_maps_to_code hA z y k H ht
  calc
    _ ≤ ∑ t ∈ dominantLarge atom z y k H, tauR (shiftAbs atom (firstMN t)) ^ 2 :=
      sum_le_sum (fun t ht => activeClose_term_le hA z y k _ _ (dominantLarge_as_activeClose ht))
    _ = ∑ v ∈ (dominantLarge atom z y k H).image closeCode, tauR (shiftAbs atom v.1) ^ 2 := by
      rw [sum_image hinj]
      rfl
    _ ≤ ∑ v ∈ dominantCodeCarrier atom k H, tauR (shiftAbs atom v.1) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := dominantCode_weight_le hA k H

def nonzeroPairs (atom : MediumAtom) : Finset (ℕ × ℕ) :=
  (actualMN atom).filter (fun p => shiftAbs atom p ≠ 0)

def shiftedSeventhMoment (atom : MediumAtom) : ℝ :=
  ∑ p ∈ nonzeroPairs atom, tauR (shiftAbs atom p) ^ 7

theorem largeFirstPairs_sixth_le_seventh (atom : MediumAtom) {H : ℝ} (hH : 0 < H) :
    (∑ p ∈ largeFirstPairs atom H, tauR (shiftAbs atom p) ^ 6) ≤
      shiftedSeventhMoment atom / H := by
  apply (le_div_iff₀ hH).mpr
  rw [sum_mul]
  calc
    _ ≤ ∑ p ∈ largeFirstPairs atom H, tauR (shiftAbs atom p) ^ 7 := by
      apply sum_le_sum
      intro p hp
      have hlarge := (mem_filter.mp hp).2.2
      calc
        _ ≤ tauR (shiftAbs atom p) ^ 6 * tauR (shiftAbs atom p) :=
          mul_le_mul_of_nonneg_left hlarge.le (by dsimp [tauR]; positivity)
        _ = _ := by ring
    _ ≤ shiftedSeventhMoment atom := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.1⟩
      · intro p hp hnp
        dsimp [tauR]
        positivity

/-- Original full cutoff complement localized at a fixed independent
moment. H is arbitrary positive, including the ORIGINAL log(x)^c. -/
theorem largeShiftMass_le_seventh {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key)
    {H : ℝ} (hH : 0 < H) :
    largeShiftMass atom z y k H ≤
      2 * (2 * atom.U / keyY atom k + 1) * shiftedSeventhMoment atom / H := by
  have hOcc : 0 ≤ 2 * atom.U / keyY atom k + 1 := by
    have hY := keyY_positive hA k
    have hU := hA.1
    positivity
  calc
    _ ≤ 2 * ∑ t ∈ dominantLarge atom z y k H, ‖S3DeletedTerm atom z y k t‖ :=
      largeShiftMass_le_two_dominant atom z y k H
    _ ≤ 2 * ((2 * atom.U / keyY atom k + 1) *
        ∑ p ∈ largeFirstPairs atom H, tauR (shiftAbs atom p) ^ 6) :=
      mul_le_mul_of_nonneg_left (dominantLarge_norm_sum_le hA z y k H) (by norm_num)
    _ ≤ 2 * ((2 * atom.U / keyY atom k + 1) * (shiftedSeventhMoment atom / H)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (largeFirstPairs_sixth_le_seventh atom hH) hOcc) (by norm_num)
    _ = _ := by ring

theorem largeShiftDeleted_norm_le_seventh {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key)
    {H : ℝ} (hH : 0 < H) :
    ‖largeShiftDeleted atom z y k H‖ ≤
      2 * (2 * atom.U / keyY atom k + 1) * shiftedSeventhMoment atom / H := by
  apply le_trans _ (largeShiftMass_le_seventh hA z y k hH)
  unfold largeShiftDeleted largeShiftMass
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro t ht
  split_ifs <;> simp

/-- An independently chosen arithmetic filter may be reinstated using
the same positive correction mass; no bound of a masked signed sum by
an unmasked signed sum is used. -/
theorem masked_cutoff_reinstatement_norm_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key)
    (P : PairIndex → Prop) [DecidablePred P] {H : ℝ} (hH : 0 < H) :
    ‖(∑ t ∈ offDiagonalCarrier atom k, if P t then S3DeletedTerm atom z y k t else 0) -
      (∑ t ∈ offDiagonalCarrier atom k,
        if P t ∧ ShiftCut atom H t then S3DeletedTerm atom z y k t else 0)‖ ≤
      2 * (2 * atom.U / keyY atom k + 1) * shiftedSeventhMoment atom / H := by
  apply le_trans _ (largeShiftMass_le_seventh hA z y k hH)
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro t ht
  by_cases hp : P t <;> by_cases hc : ShiftCut atom H t <;>
    simp [hp, hc, norm_nonneg]

end
end ImbalancedChen.Part3.OriginalS3LargeShiftLocalization20261102
