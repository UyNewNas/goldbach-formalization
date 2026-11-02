import ImbalancedChen.Part3MediumOriginalAllKeyRestorationPayment
import ImbalancedChen.Part3ElementaryCRTSpacing
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original medium completion, section 4, lines 169--181.  The cutoff is a
literal predicate on the TWO NONZERO shifts, not an estimate supplied by
the caller.  Its complement is retained in the following source ledger.
The close-pair count is performed before Poisson and before restoring zeros.
-/
namespace ImbalancedChen.Part3.OriginalS3ClosePairCount20261102
noncomputable section
open Classical Finset
open scoped BigOperators
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

def firstMN (t : PairIndex) : ℕ × ℕ := (t.1.2.2, t.2.1.2)
def secondMN (t : PairIndex) : ℕ × ℕ := (t.1.2.2, t.2.2.2)

/-- Both shifts are nonzero before any divisor cutoff is imposed. -/
def ShiftCut (atom : MediumAtom) (H : ℝ) (t : PairIndex) : Prop :=
  shiftAbs atom (firstMN t) ≠ 0 ∧ shiftAbs atom (secondMN t) ≠ 0 ∧
    tauR (shiftAbs atom (firstMN t)) ≤ H ∧
    tauR (shiftAbs atom (secondMN t)) ≤ H

def Close (T : ℝ) (t : PairIndex) : Prop :=
  |(t.2.1.2 : ℝ) - t.2.2.2| < T

def closeDeleted (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ShiftCut atom H t ∧ Close T t then S3DeletedTerm atom z y k t else 0

def activeClose (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : Finset PairIndex :=
  (offDiagonalCarrier atom k).filter (fun t =>
    ShiftCut atom H t ∧ Close T t ∧ S3DeletedTerm atom z y k t ≠ 0)

theorem closeDeleted_eq_active (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) :
    closeDeleted atom z y k H T =
      ∑ t ∈ activeClose atom z y k H T, S3DeletedTerm atom z y k t := by
  unfold closeDeleted activeClose
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t <;> by_cases hc : Close T t <;>
    by_cases hz : S3DeletedTerm atom z y k t = 0 <;> simp [hs, hc, hz]

theorem deletedIndicator_modEq {a : ℤ} {q n m : ℕ}
    (h : deletedIndicator a q n m ≠ 0) :
    Int.ModEq (q : ℤ) ((n * m : ℕ) : ℤ) a := by
  by_cases hz : ((n * m : ℕ) : ℤ) = a
  · exact False.elim (h (by simp [deletedIndicator, hz]))
  by_cases hc : ((n * m : ℕ) : ℤ) % (q : ℤ) = a % (q : ℤ)
  · exact hc
  · exact False.elim (h (by simp [deletedIndicator, hz, hc]))

/-- This is the arithmetic cancellation behind the original n2 progression.
The unit of m is derived from the original primitive residue and congruence. -/
theorem two_products_force_alpha_progression {ell m n1 n2 : ℕ} {a : ℤ}
    (ha : ell.Coprime a.natAbs)
    (h1 : Int.ModEq (ell : ℤ) ((n1 * m : ℕ) : ℤ) a)
    (h2 : Int.ModEq (ell : ℤ) ((n2 * m : ℕ) : ℤ) a) :
    Int.ModEq (ell : ℤ) (n2 : ℤ) (n1 : ℤ) := by
  have hag : Int.gcd a ell = 1 := by
    simpa only [Int.gcd, Int.natAbs_natCast, Nat.gcd_comm] using ha.gcd_eq_one
  have hnm : (n1 * m).Coprime ell := by
    have hg : Int.gcd ((n1 * m : ℕ) : ℤ) ell = 1 := by
      rw [← Int.gcd_emod ((n1 * m : ℕ) : ℤ) ell, h1.eq, Int.gcd_emod, hag]
    simpa only [Int.gcd, Int.natAbs_natCast] using hg
  have hm : m.Coprime ell := (Nat.coprime_mul_iff_left.mp hnm).2
  obtain ⟨v, hv⟩ := Int.mod_coprime hm
  have hn1 : Int.ModEq (ell : ℤ) ((n1 : ℤ) * m * v) n1 := by
    simpa only [mul_assoc, mul_one] using hv.mul_left (n1 : ℤ)
  have hn2 : Int.ModEq (ell : ℤ) ((n2 : ℤ) * m * v) n2 := by
    simpa only [mul_assoc, mul_one] using hv.mul_left (n2 : ℤ)
  exact hn2.symm.trans (((by simpa only [Nat.cast_mul] using
    h2.trans h1.symm : Int.ModEq (ell : ℤ) ((n2 : ℤ) * m) ((n1 : ℤ) * m)).mul_right v).trans hn1)

/-- Active original summands provide all support and divisibility facts;
none of the clean rough/gcd exclusions is assumed. -/
theorem activeClose_data {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ)
    {t : PairIndex} (ht : t ∈ activeClose atom z y k H T) :
    firstMN t ∈ actualMN atom ∧ secondMN t ∈ actualMN atom ∧
    (t.1.1, t.1.2.1) ∈ nativeQD atom k ∧
    (t.1.1 * t.1.2.1) * t.2.1.1 ∣ shiftAbs atom (firstMN t) ∧
    (t.1.1 * t.1.2.1) * t.2.2.1 ∣ shiftAbs atom (secondMN t) ∧
    Int.ModEq ((t.1.1 * t.1.2.1 : ℕ) : ℤ) (t.2.2.2 : ℤ) (t.2.1.2 : ℤ) := by
  obtain ⟨ht, hcut, hclose, hne⟩ := mem_filter.mp ht
  have hp := (mem_filter.mp ht).1
  have ho := (mem_product.mp hp).1
  have hraw := (mem_filter.mp ho).1
  have hi := mem_product.mp (mem_product.mp hp).2
  have hm := (mem_product.mp (mem_product.mp hraw).2).2
  have hn1 := (mem_product.mp hi.1).2
  have hn2 := (mem_product.mp hi.2).2
  have hλ : lambdaTrim atom z y k t.1.2.1 t.2.1.1 ≠ 0 := by
    intro hz
    exact hne (by simp [S3DeletedTerm, pairCoefficient, hz])
  have hdc := (lambdaTrim_support_residue hA z y k t.1.2.1 t.2.1.1 hλ).1
  have hqd : (t.1.1, t.1.2.1) ∈ nativeQD atom k :=
    mem_product.mpr ⟨mem_filter.mpr ⟨(mem_product.mp hraw).1, (mem_filter.mp ho).2⟩,
      mem_filter.mpr ⟨(mem_product.mp (mem_product.mp hraw).2).1, hdc⟩⟩
  have hfirst : firstDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro hz; exact hne (by simp [S3DeletedTerm, hz])
  have hsecond : secondDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro hz; exact hne (by simp [S3DeletedTerm, hz])
  have hL := deletedIndicator_nonzero_data hfirst
  have hR := deletedIndicator_nonzero_data hsecond
  have h1 := (deletedIndicator_modEq hfirst).of_dvd
    (show ((t.1.1 * t.1.2.1 : ℕ) : ℤ) ∣
      (((t.1.1 * t.1.2.1) * t.2.1.1 : ℕ) : ℤ) by exact_mod_cast dvd_mul_right (t.1.1 * t.1.2.1) t.2.1.1)
  have h2 := (deletedIndicator_modEq hsecond).of_dvd
    (show ((t.1.1 * t.1.2.1 : ℕ) : ℤ) ∣
      (((t.1.1 * t.1.2.1) * t.2.2.1 : ℕ) : ℤ) by exact_mod_cast dvd_mul_right (t.1.1 * t.1.2.1) t.2.2.1)
  exact ⟨mem_product.mpr ⟨hm, hn1⟩, mem_product.mpr ⟨hm, hn2⟩, hqd,
    Int.natCast_dvd.mp hL.2, Int.natCast_dvd.mp hR.2,
    two_products_force_alpha_progression (nativeQD_positive_level hA k _ hqd).2.2 h1 h2⟩

def smallFirstPairs (atom : MediumAtom) (H : ℝ) : Finset (ℕ × ℕ) :=
  (actualMN atom).filter (fun p => shiftAbs atom p ≠ 0 ∧ tauR (shiftAbs atom p) ≤ H)

def divisorQD (atom : MediumAtom) (k : Key) (p : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ((shiftAbs atom p).divisors ×ˢ (shiftAbs atom p).divisors).filter
    (fun qd => qd ∈ nativeQD atom k)

def closeSeconds (atom : MediumAtom) (H T : ℝ) (p qd : ℕ × ℕ) : Finset ℕ :=
  atom.alphaCarrier.filter (fun n =>
    |(p.2 : ℝ) - n| < T ∧
      Int.ModEq ((qd.1 * qd.2 : ℕ) : ℤ) (n : ℤ) (p.2 : ℤ) ∧
      shiftAbs atom (p.1, n) ≠ 0 ∧ tauR (shiftAbs atom (p.1, n)) ≤ H)

abbrev CloseCode := Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, Σ _ : ℕ, ℕ × ℕ
def closeCode (t : PairIndex) : CloseCode :=
  ⟨firstMN t, ⟨(t.1.1, t.1.2.1), ⟨t.2.2.2, (t.2.1.1, t.2.2.1)⟩⟩⟩
def closeDecode (v : CloseCode) : PairIndex :=
  ((v.2.1.1, v.2.1.2, v.1.1), (v.2.2.2.1, v.1.2), (v.2.2.2.2, v.2.2.1))
def closeCodeCarrier (atom : MediumAtom) (k : Key) (H T : ℝ) : Finset CloseCode :=
  (smallFirstPairs atom H).sigma (fun p => (divisorQD atom k p).sigma (fun qd =>
    (closeSeconds atom H T p qd).sigma (fun n =>
      (shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1, n)).divisors)))

theorem closeCode_injective : Function.Injective closeCode := by
  intro t u h
  exact congrArg closeDecode h

theorem activeClose_card_le_code {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    (activeClose atom z y k H T).card ≤ (closeCodeCarrier atom k H T).card := by
  apply card_le_card_of_injOn closeCode
  · intro t ht
    obtain ⟨hmn1, hmn2, hqd, hL, hR, hprog⟩ := activeClose_data hA z y k H T ht
    obtain ⟨_, hcut, hclose, _⟩ := mem_filter.mp ht
    have hq : t.1.1 ∣ shiftAbs atom (firstMN t) :=
      dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hL)
    have hd : t.1.2.1 ∣ shiftAbs atom (firstMN t) :=
      dvd_trans (dvd_mul_left _ _) (dvd_trans (dvd_mul_right _ _) hL)
    have hr : t.2.1.1 ∣ shiftAbs atom (firstMN t) := dvd_trans (dvd_mul_left _ _) hL
    have hs : t.2.2.1 ∣ shiftAbs atom (secondMN t) := dvd_trans (dvd_mul_left _ _) hR
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨hmn1, hcut.1, hcut.2.2.1⟩, mem_sigma.mpr ⟨?_, mem_sigma.mpr ⟨?_, ?_⟩⟩⟩
    · exact mem_filter.mpr ⟨mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hq, hcut.1⟩,
        Nat.mem_divisors.mpr ⟨hd, hcut.1⟩⟩, hqd⟩
    · exact mem_filter.mpr ⟨(mem_product.mp hmn2).2, hclose, hprog, hcut.2.1, hcut.2.2.2⟩
    · exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hr, hcut.1⟩,
        Nat.mem_divisors.mpr ⟨hs, hcut.2.1⟩⟩
  · exact fun t ht u hu h => closeCode_injective h

theorem closeSeconds_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (k : Key) (H T : ℝ) (hT : 0 ≤ T)
    (p qd : ℕ × ℕ) (hqd : qd ∈ nativeQD atom k) :
    ((closeSeconds atom H T p qd).card : ℝ) ≤ 4 * T / keyY atom k + 1 := by
  obtain ⟨hell, hlevel, _⟩ := nativeQD_positive_level hA k qd hqd
  have hY := keyY_positive hA k
  have hlevel' : keyY atom k / 2 ≤ ((qd.1 * qd.2 : ℕ) : ℝ) := by
    simpa only [singleZeroY, keyY, keyD, Nat.cast_pow, Nat.cast_ofNat] using hlevel
  have hc := card_real_supported_modEq_dvd_le_lcm (closeSeconds atom H T p qd)
    (a := (p.2 : ℝ) - T) (b := (p.2 : ℝ) + T)
    (q := qd.1 * qd.2) (d := 1) (r := p.2)
    (by linarith) hell (by norm_num)
    (fun n hn => by
      have hh := abs_lt.mp (mem_filter.mp hn).2.1
      constructor <;> linarith)
    (fun n hn => (mem_filter.mp hn).2.2.1)
    (fun n hn => one_dvd _)
  have hc' : ((closeSeconds atom H T p qd).card : ℝ) ≤
      2 * T / ((qd.1 * qd.2 : ℕ) : ℝ) + 1 := by
    simpa only [Nat.lcm_one_left, show (p.2 : ℝ) + T - ((p.2 : ℝ) - T) = 2*T by ring] using hc
  apply hc'.trans
  apply add_le_add_right
  apply (div_le_div_iff₀ (by exact_mod_cast hell : (0 : ℝ) < (qd.1 * qd.2 : ℕ)) hY).mpr
  have hh := mul_le_mul_of_nonneg_left hlevel' (show 0 ≤ 4*T by positivity)
  nlinarith

theorem activeClose_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ)
    (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ((activeClose atom z y k H T).card : ℝ) ≤
      12 * atom.scale * (4 * T / keyY atom k + 1) * H ^ 4 := by
  let Occ : ℝ := 4 * T / keyY atom k + 1
  have hY := keyY_positive hA k
  have hOcc : 0 ≤ Occ := by dsimp [Occ]; positivity
  have hrow (p : ℕ × ℕ) (hp : p ∈ smallFirstPairs atom H) :
      (∑ qd ∈ divisorQD atom k p, ∑ n ∈ closeSeconds atom H T p qd,
        (((shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1,n)).divisors).card : ℝ)) ≤
        Occ * H ^ 4 := by
    have htau1 := (mem_filter.mp hp).2.2
    have hQD : ((divisorQD atom k p).card : ℝ) ≤ H ^ 2 := by
      have hh := card_le_card (filter_subset (fun qd => qd ∈ nativeQD atom k)
        ((shiftAbs atom p).divisors ×ˢ (shiftAbs atom p).divisors))
      have hhR : ((divisorQD atom k p).card : ℝ) ≤ tauR (shiftAbs atom p) ^ 2 := by
        simpa only [card_product, Nat.cast_mul, tauR, pow_two] using (Nat.cast_le.mpr hh :
          ((divisorQD atom k p).card : ℝ) ≤ _)
      exact hhR.trans (pow_le_pow_left₀ (by dsimp [tauR]; positivity) htau1 2)
    calc
      _ ≤ ∑ _qd ∈ divisorQD atom k p, Occ * H ^ 2 := by
        apply sum_le_sum
        intro qd hqd
        calc
          _ ≤ ∑ _n ∈ closeSeconds atom H T p qd, H ^ 2 := by
            apply sum_le_sum
            intro n hn
            rw [card_product, Nat.cast_mul]
            change tauR (shiftAbs atom p) * tauR (shiftAbs atom (p.1,n)) ≤ H ^ 2
            simpa only [pow_two] using mul_le_mul htau1 (mem_filter.mp hn).2.2.2.2
              (show 0 ≤ tauR (shiftAbs atom (p.1,n)) by dsimp [tauR]; positivity) hH
          _ = ((closeSeconds atom H T p qd).card : ℝ) * H ^ 2 := by simp
          _ ≤ Occ * H ^ 2 := mul_le_mul_of_nonneg_right
            (closeSeconds_card_le hA k H T hT p qd (mem_filter.mp hqd).2) (sq_nonneg H)
      _ = ((divisorQD atom k p).card : ℝ) * (Occ * H ^ 2) := by simp
      _ ≤ H ^ 2 * (Occ * H ^ 2) := mul_le_mul_of_nonneg_right hQD (by positivity)
      _ = Occ * H ^ 4 := by ring
  calc
    _ ≤ ((closeCodeCarrier atom k H T).card : ℝ) := by
      exact_mod_cast activeClose_card_le_code hA z y k H T
    _ = ∑ p ∈ smallFirstPairs atom H, ∑ qd ∈ divisorQD atom k p,
        ∑ n ∈ closeSeconds atom H T p qd,
          (((shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1,n)).divisors).card : ℝ) := by
      simp only [closeCodeCarrier, card_sigma, Nat.cast_sum]
    _ ≤ ∑ _p ∈ smallFirstPairs atom H, Occ * H ^ 4 := sum_le_sum hrow
    _ = ((smallFirstPairs atom H).card : ℝ) * (Occ * H ^ 4) := by simp
    _ ≤ (12 * atom.scale) * (Occ * H ^ 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (Nat.cast_le.mpr (card_le_card (filter_subset _ _))).trans (actualMN_card_le hA)
    _ = _ := by ring

theorem activeClose_term_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ)
    {t : PairIndex} (ht : t ∈ activeClose atom z y k H T) :
    ‖S3DeletedTerm atom z y k t‖ ≤ H ^ 2 := by
  obtain ⟨hmn1, hmn2, hqd, hL, hR, _⟩ := activeClose_data hA z y k H T ht
  obtain ⟨htoff, hcut, hclose, hne⟩ := mem_filter.mp ht
  have hp := (mem_filter.mp htoff).1
  have hi := mem_product.mp (mem_product.mp hp).2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hα, _⟩ := hA
  have hH : 0 ≤ H := (show 0 ≤ tauR (shiftAbs atom (firstMN t)) by dsimp [tauR]; positivity).trans hcut.2.2.1
  have hψ : ‖(jointPsi atom t.1 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (jointPsi_nonneg atom t.1)]
    exact mul_le_one₀ (paperPsi_le_one _) (paperPsi_nonneg _) (paperPsi_le_one _)
  have hdr : t.1.2.1 * t.2.1.1 ∣ shiftAbs atom (firstMN t) := dvd_trans ⟨t.1.1, by ring⟩ hL
  have hds : t.1.2.1 * t.2.2.1 ∣ shiftAbs atom (secondMN t) := dvd_trans ⟨t.1.1, by ring⟩ hR
  have hλr := ((lambdaTrim_norm_le_tau atom z y k t.1.2.1 t.2.1.1 hA).trans
    (tauR_mono_dvd hcut.1 hdr)).trans hcut.2.2.1
  have hλs := ((lambdaTrim_norm_le_tau atom z y k t.1.2.1 t.2.2.1 hA).trans
    (tauR_mono_dvd hcut.2.1 hds)).trans hcut.2.2.2
  unfold S3DeletedTerm pairCoefficient
  simp only [norm_mul, norm_star]
  calc
    _ ≤ 1 * H * H * 1 * 1 * 1 * 1 := by
      gcongr
      · exact hψ
      · exact hλr
      · exact hλs
      · exact hα _ (mem_product.mp hi.1).2
      · exact hα _ (mem_product.mp hi.2).2
      · exact deletedIndicator_norm_le_one _ _ _ _
      · exact deletedIndicator_norm_le_one _ _ _ _
    _ = _ := by ring

/-- Literal original close correction under its actual cutoffs.
The endpoint +x*H^6 term is retained and paid using (9), not dropped. -/
theorem closeDeleted_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ)
    (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ‖closeDeleted atom z y k H T‖ ≤
      12 * atom.scale * (4 * T / keyY atom k + 1) * H ^ 6 := by
  rw [closeDeleted_eq_active]
  calc
    _ ≤ ∑ t ∈ activeClose atom z y k H T, ‖S3DeletedTerm atom z y k t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ activeClose atom z y k H T, H ^ 2 :=
      sum_le_sum (fun t ht => activeClose_term_le hA z y k H T ht)
    _ = ((activeClose atom z y k H T).card : ℝ) * H ^ 2 := by simp
    _ ≤ (12 * atom.scale * (4*T/keyY atom k+1) * H^4) * H^2 :=
      mul_le_mul_of_nonneg_right (activeClose_card_le hA z y k H T hH hT) (sq_nonneg H)
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalS3ClosePairCount20261102
