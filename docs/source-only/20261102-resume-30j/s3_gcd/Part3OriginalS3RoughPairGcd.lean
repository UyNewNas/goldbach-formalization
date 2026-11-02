import ImbalancedChen.Part3OriginalS3ClosePairResidual
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original medium completion 169--181: the actual (r,s)>1 correction
AFTER the two nonzero-shift cutoffs, with its original signed coefficient.
The other gcd gates, large-shift complement and zero-mode restoration
are neither imposed nor estimated in this module.
-/
namespace ImbalancedChen.Part3.OriginalS3RoughPairGcd20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3ClosePairCount20261102 OriginalS3ClosePairResidual20261102
open MediumLiteralS3Stages20261028 MediumLiteralS3Deleted20261028
open MediumDeletedIndicatorShift20261028 MediumActualPreliminaryCauchy20261028
open MediumPrimitivePsiSource20261028 MediumGlobalDyadicOwnership20261028
open MediumNativePrincipalSource20261028 MediumReceiverCutoffArithmetic20261028
open MediumActualDiagonalDivisorPayment20261028 OriginalSamePsiS1OwnedAtlas
open OriginalMediumS1SeparatedDivisorMean MediumOwnedCanonicalReindex20261028
open MediumCanonicalFixedBlock20261028 MediumInstalledFactorChoiceMap20261028
open MediumInstalledSplitConverse20261028
open OriginalMediumDoubleLambdaColorWindows20261028
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ElementaryTauTruncation.IntervalPayment

/-- Inclusive rough support of the literal trimmed Lambda; no support
condition on an invented independent rough coefficient is used. -/
theorem lambdaTrim_rough_support (atom : MediumAtom) (z y : ℝ)
    (k : Key) (d r : ℕ) (hn : lambdaTrim atom z y k d r ≠ 0) :
    RoughPrimeSupportedAt z r := by
  by_contra hbad
  apply hn
  unfold lambdaTrim
  apply sum_eq_zero
  intro p hp
  have hp' := (mem_filter.mp hp).1
  obtain ⟨_, _, hu, hv⟩ := choice_all_four_supports _ hp'
  have huR : RoughPrimeSupportedAt z p.u := (mem_filter.mp hu).2
  have hvR : RoughPrimeSupportedAt z p.v := (mem_filter.mp hv).2
  have hw := (choice_products hp').2.1
  apply False.elim
  apply hbad
  rw [← hw]
  refine ⟨mul_ne_zero huR.1 hvR.1, ?_⟩
  intro l hl
  rw [Nat.primeFactors_mul huR.1 hvR.1] at hl
  rcases mem_union.mp hl with hl | hl
  · exact huR.2 l hl
  · exact hvR.2 l hl

def badPairDeleted (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ShiftCut atom H t ∧ ¬Close T t ∧ ¬t.2.1.1.Coprime t.2.2.1 then
      S3DeletedTerm atom z y k t else 0

def coprimeFarFull (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ShiftCut atom H t ∧ ¬Close T t ∧ t.2.1.1.Coprime t.2.2.1 then
      S3FullTerm atom z y k t else 0

def activeBadPair (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : Finset PairIndex :=
  (offDiagonalCarrier atom k).filter (fun t => ShiftCut atom H t ∧ ¬Close T t ∧
    ¬t.2.1.1.Coprime t.2.2.1 ∧ S3DeletedTerm atom z y k t ≠ 0)

theorem badPairDeleted_eq_active (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) :
    badPairDeleted atom z y k H T =
      ∑ t ∈ activeBadPair atom z y k H T, S3DeletedTerm atom z y k t := by
  unfold badPairDeleted activeBadPair
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t <;> by_cases hc : Close T t <;>
    by_cases hg : t.2.1.1.Coprime t.2.2.1 <;>
      by_cases hn : S3DeletedTerm atom z y k t = 0 <;> simp [hs, hc, hg, hn]

/-- Exact signed split, before any triangle inequality. The deleted and
full summands agree ONLY because both original shifts are nonzero. -/
theorem farFull_eq_coprime_add_bad (atom : MediumAtom) (z y : ℝ)
    (k : Key) (H T : ℝ) :
    farFull atom z y k H T = coprimeFarFull atom z y k H T + badPairDeleted atom z y k H T := by
  unfold farFull coprimeFarFull badPairDeleted
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t
  · by_cases hc : Close T t
    · simp [hs, hc]
    · by_cases hg : t.2.1.1.Coprime t.2.2.1
      · simp [hs, hc, hg]
      · simpa [hs, hc, hg] using fullTerm_eq_deleted_of_shiftCut atom z y k H t hs
  · simp [hs]

/-- Reuse I's arithmetic extraction and coefficient bound without
requiring the actual far pair to be a close pair. The auxiliary width
here is only a proof of membership in the already analysed carrier. -/
theorem activeBadPair_as_activeClose {atom : MediumAtom} {z y H T : ℝ} {k : Key}
    {t : PairIndex} (ht : t ∈ activeBadPair atom z y k H T) :
    t ∈ activeClose atom z y k H (|(t.2.1.2 : ℝ) - t.2.2.2| + 1) := by
  obtain ⟨hoff, hcut, hfar, hgcd, hne⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨hoff, hcut, by unfold Close; linarith, hne⟩

/-- A noncoprime pair of the ACTUAL rough coefficients has gcd>z.
The original strict p>z convention is recovered through its receiver. -/
theorem activeBadPair_gcd_gt {atom : MediumAtom} {z y H T : ℝ} {k : Key}
    (hz : 0 ≤ z) {t : PairIndex}
    (ht : t ∈ activeBadPair atom (strictReceiverCutoff z) y k H T) :
    z < (Nat.gcd t.2.1.1 t.2.2.1 : ℝ) := by
  obtain ⟨hoff, hcut, hfar, hgcd, hne⟩ := mem_filter.mp ht
  have hλ : lambdaTrim atom (strictReceiverCutoff z) y k t.1.2.1 t.2.1.1 ≠ 0 := by
    intro hzero
    exact hne (by simp [S3DeletedTerm, pairCoefficient, hzero])
  have hr := lambdaTrim_rough_support atom _ y k _ _ hλ
  let f := Nat.gcd t.2.1.1 t.2.2.1
  have hf0 : 0 < f := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hr.1)
  have hf1 : f ≠ 1 := by
    intro hf
    apply hgcd
    exact hf
  have hp : Nat.Prime f.minFac := Nat.minFac_prime hf1
  have hpr : f.minFac ∣ t.2.1.1 := (Nat.minFac_dvd f).trans (Nat.gcd_dvd_left _ _)
  have hzp : z < (f.minFac : ℝ) :=
    (original_lt_nat_iff_receiver_le z hz _).mpr
      (hr.2 _ (Nat.mem_primeFactors.mpr ⟨hp, hpr, hr.1⟩))
  exact hzp.trans_le (by exact_mod_cast Nat.le_of_dvd hf0 (Nat.minFac_dvd f))

/-- The common rough gcd enlarges the actual n2 modulus from ell to
ell*gcd(r,s). No coprimality of r with ell is required. -/
theorem activeBadPair_progression {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ)
    {t : PairIndex} (ht : t ∈ activeBadPair atom z y k H T) :
    Int.ModEq (((t.1.1 * t.1.2.1) * Nat.gcd t.2.1.1 t.2.2.1 : ℕ) : ℤ)
      (t.2.2.2 : ℤ) (t.2.1.2 : ℤ) := by
  have htC := activeBadPair_as_activeClose ht
  obtain ⟨_, _, hqd, _, _, _⟩ := activeClose_data hA z y k H _ htC
  have hne := (mem_filter.mp ht).2.2.2.2
  have hλ : lambdaTrim atom z y k t.1.2.1 t.2.1.1 ≠ 0 := by
    intro hzero; exact hne (by simp [S3DeletedTerm, pairCoefficient, hzero])
  have haell := (nativeQD_positive_level hA k _ hqd).2.2
  have har := (lambdaTrim_support_residue hA z y k _ _ hλ).2
  have hag := Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left _ _) har
  have haf := Nat.coprime_mul_iff_left.mpr ⟨haell, hag⟩
  have hfirst : firstDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro hzero; exact hne (by simp [S3DeletedTerm, hzero])
  have hsecond : secondDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro hzero; exact hne (by simp [S3DeletedTerm, hzero])
  have hd1 : (t.1.1*t.1.2.1)*Nat.gcd t.2.1.1 t.2.2.1 ∣ (t.1.1*t.1.2.1)*t.2.1.1 :=
    Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left _ _)
  have hd2 : (t.1.1*t.1.2.1)*Nat.gcd t.2.1.1 t.2.2.1 ∣ (t.1.1*t.1.2.1)*t.2.2.1 :=
    Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_right _ _)
  exact two_products_force_alpha_progression haf
    ((deletedIndicator_modEq hfirst).of_dvd (by exact_mod_cast hd1))
    ((deletedIndicator_modEq hsecond).of_dvd (by exact_mod_cast hd2))

def roughDivisors (atom : MediumAtom) (z : ℝ) (p : ℕ × ℕ) : Finset ℕ :=
  (shiftAbs atom p).divisors.filter (fun f => z < (f : ℝ))

def gcdSeconds (atom : MediumAtom) (H : ℝ) (p qd : ℕ × ℕ) (f : ℕ) : Finset ℕ :=
  atom.alphaCarrier.filter (fun n =>
    Int.ModEq (((qd.1 * qd.2) * f : ℕ) : ℤ) (n : ℤ) (p.2 : ℤ) ∧
      shiftAbs atom (p.1,n) ≠ 0 ∧ tauR (shiftAbs atom (p.1,n)) ≤ H)

abbrev GcdCode := Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ × ℕ

def gcdCode (t : PairIndex) : GcdCode :=
  ⟨firstMN t, ⟨(t.1.1,t.1.2.1), ⟨Nat.gcd t.2.1.1 t.2.2.1,
    ⟨t.2.2.2, (t.2.1.1,t.2.2.1)⟩⟩⟩⟩

def gcdDecode (v : GcdCode) : PairIndex :=
  ((v.2.1.1,v.2.1.2,v.1.1), (v.2.2.2.2.1,v.1.2), (v.2.2.2.2.2,v.2.2.2.1))

def gcdCodeCarrier (atom : MediumAtom) (k : Key) (z H : ℝ) : Finset GcdCode :=
  (smallFirstPairs atom H).sigma (fun p => (divisorQD atom k p).sigma (fun qd =>
    (roughDivisors atom z p).sigma (fun f => (gcdSeconds atom H p qd f).sigma (fun n =>
      (shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1,n)).divisors))))

theorem gcdCode_injective : Function.Injective gcdCode := by
  intro t u h
  exact congrArg gcdDecode h

theorem activeBadPair_card_le_code {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (hz : 0 ≤ z)
    (k : Key) (H T : ℝ) :
    (activeBadPair atom (strictReceiverCutoff z) y k H T).card ≤
      (gcdCodeCarrier atom k z H).card := by
  apply card_le_card_of_injOn gcdCode
  · intro t ht
    have htC := activeBadPair_as_activeClose ht
    obtain ⟨hmn1, hmn2, hqd, hL, hR, _⟩ := activeClose_data hA _ y k H _ htC
    have hcut := (mem_filter.mp ht).2.1
    have hq : t.1.1 ∣ shiftAbs atom (firstMN t) :=
      dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hL)
    have hd : t.1.2.1 ∣ shiftAbs atom (firstMN t) :=
      dvd_trans (dvd_mul_left _ _) (dvd_trans (dvd_mul_right _ _) hL)
    have hr : t.2.1.1 ∣ shiftAbs atom (firstMN t) := dvd_trans (dvd_mul_left _ _) hL
    have hs : t.2.2.1 ∣ shiftAbs atom (secondMN t) := dvd_trans (dvd_mul_left _ _) hR
    have hf := (Nat.gcd_dvd_left t.2.1.1 t.2.2.1).trans hr
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨hmn1,hcut.1,hcut.2.2.1⟩, mem_sigma.mpr ⟨?_, mem_sigma.mpr ⟨?_, mem_sigma.mpr ⟨?_, ?_⟩⟩⟩⟩
    · exact mem_filter.mpr ⟨mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hq,hcut.1⟩,
        Nat.mem_divisors.mpr ⟨hd,hcut.1⟩⟩,hqd⟩
    · exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hf,hcut.1⟩,activeBadPair_gcd_gt hz ht⟩
    · exact mem_filter.mpr ⟨(mem_product.mp hmn2).2,
        activeBadPair_progression hA _ y k H T ht,hcut.2.1,hcut.2.2.2⟩
    · exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hr,hcut.1⟩,
        Nat.mem_divisors.mpr ⟨hs,hcut.2.1⟩⟩
  · exact fun t ht u hu h => gcdCode_injective h

theorem gcdSeconds_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (k : Key) (H z : ℝ) (hz : 0 < z)
    (p qd : ℕ × ℕ) (hqd : qd ∈ nativeQD atom k) (f : ℕ) (hf : z < (f : ℝ)) :
    ((gcdSeconds atom H p qd f).card : ℝ) ≤ 2 * atom.U / (keyY atom k * z) + 1 := by
  obtain ⟨hell,hlevel,_⟩ := nativeQD_positive_level hA k qd hqd
  have hY := keyY_positive hA k
  have hU : 0 < atom.U := zero_lt_one.trans_le hA.1
  have hfpos : 0 < f := by exact_mod_cast hz.trans hf
  have hlev : keyY atom k / 2 ≤ ((qd.1*qd.2 : ℕ) : ℝ) := by
    simpa only [singleZeroY,keyY,keyD,Nat.cast_pow,Nat.cast_ofNat] using hlevel
  have hcount := card_real_supported_modEq_dvd_le_lcm (gcdSeconds atom H p qd f)
    (a := atom.U) (b := 2*atom.U) (q := (qd.1*qd.2)*f) (d := 1) (r := p.2)
    (by linarith) (Nat.mul_pos hell hfpos) (by norm_num)
    (fun n hn => by
      have hi := mem_Icc.mp (mem_filter.mp (mem_filter.mp hn).1).1
      exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hi.1),
        (show (n : ℝ) ≤ Nat.floor (2*atom.U) by exact_mod_cast hi.2).trans
          (Nat.floor_le (by positivity))⟩)
    (fun n hn => (mem_filter.mp hn).2.1) (fun n hn => one_dvd _)
  have hcount' : ((gcdSeconds atom H p qd f).card : ℝ) ≤
      atom.U / (((qd.1*qd.2 : ℕ) : ℝ) * f) + 1 := by
    simpa only [Nat.lcm_one_left,Nat.cast_mul,show 2*atom.U-atom.U = atom.U by ring] using hcount
  apply hcount'.trans
  apply add_le_add_right
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < ((qd.1*qd.2 : ℕ) : ℝ)*f)
    (mul_pos hY hz)).mpr
  have hh : keyY atom k * z ≤ 2 * ((qd.1*qd.2 : ℕ) : ℝ) * f := by
    have h1 := mul_le_mul_of_nonneg_right hlev hz.le
    have h2 := mul_le_mul_of_nonneg_left hf.le
      (show 0 ≤ ((qd.1*qd.2 : ℕ) : ℝ) by positivity)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hh hU.le]

/-- Every original label survives the injection. The extra gcd label
costs one divisor cutoff H; its progression earns the actual factor 1/z. -/
theorem activeBadPair_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (hz : 0 < z)
    (k : Key) (H T : ℝ) (hH : 0 ≤ H) :
    ((activeBadPair atom (strictReceiverCutoff z) y k H T).card : ℝ) ≤
      12 * atom.scale * (2*atom.U/(keyY atom k*z)+1) * H^5 := by
  let Occ : ℝ := 2*atom.U/(keyY atom k*z)+1
  have hY := keyY_positive hA k
  have hU : 0 ≤ atom.U := zero_le_one.trans hA.1
  have hOcc : 0 ≤ Occ := by dsimp [Occ]; positivity
  have hrow (p : ℕ × ℕ) (hp : p ∈ smallFirstPairs atom H) :
      (∑ qd ∈ divisorQD atom k p, ∑ f ∈ roughDivisors atom z p,
        ∑ n ∈ gcdSeconds atom H p qd f,
          (((shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1,n)).divisors).card : ℝ)) ≤
        Occ * H^5 := by
    have htau := (mem_filter.mp hp).2.2
    have hQD : ((divisorQD atom k p).card : ℝ) ≤ H^2 := by
      have hh := card_le_card (filter_subset (fun qd => qd ∈ nativeQD atom k)
        ((shiftAbs atom p).divisors ×ˢ (shiftAbs atom p).divisors))
      have hhR : ((divisorQD atom k p).card : ℝ) ≤ tauR (shiftAbs atom p)^2 := by
        simpa only [card_product,Nat.cast_mul,tauR,pow_two] using (Nat.cast_le.mpr hh :
          ((divisorQD atom k p).card : ℝ) ≤ _)
      exact hhR.trans (pow_le_pow_left₀ (by dsimp [tauR]; positivity) htau 2)
    have hF : ((roughDivisors atom z p).card : ℝ) ≤ H :=
      (Nat.cast_le.mpr (card_le_card (filter_subset _ _))).trans htau
    calc
      _ ≤ ∑ _qd ∈ divisorQD atom k p, Occ*H^3 := by
        apply sum_le_sum
        intro qd hqd
        calc
          _ ≤ ∑ _f ∈ roughDivisors atom z p, Occ*H^2 := by
            apply sum_le_sum
            intro f hf
            calc
              _ ≤ ∑ _n ∈ gcdSeconds atom H p qd f, H^2 := by
                apply sum_le_sum
                intro n hn
                rw [card_product,Nat.cast_mul]
                change tauR (shiftAbs atom p)*tauR (shiftAbs atom (p.1,n)) ≤ H^2
                simpa only [pow_two] using mul_le_mul htau (mem_filter.mp hn).2.2.2
                  (show 0 ≤ tauR (shiftAbs atom (p.1,n)) by dsimp [tauR]; positivity) hH
              _ = ((gcdSeconds atom H p qd f).card : ℝ)*H^2 := by simp
              _ ≤ Occ*H^2 := mul_le_mul_of_nonneg_right
                (gcdSeconds_card_le hA k H z hz p qd (mem_filter.mp hqd).2 f (mem_filter.mp hf).2)
                (sq_nonneg H)
          _ = ((roughDivisors atom z p).card : ℝ)*(Occ*H^2) := by simp
          _ ≤ H*(Occ*H^2) := mul_le_mul_of_nonneg_right hF (by positivity)
          _ = Occ*H^3 := by ring
      _ = ((divisorQD atom k p).card : ℝ)*(Occ*H^3) := by simp
      _ ≤ H^2*(Occ*H^3) := mul_le_mul_of_nonneg_right hQD (by positivity)
      _ = Occ*H^5 := by ring
  calc
    _ ≤ ((gcdCodeCarrier atom k z H).card : ℝ) := by
      exact_mod_cast activeBadPair_card_le_code hA z y hz.le k H T
    _ = ∑ p ∈ smallFirstPairs atom H, ∑ qd ∈ divisorQD atom k p,
        ∑ f ∈ roughDivisors atom z p, ∑ n ∈ gcdSeconds atom H p qd f,
          (((shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1,n)).divisors).card : ℝ) := by
      simp only [gcdCodeCarrier,card_sigma,Nat.cast_sum]
    _ ≤ ∑ _p ∈ smallFirstPairs atom H, Occ*H^5 := sum_le_sum hrow
    _ = ((smallFirstPairs atom H).card : ℝ)*(Occ*H^5) := by simp
    _ ≤ (12*atom.scale)*(Occ*H^5) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (Nat.cast_le.mpr (card_le_card (filter_subset _ _))).trans (actualMN_card_le hA)
    _ = _ := by ring

/-- Concrete original rough-pair gcd correction. This is a proved count,
with the +x*H^7 endpoint present, independent of the separation width T. -/
theorem badPairDeleted_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (hz : 0 < z)
    (k : Key) (H T : ℝ) (hH : 0 ≤ H) :
    ‖badPairDeleted atom (strictReceiverCutoff z) y k H T‖ ≤
      12*atom.scale*(2*atom.U/(keyY atom k*z)+1)*H^7 := by
  rw [badPairDeleted_eq_active]
  calc
    _ ≤ ∑ t ∈ activeBadPair atom (strictReceiverCutoff z) y k H T,
        ‖S3DeletedTerm atom (strictReceiverCutoff z) y k t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ activeBadPair atom (strictReceiverCutoff z) y k H T, H^2 := by
      apply sum_le_sum
      intro t ht
      exact activeClose_term_le hA _ y k H _ (activeBadPair_as_activeClose ht)
    _ = ((activeBadPair atom (strictReceiverCutoff z) y k H T).card : ℝ)*H^2 := by simp
    _ ≤ (12*atom.scale*(2*atom.U/(keyY atom k*z)+1)*H^5)*H^2 :=
      mul_le_mul_of_nonneg_right (activeBadPair_card_le hA z y hz k H T hH) (sq_nonneg H)
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalS3RoughPairGcd20261102

