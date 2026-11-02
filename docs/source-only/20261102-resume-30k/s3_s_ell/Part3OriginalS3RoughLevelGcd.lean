import ImbalancedChen.Part3OriginalS3RoughPairGcd
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original medium completion 169--181, the (s,ell)>1 exclusion, ell=qd.
The source is the actual J r/s-coprime far packet under BOTH nonzero
shift cutoffs. Its second product is in a primitive class modulo ell*f,
f=gcd(s,ell). Its residue is NOT asserted to be n1 modulo ell*f.
-/
namespace ImbalancedChen.Part3.OriginalS3RoughLevelGcd20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3RoughPairGcd20261102
open OriginalS3ClosePairCount20261102 OriginalS3ClosePairResidual20261102
open MediumLiteralS3Stages20261028 MediumLiteralS3Deleted20261028
open MediumDeletedIndicatorShift20261028 MediumActualPreliminaryCauchy20261028
open MediumPrimitivePsiSource20261028 MediumGlobalDyadicOwnership20261028
open MediumNativePrincipalSource20261028 MediumReceiverCutoffArithmetic20261028
open MediumActualDiagonalDivisorPayment20261028 OriginalSamePsiS1OwnedAtlas
open OriginalMediumS1SeparatedDivisorMean
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ElementaryTauTruncation.IntervalPayment

def levelGcd (t : PairIndex) : ℕ := Nat.gcd t.2.2.1 (t.1.1*t.1.2.1)

def badLevelDeleted (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ShiftCut atom H t ∧ ¬Close T t ∧ t.2.1.1.Coprime t.2.2.1 ∧
        ¬t.2.2.1.Coprime (t.1.1*t.1.2.1) then S3DeletedTerm atom z y k t else 0

def levelCoprimeFarFull (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ShiftCut atom H t ∧ ¬Close T t ∧ t.2.1.1.Coprime t.2.2.1 ∧
        t.2.2.1.Coprime (t.1.1*t.1.2.1) then S3FullTerm atom z y k t else 0

def activeBadLevel (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : Finset PairIndex :=
  (offDiagonalCarrier atom k).filter (fun t => ShiftCut atom H t ∧ ¬Close T t ∧
    t.2.1.1.Coprime t.2.2.1 ∧ ¬t.2.2.1.Coprime (t.1.1*t.1.2.1) ∧
    S3DeletedTerm atom z y k t ≠ 0)

theorem badLevelDeleted_eq_active (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) :
    badLevelDeleted atom z y k H T =
      ∑ t ∈ activeBadLevel atom z y k H T, S3DeletedTerm atom z y k t := by
  unfold badLevelDeleted activeBadLevel
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t <;> by_cases hc : Close T t <;>
    by_cases hr : t.2.1.1.Coprime t.2.2.1 <;>
      by_cases hl : t.2.2.1.Coprime (t.1.1*t.1.2.1) <;>
        by_cases hn : S3DeletedTerm atom z y k t = 0 <;> simp [hs,hc,hr,hl,hn]

/-- Signed disjoint split of J's actual retained source. The original
full/deleted dictionary is invoked only under both nonzero cutoffs. -/
theorem coprimeFarFull_eq_level_add_bad (atom : MediumAtom) (z y : ℝ)
    (k : Key) (H T : ℝ) :
    coprimeFarFull atom z y k H T =
      levelCoprimeFarFull atom z y k H T + badLevelDeleted atom z y k H T := by
  unfold coprimeFarFull levelCoprimeFarFull badLevelDeleted
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t
  · by_cases hc : Close T t
    · simp [hs,hc]
    · by_cases hr : t.2.1.1.Coprime t.2.2.1
      · by_cases hl : t.2.2.1.Coprime (t.1.1*t.1.2.1)
        · simp [hs,hc,hr,hl]
        · simpa [hs,hc,hr,hl] using fullTerm_eq_deleted_of_shiftCut atom z y k H t hs
      · simp [hs,hc,hr]
  · simp [hs]

theorem activeBadLevel_as_activeClose {atom : MediumAtom} {z y H T : ℝ} {k : Key}
    {t : PairIndex} (ht : t ∈ activeBadLevel atom z y k H T) :
    t ∈ activeClose atom z y k H (|(t.2.1.2 : ℝ)-t.2.2.2|+1) := by
  obtain ⟨hoff,hcut,hfar,hrs,hse,hne⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨hoff,hcut,by unfold Close; linarith,hne⟩

/-- The SECOND actual Lambda gives strict roughness of gcd(s,ell).
This does not reuse the r/s-gcd progression. -/
theorem activeBadLevel_gcd_gt {atom : MediumAtom} {z y H T : ℝ} {k : Key}
    (hz : 0 ≤ z) {t : PairIndex}
    (ht : t ∈ activeBadLevel atom (strictReceiverCutoff z) y k H T) :
    z < (levelGcd t : ℝ) := by
  obtain ⟨hoff,hcut,hfar,hrs,hse,hne⟩ := mem_filter.mp ht
  have hλ : lambdaTrim atom (strictReceiverCutoff z) y k t.1.2.1 t.2.2.1 ≠ 0 := by
    intro hzero
    exact hne (by simp [S3DeletedTerm,pairCoefficient,hzero])
  have hs := lambdaTrim_rough_support atom _ y k _ _ hλ
  have hf0 : 0 < levelGcd t := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hs.1)
  have hf1 : levelGcd t ≠ 1 := by
    intro hf
    exact hse hf
  have hp : Nat.Prime (levelGcd t).minFac := Nat.minFac_prime hf1
  have hps : (levelGcd t).minFac ∣ t.2.2.1 :=
    (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
  have hzp : z < ((levelGcd t).minFac : ℝ) :=
    (original_lt_nat_iff_receiver_le z hz _).mpr
      (hs.2 _ (Nat.mem_primeFactors.mpr ⟨hp,hps,hs.1⟩))
  exact hzp.trans_le (by exact_mod_cast Nat.le_of_dvd hf0 (Nat.minFac_dvd _))

/-- f|ell places f in the FIRST nonzero shift's divisor bank; f|s
upgrades the SECOND original congruence to ell*f. -/
theorem activeBadLevel_arithmetic {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ)
    {t : PairIndex} (ht : t ∈ activeBadLevel atom z y k H T) :
    levelGcd t ∣ shiftAbs atom (firstMN t) ∧
      levelGcd t ∣ t.1.1*t.1.2.1 ∧
      Int.ModEq (((t.1.1*t.1.2.1)*levelGcd t : ℕ) : ℤ)
        ((t.2.2.2*t.1.2.2 : ℕ) : ℤ) atom.residue := by
  have htC := activeBadLevel_as_activeClose ht
  obtain ⟨_,_,_,hL,_,_⟩ := activeClose_data hA z y k H _ htC
  have hne := (mem_filter.mp ht).2.2.2.2.2
  have hsecond : secondDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro hzero
    exact hne (by simp [S3DeletedTerm,hzero])
  have hfe : levelGcd t ∣ t.1.1*t.1.2.1 := Nat.gcd_dvd_right _ _
  have hfs : levelGcd t ∣ t.2.2.1 := Nat.gcd_dvd_left _ _
  refine ⟨hfe.trans ((dvd_mul_right _ _).trans hL),hfe,?_⟩
  exact (deletedIndicator_modEq hsecond).of_dvd
    (by exact_mod_cast Nat.mul_dvd_mul_left (t.1.1*t.1.2.1) hfs)

def roughLevelDivisors (atom : MediumAtom) (z : ℝ) (p qd : ℕ × ℕ) : Finset ℕ :=
  (shiftAbs atom p).divisors.filter (fun f => z < (f : ℝ) ∧ f ∣ qd.1*qd.2)

def levelSeconds (atom : MediumAtom) (H : ℝ) (p qd : ℕ × ℕ) (f : ℕ) : Finset ℕ :=
  atom.alphaCarrier.filter (fun n =>
    Int.ModEq (((qd.1*qd.2)*f : ℕ) : ℤ) ((n*p.1 : ℕ) : ℤ) atom.residue ∧
      shiftAbs atom (p.1,n) ≠ 0 ∧ tauR (shiftAbs atom (p.1,n)) ≤ H)

abbrev LevelCode := Σ _ : ℕ × ℕ, Σ _ : ℕ × ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ × ℕ

def levelCode (t : PairIndex) : LevelCode :=
  ⟨firstMN t,⟨(t.1.1,t.1.2.1),⟨levelGcd t,⟨t.2.2.2,(t.2.1.1,t.2.2.1)⟩⟩⟩⟩

def levelDecode (v : LevelCode) : PairIndex :=
  ((v.2.1.1,v.2.1.2,v.1.1),(v.2.2.2.2.1,v.1.2),(v.2.2.2.2.2,v.2.2.2.1))

def levelCodeCarrier (atom : MediumAtom) (k : Key) (z H : ℝ) : Finset LevelCode :=
  (smallFirstPairs atom H).sigma (fun p => (divisorQD atom k p).sigma (fun qd =>
    (roughLevelDivisors atom z p qd).sigma (fun f => (levelSeconds atom H p qd f).sigma
      (fun n => (shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1,n)).divisors))))

theorem levelCode_injective : Function.Injective levelCode := by
  intro t u h
  exact congrArg levelDecode h

theorem activeBadLevel_card_le_code {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (hz : 0 ≤ z)
    (k : Key) (H T : ℝ) :
    (activeBadLevel atom (strictReceiverCutoff z) y k H T).card ≤
      (levelCodeCarrier atom k z H).card := by
  apply card_le_card_of_injOn levelCode
  · intro t ht
    have htC := activeBadLevel_as_activeClose ht
    obtain ⟨hmn1,hmn2,hqd,hL,hR,_⟩ := activeClose_data hA _ y k H _ htC
    obtain ⟨hf,hfe,hsecond⟩ := activeBadLevel_arithmetic hA _ y k H T ht
    have hcut := (mem_filter.mp ht).2.1
    have hq : t.1.1 ∣ shiftAbs atom (firstMN t) :=
      dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hL)
    have hd : t.1.2.1 ∣ shiftAbs atom (firstMN t) :=
      dvd_trans (dvd_mul_left _ _) (dvd_trans (dvd_mul_right _ _) hL)
    have hr : t.2.1.1 ∣ shiftAbs atom (firstMN t) := dvd_trans (dvd_mul_left _ _) hL
    have hs : t.2.2.1 ∣ shiftAbs atom (secondMN t) := dvd_trans (dvd_mul_left _ _) hR
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨hmn1,hcut.1,hcut.2.2.1⟩,
      mem_sigma.mpr ⟨?_,mem_sigma.mpr ⟨?_,mem_sigma.mpr ⟨?_,?_⟩⟩⟩⟩
    · exact mem_filter.mpr ⟨mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hq,hcut.1⟩,
        Nat.mem_divisors.mpr ⟨hd,hcut.1⟩⟩,hqd⟩
    · exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hf,hcut.1⟩,activeBadLevel_gcd_gt hz ht,hfe⟩
    · exact mem_filter.mpr ⟨(mem_product.mp hmn2).2,hsecond,hcut.2.1,hcut.2.2.2⟩
    · exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hr,hcut.1⟩,
        Nat.mem_divisors.mpr ⟨hs,hcut.2.1⟩⟩
  · exact fun t ht u hu h => levelCode_injective h

/-- Any nonempty SECOND product fibre has one primitive n2 residue
modulo ell*f. Its chosen representative need not be the original n1.
Repeated prime factors in ell and f are retained. -/
theorem levelSeconds_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (k : Key) (H z : ℝ) (hz : 0 < z)
    (p qd : ℕ × ℕ) (hqd : qd ∈ nativeQD atom k) (f : ℕ)
    (hf : z < (f : ℝ)) (hfell : f ∣ qd.1*qd.2) :
    ((levelSeconds atom H p qd f).card : ℝ) ≤ 2*atom.U/(keyY atom k*z)+1 := by
  obtain ⟨hell,hlevel,haell⟩ := nativeQD_positive_level hA k qd hqd
  have hY := keyY_positive hA k
  have hU : 0 < atom.U := zero_lt_one.trans_le hA.1
  have hfpos : 0 < f := by exact_mod_cast hz.trans hf
  have hlev : keyY atom k/2 ≤ ((qd.1*qd.2 : ℕ) : ℝ) := by
    simpa only [singleZeroY,keyY,keyD,Nat.cast_pow,Nat.cast_ofNat] using hlevel
  by_cases hne : (levelSeconds atom H p qd f).Nonempty
  · obtain ⟨n0,hn0⟩ := hne
    have ha : ((qd.1*qd.2)*f).Coprime atom.residue.natAbs :=
      Nat.coprime_mul_iff_left.mpr ⟨haell,Nat.Coprime.of_dvd_left hfell haell⟩
    have hroot := (mem_filter.mp hn0).2.1
    have hcount := card_real_supported_modEq_dvd_le_lcm (levelSeconds atom H p qd f)
      (a := atom.U) (b := 2*atom.U) (q := (qd.1*qd.2)*f) (d := 1) (r := n0)
      (by linarith) (Nat.mul_pos hell hfpos) (by norm_num)
      (fun n hn => by
        have hi := mem_Icc.mp (mem_filter.mp (mem_filter.mp hn).1).1
        exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hi.1),
          (show (n : ℝ) ≤ Nat.floor (2*atom.U) by exact_mod_cast hi.2).trans
            (Nat.floor_le (by positivity))⟩)
      (fun n hn => two_products_force_alpha_progression ha hroot (mem_filter.mp hn).2.1)
      (fun n hn => one_dvd _)
    have hcount' : ((levelSeconds atom H p qd f).card : ℝ) ≤
        atom.U/(((qd.1*qd.2 : ℕ) : ℝ)*f)+1 := by
      simpa only [Nat.lcm_one_left,Nat.cast_mul,show 2*atom.U-atom.U = atom.U by ring] using hcount
    apply hcount'.trans
    apply add_le_add_right
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < ((qd.1*qd.2 : ℕ) : ℝ)*f)
      (mul_pos hY hz)).mpr
    have hh : keyY atom k*z ≤ 2*((qd.1*qd.2 : ℕ) : ℝ)*f := by
      have h1 := mul_le_mul_of_nonneg_right hlev hz.le
      have h2 := mul_le_mul_of_nonneg_left hf.le
        (show 0 ≤ ((qd.1*qd.2 : ℕ) : ℝ) by positivity)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh hU.le]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [card_empty,Nat.cast_zero]
    positivity

/-- All q,d,f,r,s labels are counted. The f-label costs one divisor H;
the new primitive SECOND-product progression supplies the saving 1/z. -/
theorem activeBadLevel_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (hz : 0 < z)
    (k : Key) (H T : ℝ) (hH : 0 ≤ H) :
    ((activeBadLevel atom (strictReceiverCutoff z) y k H T).card : ℝ) ≤
      12*atom.scale*(2*atom.U/(keyY atom k*z)+1)*H^5 := by
  let Occ : ℝ := 2*atom.U/(keyY atom k*z)+1
  have hY := keyY_positive hA k
  have hU : 0 ≤ atom.U := zero_le_one.trans hA.1
  have hOcc : 0 ≤ Occ := by dsimp [Occ]; positivity
  have hrow (p : ℕ × ℕ) (hp : p ∈ smallFirstPairs atom H) :
      (∑ qd ∈ divisorQD atom k p, ∑ f ∈ roughLevelDivisors atom z p qd,
        ∑ n ∈ levelSeconds atom H p qd f,
          (((shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1,n)).divisors).card : ℝ)) ≤
        Occ*H^5 := by
    have htau := (mem_filter.mp hp).2.2
    have hQD : ((divisorQD atom k p).card : ℝ) ≤ H^2 := by
      have hh := card_le_card (filter_subset (fun qd => qd ∈ nativeQD atom k)
        ((shiftAbs atom p).divisors ×ˢ (shiftAbs atom p).divisors))
      have hhR : ((divisorQD atom k p).card : ℝ) ≤ tauR (shiftAbs atom p)^2 := by
        simpa only [card_product,Nat.cast_mul,tauR,pow_two] using (Nat.cast_le.mpr hh :
          ((divisorQD atom k p).card : ℝ) ≤ _)
      exact hhR.trans (pow_le_pow_left₀ (by dsimp [tauR]; positivity) htau 2)
    have hF (qd : ℕ × ℕ) : ((roughLevelDivisors atom z p qd).card : ℝ) ≤ H :=
      (Nat.cast_le.mpr (card_le_card (filter_subset _ _))).trans htau
    calc
      _ ≤ ∑ _qd ∈ divisorQD atom k p, Occ*H^3 := by
        apply sum_le_sum
        intro qd hqd
        calc
          _ ≤ ∑ _f ∈ roughLevelDivisors atom z p qd, Occ*H^2 := by
            apply sum_le_sum
            intro f hf
            calc
              _ ≤ ∑ _n ∈ levelSeconds atom H p qd f, H^2 := by
                apply sum_le_sum
                intro n hn
                rw [card_product,Nat.cast_mul]
                change tauR (shiftAbs atom p)*tauR (shiftAbs atom (p.1,n)) ≤ H^2
                simpa only [pow_two] using mul_le_mul htau (mem_filter.mp hn).2.2.2
                  (show 0 ≤ tauR (shiftAbs atom (p.1,n)) by dsimp [tauR]; positivity) hH
              _ = ((levelSeconds atom H p qd f).card : ℝ)*H^2 := by simp
              _ ≤ Occ*H^2 := mul_le_mul_of_nonneg_right
                (levelSeconds_card_le hA k H z hz p qd (mem_filter.mp hqd).2 f
                  (mem_filter.mp hf).2.1 (mem_filter.mp hf).2.2) (sq_nonneg H)
          _ = ((roughLevelDivisors atom z p qd).card : ℝ)*(Occ*H^2) := by simp
          _ ≤ H*(Occ*H^2) := mul_le_mul_of_nonneg_right (hF qd) (by positivity)
          _ = Occ*H^3 := by ring
      _ = ((divisorQD atom k p).card : ℝ)*(Occ*H^3) := by simp
      _ ≤ H^2*(Occ*H^3) := mul_le_mul_of_nonneg_right hQD (by positivity)
      _ = Occ*H^5 := by ring
  calc
    _ ≤ ((levelCodeCarrier atom k z H).card : ℝ) := by
      exact_mod_cast activeBadLevel_card_le_code hA z y hz.le k H T
    _ = ∑ p ∈ smallFirstPairs atom H, ∑ qd ∈ divisorQD atom k p,
        ∑ f ∈ roughLevelDivisors atom z p qd, ∑ n ∈ levelSeconds atom H p qd f,
          (((shiftAbs atom p).divisors ×ˢ (shiftAbs atom (p.1,n)).divisors).card : ℝ) := by
      simp only [levelCodeCarrier,card_sigma,Nat.cast_sum]
    _ ≤ ∑ _p ∈ smallFirstPairs atom H, Occ*H^5 := sum_le_sum hrow
    _ = ((smallFirstPairs atom H).card : ℝ)*(Occ*H^5) := by simp
    _ ≤ (12*atom.scale)*(Occ*H^5) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (Nat.cast_le.mpr (card_le_card (filter_subset _ _))).trans (actualMN_card_le hA)
    _ = _ := by ring

theorem badLevelDeleted_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (hz : 0 < z)
    (k : Key) (H T : ℝ) (hH : 0 ≤ H) :
    ‖badLevelDeleted atom (strictReceiverCutoff z) y k H T‖ ≤
      12*atom.scale*(2*atom.U/(keyY atom k*z)+1)*H^7 := by
  rw [badLevelDeleted_eq_active]
  calc
    _ ≤ ∑ t ∈ activeBadLevel atom (strictReceiverCutoff z) y k H T,
        ‖S3DeletedTerm atom (strictReceiverCutoff z) y k t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ activeBadLevel atom (strictReceiverCutoff z) y k H T, H^2 := by
      apply sum_le_sum
      intro t ht
      exact activeClose_term_le hA _ y k H _ (activeBadLevel_as_activeClose ht)
    _ = ((activeBadLevel atom (strictReceiverCutoff z) y k H T).card : ℝ)*H^2 := by simp
    _ ≤ (12*atom.scale*(2*atom.U/(keyY atom k*z)+1)*H^5)*H^2 :=
      mul_le_mul_of_nonneg_right (activeBadLevel_card_le hA z y hz k H T hH) (sq_nonneg H)
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalS3RoughLevelGcd20261102
