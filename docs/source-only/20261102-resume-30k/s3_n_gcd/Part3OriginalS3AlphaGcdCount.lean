import ImbalancedChen.Part3OriginalS3RoughPairGcdResidual
import ImbalancedChen.RoughSquareException
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original completion 172--177, n1/n2 exclusion after the literal
shift cutoffs and the already paid r/s and close exclusions.
Alpha is rough at roughZ(scale), independently of the Lambda receiver.
No squarefreeness is needed: the full gcd, including prime powers, is counted.
-/
namespace ImbalancedChen.Part3.OriginalS3AlphaGcdCount20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3RoughPairGcd20261102 OriginalS3RoughPairGcdResidual20261102
open OriginalS3ClosePairCount20261102 OriginalS3ClosePairResidual20261102
open MediumLiteralS3Stages20261028 MediumLiteralS3Deleted20261028
open MediumDeletedIndicatorShift20261028 MediumActualPreliminaryCauchy20261028
open MediumPrimitivePsiSource20261028 MediumGlobalDyadicOwnership20261028
open MediumNativePrincipalSource20261028 MediumReceiverCutoffArithmetic20261028
open MediumActualDiagonalDivisorPayment20261028 OriginalSamePsiS1OwnedAtlas
open ActualRoughContourParameters20261026b
open OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ElementaryTauTruncation.IntervalPayment

def alphaBadDeleted (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ShiftCut atom H t ∧ ¬Close T t ∧ t.2.1.1.Coprime t.2.2.1 ∧
        ¬t.2.1.2.Coprime t.2.2.2 then S3DeletedTerm atom z y k t else 0

def doubleCoprimeFarFull (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ShiftCut atom H t ∧ ¬Close T t ∧ t.2.1.1.Coprime t.2.2.1 ∧
        t.2.1.2.Coprime t.2.2.2 then S3FullTerm atom z y k t else 0

def alphaBadActive (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : Finset PairIndex :=
  (offDiagonalCarrier atom k).filter (fun t => ShiftCut atom H t ∧ ¬Close T t ∧
    t.2.1.1.Coprime t.2.2.1 ∧ ¬t.2.1.2.Coprime t.2.2.2 ∧ S3DeletedTerm atom z y k t ≠ 0)

theorem alphaBadDeleted_eq_active (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) :
    alphaBadDeleted atom z y k H T =
      ∑ t ∈ alphaBadActive atom z y k H T, S3DeletedTerm atom z y k t := by
  unfold alphaBadDeleted alphaBadActive
  rw [sum_filter]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t <;> by_cases hc : Close T t <;>
    by_cases hr : t.2.1.1.Coprime t.2.2.1 <;>
      by_cases hn : t.2.1.2.Coprime t.2.2.2 <;>
        by_cases hz : S3DeletedTerm atom z y k t = 0 <;> simp [hs,hc,hr,hn,hz]

theorem coprimeFarFull_eq_double_add_bad (atom : MediumAtom) (z y : ℝ)
    (k : Key) (H T : ℝ) :
    coprimeFarFull atom z y k H T =
      doubleCoprimeFarFull atom z y k H T + alphaBadDeleted atom z y k H T := by
  unfold coprimeFarFull doubleCoprimeFarFull alphaBadDeleted
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t
  · by_cases hc : Close T t <;> by_cases hr : t.2.1.1.Coprime t.2.2.1
    · simp [hs,hc,hr]
    · simp [hs,hc,hr]
    · by_cases hn : t.2.1.2.Coprime t.2.2.2
      · simp [hs,hc,hr,hn]
      · simpa [hs,hc,hr,hn] using fullTerm_eq_deleted_of_shiftCut atom z y k H t hs
    · simp [hs,hc,hr]
  · simp [hs]

theorem alphaBadActive_as_activeClose {atom : MediumAtom} {z y H T : ℝ} {k : Key}
    {t : PairIndex} (ht : t ∈ alphaBadActive atom z y k H T) :
    t ∈ activeClose atom z y k H (|(t.2.1.2 : ℝ)-t.2.2.2|+1) := by
  obtain ⟨hoff,hcut,hfar,hrs,hnn,hne⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨hoff,hcut,by unfold Close; linarith,hne⟩

theorem alpha_mem_bounds {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) {n : ℕ} (hn : n ∈ atom.alphaCarrier) :
    atom.U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*atom.U ∧ 0 < n := by
  have hi := mem_Icc.mp (mem_filter.mp hn).1
  have hlo : atom.U ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hi.1)
  have hhi : (n : ℝ) ≤ 2*atom.U :=
    (show (n : ℝ) ≤ Nat.floor (2*atom.U) by exact_mod_cast hi.2).trans
      (Nat.floor_le (by linarith [hA.1]))
  exact ⟨hlo,hhi,by exact_mod_cast (zero_lt_one.trans_le (hA.1.trans hlo))⟩

/-- The alpha roughness gate is the ORIGINAL roughZ, not the independently
chosen numerical Lambda receiver. Both full gcd divisibilities survive. -/
theorem alphaBadActive_gcd_data {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ)
    {t : PairIndex} (ht : t ∈ alphaBadActive atom z y k H T) :
    roughZ atom.scale < (Nat.gcd t.2.1.2 t.2.2.2 : ℝ) ∧
    (Nat.gcd t.2.1.2 t.2.2.2 : ℝ) ≤ 2*atom.U ∧
    (Nat.gcd t.2.1.2 t.2.2.2).Coprime (t.1.1*t.1.2.1) := by
  have hC := alphaBadActive_as_activeClose ht
  obtain ⟨hmn1,hmn2,hqd,hL,hR,hmod⟩ := activeClose_data hA z y k H _ hC
  obtain ⟨hoff,hcut,hfar,hrs,hnn,hne⟩ := mem_filter.mp ht
  have hn1 := (mem_product.mp hmn1).2
  have hnb := alpha_mem_bounds hA hn1
  have hα : atom.alpha t.2.1.2 ≠ 0 := by
    intro hz; exact hne (by simp [S3DeletedTerm,pairCoefficient,hz])
  have hrough := hA
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hrough,_⟩ := hrough
  let f := Nat.gcd t.2.1.2 t.2.2.2
  have hfpos : 0 < f := Nat.gcd_pos_of_pos_left _ hnb.2.2
  have hfne : f ≠ 1 := by intro h; exact hnn h
  have hprime : Nat.Prime f.minFac := Nat.minFac_prime hfne
  have hpr : f.minFac ∣ t.2.1.2 := (Nat.minFac_dvd f).trans (Nat.gcd_dvd_left _ _)
  have hzf : roughZ atom.scale < (f : ℝ) := by
    have hp : roughZ atom.scale < (f.minFac : ℝ) := hrough _ hn1 hα _ hprime hpr
    exact hp.trans_le (by exact_mod_cast Nat.le_of_dvd hfpos (Nat.minFac_dvd f))
  have hfupper : (f : ℝ) ≤ 2*atom.U :=
    (show (f : ℝ) ≤ t.2.1.2 by exact_mod_cast
      Nat.le_of_dvd hnb.2.2 (Nat.gcd_dvd_left _ _)).trans hnb.2.1
  have hfirst : firstDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro hz; exact hne (by simp [S3DeletedTerm,hz])
  have hcong := (deletedIndicator_modEq hfirst).of_dvd
    (show ((t.1.1*t.1.2.1 : ℕ) : ℤ) ∣
      (((t.1.1*t.1.2.1)*t.2.1.1 : ℕ) : ℤ) by exact_mod_cast dvd_mul_right _ _)
  have ha := (nativeQD_positive_level hA k _ hqd).2.2
  have hag : Int.gcd atom.residue ((t.1.1*t.1.2.1 : ℕ) : ℤ) = 1 := by
    simpa only [Int.gcd,Int.natAbs_natCast,Nat.gcd_comm] using ha.gcd_eq_one
  have hprod : (t.2.1.2*t.1.2.2).Coprime (t.1.1*t.1.2.1) := by
    have hh : Int.gcd ((t.2.1.2*t.1.2.2 : ℕ) : ℤ) ((t.1.1*t.1.2.1 : ℕ) : ℤ) = 1 := by
      rw [← Int.gcd_emod ((t.2.1.2*t.1.2.2 : ℕ) : ℤ) ((t.1.1*t.1.2.1 : ℕ) : ℤ),
        hcong.eq,Int.gcd_emod,hag]
    simpa only [Int.gcd,Int.natAbs_natCast] using hh
  exact ⟨hzf,hfupper,Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left _ _)
    (Nat.coprime_mul_iff_left.mp hprod).1⟩

def alphaGcdBank (atom : MediumAtom) : Finset ℕ :=
  (Icc 1 (Nat.floor (2*atom.U))).filter (fun f => roughZ atom.scale < (f : ℝ))

def alphaFirsts (atom : MediumAtom) (H : ℝ) (m f : ℕ) : Finset ℕ :=
  atom.alphaCarrier.filter (fun n => f ∣ n ∧ shiftAbs atom (m,n) ≠ 0 ∧
    tauR (shiftAbs atom (m,n)) ≤ H)

def alphaQD (atom : MediumAtom) (k : Key) (m f n : ℕ) : Finset (ℕ × ℕ) :=
  (divisorQD atom k (m,n)).filter (fun qd => f.Coprime (qd.1*qd.2))

def alphaSeconds (atom : MediumAtom) (H : ℝ) (m f n1 : ℕ) (qd : ℕ × ℕ) : Finset ℕ :=
  atom.alphaCarrier.filter (fun n =>
    Int.ModEq ((qd.1*qd.2 : ℕ) : ℤ) (n : ℤ) (n1 : ℤ) ∧ f ∣ n ∧
    shiftAbs atom (m,n) ≠ 0 ∧ tauR (shiftAbs atom (m,n)) ≤ H)

abbrev AlphaCode := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ × ℕ, Σ _ : ℕ, ℕ × ℕ
def alphaCode (t : PairIndex) : AlphaCode :=
  ⟨t.1.2.2,⟨Nat.gcd t.2.1.2 t.2.2.2,⟨t.2.1.2,
    ⟨(t.1.1,t.1.2.1),⟨t.2.2.2,(t.2.1.1,t.2.2.1)⟩⟩⟩⟩⟩
def alphaDecode (v : AlphaCode) : PairIndex :=
  ((v.2.2.2.1.1,v.2.2.2.1.2,v.1),
    (v.2.2.2.2.2.1,v.2.2.1),(v.2.2.2.2.2.2,v.2.2.2.2.1))
def alphaCodeCarrier (atom : MediumAtom) (k : Key) (H : ℝ) : Finset AlphaCode :=
  (paperPsiNaturalCarrier atom.V).sigma (fun m => (alphaGcdBank atom).sigma (fun f =>
    (alphaFirsts atom H m f).sigma (fun n1 => (alphaQD atom k m f n1).sigma (fun qd =>
      (alphaSeconds atom H m f n1 qd).sigma (fun n2 =>
        (shiftAbs atom (m,n1)).divisors ×ˢ (shiftAbs atom (m,n2)).divisors)))))

theorem alphaCode_injective : Function.Injective alphaCode := by
  intro t u h
  exact congrArg alphaDecode h

theorem alphaBadActive_card_le_code {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    (alphaBadActive atom z y k H T).card ≤ (alphaCodeCarrier atom k H).card := by
  apply card_le_card_of_injOn alphaCode
  · intro t ht
    obtain ⟨hmn1,hmn2,hqd,hL,hR,hmod⟩ :=
      activeClose_data hA z y k H _ (alphaBadActive_as_activeClose ht)
    obtain ⟨hzf,hfupper,hfcop⟩ := alphaBadActive_gcd_data hA z y k H T ht
    have hcut := (mem_filter.mp ht).2.1
    have hn1 := alpha_mem_bounds hA (mem_product.mp hmn1).2
    have hfpos := Nat.gcd_pos_of_pos_left t.2.2.2 hn1.2.2
    have hq : t.1.1 ∣ shiftAbs atom (firstMN t) :=
      dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hL)
    have hd : t.1.2.1 ∣ shiftAbs atom (firstMN t) :=
      dvd_trans (dvd_mul_left _ _) (dvd_trans (dvd_mul_right _ _) hL)
    have hr : t.2.1.1 ∣ shiftAbs atom (firstMN t) := dvd_trans (dvd_mul_left _ _) hL
    have hs : t.2.2.1 ∣ shiftAbs atom (secondMN t) := dvd_trans (dvd_mul_left _ _) hR
    apply mem_sigma.mpr
    refine ⟨(mem_product.mp hmn1).1,mem_sigma.mpr ⟨?_,mem_sigma.mpr ⟨?_,
      mem_sigma.mpr ⟨?_,mem_sigma.mpr ⟨?_,?_⟩⟩⟩⟩⟩
    · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hfpos,Nat.le_floor hfupper⟩,hzf⟩
    · exact mem_filter.mpr ⟨(mem_product.mp hmn1).2,
        Nat.gcd_dvd_left _ _,hcut.1,hcut.2.2.1⟩
    · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨hq,hcut.1⟩,Nat.mem_divisors.mpr ⟨hd,hcut.1⟩⟩,hqd⟩,hfcop⟩
    · exact mem_filter.mpr ⟨(mem_product.mp hmn2).2,hmod,
        Nat.gcd_dvd_right _ _,hcut.2.1,hcut.2.2.2⟩
    · exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hr,hcut.1⟩,
        Nat.mem_divisors.mpr ⟨hs,hcut.2.1⟩⟩
  · exact fun t ht u hu h => alphaCode_injective h

/-- The first reciprocal factor comes from an actual alpha multiple count.
The finite bank cap absorbs the +1 without a divisor maximum. -/
theorem alphaFirsts_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (H : ℝ) (m f : ℕ)
    (hf : f ∈ alphaGcdBank atom) :
    ((alphaFirsts atom H m f).card : ℝ) ≤ 3*atom.U/(f : ℝ) := by
  have hfI := mem_Icc.mp (mem_filter.mp hf).1
  have hfpos : 0 < f := hfI.1
  have hfR : (0 : ℝ) < f := by exact_mod_cast hfpos
  have hfU : (f : ℝ) ≤ 2*atom.U :=
    (show (f : ℝ) ≤ Nat.floor (2*atom.U) by exact_mod_cast hfI.2).trans
      (Nat.floor_le (by linarith [hA.1]))
  have hh := real_supported_multiples_card_le atom.alphaCarrier
    (a := atom.U) (b := 2*atom.U) (by linarith [hA.1]) (by linarith [hA.1]) hfpos
    (fun n hn => ⟨(alpha_mem_bounds hA hn).1,(alpha_mem_bounds hA hn).2.1⟩)
  have hs : alphaFirsts atom H m f ⊆ atom.alphaCarrier.filter (fun n => f ∣ n) := by
    intro n hn
    exact mem_filter.mpr ⟨(mem_filter.mp hn).1,(mem_filter.mp hn).2.1⟩
  have hcount : ((alphaFirsts atom H m f).card : ℝ) ≤ atom.U/(f : ℝ)+1 := by
    exact (Nat.cast_le.mpr (card_le_card hs)).trans (by simpa only [show 2*atom.U-atom.U=atom.U by ring] using hh)
  apply hcount.trans
  apply (le_div_iff₀ hfR).mpr
  have hid : (atom.U/(f : ℝ)+1)*(f : ℝ) = atom.U+f := by field_simp [hfR.ne']; ring
  rw [hid]
  linarith

/-- Both original products force one ell progression; gcd(f,ell)=1 turns
the simultaneous multiple condition into ell*f spacing. -/
theorem alphaSeconds_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (k : Key) (H : ℝ) (m f n1 : ℕ)
    (hf : 0 < f) (qd : ℕ × ℕ) (hqd : qd ∈ alphaQD atom k m f n1) :
    ((alphaSeconds atom H m f n1 qd).card : ℝ) ≤ 2*atom.U/(keyY atom k*f)+1 := by
  have hcop := (mem_filter.mp hqd).2
  have hnative := (mem_filter.mp (mem_filter.mp hqd).1).2
  obtain ⟨hell,hlevel,_⟩ := nativeQD_positive_level hA k qd hnative
  have hY := keyY_positive hA k
  have hlev : keyY atom k/2 ≤ ((qd.1*qd.2 : ℕ) : ℝ) := by
    simpa only [singleZeroY,keyY,keyD,Nat.cast_pow,Nat.cast_ofNat] using hlevel
  have hcount := card_real_supported_modEq_dvd_le_lcm (alphaSeconds atom H m f n1 qd)
    (a := atom.U) (b := 2*atom.U) (q := qd.1*qd.2) (d := f) (r := n1)
    (by linarith [hA.1]) hell hf
    (fun n hn => ⟨(alpha_mem_bounds hA (mem_filter.mp hn).1).1,
      (alpha_mem_bounds hA (mem_filter.mp hn).1).2.1⟩)
    (fun n hn => (mem_filter.mp hn).2.1) (fun n hn => (mem_filter.mp hn).2.2.1)
  have hcount' : ((alphaSeconds atom H m f n1 qd).card : ℝ) ≤
      atom.U/((f : ℝ)*((qd.1*qd.2 : ℕ) : ℝ))+1 := by
    simpa only [hcop.lcm_eq_mul,Nat.cast_mul,show 2*atom.U-atom.U=atom.U by ring] using hcount
  apply hcount'.trans
  apply add_le_add_right
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<(f : ℝ)*((qd.1*qd.2 : ℕ) : ℝ))
    (by positivity : (0 : ℝ)<keyY atom k*f)).mpr
  have hU : 0 ≤ atom.U := by linarith [hA.1]
  nlinarith [mul_le_mul_of_nonneg_left hlev (mul_nonneg hU (Nat.cast_nonneg f))]

theorem alphaQD_card_le {atom : MediumAtom} {k : Key} {m f n : ℕ} {H : ℝ}
    (hH : 0 ≤ H) (hn : n ∈ alphaFirsts atom H m f) :
    ((alphaQD atom k m f n).card : ℝ) ≤ H^2 := by
  have htau := (mem_filter.mp hn).2.2.2
  have hs : alphaQD atom k m f n ⊆
      (shiftAbs atom (m,n)).divisors ×ˢ (shiftAbs atom (m,n)).divisors :=
    (filter_subset _ _).trans (filter_subset _ _)
  have hh : ((alphaQD atom k m f n).card : ℝ) ≤ tauR (shiftAbs atom (m,n))^2 := by
    simpa only [card_product,Nat.cast_mul,tauR,pow_two] using
      (Nat.cast_le.mpr (card_le_card hs) : ((alphaQD atom k m f n).card : ℝ) ≤ _)
  exact hh.trans (pow_le_pow_left₀ (by unfold tauR; positivity) htau 2)

theorem paperM_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) :
    ((paperPsiNaturalCarrier atom.V).card : ℝ) ≤ 4*atom.V := by
  have hs : paperPsiNaturalCarrier atom.V ⊆ range (Nat.floor (5*atom.V/2)+1) := by
    intro m hm
    exact mem_range.mpr (by have := (mem_Icc.mp hm).2; omega)
  have hc := card_le_card hs
  simp only [card_range] at hc
  have hcR : ((paperPsiNaturalCarrier atom.V).card : ℝ) ≤
      (Nat.floor (5*atom.V/2) : ℝ)+1 := by exact_mod_cast hc
  have hf := Nat.floor_le (show 0 ≤ 5*atom.V/2 by linarith [hA.2.1])
  linarith [hA.2.1]

/-- Every original q,d,r,s label costs H^4; the gcd is summed directly,
not charged to a pointwise divisor power of n1. -/
theorem alphaBadActive_card_le_sum {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) (hH : 0 ≤ H) :
    ((alphaBadActive atom z y k H T).card : ℝ) ≤
      4*atom.V * (∑ f ∈ alphaGcdBank atom,
        (3*atom.U/(f : ℝ))*(2*atom.U/(keyY atom k*f)+1)) * H^4 := by
  have hU : 0 ≤ atom.U := by linarith [hA.1]
  have hY := keyY_positive hA k
  have hrow (m f : ℕ) (hf : f ∈ alphaGcdBank atom) :
      (∑ n1 ∈ alphaFirsts atom H m f, ∑ qd ∈ alphaQD atom k m f n1,
        ∑ n2 ∈ alphaSeconds atom H m f n1 qd,
          (((shiftAbs atom (m,n1)).divisors ×ˢ (shiftAbs atom (m,n2)).divisors).card : ℝ)) ≤
        ((3*atom.U/(f : ℝ))*(2*atom.U/(keyY atom k*f)+1))*H^4 := by
    have hfpos : 0 < f := (mem_Icc.mp (mem_filter.mp hf).1).1
    let O : ℝ := 2*atom.U/(keyY atom k*f)+1
    have hO : 0 ≤ O := by dsimp [O]; positivity
    calc
      _ ≤ ∑ _n1 ∈ alphaFirsts atom H m f, O*H^4 := by
        apply sum_le_sum
        intro n1 hn1
        have htau := (mem_filter.mp hn1).2.2.2
        calc
          _ ≤ ∑ _qd ∈ alphaQD atom k m f n1, O*H^2 := by
            apply sum_le_sum
            intro qd hqd
            calc
              _ ≤ ∑ _n2 ∈ alphaSeconds atom H m f n1 qd, H^2 := by
                apply sum_le_sum
                intro n2 hn2
                rw [card_product,Nat.cast_mul]
                change tauR (shiftAbs atom (m,n1))*tauR (shiftAbs atom (m,n2)) ≤ H^2
                simpa only [pow_two] using mul_le_mul htau (mem_filter.mp hn2).2.2.2.2
                  (show 0 ≤ tauR (shiftAbs atom (m,n2)) by unfold tauR; positivity) hH
              _ = ((alphaSeconds atom H m f n1 qd).card : ℝ)*H^2 := by simp
              _ ≤ O*H^2 := mul_le_mul_of_nonneg_right
                (alphaSeconds_card_le hA k H m f n1 hfpos qd hqd) (sq_nonneg H)
          _ = ((alphaQD atom k m f n1).card : ℝ)*(O*H^2) := by simp
          _ ≤ H^2*(O*H^2) := mul_le_mul_of_nonneg_right (alphaQD_card_le hH hn1) (by positivity)
          _ = O*H^4 := by ring
      _ = ((alphaFirsts atom H m f).card : ℝ)*(O*H^4) := by simp
      _ ≤ (3*atom.U/(f : ℝ))*(O*H^4) :=
        mul_le_mul_of_nonneg_right (alphaFirsts_card_le hA H m f hf) (by positivity)
      _ = _ := by dsimp [O]; ring
  calc
    _ ≤ ((alphaCodeCarrier atom k H).card : ℝ) := by
      exact_mod_cast alphaBadActive_card_le_code hA z y k H T
    _ = ∑ m ∈ paperPsiNaturalCarrier atom.V, ∑ f ∈ alphaGcdBank atom,
        ∑ n1 ∈ alphaFirsts atom H m f, ∑ qd ∈ alphaQD atom k m f n1,
          ∑ n2 ∈ alphaSeconds atom H m f n1 qd,
            (((shiftAbs atom (m,n1)).divisors ×ˢ (shiftAbs atom (m,n2)).divisors).card : ℝ) := by
      simp only [alphaCodeCarrier,card_sigma,Nat.cast_sum]
    _ ≤ ∑ _m ∈ paperPsiNaturalCarrier atom.V, ∑ f ∈ alphaGcdBank atom,
        ((3*atom.U/(f : ℝ))*(2*atom.U/(keyY atom k*f)+1))*H^4 := by
      apply sum_le_sum
      intro m hm
      exact sum_le_sum (hrow m)
    _ = ((paperPsiNaturalCarrier atom.V).card : ℝ) *
        (∑ f ∈ alphaGcdBank atom, (3*atom.U/(f : ℝ))*(2*atom.U/(keyY atom k*f)+1))*H^4 := by
      rw [← sum_mul]; simp only [sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (paperM_card_le hA) (sum_nonneg (by intro f hf; positivity))

theorem alphaGcdBank_square_tail (atom : MediumAtom) (hz : 2 ≤ roughZ atom.scale) :
    (∑ f ∈ alphaGcdBank atom, 1/(f : ℝ)^2) ≤ 2/roughZ atom.scale := by
  have hceil : 2 ≤ Nat.ceil (roughZ atom.scale) :=
    Nat.add_one_le_ceil_iff.mpr (by linarith)
  have hs : alphaGcdBank atom ⊆ Icc (Nat.ceil (roughZ atom.scale)) (Nat.floor (2*atom.U)) := by
    intro f hf
    exact mem_Icc.mpr ⟨Nat.ceil_le.mpr (mem_filter.mp hf).2.le,
      (mem_Icc.mp (mem_filter.mp hf).1).2⟩
  calc
    _ ≤ ∑ f ∈ Icc (Nat.ceil (roughZ atom.scale)) (Nat.floor (2*atom.U)), 1/(f : ℝ)^2 :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    _ ≤ 1/((Nat.ceil (roughZ atom.scale) : ℝ)-1) := ImbalancedChen.reciprocalSquare_Icc_tail_le _ hceil
    _ ≤ 1/(roughZ atom.scale-1) := div_le_div_of_nonneg_left (by norm_num)
      (by linarith) (sub_le_sub_right (Nat.le_ceil _) 1)
    _ ≤ 2/roughZ atom.scale := by
      apply (div_le_div_iff₀ (by linarith : 0 < roughZ atom.scale-1) (by linarith)).mpr
      linarith

theorem alphaGcdBank_harmonic {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) :
    (∑ f ∈ alphaGcdBank atom, 1/(f : ℝ)) ≤ 1+Real.log (2*atom.U) := by
  have hf : 1 ≤ Nat.floor (2*atom.U) := Nat.le_floor (by norm_num; linarith [hA.1])
  have hfpos : (0 : ℝ) < Nat.floor (2*atom.U) := by
    exact_mod_cast (zero_lt_one.trans_le hf)
  calc
    _ ≤ ∑ f ∈ Icc 1 (Nat.floor (2*atom.U)), 1/(f : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (harmonic (Nat.floor (2*atom.U)) : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
    _ ≤ 1+Real.log (Nat.floor (2*atom.U)) := harmonic_le_one_add_log _
    _ ≤ 1+Real.log (2*atom.U) := add_le_add_left
      (Real.log_le_log hfpos (Nat.floor_le (by linarith [hA.1]))) 1

/-- The actual n-gcd source, with BOTH reciprocal factors and the entire
endpoint retained. There is no assumed gcd error or shifted moment. -/
theorem alphaBadDeleted_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ)
    (hH : 0 ≤ H) (hz : 2 ≤ roughZ atom.scale) :
    ‖alphaBadDeleted atom z y k H T‖ ≤
      (48*actualVScale atom k/roughZ atom.scale +
        12*atom.scale*(1+Real.log (2*atom.U)))*H^6 := by
  have hU : 0 ≤ atom.U := by linarith [hA.1]
  have hM : 0 ≤ atom.V := by linarith [hA.2.1]
  have hY := keyY_positive hA k
  have hsum : (∑ f ∈ alphaGcdBank atom,
      (3*atom.U/(f : ℝ))*(2*atom.U/(keyY atom k*f)+1)) ≤
        12*atom.U^2/(keyY atom k*roughZ atom.scale)+3*atom.U*(1+Real.log (2*atom.U)) := by
    calc
      _ = (6*atom.U^2/keyY atom k)*(∑ f ∈ alphaGcdBank atom,1/(f : ℝ)^2) +
          3*atom.U*(∑ f ∈ alphaGcdBank atom,1/(f : ℝ)) := by
        rw [mul_sum,mul_sum,← sum_add_distrib]
        apply sum_congr rfl
        intro f hf
        simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
        ring
      _ ≤ (6*atom.U^2/keyY atom k)*(2/roughZ atom.scale)+
          3*atom.U*(1+Real.log (2*atom.U)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (alphaGcdBank_square_tail atom hz) (by positivity))
          (mul_le_mul_of_nonneg_left (alphaGcdBank_harmonic hA) (by positivity))
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [alphaBadDeleted_eq_active]
  calc
    _ ≤ ∑ t ∈ alphaBadActive atom z y k H T, ‖S3DeletedTerm atom z y k t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ alphaBadActive atom z y k H T,H^2 := by
      apply sum_le_sum
      intro t ht
      exact activeClose_term_le hA z y k H _ (alphaBadActive_as_activeClose ht)
    _ = ((alphaBadActive atom z y k H T).card : ℝ)*H^2 := by simp
    _ ≤ (4*atom.V*(∑ f ∈ alphaGcdBank atom,
        (3*atom.U/(f : ℝ))*(2*atom.U/(keyY atom k*f)+1))*H^4)*H^2 :=
      mul_le_mul_of_nonneg_right (alphaBadActive_card_le_sum hA z y k H T hH) (sq_nonneg H)
    _ ≤ (4*atom.V*(12*atom.U^2/(keyY atom k*roughZ atom.scale)+
        3*atom.U*(1+Real.log (2*atom.U)))*H^4)*H^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity))
          (by positivity)) (sq_nonneg H)
    _ = _ := by
      unfold actualVScale MediumAtom.scale
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end
end ImbalancedChen.Part3.OriginalS3AlphaGcdCount20261102
