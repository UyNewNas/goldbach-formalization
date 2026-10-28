import ImbalancedChen.Part3OriginalSingleZeroPolynomialTau
import Mathlib.Tactic

/-! Actual-source counting, before the following uniform subpower
instantiation. The first-zero labels inject into original q,d,r,
positive factor pairs of a, and the existing nonzero-shift fibre.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalActualSingleZeroCounting

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalActualSingleZeroSource
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3.MediumSingleZeroFiber20261028
open ImbalancedChen.Part3.MediumNativePrincipalSource20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumLiteralS3Deleted20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open Classical Finset
open scoped BigOperators

noncomputable section

def singleZeroY (d : MediumAtom) (k : Key) : ℝ := d.Q1 * (2 : ℝ) ^ k.d
def singleZeroR (k : Key) : ℝ := (2 : ℝ) ^ k.w

abbrev FirstCode := Σ _ : (ℕ × ℕ) × ℕ, Σ _ : ℕ × ℕ, ℕ × ℕ

def firstCode (t : PairIndex) : FirstCode :=
  ⟨((t.1.1, t.1.2.1), t.2.1.1), ⟨(t.1.2.2, t.2.1.2), (t.2.2.2, t.2.2.1)⟩⟩

def firstDecode (c : FirstCode) : PairIndex :=
  ((c.1.1.1, c.1.1.2, c.2.1.1), (c.1.2, c.2.1.2), (c.2.2.2, c.2.2.1))

def firstCodeCarrier (d : MediumAtom) (k : Key) : Finset FirstCode :=
  (nativeQD d k ×ˢ dyadicWindow k.w).sigma (fun p =>
    (firstProductPairs (paperPsiNaturalCarrier d.V) d.alphaCarrier d.residue.natAbs).sigma
      (fun mn => firstZeroFiber (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1)
        mn.1 mn.2 p.1.1 p.1.2 d.residue.natAbs (dyadicWindow k.w)))

theorem firstCode_injective : Function.Injective firstCode := by
  intro t u heq
  exact congrArg firstDecode heq

theorem firstActive_card_le_code
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) :
    (firstActive d z y k).card ≤ (firstCodeCarrier d k).card := by
  apply Finset.card_le_card_of_injOn firstCode
  · intro t ht
    have hdata := firstActive_data hd z y k t ht
    have hqd := firstActive_qd_mem_nativeQD hd z y k t ht
    have hpair := hdata.1
    have ho := (Finset.mem_filter.mp (Finset.mem_product.mp hpair).1).1
    have hm := (Finset.mem_product.mp (Finset.mem_product.mp ho).2).2
    have hi := (Finset.mem_product.mp (Finset.mem_product.mp hpair).2).1
    have hr := (Finset.mem_product.mp hi).1
    have hn := (Finset.mem_product.mp hi).2
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_product.mpr ⟨hqd, hr⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm, hn⟩,
        by simpa only [oldIndex, Nat.mul_comm] using hdata.2.2.2.1⟩
    · exact firstActive_mem_existing_fibre hd z y k t ht
  · exact fun t ht u hu heq => firstCode_injective heq

theorem dyadicWindow_card (j : ℕ) : (dyadicWindow j).card = 2 ^ j := by
  simp [dyadicWindow, Nat.card_Ico, pow_succ, Nat.mul_two]

theorem nativeQD_positive_level
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k : Key) (p : ℕ × ℕ)
    (hp : p ∈ nativeQD d k) :
    0 < p.1 * p.2 ∧ singleZeroY d k / 2 ≤ ((p.1 * p.2 : ℕ) : ℝ) ∧
      (p.1 * p.2).Coprime d.residue.natAbs := by
  obtain ⟨hq, hsmall⟩ := Finset.mem_product.mp hp
  have hqdata := nativeQ_data (by linarith [hd.2.2.1]) hq
  obtain ⟨hwin, hdc⟩ := Finset.mem_filter.mp hsmall
  have hdlo : (2 : ℝ) ^ k.d ≤ (p.2 : ℝ) := by
    exact_mod_cast (Finset.mem_Ico.mp hwin).1
  have hdpos : 0 < p.2 :=
    (pow_pos (by norm_num : (0 : ℕ) < 2) k.d).trans_le (Finset.mem_Ico.mp hwin).1
  refine ⟨Nat.mul_pos hqdata.2.2.2 hdpos, ?_,
    Nat.coprime_mul_iff_left.mpr ⟨hqdata.2.2.1, hdc⟩⟩
  have hh := mul_le_mul hqdata.1 hdlo (by positivity : (0 : ℝ) ≤ 2 ^ k.d)
    (Nat.cast_nonneg p.1)
  dsimp [singleZeroY]
  push_cast
  nlinarith

theorem actual_progression_occupancy_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k : Key) (p : ℕ × ℕ)
    (hp : p ∈ nativeQD d k) :
    (((Nat.floor (2 * d.U) + 1) / (p.1 * p.2) + 1 : ℕ) : ℝ) ≤
      6 * d.U / singleZeroY d k + 1 := by
  obtain ⟨hell, hlevel, hcop⟩ := nativeQD_positive_level hd k p hp
  have hY : 0 < singleZeroY d k := by
    unfold singleZeroY
    have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
    positivity
  have hUcap : ((Nat.floor (2 * d.U) + 1 : ℕ) : ℝ) ≤ 3 * d.U := by
    push_cast
    have hfloor := Nat.floor_le (show (0 : ℝ) ≤ 2 * d.U by linarith [hd.1])
    linarith [hd.1]
  have hmul : ((((Nat.floor (2 * d.U) + 1) / (p.1 * p.2) : ℕ) : ℝ)) *
      ((p.1 * p.2 : ℕ) : ℝ) ≤ ((Nat.floor (2 * d.U) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (Nat.floor (2 * d.U) + 1) (p.1 * p.2)
  have hh := mul_le_mul_of_nonneg_left hlevel
    (Nat.cast_nonneg ((Nat.floor (2 * d.U) + 1) / (p.1 * p.2)))
  have hquot : ((((Nat.floor (2 * d.U) + 1) / (p.1 * p.2) : ℕ) : ℝ)) ≤
      6 * d.U / singleZeroY d k := by
    apply (le_div_iff₀ hY).mpr
    nlinarith
  push_cast
  linarith

theorem nativeQ_card_le_four_Q
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ((nativeQCarrier d).card : ℝ) ≤ 4 * d.Q1 := by
  have hsub : nativeQCarrier d ⊆ Finset.Icc 0 (Nat.floor (5 * d.Q1 / 2)) := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2⟩
  have hc := Finset.card_le_card hsub
  have hcR : ((nativeQCarrier d).card : ℝ) ≤ Nat.floor (5 * d.Q1 / 2) + 1 := by
    exact_mod_cast (by simpa only [Nat.card_Icc, Nat.sub_zero] using hc)
  have hf := Nat.floor_le (show (0 : ℝ) ≤ 5 * d.Q1 / 2 by linarith [hd.2.2.1])
  linarith [hd.2.2.1]

/-- This intermediate estimate is on the genuine actual first-zero
source. The next source instantiates H by a proved classical subpower
bound; this pointwise integer H is not an assumed restoration estimate. -/
theorem actual_first_zero_card_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (H : ℕ) (ha : 0 < d.residue.natAbs)
    (hA : d.residue.natAbs.divisors.card ≤ H)
    (hshift : ∀ m ∈ paperPsiNaturalCarrier d.V,
      ∀ n ∈ Finset.Ico (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1),
        (otherShiftAbs m n d.residue.natAbs).divisors.card ≤ H) :
    ((firstActive d z y k).card : ℝ) ≤
      24 * singleZeroR k * (d.U + singleZeroY d k) * (H : ℝ) ^ 2 := by
  let P := firstProductPairs (paperPsiNaturalCarrier d.V) d.alphaCarrier d.residue.natAbs
  let O := nativeQD d k ×ˢ dyadicWindow k.w
  let Occ := 6 * d.U / singleZeroY d k + 1
  have hY : 0 < singleZeroY d k := by
    unfold singleZeroY
    have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
    positivity
  have hrow (p : (ℕ × ℕ) × ℕ) (hp : p ∈ O) (mn : ℕ × ℕ) (hmn : mn ∈ P) :
      ((firstZeroFiber (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1)
        mn.1 mn.2 p.1.1 p.1.2 d.residue.natAbs (dyadicWindow k.w)).card : ℝ) ≤
        Occ * H := by
    obtain ⟨hcarrier, hprod⟩ := Finset.mem_filter.mp hmn
    have hm := (Finset.mem_product.mp hcarrier).1
    have hbase := nativeQD_positive_level hd k p.1 (Finset.mem_product.mp hp).1
    have hmpos : 0 < mn.1 := by
      by_contra hz
      have hz' : mn.1 = 0 := Nat.eq_zero_of_not_pos hz
      simp [hz'] at hprod
      omega
    have hmdiv : mn.1 ∣ d.residue.natAbs := ⟨mn.2, hprod.symm⟩
    have hmCop : mn.1.Coprime (p.1.1 * p.1.2) :=
      (Nat.Coprime.of_dvd_right hmdiv hbase.2.2).symm
    have henv : secondDivisorEnvelope (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1)
        mn.1 mn.2 p.1.1 p.1.2 d.residue.natAbs ≤ H := by
      apply Finset.sup_le
      intro n hn
      exact hshift mn.1 hm n (Finset.mem_filter.mp hn).1
    have hc := firstZeroFiber_card_le_progression_times_divisors
      (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1) mn.1 mn.2 p.1.1 p.1.2
      d.residue.natAbs (dyadicWindow k.w) hmpos hprod hmCop hbase.1
    calc
      _ ≤ ((((Nat.floor (2 * d.U) + 1) / (p.1.1 * p.1.2) + 1) *
          secondDivisorEnvelope (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1)
            mn.1 mn.2 p.1.1 p.1.2 d.residue.natAbs : ℕ) : ℝ) := by exact_mod_cast hc
      _ ≤ Occ * H := by
        push_cast
        exact mul_le_mul (actual_progression_occupancy_le hd k p.1 (Finset.mem_product.mp hp).1)
          (by exact_mod_cast henv) (Nat.cast_nonneg _) (by dsimp [Occ]; positivity)
  have hP : (P.card : ℝ) ≤ H := by
    exact_mod_cast (firstProductPairs_card_le_divisors _ _ _ ha).trans hA
  have hO : (O.card : ℝ) ≤ 4 * singleZeroY d k * singleZeroR k := by
    have hdsub : activeD d k ⊆ dyadicWindow k.d := Finset.filter_subset _ _
    have hD : ((activeD d k).card : ℝ) ≤ (2 : ℝ) ^ k.d := by
      exact_mod_cast (Finset.card_le_card hdsub).trans_eq (dyadicWindow_card k.d)
    dsimp [O]
    rw [Finset.card_product, Nat.cast_mul]
    change ((nativeQCarrier d ×ˢ activeD d k).card : ℝ) * _ ≤ _
    rw [Finset.card_product, Nat.cast_mul, dyadicWindow_card]
    push_cast
    simpa only [singleZeroY, singleZeroR, mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul (nativeQ_card_le_four_Q hd) hD (Nat.cast_nonneg _)
        (by linarith [hd.2.2.1] : 0 ≤ 4 * d.Q1)) (by positivity)
  calc
    _ ≤ ((firstCodeCarrier d k).card : ℝ) := by exact_mod_cast firstActive_card_le_code hd z y k
    _ = ∑ p ∈ O, ∑ mn ∈ P,
        ((firstZeroFiber (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1)
          mn.1 mn.2 p.1.1 p.1.2 d.residue.natAbs (dyadicWindow k.w)).card : ℝ) := by
      simp only [firstCodeCarrier, Finset.card_sigma, Nat.cast_sum]
    _ ≤ ∑ p ∈ O, ∑ mn ∈ P, Occ * H :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun mn hmn => hrow p hp mn hmn))
    _ = (O.card : ℝ) * (P.card : ℝ) * Occ * H := by simp; ring
    _ ≤ (4 * singleZeroY d k * singleZeroR k) * H * Occ * H := by
      gcongr <;> first | exact hO | exact hP | positivity
    _ ≤ _ := by
      dsimp [Occ]
      field_simp [hY.ne']
      nlinarith [show (0 : ℝ) ≤ singleZeroR k * (H : ℝ) ^ 2 by positivity]

end
end ImbalancedChen.Part3OriginalActualSingleZeroCounting
