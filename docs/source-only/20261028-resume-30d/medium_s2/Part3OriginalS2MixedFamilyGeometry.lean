import ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
import Mathlib.Tactic

/-!
Actual coefficient subfamilies with arbitrary independent r,s bins.
Only original support, the literal left modulus and a lower bound on q*d
are used. Thus all mixed rough blocks remain inside one finite estimate.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2MixedFamilyGeometry

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open Classical Finset
open scoped BigOperators

noncomputable section

def subsetTripleCarrier (S : Finset CoefficientIndex) : Finset TripleIndex :=
  S.image coefficientTriple

def subsetPacket (d : MediumAtom) (z : ℝ) (S : Finset CoefficientIndex) : ℂ :=
  ∑ c ∈ S, psiThreeTailInner d d.scale z c

def subsetGeometryFactor (d : MediumAtom) (Y : ℝ) (l : ℕ) : ℝ :=
  (12 * d.U / Y) * tauR l ^ 4 * logBudget (physicalCap d) *
    (1 + Real.log (roughCap d)) ^ 4

theorem subsetTriple_card_le (S : Finset CoefficientIndex) (l : ℕ) (hl : 0 < l)
    (hmod : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l) :
    ((subsetTripleCarrier S).card : ℝ) ≤ tauR l ^ 2 := by
  have hprod : ∀ t ∈ subsetTripleCarrier S, t.1 * t.2.1 * t.2.2 = l := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
    exact hmod c hc
  have hcard : (subsetTripleCarrier S).card ≤ (l.divisors ×ˢ l.divisors).card := by
    apply Finset.card_le_card_of_injOn (fun t : TripleIndex => (t.1, t.2.1))
    · intro t ht
      have hp := hprod t ht
      apply Finset.mem_product.mpr
      constructor
      · exact Nat.mem_divisors.mpr ⟨⟨t.2.1 * t.2.2, by rw [← hp]; ring⟩, hl.ne'⟩
      · exact Nat.mem_divisors.mpr ⟨⟨t.1 * t.2.2, by rw [← hp]; ring⟩, hl.ne'⟩
    · intro t ht u hu heq
      have hq : t.1 = u.1 := congrArg Prod.fst heq
      have hd : t.2.1 = u.2.1 := congrArg Prod.snd heq
      have hqd : t.1 * t.2.1 ≠ 0 := by
        intro hz
        exact hl.ne' (by simpa [hz] using (hprod t ht).symm)
      have hr : t.2.2 = u.2.2 := by
        apply mul_left_cancel₀ hqd
        calc
          t.1 * t.2.1 * t.2.2 = l := hprod t ht
          _ = u.1 * u.2.1 * u.2.2 := (hprod u hu).symm
          _ = t.1 * t.2.1 * u.2.2 := by rw [hq, hd]
      exact Prod.ext hq (Prod.ext hd hr)
  simpa only [Finset.card_product, Nat.cast_mul, tauR, pow_two] using
    (show ((subsetTripleCarrier S).card : ℝ) ≤
      ((l.divisors ×ˢ l.divisors).card : ℝ) by exact_mod_cast hcard)

private theorem pair_injective : Function.Injective coefficientPair := by
  intro c c' h
  rcases c with ⟨⟨q, small⟩, r, s⟩
  rcases c' with ⟨⟨q', small'⟩, r', s'⟩
  change (((q, (small, r)), s) : TripleIndex × ℕ) = ((q', (small', r')), s') at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨hq, hd, hr⟩, hs⟩
  cases hq
  cases hd
  cases hr
  cases hs
  rfl

theorem subset_s_harmonic_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ)
    (S : Finset CoefficientIndex) (hS : S ⊆ coefficientCarrier d z)
    (l : ℕ) (hl : 0 < l) (hmod : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l) :
    (∑ c ∈ S, tauR c.2.2 / (c.2.2 : ℝ)) ≤
      tauR l ^ 2 * (1 + Real.log (roughCap d)) ^ 4 := by
  let T := subsetTripleCarrier S
  let U := Finset.Ioc 0 (Nat.floor (roughCap d))
  have hsub : S.image coefficientPair ⊆ T ×ˢ U := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hc, supported_s_mem_roughCap hd z c (hS hc)⟩
  calc
    _ = ∑ p ∈ S.image coefficientPair, tauR p.2 / (p.2 : ℝ) := by
      rw [Finset.sum_image pair_injective.injOn]
      rfl
    _ ≤ ∑ p ∈ T ×ˢ U, tauR p.2 / (p.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => div_nonneg (tauR_nonneg _) (Nat.cast_nonneg _))
    _ = (T.card : ℝ) * ∑ s ∈ U, tauR s / (s : ℝ) := by
      simp only [Finset.sum_product, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (T.card : ℝ) * (1 + Real.log (roughCap d)) ^ 4 :=
      mul_le_mul_of_nonneg_left
        (sum_tauR_div_le_log U (roughCap d) (one_le_roughCap hd)
          (by intro n hn; exact hn)) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (subsetTriple_card_le S l hl hmod) (by positivity)

theorem coefficientCost_le_subset_geometry
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z Y : ℝ) (hY : 0 < Y)
    (l : ℕ) (hl : 0 < l) (c : CoefficientIndex)
    (hc : c ∈ coefficientCarrier d z) (hmod : c.1.1 * c.1.2 * c.2.1 = l)
    (hlevel : Y ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ)) :
    coefficientCost d c ≤
      ((12 * d.U / Y) * tauR l ^ 2 * logBudget (physicalCap d)) *
        (tauR c.2.2 / (c.2.2 : ℝ)) := by
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hqmem := (Finset.mem_filter.mp (Finset.mem_product.mp hqd).1).1
  have hq := factorCarrier_pos hd.2.2.1 hqmem
  have hdpos := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
  have hs := roughFiber_pos d z c.1.2 c.2.2 (Finset.mem_product.mp hrs).2
  have hphi := reciprocal_totient_le_logBudget
    (Nat.mul_pos (Nat.mul_pos hq hdpos) hs)
    (supported_right_modulus_le_physicalCap hd z c hc)
  have hdr : c.1.2 * c.2.1 ∣ l := by
    refine ⟨c.1.1, ?_⟩
    rw [← hmod]
    ring
  have hdd : c.1.2 ∣ l := dvd_trans (dvd_mul_right _ _) hdr
  have htr := tauR_le_of_dvd hdr hl
  have htd := tauR_le_of_dvd hdd hl
  have hts : tauR (c.1.2 * c.2.2) ≤ tauR l * tauR c.2.2 :=
    (tauR_mul_le _ _).trans (mul_le_mul_of_nonneg_right htd (tauR_nonneg _))
  have hn := freeAlphaCount_le_two_U hd (c.1.1 * c.1.2 * c.2.2)
  have hi : 1 / ((c.1.1 * c.1.2 : ℕ) : ℝ) ≤ 1 / Y :=
    one_div_le_one_div_of_le hY hlevel
  have hlog := logBudget_nonneg (physicalCap d)
  have htn := tauR_nonneg l
  have hsn := tauR_nonneg c.2.2
  calc
    coefficientCost d c =
      (3 * tauR (c.1.2 * c.2.1) * tauR (c.1.2 * c.2.2) *
        freeAlphaCount d (c.1.1 * c.1.2 * c.2.2)) *
        (1 / (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)) := by
          dsimp [coefficientCost, tauR]
          ring
    _ ≤ (3 * tauR l * (tauR l * tauR c.2.2) * (2 * d.U)) *
        (2 * ((1 / ((c.1.1 * c.1.2 * c.2.2 : ℕ) : ℝ)) *
          logBudget (physicalCap d))) := by
          gcongr <;> first | assumption | positivity
    _ = (12 * d.U * tauR l ^ 2 * logBudget (physicalCap d)) *
        (1 / ((c.1.1 * c.1.2 : ℕ) : ℝ)) *
        (tauR c.2.2 / (c.2.2 : ℝ)) := by
          push_cast
          simp only [one_div, mul_inv_rev]
          ring
    _ ≤ (12 * d.U * tauR l ^ 2 * logBudget (physicalCap d)) *
        (1 / Y) * (tauR c.2.2 / (c.2.2 : ℝ)) := by
          gcongr <;> first | exact hi | positivity
    _ = _ := by ring

theorem subsetGeometry_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z Y : ℝ) (hY : 0 < Y)
    (S : Finset CoefficientIndex) (hS : S ⊆ coefficientCarrier d z)
    (l : ℕ) (hl : 0 < l) (hmod : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l)
    (hlevel : ∀ c ∈ S, Y ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ)) :
    (∑ c ∈ S, coefficientCost d c) ≤ subsetGeometryFactor d Y l := by
  let K := (12 * d.U / Y) * tauR l ^ 2 * logBudget (physicalCap d)
  have hK : 0 ≤ K := by
    dsimp [K]
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hlog := logBudget_nonneg (physicalCap d)
    positivity
  calc
    _ ≤ ∑ c ∈ S, K * (tauR c.2.2 / (c.2.2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact coefficientCost_le_subset_geometry hd z Y hY l hl c (hS hc)
        (hmod c hc) (hlevel c hc)
    _ = K * ∑ c ∈ S, tauR c.2.2 / (c.2.2 : ℝ) := (Finset.mul_sum ..).symm
    _ ≤ K * (tauR l ^ 2 * (1 + Real.log (roughCap d)) ^ 4) :=
      mul_le_mul_of_nonneg_left (subset_s_harmonic_le hd z S hS l hl hmod) hK
    _ = _ := by dsimp [K, subsetGeometryFactor]; ring

theorem nonzero_subsetPacket_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ)
    (S : Finset CoefficientIndex) (hS : S ⊆ coefficientCarrier d z)
    (l : ℕ) (hmod : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l)
    (hne : subsetPacket d z S ≠ 0) : Nat.Coprime l d.residue.natAbs := by
  have hwit : ∃ c ∈ S, psiThreeTailInner d d.scale z c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Finset.sum_eq_zero (fun c hc => h c hc))
  obtain ⟨c, hc, hterm⟩ := hwit
  have hq := (Finset.mem_product.mp (Finset.mem_sigma.mp (hS hc)).1).1
  have hqc := (Finset.mem_filter.mp hq).2
  have hleft : lambdaSmoothTail d d.scale z c.1.2 c.2.1 ≠ 0 ∨
      lambdaSmoothKept d d.scale z c.1.2 c.2.1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    exact hterm (by simp [psiThreeTailInner, psiCoefficientInner,
      samePsiTerm, s2TermWithM, h.1, h.2])
  have hdc : Nat.Coprime (c.1.2 * c.2.1) d.residue.natAbs := by
    rcases hleft with ht | hk
    · exact nonzero_smoothTail_coprime hd d.scale z c.1.2 c.2.1 ht
    · exact nonzero_smoothKept_coprime hd d.scale z c.1.2 c.2.1 hk
  simpa only [← Nat.mul_assoc, hmod c hc] using
    (Nat.coprime_mul_iff_left.mpr ⟨hqc, hdc⟩)

theorem subsetPacket_norm_le_geometry
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z Y : ℝ) (hY : 0 < Y)
    (S : Finset CoefficientIndex) (hS : S ⊆ coefficientCarrier d z)
    (l : ℕ) (hl : 0 < l) (hmod : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l)
    (hlevel : ∀ c ∈ S, Y ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ)) :
    ‖subsetPacket d z S‖ ≤ psiDivisorProgression d l * subsetGeometryFactor d Y l := by
  have hT : 0 ≤ psiDivisorProgression d l := by
    unfold psiDivisorProgression
    apply Finset.sum_nonneg
    intro v hv
    split_ifs <;> positivity
  calc
    _ ≤ ∑ c ∈ S, ‖psiThreeTailInner d d.scale z c‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ S, coefficientCost d c * psiDivisorProgression d l := by
      apply Finset.sum_le_sum
      intro c hc
      simpa only [hmod c hc] using psiThreeTailInner_norm_le hd d.scale z c (hS hc)
    _ = psiDivisorProgression d l * ∑ c ∈ S, coefficientCost d c := by
      rw [← Finset.sum_mul]
      exact mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (subsetGeometry_le hd z Y hY S hS l hl hmod hlevel) hT

end
end ImbalancedChen.Part3OriginalS2MixedFamilyGeometry
