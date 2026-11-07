import ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
import ImbalancedChen.Part3OriginalMediumS1SeparatedDivisorMean
import Mathlib.Tactic

/-!
# The original S2 same-d packet geometry, with the free n2 paid by 2N

For the literal H(l,D,R) defined by the preceding packet source, this file
retains phi(q*d*s) until the elementary reciprocal-totient comparison.
The two Lambda divisor envelopes contribute tau(l)^2 * tau(s). The
physical lower bounds q>=Q1 and d>=D retain 1/(Q1*D). Distinct q,d,r
with q*d*r=l inject into two divisors of l, so their multiplicity costs
tau(l)^2. The remaining s harmonic mean is the existing all-integer tau2
mean, not a pointwise x^epsilon bound.

Thus H is at most 12*N/(Q1*D) times tau(l)^4 and fixed logarithmic
factors. Together with primitive Shiu's x/l and x=M*N, this has exactly
the paper's scale V/l=M*N^2/((Q1*D)*l). The primitive Shiu application,
the summation over dyadic blocks and the collapsed smooth tail remain
separate. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2ActualBlockGeometry

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open Classical Finset
open scoped BigOperators

noncomputable section

abbrev TripleIndex := ℕ × ℕ × ℕ

def coefficientTriple (c : CoefficientIndex) : TripleIndex :=
  (c.1.1, c.1.2, c.2.1)

def coefficientPair (c : CoefficientIndex) : TripleIndex × ℕ :=
  (coefficientTriple c, c.2.2)

def actualTripleCarrier (d : MediumAtom) (z D R : ℝ) (l : ℕ) :
    Finset TripleIndex :=
  (blockCoefficientCarrier d z D R l).image coefficientTriple

def physicalCap (d : MediumAtom) : ℕ :=
  Nat.floor (8 * d.Q1 * d.Q2 * d.Q3)

def roughCap (d : MediumAtom) : ℝ := 4 * d.Q2 * d.Q3

def geometryFactor (d : MediumAtom) (D : ℝ) (l : ℕ) : ℝ :=
  (12 * d.U / (d.Q1 * D)) * tauR l ^ 4 * logBudget (physicalCap d) *
    (1 + Real.log (roughCap d)) ^ 4

theorem tauR_nonneg (n : ℕ) : 0 ≤ tauR n := by
  dsimp [tauR]
  positivity

theorem tauR_le_of_dvd {a b : ℕ} (hdiv : a ∣ b) (hb : 0 < b) :
    tauR a ≤ tauR b := by
  have hsub : a.divisors ⊆ b.divisors := by
    intro k hk
    exact Nat.mem_divisors.mpr
      ⟨dvd_trans (Nat.dvd_of_mem_divisors hk) hdiv, hb.ne'⟩
  exact_mod_cast Finset.card_le_card hsub

/-- The free n2 coordinate has its real original alpha interval support. -/
theorem freeAlphaCount_le_two_U
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k : ℕ) :
    freeAlphaCount d k ≤ 2 * d.U := by
  have hsub : d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U)) := by
    intro n hn
    have hsource := (Finset.mem_filter.mp hn).1
    have hlo := (Finset.mem_Icc.mp hsource).1
    have hhi := (Finset.mem_Icc.mp hsource).2
    have hceil : 1 ≤ Nat.ceil d.U := by
      exact_mod_cast hd.1.trans (Nat.le_ceil d.U)
    exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩
  have hfiltered : (d.alphaCarrier.filter (fun n => Nat.Coprime n k)).card ≤
      (Finset.Ioc 0 (Nat.floor (2 * d.U))).card :=
    Finset.card_le_card ((Finset.filter_subset _ _).trans hsub)
  simp only [Nat.card_Ioc, Nat.sub_zero] at hfiltered
  calc
    freeAlphaCount d k ≤ (Nat.floor (2 * d.U) : ℝ) := by
      exact_mod_cast hfiltered
    _ ≤ 2 * d.U := Nat.floor_le (by linarith [hd.1])

private theorem factorCarrier_le_two {Q : ℝ} (hQ : 0 ≤ Q)
    {n : ℕ} (hn : n ∈ factorCarrier Q) : (n : ℝ) ≤ 2 * Q := by
  exact (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by
    exact_mod_cast (Finset.mem_Icc.mp hn).2).trans
      (Nat.floor_le (by positivity))

/-- A roughFiber member comes from an actual q2,q3 pair with small*s=q2*q3.
This is stronger than the bound on s alone and pays the full right modulus. -/
theorem small_mul_rough_le_four
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (z : ℝ) (small s : ℕ) (hs : s ∈ roughFiber d z small) :
    ((small * s : ℕ) : ℝ) ≤ 4 * d.Q2 * d.Q3 := by
  have hQ2 : 1 ≤ d.Q2 := hd.2.2.2.1
  have hQ3 : 1 ≤ d.Q3 := hd.2.2.2.2.1
  obtain ⟨dw, hdw, hds⟩ := Finset.mem_image.mp hs
  obtain ⟨v, hv, hlabel⟩ :=
    Finset.mem_image.mp (Finset.mem_filter.mp hdw).1
  have hsmall := (Finset.mem_filter.mp hdw).2
  have hp : v.1 * v.2 = small * s := by
    have h := labelDW_product d z hv hQ2 hQ3
    rw [hlabel, hsmall, hds] at h
    exact h
  have h2 := factorCarrier_le_two hQ2.le (Finset.mem_product.mp hv).1
  have h3 := factorCarrier_le_two hQ3.le (Finset.mem_product.mp hv).2
  calc
    ((small * s : ℕ) : ℝ) = (v.1 : ℝ) * (v.2 : ℝ) := by
      exact_mod_cast hp.symm
    _ ≤ (2 * d.Q2) * (2 * d.Q3) :=
      mul_le_mul h2 h3 (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

theorem supported_right_modulus_le_physicalCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (z : ℝ) (c : CoefficientIndex) (hc : c ∈ coefficientCarrier d z) :
    c.1.1 * c.1.2 * c.2.2 ≤ physicalCap d := by
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hq := (Finset.mem_filter.mp (Finset.mem_product.mp hqd).1).1
  have hs := (Finset.mem_product.mp hrs).2
  have hqhi := factorCarrier_le_two (by linarith [hd.2.2.1]) hq
  have hds := small_mul_rough_le_four hd z c.1.2 c.2.2 hs
  have hreal : ((c.1.1 * c.1.2 * c.2.2 : ℕ) : ℝ) ≤
      8 * d.Q1 * d.Q2 * d.Q3 := by
    calc
      _ = (c.1.1 : ℝ) * ((c.1.2 * c.2.2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (2 * d.Q1) * (4 * d.Q2 * d.Q3) :=
        mul_le_mul hqhi hds (Nat.cast_nonneg _) (by linarith [hd.2.2.1])
      _ = _ := by ring
  exact Nat.le_floor hreal

theorem supported_s_mem_roughCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (z : ℝ) (c : CoefficientIndex) (hc : c ∈ coefficientCarrier d z) :
    c.2.2 ∈ Finset.Ioc 0 (Nat.floor (roughCap d)) := by
  have hs := (Finset.mem_product.mp (Finset.mem_sigma.mp hc).2).2
  exact Finset.mem_Ioc.mpr
    ⟨roughFiber_pos d z c.1.2 c.2.2 hs,
      Nat.le_floor (roughFiber_le_four_Q2_Q3 hd z c.1.2 c.2.2 hs)⟩

theorem one_le_roughCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ roughCap d := by
  have h2 : 1 ≤ d.Q2 := hd.2.2.2.1
  have h3 : 1 ≤ d.Q3 := hd.2.2.2.2.1
  have hp := mul_le_mul h2 h3 zero_le_one (by linarith)
  dsimp [roughCap]
  nlinarith

theorem actualTriple_product (d : MediumAtom) (z D R : ℝ) (l : ℕ)
    {t : TripleIndex} (ht : t ∈ actualTripleCarrier d z D R l) :
    t.1 * t.2.1 * t.2.2 = l := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
  exact (Finset.mem_filter.mp hc).2.2

/-- Repeated primes and shared prime powers are allowed: fixing q and d
fixes r, and q,d are both divisors of the full l. -/
theorem actualTriple_card_le_tau_square (d : MediumAtom) (z D R : ℝ)
    (l : ℕ) (hl : 0 < l) :
    ((actualTripleCarrier d z D R l).card : ℝ) ≤ tauR l ^ 2 := by
  have hcard : (actualTripleCarrier d z D R l).card ≤
      (l.divisors ×ˢ l.divisors).card := by
    apply Finset.card_le_card_of_injOn (fun t : TripleIndex => (t.1, t.2.1))
    · intro t ht
      have hp := actualTriple_product d z D R l ht
      apply Finset.mem_product.mpr
      constructor
      · exact Nat.mem_divisors.mpr ⟨⟨t.2.1 * t.2.2, by rw [← hp]; ring⟩, hl.ne'⟩
      · exact Nat.mem_divisors.mpr ⟨⟨t.1 * t.2.2, by rw [← hp]; ring⟩, hl.ne'⟩
    · intro t ht u hu heq
      have htprod := actualTriple_product d z D R l ht
      have huprod := actualTriple_product d z D R l hu
      have hq : t.1 = u.1 := congrArg Prod.fst heq
      have hd : t.2.1 = u.2.1 := congrArg Prod.snd heq
      have hqd : t.1 * t.2.1 ≠ 0 := by
        intro hz
        have hzero : l = 0 := by simpa [hz] using htprod.symm
        exact hl.ne' hzero
      have hr : t.2.2 = u.2.2 := by
        apply mul_left_cancel₀ hqd
        calc
          t.1 * t.2.1 * t.2.2 = l := htprod
          _ = u.1 * u.2.1 * u.2.2 := huprod.symm
          _ = t.1 * t.2.1 * u.2.2 := by rw [hq, hd]
      exact Prod.ext hq (Prod.ext hd hr)
  simpa only [Finset.card_product, Nat.cast_mul, tauR, pow_two] using
    (show ((actualTripleCarrier d z D R l).card : ℝ) ≤
      ((l.divisors ×ˢ l.divisors).card : ℝ) by exact_mod_cast hcard)

private theorem coefficientPair_injective : Function.Injective coefficientPair := by
  intro c c' h
  rcases c with ⟨⟨q, small⟩, r, s⟩
  rcases c' with ⟨⟨q', small'⟩, r', s'⟩
  change (((q, (small, r)), s) : TripleIndex × ℕ) =
    ((q', (small', r')), s') at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨hq, hd, hr⟩, hs⟩
  cases hq
  cases hd
  cases hr
  cases hs
  rfl

/-- The exact coefficient set injects into (actual q,d,r triples) times s.
Only the positive s support is enlarged to its real physical cap. -/
theorem sum_actual_s_weight_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (z D R : ℝ) (l : ℕ) :
    (∑ c ∈ blockCoefficientCarrier d z D R l,
      tauR c.2.2 / (c.2.2 : ℝ)) ≤
      ((actualTripleCarrier d z D R l).card : ℝ) *
        (1 + Real.log (roughCap d)) ^ 4 := by
  let C := blockCoefficientCarrier d z D R l
  let T := actualTripleCarrier d z D R l
  let S := Finset.Ioc 0 (Nat.floor (roughCap d))
  have hsub : C.image coefficientPair ⊆ T ×ˢ S := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem coefficientTriple hc,
        supported_s_mem_roughCap hd z c (Finset.mem_filter.mp hc).1⟩
  have hinj : Set.InjOn coefficientPair (C : Set CoefficientIndex) :=
    coefficientPair_injective.injOn
  calc
    _ = ∑ p ∈ C.image coefficientPair, tauR p.2 / (p.2 : ℝ) := by
      rw [Finset.sum_image hinj]
      rfl
    _ ≤ ∑ p ∈ T ×ˢ S, tauR p.2 / (p.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => div_nonneg (tauR_nonneg _) (Nat.cast_nonneg _))
    _ = (T.card : ℝ) * ∑ s ∈ S, tauR s / (s : ℝ) := by
      simp only [Finset.sum_product, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (T.card : ℝ) * (1 + Real.log (roughCap d)) ^ 4 :=
      mul_le_mul_of_nonneg_left
        (sum_tauR_div_le_log S (roughCap d) (one_le_roughCap hd)
          (by intro n hn; exact hn))
        (Nat.cast_nonneg _)

/-- The literal phi(q*d*s) denominator gives the required 1/(Q1*D*s)
before any q,d,r multiplicity is summed. The n2 count is paid by 2U. -/
theorem coefficientCost_le_physical_geometry
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (z D R : ℝ) (hD : 0 < D) (l : ℕ) (hl : 0 < l)
    (c : CoefficientIndex) (hc : c ∈ blockCoefficientCarrier d z D R l) :
    coefficientCost d c ≤
      ((12 * d.U / (d.Q1 * D)) * tauR l ^ 2 *
        logBudget (physicalCap d)) * (tauR c.2.2 / (c.2.2 : ℝ)) := by
  have hsource := (Finset.mem_filter.mp hc).1
  have hblock := (Finset.mem_filter.mp hc).2.1
  have hlit := (Finset.mem_filter.mp hc).2.2
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hsource
  have hqmem := (Finset.mem_filter.mp (Finset.mem_product.mp hqd).1).1
  have hsmall := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
  have hs := roughFiber_pos d z c.1.2 c.2.2 (Finset.mem_product.mp hrs).2
  have hq := factorCarrier_pos hd.2.2.1 hqmem
  have hphi := reciprocal_totient_le_logBudget
    (Nat.mul_pos (Nat.mul_pos hq hsmall) hs)
    (supported_right_modulus_le_physicalCap hd z c hsource)
  have hdrdiv : c.1.2 * c.2.1 ∣ l := by
    refine ⟨c.1.1, ?_⟩
    rw [← hlit]
    ring
  have hddiv : c.1.2 ∣ l := dvd_trans (dvd_mul_right _ _) hdrdiv
  have htr := tauR_le_of_dvd hdrdiv hl
  have htd := tauR_le_of_dvd hddiv hl
  have hts : tauR (c.1.2 * c.2.2) ≤ tauR l * tauR c.2.2 :=
    (tauR_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right htd (tauR_nonneg _))
  have hn := freeAlphaCount_le_two_U hd (c.1.1 * c.1.2 * c.2.2)
  have hqlo : d.Q1 ≤ (c.1.1 : ℝ) :=
    (Nat.le_ceil d.Q1).trans (by exact_mod_cast (Finset.mem_Icc.mp hqmem).1)
  have hdlo : D ≤ (c.1.2 : ℝ) := hblock.1
  have hQpos : 0 < d.Q1 := by linarith [hd.2.2.1]
  have hqdlo : d.Q1 * D ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hqlo hdlo hD.le (Nat.cast_nonneg _)
  have hi : 1 / ((c.1.1 * c.1.2 : ℕ) : ℝ) ≤ 1 / (d.Q1 * D) :=
    one_div_le_one_div_of_le (mul_pos hQpos hD) hqdlo
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
        (1 / (d.Q1 * D)) * (tauR c.2.2 / (c.2.2 : ℝ)) := by
          gcongr <;> first | exact hi | positivity
    _ = _ := by ring

/-- The second missing packet inequality, on the actual H from (F).
It has exactly N/Y with N=U and Y=Q1*D; no extra free-alpha loss is hidden. -/
theorem blockGeometryCost_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (z D R : ℝ) (hD : 0 < D) (l : ℕ) (hl : 0 < l) :
    blockGeometryCost d z D R l ≤ geometryFactor d D l := by
  let K := (12 * d.U / (d.Q1 * D)) * tauR l ^ 2 * logBudget (physicalCap d)
  have hK : 0 ≤ K := by
    dsimp [K]
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hQ : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
    have hlog := logBudget_nonneg (physicalCap d)
    positivity
  have hlogR : 0 ≤ (1 + Real.log (roughCap d)) ^ 4 := by positivity
  calc
    blockGeometryCost d z D R l ≤
      ∑ c ∈ blockCoefficientCarrier d z D R l,
        K * (tauR c.2.2 / (c.2.2 : ℝ)) := by
          apply Finset.sum_le_sum
          intro c hc
          exact coefficientCost_le_physical_geometry hd z D R hD l hl c hc
    _ = K * ∑ c ∈ blockCoefficientCarrier d z D R l,
        tauR c.2.2 / (c.2.2 : ℝ) := (Finset.mul_sum ..).symm
    _ ≤ K * (((actualTripleCarrier d z D R l).card : ℝ) *
        (1 + Real.log (roughCap d)) ^ 4) :=
          mul_le_mul_of_nonneg_left (sum_actual_s_weight_le hd z D R l) hK
    _ ≤ K * (tauR l ^ 2 * (1 + Real.log (roughCap d)) ^ 4) := by
          gcongr
          exact actualTriple_card_le_tau_square d z D R l hl
    _ = geometryFactor d D l := by dsimp [K, geometryFactor]; ring

/-- Combine the new H geometry with (F) without assuming any progression
estimate. The actual moving-residue divisor sum is still exposed. -/
theorem actualPaperBlockPacket_norm_le_geometry
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z D R : ℝ) (hD : 0 < D) (l : ℕ) (hl : 0 < l) :
    ‖actualPaperBlockPacket d x z D R l‖ ≤
      divisorProgression d l d.residue * geometryFactor d D l := by
  exact (actualPaperBlockPacket_norm_le hd x z D R l).trans
    (mul_le_mul_of_nonneg_left (blockGeometryCost_le hd z D R hD l hl)
      (divisorProgression_nonneg d l d.residue))

end
end ImbalancedChen.Part3OriginalS2ActualBlockGeometry
