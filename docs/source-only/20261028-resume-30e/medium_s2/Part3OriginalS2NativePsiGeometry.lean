import ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
import ImbalancedChen.Part3OriginalS2FixedDMixedTail
import ImbalancedChen.Part3MediumLiteralS3Stages
import Mathlib.Tactic

/-!
Geometry on the actual primitive paperPsi q support [Q1/2,5Q1/2].
All d in one dyadic window are estimated at once. The larger q support
costs the explicit factor two in the level Q1*D/2, and never loses 1/D.
Independent r/s windows may be selected by any further subset.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2NativePsiGeometry

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2LambdaDivisorPacket
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalS2MixedFamilyGeometry
open ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open Classical Finset
open scoped BigOperators

noncomputable section

def nativeQCarrier (d : MediumAtom) : Finset ℕ :=
  (paperPsiNaturalCarrier d.Q1).filter (fun q => q.Coprime d.residue.natAbs)

def nativeCoefficientCarrier (d : MediumAtom) (z : ℝ) : Finset CoefficientIndex :=
  (nativeQCarrier d ×ˢ dCarrier d z).sigma
    (fun qd => roughFiber d z qd.2 ×ˢ roughFiber d z qd.2)

def nativeKeyFamily (d : MediumAtom) (z : ℝ) (k : Key) : Finset CoefficientIndex :=
  (nativeCoefficientCarrier d z).filter (fun c =>
    c.1.2 ∈ dyadicWindow k.d ∧ c.2.1 ∈ dyadicWindow k.w ∧ c.2.2 ∈ dyadicWindow k.w)

def nativePhysicalCap (d : MediumAtom) : ℕ := Nat.floor (10 * d.Q1 * d.Q2 * d.Q3)

def nativeGeometryFactor (d : MediumAtom) (Y : ℝ) (l : ℕ) : ℝ :=
  (12 * d.U / Y) * tauR l ^ 4 * logBudget (nativePhysicalCap d) *
    (1 + Real.log (roughCap d)) ^ 4

theorem nativeQ_data {d : MediumAtom} (hQ : 0 < d.Q1) {q : ℕ}
    (hq : q ∈ nativeQCarrier d) :
    d.Q1 / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 5 * d.Q1 / 2 ∧
      q.Coprime d.residue.natAbs ∧ 0 < q := by
  obtain ⟨hq, hcop⟩ := Finset.mem_filter.mp hq
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hq
  have hloR : d.Q1 / 2 ≤ (q : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hlo)
  have hhiR : (q : ℝ) ≤ 5 * d.Q1 / 2 :=
    (show (q : ℝ) ≤ (Nat.floor (5 * d.Q1 / 2) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith))
  exact ⟨hloR, hhiR, hcop, by exact_mod_cast (lt_of_lt_of_le (by linarith : (0 : ℝ) < d.Q1 / 2) hloR)⟩

theorem native_supported_modulus_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ)
    (c : CoefficientIndex) (hc : c ∈ nativeCoefficientCarrier d z) :
    c.1.1 * c.1.2 * c.2.1 ≤ nativePhysicalCap d ∧
      c.1.1 * c.1.2 * c.2.2 ≤ nativePhysicalCap d := by
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hq := (nativeQ_data (by linarith [hd.2.2.1]) (Finset.mem_product.mp hqd).1).2.1
  have hbound (u : ℕ) (hu : u ∈ roughFiber d z c.1.2) :
      c.1.1 * c.1.2 * u ≤ nativePhysicalCap d := by
    have hdu := small_mul_rough_le_four hd z c.1.2 u hu
    apply Nat.le_floor
    calc
      ((c.1.1 * c.1.2 * u : ℕ) : ℝ) =
          (c.1.1 : ℝ) * ((c.1.2 * u : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (5 * d.Q1 / 2) * (4 * d.Q2 * d.Q3) :=
        mul_le_mul hq hdu (Nat.cast_nonneg _) (by linarith [hd.2.2.1])
      _ = _ := by ring
  exact ⟨hbound _ (Finset.mem_product.mp hrs).1,
    hbound _ (Finset.mem_product.mp hrs).2⟩

theorem nativeKey_level
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (k : Key)
    (c : CoefficientIndex) (hc : c ∈ nativeKeyFamily d z k) :
    d.Q1 * (2 : ℝ) ^ k.d / 2 ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ) := by
  obtain ⟨hsource, hwindow, _⟩ := Finset.mem_filter.mp hc
  have hqd := (Finset.mem_sigma.mp hsource).1
  have hq := (nativeQ_data (by linarith [hd.2.2.1]) (Finset.mem_product.mp hqd).1).1
  have hdlo : (2 : ℝ) ^ k.d ≤ (c.1.2 : ℝ) := by
    exact_mod_cast (Finset.mem_Ico.mp hwindow).1
  rw [Nat.cast_mul]
  have h := mul_le_mul hq hdlo (by positivity : (0 : ℝ) ≤ 2 ^ k.d)
    (Nat.cast_nonneg c.1.1)
  nlinarith

private theorem pair_injective : Function.Injective coefficientPair := by
  intro c c' h
  rcases c with ⟨⟨q, small⟩, r, s⟩
  rcases c' with ⟨⟨q', small'⟩, r', s'⟩
  change (((q, (small, r)), s) : TripleIndex × ℕ) = ((q', (small', r')), s') at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨hq, hd, hr⟩, hs⟩
  cases hq; cases hd; cases hr; cases hs
  rfl

theorem native_s_harmonic_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ)
    (S : Finset CoefficientIndex) (hS : S ⊆ nativeCoefficientCarrier d z)
    (l : ℕ) (hl : 0 < l) (hmod : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l) :
    (∑ c ∈ S, tauR c.2.2 / (c.2.2 : ℝ)) ≤
      tauR l ^ 2 * (1 + Real.log (roughCap d)) ^ 4 := by
  let T := subsetTripleCarrier S
  let U := Finset.Ioc 0 (Nat.floor (roughCap d))
  have hsub : S.image coefficientPair ⊆ T ×ˢ U := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    have hs := (Finset.mem_product.mp (Finset.mem_sigma.mp (hS hc)).2).2
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hc,
      Finset.mem_Ioc.mpr ⟨roughFiber_pos d z c.1.2 c.2.2 hs,
        Nat.le_floor (roughFiber_le_four_Q2_Q3 hd z c.1.2 c.2.2 hs)⟩⟩
  calc
    _ = ∑ p ∈ S.image coefficientPair, tauR p.2 / (p.2 : ℝ) := by
      rw [Finset.sum_image pair_injective.injOn]; rfl
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

theorem native_coefficientCost_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z Y : ℝ) (hY : 0 < Y)
    (l : ℕ) (hl : 0 < l) (c : CoefficientIndex)
    (hc : c ∈ nativeCoefficientCarrier d z) (hmod : c.1.1 * c.1.2 * c.2.1 = l)
    (hlevel : Y ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ)) :
    coefficientCost d c ≤
      ((12 * d.U / Y) * tauR l ^ 2 * logBudget (nativePhysicalCap d)) *
        (tauR c.2.2 / (c.2.2 : ℝ)) := by
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hq := (nativeQ_data (by linarith [hd.2.2.1]) (Finset.mem_product.mp hqd).1).2.2.2
  have hdpos := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
  have hs := roughFiber_pos d z c.1.2 c.2.2 (Finset.mem_product.mp hrs).2
  have hphi := reciprocal_totient_le_logBudget (Nat.mul_pos (Nat.mul_pos hq hdpos) hs)
    (native_supported_modulus_le hd z c hc).2
  have hdr : c.1.2 * c.2.1 ∣ l := by
    refine ⟨c.1.1, ?_⟩; rw [← hmod]; ring
  have hdd : c.1.2 ∣ l := dvd_trans (dvd_mul_right _ _) hdr
  have htr := tauR_le_of_dvd hdr hl
  have htd := tauR_le_of_dvd hdd hl
  have hts : tauR (c.1.2 * c.2.2) ≤ tauR l * tauR c.2.2 :=
    (tauR_mul_le _ _).trans (mul_le_mul_of_nonneg_right htd (tauR_nonneg _))
  have hn := freeAlphaCount_le_two_U hd (c.1.1 * c.1.2 * c.2.2)
  have hi : 1 / ((c.1.1 * c.1.2 : ℕ) : ℝ) ≤ 1 / Y :=
    one_div_le_one_div_of_le hY hlevel
  have hlog := logBudget_nonneg (nativePhysicalCap d)
  have htn := tauR_nonneg l
  have hsn := tauR_nonneg c.2.2
  calc
    coefficientCost d c =
      (3 * tauR (c.1.2 * c.2.1) * tauR (c.1.2 * c.2.2) *
        freeAlphaCount d (c.1.1 * c.1.2 * c.2.2)) *
        (1 / (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)) := by
          dsimp [coefficientCost, tauR]; ring
    _ ≤ (3 * tauR l * (tauR l * tauR c.2.2) * (2 * d.U)) *
        (2 * ((1 / ((c.1.1 * c.1.2 * c.2.2 : ℕ) : ℝ)) *
          logBudget (nativePhysicalCap d))) := by
          gcongr <;> first | assumption | positivity
    _ = (12 * d.U * tauR l ^ 2 * logBudget (nativePhysicalCap d)) *
        (1 / ((c.1.1 * c.1.2 : ℕ) : ℝ)) *
        (tauR c.2.2 / (c.2.2 : ℝ)) := by
          push_cast; simp only [one_div, mul_inv_rev]; ring
    _ ≤ (12 * d.U * tauR l ^ 2 * logBudget (nativePhysicalCap d)) *
        (1 / Y) * (tauR c.2.2 / (c.2.2 : ℝ)) := by
          gcongr <;> first | exact hi | positivity
    _ = _ := by ring

theorem nativeGeometry_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z Y : ℝ) (hY : 0 < Y)
    (S : Finset CoefficientIndex) (hS : S ⊆ nativeCoefficientCarrier d z)
    (l : ℕ) (hl : 0 < l) (hmod : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l)
    (hlevel : ∀ c ∈ S, Y ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ)) :
    (∑ c ∈ S, coefficientCost d c) ≤ nativeGeometryFactor d Y l := by
  let K := (12 * d.U / Y) * tauR l ^ 2 * logBudget (nativePhysicalCap d)
  have hK : 0 ≤ K := by
    dsimp [K]
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hlog := logBudget_nonneg (nativePhysicalCap d)
    positivity
  calc
    _ ≤ ∑ c ∈ S, K * (tauR c.2.2 / (c.2.2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact native_coefficientCost_le hd z Y hY l hl c (hS hc) (hmod c hc) (hlevel c hc)
    _ = K * ∑ c ∈ S, tauR c.2.2 / (c.2.2 : ℝ) := (Finset.mul_sum ..).symm
    _ ≤ K * (tauR l ^ 2 * (1 + Real.log (roughCap d)) ^ 4) :=
      mul_le_mul_of_nonneg_left (native_s_harmonic_le hd z S hS l hl hmod) hK
    _ = _ := by dsimp [K, nativeGeometryFactor]; ring

end
end ImbalancedChen.Part3OriginalS2NativePsiGeometry
