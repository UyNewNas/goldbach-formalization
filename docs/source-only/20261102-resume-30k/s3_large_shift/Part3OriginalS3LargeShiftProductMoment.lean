import ImbalancedChen.Part3OriginalS3LargeShiftLocalization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Collapse the genuine smooth-m/alpha pairs into v=mn.  The actual support
is 1 <= v <= floor(5*x), and v=a is deleted BEFORE any tau evaluation.
The ordered factor-pair multiplicity is tau(v); it is not a subpower
supremum.  The following module pays this fixed mixed moment.
-/
namespace ImbalancedChen.Part3.OriginalS3LargeShiftProductMoment20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3LargeShiftLocalization20261102 OriginalS3ClosePairResidual20261102
open MediumActualDiagonalDivisorPayment20261028 MediumGlobalDyadicOwnership20261028
open OriginalMediumS1SeparatedDivisorMean OriginalGevreyPoissonPacket20261028
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def productSource (atom : MediumAtom) : Finset ℕ :=
  (Icc 1 (Nat.floor (5 * atom.scale))).filter (fun v => (v : ℤ) ≠ atom.residue)

def productShift (atom : MediumAtom) (v : ℕ) : ℕ := ((v : ℤ) - atom.residue).natAbs

def collapsedSeventhMoment (atom : MediumAtom) : ℝ :=
  ∑ v ∈ productSource atom, tauR v * tauR (productShift atom v) ^ 7

abbrev ProductCode := Σ _v : ℕ, ℕ
def productCode (p : ℕ × ℕ) : ProductCode := ⟨p.1 * p.2, p.1⟩
def productDecode (v : ProductCode) : ℕ × ℕ := (v.2, v.1 / v.2)

def productCodeCarrier (atom : MediumAtom) : Finset ProductCode :=
  (productSource atom).sigma (fun v => v.divisors)

theorem actualMN_positive {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) {p : ℕ × ℕ} (hp : p ∈ actualMN atom) :
    0 < p.1 ∧ 0 < p.2 := by
  obtain ⟨hm, hn⟩ := mem_product.mp hp
  have hmlo := (mem_Icc.mp hm).1
  have hnlo := (mem_Icc.mp (mem_filter.mp hn).1).1
  have hmpos : 0 < Nat.ceil (atom.V / 2) := Nat.ceil_pos.mpr (by linarith [hA.2.1])
  have hnpos : 0 < Nat.ceil atom.U := Nat.ceil_pos.mpr (by linarith [hA.1])
  exact ⟨hmpos.trans_le hmlo, hnpos.trans_le hnlo⟩

theorem productDecode_code {p : ℕ × ℕ} (hm : 0 < p.1) :
    productDecode (productCode p) = p := by
  rcases p with ⟨m, n⟩
  simp only [productDecode, productCode, Nat.mul_div_cancel_left _ hm]

/-- Signed product translation, retaining the exact five-x smooth cap.
No shift absolute-value map is used for the product reindexing. -/
theorem nonzeroPairs_maps_to_productCode {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) {p : ℕ × ℕ} (hp : p ∈ nonzeroPairs atom) :
    productCode p ∈ productCodeCarrier atom := by
  obtain ⟨hp, hshift⟩ := mem_filter.mp hp
  obtain ⟨hm, hn⟩ := actualMN_positive hA hp
  obtain ⟨hmR, hnR⟩ := actualMN_real_bounds hA hp
  have hprod : (p.1 * p.2 : ℕ) ≤ Nat.floor (5 * atom.scale) := by
    apply Nat.le_floor
    push_cast
    calc
      _ ≤ (5 * atom.V / 2) * (2 * atom.U) :=
        mul_le_mul hmR hnR (Nat.cast_nonneg _) (by linarith [hA.2.1])
      _ = _ := by unfold MediumAtom.scale; ring
  have hvne : ((p.1 * p.2 : ℕ) : ℤ) ≠ atom.residue := by
    intro he
    apply hshift
    simp only [shiftAbs, Nat.mul_comm p.2 p.1, he, sub_self, Int.natAbs_zero]
  exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hm hn, hprod⟩, hvne⟩,
    Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, (Nat.mul_pos hm hn).ne'⟩⟩

theorem productCode_injOn_nonzeroPairs {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) : Set.InjOn productCode (nonzeroPairs atom) := by
  intro p hp q hq he
  have hm := (actualMN_positive hA (mem_filter.mp hp).1).1
  have hm' := (actualMN_positive hA (mem_filter.mp hq).1).1
  have hh := congrArg productDecode he
  simpa only [productDecode_code hm, productDecode_code hm'] using hh

/-- The exact order-seven source is paid by the independently defined
mixed product moment. This is a proved injection with its multiplicity,
not an assumed source-moment relation. -/
theorem shiftedSeventhMoment_le_collapsed {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) :
    shiftedSeventhMoment atom ≤ collapsedSeventhMoment atom := by
  have hinj := productCode_injOn_nonzeroPairs hA
  have hsub : (nonzeroPairs atom).image productCode ⊆ productCodeCarrier atom := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    exact nonzeroPairs_maps_to_productCode hA hp
  calc
    _ = ∑ v ∈ (nonzeroPairs atom).image productCode, tauR (productShift atom v.1) ^ 7 := by
      rw [sum_image hinj]
      simp only [shiftedSeventhMoment, productCode, productShift, shiftAbs, Nat.mul_comm]
    _ ≤ ∑ v ∈ productCodeCarrier atom, tauR (productShift atom v.1) ^ 7 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by dsimp [tauR]; positivity)
    _ = collapsedSeventhMoment atom := by
      simp only [productCodeCarrier, sum_sigma, sum_const, nsmul_eq_mul,
        collapsedSeventhMoment, tauR]

end
end ImbalancedChen.Part3.OriginalS3LargeShiftProductMoment20261102
