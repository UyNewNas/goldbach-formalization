import ImbalancedChen.Part3OriginalS2MixedFamilyGeometry
import ImbalancedChen.Part3OriginalS2SmoothModulusValuationBridge
import ImbalancedChen.Part3OriginalSmoothCollapsedArbitraryLog
import Mathlib.Tactic

/-!
The full same-Gevrey three-tail S2 family, including every mixed r/s bin,
is grouped by its literal left modulus. Its nonzero support is the original
smooth collapsed filter. A single coefficient estimate precedes any dyadic
partition; there is no summation of D independently supplied remainders.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2FullMixedCollapsedTail

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2SmoothModulusValuationBridge
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalS2MixedFamilyGeometry
open ImbalancedChen.Part3OriginalSmoothCollapsedHalfRankin
open ImbalancedChen.Part3OriginalSmoothCollapsedDivisorMoment
open ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuEuler20261028
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open Classical Finset
open scoped BigOperators

noncomputable section

def fullModulusCarrier (d : MediumAtom) (z : ℝ) (l : ℕ) : Finset CoefficientIndex :=
  (coefficientCarrier d z).filter (fun c => c.1.1 * c.1.2 * c.2.1 = l)

def fullModulusPacket (d : MediumAtom) (z : ℝ) (l : ℕ) : ℂ :=
  subsetPacket d z (fullModulusCarrier d z l)

def fullSamePsiTail (d : MediumAtom) (z : ℝ) : ℂ :=
  ∑ c ∈ coefficientCarrier d z, psiThreeTailInner d d.scale z c

def collapsedModuli (d : MediumAtom) (z : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor (d.scale ^ ((4 : ℝ) / 5)))).filter
    (fun l => roughY d.scale < (zSmoothPart z l : ℝ))

def wholeFamilyScale (d : MediumAtom) : ℝ := d.V * d.U ^ 2 / d.Q1

def wholeLogFactor
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (d : MediumAtom) : ℝ :=
  90 * hShiu.A * uniformEulerConstant 1 * logBudget (physicalCap d) *
    (1 + Real.log (roughCap d)) ^ 4 * Real.log (8 * d.scale)

theorem supported_left_modulus_le_physicalCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ)
    (c : CoefficientIndex) (hc : c ∈ coefficientCarrier d z) :
    c.1.1 * c.1.2 * c.2.1 ≤ physicalCap d := by
  have hs : (⟨c.1, (c.2.2, c.2.1)⟩ : CoefficientIndex) ∈ coefficientCarrier d z := by
    obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
    exact Finset.mem_sigma.mpr ⟨hqd,
      Finset.mem_product.mpr ⟨(Finset.mem_product.mp hrs).2,
        (Finset.mem_product.mp hrs).1⟩⟩
  exact supported_right_modulus_le_physicalCap hd z _ hs

theorem nonzero_psiTail_has_literal_tail (d : MediumAtom) (z : ℝ)
    (c : CoefficientIndex) (hne : psiThreeTailInner d d.scale z c ≠ 0) :
    lambdaSmoothTail d d.scale z c.1.2 c.2.1 ≠ 0 ∨
      lambdaSmoothTail d d.scale z c.1.2 c.2.2 ≠ 0 := by
  by_contra h
  simp only [not_or, not_ne_iff] at h
  exact hne (by simp [psiThreeTailInner, psiCoefficientInner,
    samePsiTerm, s2TermWithM, h.1, h.2])

/-- The original smooth filter now follows from the actual same-psi
coefficient. It is independent of the formerly hard-coded old m cutoff. -/
theorem nonzero_psiTail_modulus_mem_collapsed
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ)
    (hphysical : physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5)))
    (c : CoefficientIndex) (hc : c ∈ coefficientCarrier d z)
    (hne : psiThreeTailInner d d.scale z c ≠ 0) :
    c.1.1 * c.1.2 * c.2.1 ∈ collapsedModuli d z := by
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hq := factorCarrier_pos hd.2.2.1
    (Finset.mem_filter.mp (Finset.mem_product.mp hqd).1).1
  have hr := roughFiber_pos d z c.1.2 c.2.1 (Finset.mem_product.mp hrs).1
  have hs := roughFiber_pos d z c.1.2 c.2.2 (Finset.mem_product.mp hrs).2
  have hleft := (supported_left_modulus_le_physicalCap hd z c hc).trans hphysical
  have hright := (supported_right_modulus_le_physicalCap hd z c hc).trans hphysical
  have hy : 0 ≤ roughY d.scale := Real.rpow_nonneg (by
    dsimp [MediumAtom.scale]
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hV : 0 ≤ d.V := by linarith [hd.2.1]
    positivity) _
  rcases nonzero_psiTail_has_literal_tail d z c hne with hl | hrTail
  · exact (tail_both_moduli_in_collapsed_filter d d.scale z c.1.2 c.2.1
      c.1.1 c.2.1 c.2.2 _ hl hy hq hr hs hleft hright).1
  · exact (tail_both_moduli_in_collapsed_filter d d.scale z c.1.2 c.2.2
      c.1.1 c.2.1 c.2.2 _ hrTail hy hq hr hs hleft hright).1

theorem fullSamePsiTail_eq_collapsed_packets
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ)
    (hphysical : physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    fullSamePsiTail d z = ∑ l ∈ collapsedModuli d z, fullModulusPacket d z l := by
  unfold fullSamePsiTail fullModulusPacket subsetPacket fullModulusCarrier
  calc
    _ = ∑ c ∈ coefficientCarrier d z, ∑ l ∈ collapsedModuli d z,
        if c.1.1 * c.1.2 * c.2.1 = l then psiThreeTailInner d d.scale z c else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hz : psiThreeTailInner d d.scale z c = 0
      · simp [hz]
      · have hm := nonzero_psiTail_modulus_mem_collapsed hd z hphysical c hc hz
        simp [hm]
    _ = ∑ l ∈ collapsedModuli d z, ∑ c ∈ coefficientCarrier d z,
        if c.1.1 * c.1.2 * c.2.1 = l then psiThreeTailInner d d.scale z c else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [Finset.sum_filter]

theorem fullModulus_level_lower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (l : ℕ)
    (c : CoefficientIndex) (hc : c ∈ fullModulusCarrier d z l) :
    d.Q1 ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ) := by
  have hsource := (Finset.mem_filter.mp hc).1
  have hqd := (Finset.mem_sigma.mp hsource).1
  have hqraw := (Finset.mem_filter.mp (Finset.mem_product.mp hqd).1).1
  have hqlo : d.Q1 ≤ (c.1.1 : ℝ) :=
    (Nat.le_ceil d.Q1).trans (by exact_mod_cast (Finset.mem_Icc.mp hqraw).1)
  have hdpos := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
  have hdlo : (1 : ℝ) ≤ c.1.2 := by exact_mod_cast hdpos
  rw [Nat.cast_mul]
  calc
    d.Q1 ≤ (c.1.1 : ℝ) := hqlo
    _ = (c.1.1 : ℝ) * 1 := by ring
    _ ≤ (c.1.1 : ℝ) * (c.1.2 : ℝ) :=
      mul_le_mul_of_nonneg_left hdlo (Nat.cast_nonneg _)

theorem fullModulusPacket_return
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ d.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale)
    (hthreshold : 3 * hShiu.X0 ≤ d.scale) (z : ℝ) (l : ℕ) (hl : 0 < l)
    (hmod : l ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    ‖fullModulusPacket d z l‖ ≤
      (wholeLogFactor hShiu d * wholeFamilyScale d) *
        ((l.divisors.card : ℝ) ^ 5 / (l : ℝ)) := by
  let S := fullModulusCarrier d z l
  have hS : S ⊆ coefficientCarrier d z := Finset.filter_subset _ _
  have hmodS : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have hQ : 0 < d.Q1 := by linarith [hd.2.2.1]
  have hlevel := fullModulus_level_lower hd z l
  have hgeom : 0 ≤ subsetGeometryFactor d d.Q1 l := by
    unfold subsetGeometryFactor
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hlog := logBudget_nonneg (physicalCap d)
    positivity
  have hbudget : 0 ≤ progressionLogBudget hShiu d l := by
    unfold progressionLogBudget
    have hA := hShiu.A_pos.le
    have hE := (uniformEulerConstant_pos 1).le
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 8 * d.scale by linarith)
    positivity
  have hreturn : ‖fullModulusPacket d z l‖ ≤
      progressionLogBudget hShiu d l * subsetGeometryFactor d d.Q1 l := by
    by_cases hz : fullModulusPacket d z l = 0
    · rw [hz, norm_zero]
      exact mul_nonneg hbudget hgeom
    · have hcop := nonzero_subsetPacket_coprime hd z S hS l hmodS hz
      have hX0 : hShiu.X0 ≤ (firstWindowScale d : ℝ) := by
        have hK := (firstWindowScale_bounds d hx).1
        linarith
      have hmodR : (l : ℝ) ≤ d.scale ^ ((4 : ℝ) / 5) :=
        (show (l : ℝ) ≤ (Nat.floor (d.scale ^ ((4 : ℝ) / 5)) : ℝ) by
          exact_mod_cast hmod).trans
            (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ d.scale) _))
      exact (subsetPacket_norm_le_geometry hd z d.Q1 hQ S hS l hl hmodS hlevel).trans
        (mul_le_mul_of_nonneg_right
          (psiDivisorProgression_le_logBudget hd hx hShiu l hl hcop hX0
            (physical_modulus_shiu_margin d hx hlarge l hmodR)) hgeom)
  calc
    _ ≤ progressionLogBudget hShiu d l * subsetGeometryFactor d d.Q1 l := hreturn
    _ = _ := by
      unfold progressionLogBudget subsetGeometryFactor wholeLogFactor wholeFamilyScale
        MediumAtom.scale tauR
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- One finite bound for ALL d and independent r,s bins. The returned
normalizer is explicitly V0=M*N^2/Q1, not an individual block's V(D). -/
theorem fullSamePsiTail_le_collapsed_arithmetic
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ d.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale)
    (hthreshold : 3 * hShiu.X0 ≤ d.scale) (z : ℝ)
    (hphysical : physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    ‖fullSamePsiTail d z‖ ≤
      (wholeLogFactor hShiu d * wholeFamilyScale d) *
        collapsedSmoothTail 5 (Nat.floor (d.scale ^ ((4 : ℝ) / 5))) d.scale z := by
  rw [fullSamePsiTail_eq_collapsed_packets hd z hphysical]
  calc
    _ ≤ ∑ l ∈ collapsedModuli d z, ‖fullModulusPacket d z l‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ collapsedModuli d z,
        (wholeLogFactor hShiu d * wholeFamilyScale d) *
          ((l.divisors.card : ℝ) ^ 5 / (l : ℝ)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hli := Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1
      exact fullModulusPacket_return hd hShiu hx hlarge hthreshold z l hli.1 hli.2
    _ = _ := by
      rw [← Finset.mul_sum]
      rfl

abbrev MixedKey := ℕ × ℕ × ℕ

def mixedOwner (c : CoefficientIndex) : MixedKey :=
  (Nat.log2 c.1.2, Nat.log2 c.2.1, Nat.log2 c.2.2)

def mixedBank (d : MediumAtom) (z : ℝ) : Finset MixedKey :=
  (coefficientCarrier d z).image mixedOwner

def mixedOwnedTail (d : MediumAtom) (z : ℝ) (key : MixedKey) : ℂ :=
  ∑ c ∈ (coefficientCarrier d z).filter (fun c => mixedOwner c = key),
    psiThreeTailInner d d.scale z c

theorem fullSamePsiTail_eq_all_mixed_owners (d : MediumAtom) (z : ℝ) :
    fullSamePsiTail d z = ∑ key ∈ mixedBank d z, mixedOwnedTail d z key := by
  have hmap : ∀ c ∈ coefficientCarrier d z, mixedOwner c ∈ mixedBank d z :=
    fun c hc => Finset.mem_image_of_mem _ hc
  have h := Finset.sum_fiberwise_of_maps_to'
    (s := coefficientCarrier d z) (t := mixedBank d z) (g := mixedOwner)
    hmap (fun c => psiThreeTailInner d d.scale z c)
  exact h.symm

theorem mixedOwner_literal_windows
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ)
    (c : CoefficientIndex) (hc : c ∈ coefficientCarrier d z) :
    (2 ^ (mixedOwner c).1 ≤ c.1.2 ∧ c.1.2 < 2 ^ ((mixedOwner c).1 + 1)) ∧
    (2 ^ (mixedOwner c).2.1 ≤ c.2.1 ∧ c.2.1 < 2 ^ ((mixedOwner c).2.1 + 1)) ∧
    (2 ^ (mixedOwner c).2.2 ≤ c.2.2 ∧ c.2.2 < 2 ^ ((mixedOwner c).2.2 + 1)) := by
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hdpos := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
  have hrpos := roughFiber_pos d z c.1.2 c.2.1 (Finset.mem_product.mp hrs).1
  have hspos := roughFiber_pos d z c.1.2 c.2.2 (Finset.mem_product.mp hrs).2
  exact ⟨(Nat.log2_eq_iff hdpos.ne').mp rfl,
    (Nat.log2_eq_iff hrpos.ne').mp rfl, (Nat.log2_eq_iff hspos.ne').mp rfl⟩

end
end ImbalancedChen.Part3OriginalS2FullMixedCollapsedTail
