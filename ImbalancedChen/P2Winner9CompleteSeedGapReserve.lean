import ImbalancedChen.P2Winner9CompleteSeedPositiveDomains
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The genuine complete seed family admits one common inward M-R cutoff.
The lost physical density is bounded directly by its vanishing numerator,
using the existing common factor minima and actual support volumes. No
triangulation, positive volume, stored volume identity or row enclosure is
assumed. The sum counts every original row, so overlaps only enlarge this
reserve bound; this does not license summing overlapping positive savings.
-/

namespace ImbalancedChen.P2Winner9CompleteSeedGapReserve

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9CompleteSeedData
open ImbalancedChen.P2Winner9CompleteSeedPositiveDomains
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps

/-- Product of the ten actual 201-vertex lower bounds, with no new literals. -/
def factorFloor : ℝ := ∏ j : Fin 10, (minimumFactor j : ℝ)

theorem factorFloor_pos : 0 < factorFloor := by
  apply Finset.prod_pos
  intro j hj
  exact_mod_cast (original_vertex_analytic_guards.1 j).1

theorem factorFloor_le (i : RowIndex) {z : Ambient} (hz : z ∈ actualSupport i) :
    factorFloor ≤ ∏ j : Fin 10, physicalFactor j z := by
  apply Finset.prod_le_prod
  · intro j hj
    exact le_of_lt (by exact_mod_cast (original_vertex_analytic_guards.1 j).1)
  · intro j hj
    exact ((all_actual_support_positive i hz).2 j).1

theorem actual_density_nonneg (i : RowIndex) {z : Ambient}
    (hz : z ∈ actualSupport i) : 0 ≤ physicalUpperIntegrand z := by
  unfold physicalUpperIntegrand
  exact div_nonneg (mul_nonneg (by norm_num) (all_actual_support_positive i hz).1)
    (le_of_lt (lt_of_lt_of_le factorFloor_pos (factorFloor_le i hz)))

def gapCollar (i : RowIndex) (δ : ℝ) : Set Ambient :=
  actualSupport i ∩ {z | physicalGap z ≤ δ}

def retainedSupport (i : RowIndex) (δ : ℝ) : Set Ambient :=
  actualSupport i \ gapCollar i δ

theorem gapCollar_measurable (i : RowIndex) (δ : ℝ) :
    MeasurableSet (gapCollar i δ) :=
  (all_actual_support_measurable i).inter
    (isClosed_le continuous_physicalGap continuous_const).measurableSet

theorem retainedSupport_measurable (i : RowIndex) (δ : ℝ) :
    MeasurableSet (retainedSupport i δ) :=
  (all_actual_support_measurable i).diff (gapCollar_measurable i δ)

theorem mem_retainedSupport_iff (i : RowIndex) (δ : ℝ) (z : Ambient) :
    z ∈ retainedSupport i δ ↔ z ∈ actualSupport i ∧ δ < physicalGap z := by
  simp only [retainedSupport, gapCollar, mem_sdiff, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, lt_of_not_ge (fun h => hn ⟨hz, h⟩)⟩
  · rintro ⟨hz, hgap⟩
    exact ⟨hz, fun h => (not_le_of_gt hgap) h.2⟩

def fullMass (i : RowIndex) : ℝ :=
  ∫ z in actualSupport i, physicalUpperIntegrand z

def lostMass (i : RowIndex) (δ : ℝ) : ℝ :=
  ∫ z in gapCollar i δ, physicalUpperIntegrand z

def retainedMass (i : RowIndex) (δ : ℝ) : ℝ :=
  ∫ z in retainedSupport i δ, physicalUpperIntegrand z

/-- This is the real Lebesgue volume, not the archive's unproved volume field. -/
def supportVolume (i : RowIndex) : ℝ := ∫ _z in actualSupport i, (1 : ℝ)

theorem unit_integrable (i : RowIndex) :
    IntegrableOn (fun _z : Ambient => (1 : ℝ)) (actualSupport i) :=
  continuous_const.continuousOn.integrableOn_compact (all_actual_support_compact i)

theorem supportVolume_nonneg (i : RowIndex) : 0 ≤ supportVolume i :=
  integral_nonneg (fun _ => zero_le_one)

theorem lostMass_nonneg (i : RowIndex) (δ : ℝ) : 0 ≤ lostMass i δ := by
  apply setIntegral_nonneg (gapCollar_measurable i δ)
  intro z hz
  exact actual_density_nonneg i hz.1

theorem retainedMass_nonneg (i : RowIndex) (δ : ℝ) : 0 ≤ retainedMass i δ := by
  apply setIntegral_nonneg (retainedSupport_measurable i δ)
  intro z hz
  exact actual_density_nonneg i hz.1

/-- A genuine same-domain subtraction, not an asserted reserve payment. -/
theorem retainedMass_eq (i : RowIndex) (δ : ℝ) :
    retainedMass i δ = fullMass i - lostMass i δ := by
  exact setIntegral_sdiff (gapCollar_measurable i δ)
    (all_actual_density_integrable i) inter_subset_left

/-- The numerator vanishes at the actual M=R boundary. All ten original
denominators, including R-S and M-S, remain in this bound. -/
theorem collar_density_le (i : RowIndex) {δ : ℝ} (hδ : 0 ≤ δ)
    {z : Ambient} (hz : z ∈ gapCollar i δ) :
    physicalUpperIntegrand z ≤ 4 * δ / factorFloor := by
  have hp := lt_of_lt_of_le factorFloor_pos (factorFloor_le i hz.1)
  unfold physicalUpperIntegrand
  calc
    _ ≤ 4 * δ / (∏ j : Fin 10, physicalFactor j z) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz.2 (by norm_num)) hp.le
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hδ)
      factorFloor_pos (factorFloor_le i hz.1)

theorem collar_unit_le (i : RowIndex) (δ : ℝ) :
    (∫ _z in gapCollar i δ, (1 : ℝ)) ≤ supportVolume i := by
  apply setIntegral_mono_set (unit_integrable i)
  · exact Filter.Eventually.of_forall (fun _ => zero_le_one)
  · exact Filter.Eventually.of_forall (fun _ hz => hz.1)

/-- Explicit all-row loss bound; singular or zero-volume rows are harmless. -/
theorem lostMass_le (i : RowIndex) {δ : ℝ} (hδ : 0 ≤ δ) :
    lostMass i δ ≤ (4 / factorFloor) * δ * supportVolume i := by
  have hc : IntegrableOn (fun _z : Ambient => 4 * δ / factorFloor) (gapCollar i δ) :=
    (continuous_const.continuousOn.integrableOn_compact
      (all_actual_support_compact i)).mono_set inter_subset_left
  have h := setIntegral_mono_on
    ((all_actual_density_integrable i).mono_set inter_subset_left) hc
    (gapCollar_measurable i δ) (fun z hz => collar_density_le i hδ hz)
  have he : (∫ _z in gapCollar i δ, (4 * δ / factorFloor : ℝ)) =
      (4 * δ / factorFloor) * ∫ _z in gapCollar i δ, (1 : ℝ) := by
    simpa only [mul_one] using
      (integral_const_mul (4 * δ / factorFloor) (fun _z : Ambient => (1 : ℝ))
        (μ := volume.restrict (gapCollar i δ)))
  rw [he] at h
  calc
    _ ≤ (4 * δ / factorFloor) * ∫ _z in gapCollar i δ, (1 : ℝ) := h
    _ ≤ (4 * δ / factorFloor) * supportVolume i :=
      mul_le_mul_of_nonneg_left (collar_unit_le i δ)
        (div_nonneg (mul_nonneg (by norm_num) hδ) factorFloor_pos.le)
    _ = _ := by ring

def familySlope : ℝ := (4 / factorFloor) * ∑ i : RowIndex, supportVolume i

def familyLoss (δ : ℝ) : ℝ := ∑ i : RowIndex, lostMass i δ

theorem familySlope_nonneg : 0 ≤ familySlope :=
  mul_nonneg (div_nonneg (by norm_num) factorFloor_pos.le)
    (Finset.sum_nonneg (fun i _ => supportVolume_nonneg i))

theorem familyLoss_nonneg (δ : ℝ) : 0 ≤ familyLoss δ :=
  Finset.sum_nonneg (fun i _ => lostMass_nonneg i δ)

theorem lostMass_le_familyLoss (i : RowIndex) (δ : ℝ) :
    lostMass i δ ≤ familyLoss δ := by
  exact Finset.single_le_sum (fun j _ => lostMass_nonneg j δ) (Finset.mem_univ i)

/-- Counts all 11026 actual support losses. No physical disjointness is used. -/
theorem familyLoss_le {δ : ℝ} (hδ : 0 ≤ δ) : familyLoss δ ≤ familySlope * δ := by
  calc
    _ ≤ ∑ i : RowIndex, (4 / factorFloor) * δ * supportVolume i :=
      Finset.sum_le_sum (fun i _ => lostMass_le i hδ)
    _ = familySlope * δ := by
      rw [← Finset.mul_sum]
      unfold familySlope
      ring

/-- A single cutoff chosen before any arithmetic N and shared by every row. -/
def reserveCutoff (ε : ℝ) : ℝ := ε / (2 * (familySlope + 1))

theorem reserveCutoff_pos {ε : ℝ} (hε : 0 < ε) : 0 < reserveCutoff ε := by
  unfold reserveCutoff
  exact div_pos hε (mul_pos (by norm_num) (by linarith [familySlope_nonneg]))

/-- Every smaller nonnegative cutoff spends strictly less than the prescribed
allowance; no asymptotic loss premise or density-floor premise is accepted. -/
theorem common_gap_reserve {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ reserveCutoff ε) : familyLoss δ < ε := by
  have hp : 0 < familySlope + 1 := by linarith [familySlope_nonneg]
  have he : (familySlope + 1) * reserveCutoff ε = ε / 2 := by
    unfold reserveCutoff
    field_simp [ne_of_gt hp]
    <;> ring
  calc
    familyLoss δ ≤ familySlope * δ := familyLoss_le hδ
    _ ≤ (familySlope + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ
    _ ≤ (familySlope + 1) * reserveCutoff ε := mul_le_mul_of_nonneg_left hsmall hp.le
    _ = ε / 2 := he
    _ < ε := by linarith

/-- The full physical sum survives the inward crop with the same one reserve.
This is a sum of actual row integrals, not yet an integral over their union. -/
theorem complete_family_retained_mass {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ reserveCutoff ε) :
    (∑ i : RowIndex, fullMass i) - ε < ∑ i : RowIndex, retainedMass i δ := by
  simp_rw [retainedMass_eq]
  rw [Finset.sum_sub_distrib]
  have h := common_gap_reserve hε hδ hsmall
  change (∑ i : RowIndex, fullMass i) - ε <
    (∑ i : RowIndex, fullMass i) - familyLoss δ
  linarith

end

end ImbalancedChen.P2Winner9CompleteSeedGapReserve
