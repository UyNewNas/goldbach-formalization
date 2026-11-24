import ImbalancedChen.P5OriginalTaylorFiveDimensionalMidpoint
import ImbalancedChen.P5OriginalTaylorAffineBranchBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original accepted fifth cell has side length 1/grid in every physical
coordinate. The closed Taylor box and the producer's half-open owner box
are equal almost everywhere for the SAME Lebesgue volume. The signed
weighted integrand keeps its factor 4/(t1*t2*t3*t4*t5^2) inside integration.
-/
namespace ImbalancedChen.P5OriginalTaylorSameBoxGeometry
noncomputable section
open Set MeasureTheory
open scoped BigOperators Classical
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthCorrelatedRawBoxGates
open P5OriginalTaylorAffineBranchBinding P5OriginalTaylorActualSignedKernel

abbrev Point := Fin 5 → ℝ

def rawMidpoint (raw : FifthWireRow) : Point :=
  fun i => ((raw.lower i : ℝ)+(raw.upper i : ℝ))/2

def rawWidth (raw : FifthWireRow) (i : Fin 5) : ℝ :=
  (raw.upper i : ℝ)-(raw.lower i : ℝ)

def rawVolume (raw : FifthWireRow) : ℝ := ∏ i, rawWidth raw i

def rawRemainder (raw : FifthWireRow) (M : Fin 5 → ℝ) : ℝ :=
  (∑ i, (rawWidth raw i)^2*M i)/24

theorem rawClosedBox_eq_Icc (raw : FifthWireRow) :
    rawClosedBox raw = Icc (fun i => (raw.lower i : ℝ)) (fun i => (raw.upper i : ℝ)) := by
  ext t
  change (∀ i, (raw.lower i : ℝ) ≤ t i ∧ t i ≤ (raw.upper i : ℝ)) ↔ _
  simp only [mem_Icc]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩,
    fun h i => ⟨h.1 i, h.2 i⟩⟩

theorem rawWidth_eq_one_div_grid (raw : FifthWireRow) (i : Fin 5) :
    rawWidth raw i = 1/(raw.grid : ℝ) := by
  simp only [rawWidth, FifthWireRow.upper, FifthWireRow.lower,
    Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_intCast]
  ring

theorem rawWidth_pos (raw : FifthWireRow) (hg : 0 < raw.grid) (i : Fin 5) :
    0 < rawWidth raw i := by
  rw [rawWidth_eq_one_div_grid]
  exact one_div_pos.mpr (by exact_mod_cast hg)

theorem raw_lower_le_upper (raw : FifthWireRow) (hg : 0 < raw.grid) (i : Fin 5) :
    (raw.lower i : ℝ) ≤ (raw.upper i : ℝ) := by
  have h := (rawWidth_pos raw hg i).le
  exact sub_nonneg.mp h

theorem rawMidpoint_mem (raw : FifthWireRow) (hg : 0 < raw.grid) :
    rawMidpoint raw ∈ rawClosedBox raw := by
  intro i
  have h := raw_lower_le_upper raw hg i
  change (raw.lower i : ℝ) ≤ ((raw.lower i : ℝ)+(raw.upper i : ℝ))/2 ∧
    ((raw.lower i : ℝ)+(raw.upper i : ℝ))/2 ≤ (raw.upper i : ℝ)
  constructor <;> linarith

theorem update_mem_rawClosedBox (raw : FifthWireRow) (t : Point)
    (ht : t ∈ rawClosedBox raw) (i : Fin 5) (x : ℝ)
    (hx : x ∈ Icc (raw.lower i : ℝ) (raw.upper i : ℝ)) :
    Function.update t i x ∈ rawClosedBox raw := by
  intro j
  by_cases h : j = i
  · subst j
    simpa using hx
  · simpa [Function.update, h, Ne.symm h] using ht j

theorem rawVolume_eq_grid_power (raw : FifthWireRow) :
    rawVolume raw = (1/(raw.grid : ℝ))^5 := by
  simp [rawVolume, rawWidth_eq_one_div_grid]

theorem rawVolume_nonneg (raw : FifthWireRow) (hg : 0 < raw.grid) :
    0 ≤ rawVolume raw :=
  Finset.prod_nonneg (fun i _ => (rawWidth_pos raw hg i).le)

theorem rawRemainder_eq_pilot (raw : FifthWireRow) (M : Fin 5 → ℝ) :
    rawRemainder raw M = (1/(raw.grid : ℝ))^2*(∑ i, M i)/24 := by
  simp only [rawRemainder, rawWidth_eq_one_div_grid, Finset.mul_sum]

/-- Coordinate upper faces are null; this changes no integration density,
Jacobian, normalization, or owner. In particular the volume is not the
reciprocal-prime mass, which is already included in G. -/
theorem originalBox_ae_eq_rawClosedBox (raw : FifthWireRow) :
    raw.originalBox =ᵐ[volume] rawClosedBox raw := by
  have hi (i : Fin 5) :
      (Ico (raw.lower i : ℝ) (raw.upper i : ℝ) : Set ℝ) =ᵐ[volume]
        Icc (raw.lower i : ℝ) (raw.upper i : ℝ) := by
    have hu : (Iio (raw.upper i : ℝ) : Set ℝ) =ᵐ[volume]
        Iic (raw.upper i : ℝ) := Iio_ae_eq_Iic
    filter_upwards [hu] with x hx
    change ((raw.lower i : ℝ) ≤ x ∧ x < (raw.upper i : ℝ)) ↔
      ((raw.lower i : ℝ) ≤ x ∧ x ≤ (raw.upper i : ℝ))
    exact and_congr_right (fun _ => hx)
  have hp := ae_eq_set_pi (μ := fun _ : Fin 5 => (volume : Measure ℝ))
    (I := (univ : Set (Fin 5))) (fun i _ => hi i)
  have hO : raw.originalBox = univ.pi (fun i => Ico (raw.lower i : ℝ) (raw.upper i : ℝ)) := by
    ext t
    simp [FifthWireRow.originalBox]
  have hC : rawClosedBox raw = univ.pi (fun i => Icc (raw.lower i : ℝ) (raw.upper i : ℝ)) := by
    ext t
    simp [rawClosedBox]
  rw [hO, hC, volume_pi]
  exact hp

theorem originalBox_integral_eq_closed (raw : FifthWireRow) (f : Point → ℝ) :
    (∫ t in raw.originalBox, f t) = ∫ t in rawClosedBox raw, f t :=
  setIntegral_congr_set (originalBox_ae_eq_rawClosedBox raw)

/-- The exact physical volume. This is the factor multiplying the
midpoint value and diagonal remainder, once each. -/
theorem rawClosedBox_volume (raw : FifthWireRow) (hg : 0 < raw.grid) :
    (volume (rawClosedBox raw)).toReal = rawVolume raw := by
  rw [rawClosedBox_eq_Icc]
  exact Real.volume_Icc_pi_toReal (fun i => raw_lower_le_upper raw hg i)

theorem originalBox_volume (raw : FifthWireRow) (hg : 0 < raw.grid) :
    (volume raw.originalBox).toReal = (1/(raw.grid : ℝ))^5 := by
  rw [measure_congr (originalBox_ae_eq_rawClosedBox raw), rawClosedBox_volume raw hg,
    rawVolume_eq_grid_power]

end
end ImbalancedChen.P5OriginalTaylorSameBoxGeometry

