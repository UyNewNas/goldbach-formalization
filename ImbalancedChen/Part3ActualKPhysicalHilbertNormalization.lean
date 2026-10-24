import ImbalancedChen.Part3ActualFullPacketRawHeightEnergy
import ImbalancedChen.Part3EvenFourierHilbert
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / CODE_ONLY, 2026-10-24.

This records the normalization of the *actual full physical packet* in the
ordinary Euclidean Fourier Hilbert space. The packet dependency comes through
`physicalEvenProfile`, whose q-amplitude is the original finite packet and
whose support is the physical interval `[Y0/16,16Y0]`. All identities below
use raw Lebesgue height. They assert no KL, Kuznetsov, or automorphic
Plancherel theorem.

For Mathlib's phase `exp(-2*pi*i*u*xi)`, the K order `2*t` gives `xi=t/pi`.
If angular frequency is called `omega=2*t`, this is `xi=omega/(2*pi)`.
The even full-line profile produces an amplitude factor `1/2` and its L2
mass is twice the positive-half-line mass. Thus the full `dt` energy has
factor `pi/4` against the full profile and `pi/2` against its positive half.
-/

namespace ImbalancedChen.Part3.ActualKPhysicalHilbertNormalization20261024zz

noncomputable section

open Set MeasureTheory FourierTransform
open scoped FourierTransform
open P3ActualLiteralPacketIntegralSourceOnly
open ActualFullPacketFourierBridgeSourceOnly
open ActualFullPacketRawHeightEnergySourceOnly
open ActualKTransformFourier20261024z
open EvenFourierHilbertSourceOnly
open FourierL1L2PlancherelSourceOnly

variable {ι : Type*}

/-- The actual packet profile as a class in the closed even subspace of L2. -/
def physicalEvenHilbert (P : PacketData ι) : evenL2 :=
  ⟨(physicalEvenProfile_memLp_two P).toLp (physicalEvenProfile P),
    toLp_mem_evenL2 (physicalEvenProfile_memLp_two P)
      (physicalEvenProfile_even P)⟩

/-- The Hilbert norm uses the full-line spatial measure, with no hidden
half-line factor. -/
theorem physicalEvenHilbert_norm_sq (P : PacketData ι) :
    ‖physicalEvenHilbert P‖ ^ 2 =
      ∫ u : ℝ, ‖physicalEvenProfile P u‖ ^ 2 := by
  have h := integral_norm_sq_lp
    ((physicalEvenHilbert P : evenL2) : ComplexL2)
  have hcoe := (physicalEvenProfile_memLp_two P).coeFn_toLp
  calc
    ‖physicalEvenHilbert P‖ ^ 2 =
        ∫ u : ℝ, ‖((physicalEvenHilbert P : evenL2) : ComplexL2) u‖ ^ 2 :=
      h.symm
    _ = ∫ u : ℝ, ‖physicalEvenProfile P u‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hcoe] with u hu
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hu

/-- The Fourier image is the actual full packet at the corresponding raw
height; the factor two is the even-extension normalization. -/
theorem evenFourier_physicalEvenHilbert_ae (P : PacketData ι) :
    (((evenFourier (physicalEvenHilbert P) : ComplexL2) : ℝ → ℂ))
      =ᵐ[volume]
        fun ξ : ℝ => (2 : ℂ) * fullPhysicalHeight P (Real.pi * ξ) := by
  have hbridge := fourier_toLp_ae_eq
    (physicalEvenProfile_integrable P) (physicalEvenProfile_memLp_two P)
  refine hbridge.trans (Filter.Eventually.of_forall fun ξ => ?_)
  have harg : Real.pi * ξ / Real.pi = ξ := by
    field_simp [Real.pi_ne_zero]
  have h := fullPhysicalHeight_eq_half_fourier P (Real.pi * ξ)
  rw [harg] at h
  rw [h]
  ring

/-- The positive-half-line energy displays the factor two caused by even
reflection. -/
theorem fullPhysicalHeight_energy_half (P : PacketData ι) :
    (∫ t : ℝ, ‖fullPhysicalHeight P t‖ ^ 2) =
      (Real.pi / 2) *
        ∫ u in Ioi (0 : ℝ), ‖physicalEvenProfile P u‖ ^ 2 := by
  have habs (u : ℝ) : physicalEvenProfile P |u| = physicalEvenProfile P u := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg (lt_of_not_ge hu), physicalEvenProfile_even]
  have hmass : (∫ u : ℝ, ‖physicalEvenProfile P u‖ ^ 2) =
      2 * ∫ u in Ioi (0 : ℝ), ‖physicalEvenProfile P u‖ ^ 2 := by
    calc
      _ = ∫ u : ℝ, ‖physicalEvenProfile P |u|‖ ^ 2 := by
        simp_rw [habs]
      _ = _ := integral_comp_abs
        (f := fun u : ℝ => ‖physicalEvenProfile P u‖ ^ 2)
  rw [fullPhysicalHeight_energy, hmass]
  ring

/-- Angular-frequency convention `omega=2*t`: its Fourier argument has
the explicit `2*pi` denominator. -/
theorem fullPhysicalHeight_angular_fourier (P : PacketData ι) (omega : ℝ) :
    fullPhysicalHeight P (omega / 2) =
      (1 / 2 : ℂ) *
        𝓕 (physicalEvenProfile P) (omega / (2 * Real.pi)) := by
  rw [fullPhysicalHeight_eq_half_fourier]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

/-- Changing from `dt` to `d omega` doubles the full-height energy. -/
theorem fullPhysicalHeight_angular_energy (P : PacketData ι) :
    (∫ omega : ℝ, ‖fullPhysicalHeight P (omega / 2)‖ ^ 2) =
      Real.pi *
        ∫ u in Ioi (0 : ℝ), ‖physicalEvenProfile P u‖ ^ 2 := by
  calc
    _ = 2 * ∫ t : ℝ, ‖fullPhysicalHeight P t‖ ^ 2 := by
      rw [Measure.integral_comp_div]
      norm_num
    _ = _ := by rw [fullPhysicalHeight_energy_half]; ring

/-- Equivalent Hilbert normalization of the actual packet in raw height. -/
theorem fullPhysicalHeight_energy_hilbert (P : PacketData ι) :
    (∫ t : ℝ, ‖fullPhysicalHeight P t‖ ^ 2) =
      (Real.pi / 4) * ‖physicalEvenHilbert P‖ ^ 2 := by
  rw [fullPhysicalHeight_energy, physicalEvenHilbert_norm_sq]

end

end ImbalancedChen.Part3.ActualKPhysicalHilbertNormalization20261024zz
