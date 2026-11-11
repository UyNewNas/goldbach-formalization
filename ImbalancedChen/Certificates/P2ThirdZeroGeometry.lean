import ImbalancedChen.P4AOriginalZeroLeafSuppliers
import ImbalancedChen.P4AClosedTreeCoordinatePropagation

/-!
P2 SOURCE ONLY / UNCOMPILED.
Pure integer zero-geometry checks for the original compact third leaf.
All analytic zero/null-face arguments are the existing P4A suppliers.
Closed equality cases remain faces; they are not declared empty.
This does not turn a selected OLD/minorant early mean into zero correction.
-/
namespace ImbalancedChen.Certificates.P2ThirdZeroGeometry

open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P4AOriginalZeroLeafSuppliersSourceOnly

/-- Original DEN=48000*2^24, cutoff=1/100, rho=19/96, Theta=299/500.
The last test is the ROOT cube gate, not a selected OLD/minorant clamp. -/
def Geometry (lo hi : Fin 3 → ℤ) : Prop :=
  hi 2≤(480*2^24:ℤ) ∨
  (9500*2^24:ℤ)≤lo 0 ∨
  hi 0≤lo 1 ∨
  hi 1≤lo 2 ∨
  (∃ j : Fin 3,hi j≤lo j) ∨
  (481573208064:ℤ)≤lo 0+lo 1+3*lo 2

instance (lo hi : Fin 3 → ℤ) : Decidable (Geometry lo hi) := by
  unfold Geometry
  infer_instance

/-- This Bool has only finite integer decisions, with no reader/log/cost
or real predicate. No concrete original-data evaluation is claimed here. -/
def check (lo hi : Fin 3 → ℤ) : Bool := decide (Geometry lo hi)

theorem check_sound {lo hi : Fin 3 → ℤ} (h : check lo hi=true) : Geometry lo hi :=
  of_decide_eq_true h

theorem check_iff {lo hi : Fin 3 → ℤ} : check lo hi=true ↔ Geometry lo hi := by
  simp only [check,decide_eq_true_eq]

noncomputable section

def leaf (lo hi : Fin 3 → ℤ) : Set Point :=
  compactRegion ∩ Icc (decodeCoordinates lo) (decodeCoordinates hi)

/-- Exact original leaf integral zero from checked integer geometry.
No width/positivity, integral-zero or measurability assumption is stored.
Every branch calls an existing actual-kernel supplier unchanged. -/
theorem check_integral_eq_zero (lo hi : Fin 3 → ℤ) (h : check lo hi=true) :
    (∫ t in leaf lo hi,compactKernel t)=0 := by
  have hs : leaf lo hi⊆compactRegion ∩ Icc (decodeCoordinates lo) (decodeCoordinates hi) :=
    fun _ ht => ht
  have hle (u v : ℤ) (huv : u≤v) :
      (u:ℝ)/coordinateDenominator≤(v:ℝ)/coordinateDenominator :=
    div_le_div_of_nonneg_right (by exact_mod_cast huv) original_coordinateDenominator_pos.le
  rcases check_sound h with hcut | hrho | hxy | hyz | ⟨j,hj⟩ | hgate
  · apply integral_eq_zero_of_box_below_cutoff hs
    calc
      decodeCoordinates hi 2≤((480*2^24:ℤ):ℝ)/coordinateDenominator := hle _ _ hcut
      _=(1/100:ℝ) := by norm_num [coordinateDenominator]
  · apply integral_eq_zero_of_box_above_rho hs
    calc
      thirdPrefixRho=((9500*2^24:ℤ):ℝ)/coordinateDenominator := by
        norm_num [thirdPrefixRho,coordinateDenominator]
      _≤decodeCoordinates lo 0 := hle _ _ hrho
  · exact integral_eq_zero_of_box_xy_order hs (hle _ _ hxy)
  · exact integral_eq_zero_of_box_yz_order hs (hle _ _ hyz)
  · exact integral_eq_zero_of_box_coordinate hs j (hle _ _ hj)
  · apply integral_eq_zero_of_box_old_gate hs
    calc
      thirdPrefixTheta=((481573208064:ℤ):ℝ)/coordinateDenominator := by
        norm_num [thirdPrefixTheta,coordinateDenominator]
      _≤((lo 0+lo 1+3*lo 2:ℤ):ℝ)/coordinateDenominator := hle _ _ hgate
      _=decodeCoordinates lo 0+decodeCoordinates lo 1+3*decodeCoordinates lo 2 := by
        simp only [decodeCoordinates,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
        ring

end
end ImbalancedChen.Certificates.P2ThirdZeroGeometry
