import ImbalancedChen.StoredHistoricalBoxPermit

/-!
Kernel computation probes for an actual stored cap.  The accepted cap is
different from the midpoint; both equality endpoints, a stronger supplied
historical old level, the cell mask and the ceiling affect acceptance.
These small data are not an adopted manuscript certificate.
-/

namespace P1StoredCapProbe

open ImbalancedChen
open scoped Classical BigOperators

def mask : Finset (Fin 1) := {0}
def lo : Fin 1 → ℚ := fun _ => 1 / 10
def hi : Fin 1 → ℚ := fun _ => 11 / 100
def cell : Fin 1 → Fin 1 := fun _ => 0

theorem accepts_stored_cap :
    storedBoxCapCheck mask (1 / 2) (3 / 5) lo hi (53 / 100) = true := by
  decide +kernel

theorem midpoint_value :
    selectedBoxCap mask (1 / 2) (3 / 5) lo hi = (21 / 40 : ℚ) := by
  decide +kernel

theorem stored_cap_is_not_midpoint :
    (53 / 100 : ℚ) ≠ selectedBoxCap mask (1 / 2) (3 / 5) lo hi := by
  rw [midpoint_value]
  norm_num

theorem rejects_lower_equality :
    storedBoxCapCheck mask (1 / 2) (3 / 5) lo hi (1 / 2) = false := by
  decide +kernel

theorem rejects_upper_equality :
    storedBoxCapCheck mask (1 / 2) (3 / 5) lo hi (11 / 20) = false := by
  decide +kernel

theorem rejects_stronger_history :
    storedBoxCapCheck mask (11 / 20) (3 / 5) lo hi (53 / 100) = false := by
  decide +kernel

theorem rejects_empty_mask :
    storedBoxCapCheck (∅ : Finset (Fin 1)) (1 / 2) (3 / 5) lo hi (53 / 100) =
      false := by
  decide +kernel

theorem rejects_lower_ceiling :
    storedBoxCapCheck mask (1 / 2) (13 / 25) lo hi (53 / 100) = false := by
  decide +kernel

theorem accepts_stored_mesh_cap :
    storedMeshCapCheck (n := 1) (1 / 10) (11 / 100) 0 {cell}
      (fun _ => mask) (fun _ => 1 / 2) (fun _ => 3 / 5)
      (fun _ => 53 / 100) = true := by
  decide +kernel

end P1StoredCapProbe
