import Mathlib

namespace ImbalancedChen.Probes.StructuralControl

def count : Nat → Nat
  | 0 => 0
  | n + 1 => count n + 1

end ImbalancedChen.Probes.StructuralControl
