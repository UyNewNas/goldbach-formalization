import Mathlib

namespace ImbalancedChen.P5Z.ActualHBPostModulusLogCutoff
noncomputable section
open Classical
open scoped BigOperators

variable {m : ℕ}

def completeProduct (n : Fin m → ℕ) : ℕ := ∏ a, n a

end
end ImbalancedChen.P5Z.ActualHBPostModulusLogCutoff
