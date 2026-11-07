import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Data

/- SOURCEONLY. Unspecified blocks remain the SAME arbitrary tail.
A later assembly must prove each explicit slot equality, never substitute
a separately rounded or differently hashed copy of a block. -/

namespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly

def window00 (tail : Nat → Block) (b : Nat) : Block :=
  if b = 0 then block00 else
  tail b

theorem window00_eq_self (tail : Nat → Block)
    (h0 : tail 0 = block00)
    : window00 tail = tail := by
  funext b
  by_cases hc0 : b = 0
  · subst b
    simpa [window00] using h0.symm
  simp [window00, hc0]

end ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
