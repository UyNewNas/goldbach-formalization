import ImbalancedChen.P4AOriginalAscendingFourteenSourceDefinitions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! SOURCE ONLY. Literal source transcription, not a new numerical certificate.
Original ascending family IDs 0..14 except 7, in original order.
No geometry, centre, facet, integral, or finite proof is evaluated. -/

namespace ImbalancedChen.P4AOriginalAscendingFourteenAffineSource
noncomputable section
open scoped Classical BigOperators

def originalId : Fin 14 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14]
def leftMasks : Fin 14 → Finset ℕ :=
  ![{1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 58, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 50, 52, 56, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 52, 56, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 44, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 44, 48, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 56}]




end
end ImbalancedChen.P4AOriginalAscendingFourteenAffineSource
