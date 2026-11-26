import ImbalancedChen.Part3MediumAtomCore
import ImbalancedChen.Part3LiteralReciprocalSource
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! The literal signed nonzero source of an actual medium atom. -/

namespace ImbalancedChen.Part3

noncomputable section

def MediumAtom.sharedSmoothFrequencyBound (d : MediumAtom) (Z : ℝ) (D : ℕ) : ℕ :=
  Nat.ceil (64 * Z * d.Q1 * d.Q3 ^ 2 * d.Q2 ^ 2 / ((D : ℝ) * d.V))

namespace ActualSeparatedRowPacketMatchSourceOnly

open Classical Finset

def baseCarrier (e : MediumAtom) (q : ℕ) : Finset ℕ :=
  ((factorCarrier e.Q2).filter (fun s => q ∣ s)).image (fun s => s / q)

def signedResidue (negative : Bool) (a : ℤ) : ℤ := if negative then -a else a

end ActualSeparatedRowPacketMatchSourceOnly

namespace ActualPositiveLatticeSmoothCoverSourceOnly

def scaleF (e : MediumAtom) (D g : ℕ) : ℝ := e.U/((g : ℝ)*e.Q1*D)

end ActualPositiveLatticeSmoothCoverSourceOnly

namespace ActualM2FinitePoissonAdapterSourceOnly

open ActualSeparatedRowPacketMatchSourceOnly

theorem signedResidue_natAbs (negative : Bool) (a : ℤ) :
    (signedResidue negative a).natAbs = a.natAbs := by
  cases negative <;> simp [signedResidue]

end ActualM2FinitePoissonAdapterSourceOnly

namespace ActualModeBetaPositiveCountSourceOnly

open Classical Finset
open ActualCompletedSquarePushforwardSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly
attribute [local instance] Classical.propDecidable

/-- Literal nonzero part of the completed mode's source, before any
counting enlargement. y=0 remains in the separate existing zeroSource. -/
def actualNonzeroSource (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (negative : Bool) : Finset Source :=
  nonzeroSource (carrier (g*l) (signedResidue negative e.residue)
    (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
    (Icc (Int.ceil (-scaleF e D g)) (Int.floor (scaleF e D g))))

end ActualModeBetaPositiveCountSourceOnly

end

end ImbalancedChen.Part3
