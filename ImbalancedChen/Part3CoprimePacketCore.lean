import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ImbalancedChen.Part3
noncomputable section

open Classical

/-- The ABL transformed coefficient has no spectral-height argument.
The coprimality of the packet level and moving residue remains required. -/
structure CoprimePacket where
  residue : ℕ
  level : ℕ
  multiplier : ℕ
  level_pos : 0 < level
  residue_coprime : Nat.Coprime residue level
  beta : ℕ → ℕ → ℂ

def CoprimePacket.transformedCoefficient (d : CoprimePacket) (n : ℕ) : ℂ :=
  if Nat.Coprime n d.residue then
    d.beta (d.multiplier * n) d.level *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (d.level : ℂ))
  else 0

end
end ImbalancedChen.Part3
