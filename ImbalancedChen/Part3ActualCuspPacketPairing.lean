import ImbalancedChen.Part3ActualCuspFourierSection
import ImbalancedChen.Part3ActualLiteralPacketIntegral

/-!
SOURCE ONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

This is the algebraic interface between the existing physical coprime packet
and the actual normalized-Haar Fourier coefficient of a Gamma0
invariant function in the two cusp-1 scaling charts. The old chart adds
`e(n/N)` to the coefficient; the existing transformed packet contributes
`e(-n/N)`. Their product is the new-chart coefficient paired with the
untransformed packet entry. This does not construct a Maass or Eisenstein
function, a quotient measure, or a Kuznetsov spectral supplier.
-/

namespace ImbalancedChen.Part3.ActualCuspPacketPairingSourceOnly

noncomputable section

open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3 (CoprimePacket)
open ImbalancedChen.Part3.ActualCuspFourierSectionSourceOnly

/-- The actual physical packet phase cancels the old-chart phase of any
Gamma0-invariant function. No spectral realization of `f` is assumed. -/
theorem transformedCoefficient_mul_oldFourierCoeff
    (N : ℕ) (hN : 0 < N) (p : CoprimePacket) (hlevel : p.level = N)
    (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) (n : ℕ) :
    p.transformedCoefficient n * oldFourierCoeff N hN f hfΓ y hy (n : ℤ) =
      (if Nat.Coprime n p.residue then
        p.beta (p.multiplier * n) p.level else 0) *
        newFourierCoeff N hN f hfΓ y hy (n : ℤ) := by
  have hphase : cuspPhase false p.level n *
      oldFourierCoeff N hN f hfΓ y hy (n : ℤ) =
        newFourierCoeff N hN f hfΓ y hy (n : ℤ) := by
    simpa only [hlevel] using
      cuspPhase_cancels_actual_section N hN f hfΓ y hy n
  rw [← signedCoefficient_false_eq_actual p n]
  by_cases hc : Nat.Coprime n p.residue
  · simp only [signedCoefficient, if_pos hc]
    calc
      (p.beta (p.multiplier * n) p.level * cuspPhase false p.level n) *
          oldFourierCoeff N hN f hfΓ y hy (n : ℤ) =
        p.beta (p.multiplier * n) p.level *
          (cuspPhase false p.level n *
            oldFourierCoeff N hN f hfΓ y hy (n : ℤ)) := by ring
      _ = p.beta (p.multiplier * n) p.level *
            newFourierCoeff N hN f hfΓ y hy (n : ℤ) := by rw [hphase]
  · simp only [signedCoefficient, if_neg hc, zero_mul]

/-- On the pre-existing mode packet the surviving entry has exactly the
original beta coefficient and its two retained k2/k3 phases. -/
theorem modePacket_mul_oldFourierCoeff
    (N : ℕ) (hN : 0 < N) (d : CoprimePacket) (hlevel : d.level = N)
    (k : D4 → ℤ) (U Z : ℝ) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) (n : ℕ) :
    (modePacket d k U Z).transformedCoefficient n *
        oldFourierCoeff N hN f hfΓ y hy (n : ℤ) =
      (if Nat.Coprime n d.residue then
        d.beta (d.multiplier * n) d.level *
          P3Period64NativeReconstructionSourceOnly.e
            ((k 2 : ℝ) / 64 * (((d.multiplier * n : ℕ) : ℝ) / U) +
              (k 3 : ℝ) / 64 * ((d.level : ℝ) / Z))
       else 0) * newFourierCoeff N hN f hfΓ y hy (n : ℤ) := by
  have hmode : (modePacket d k U Z).level = N := hlevel
  rw [transformedCoefficient_mul_oldFourierCoeff N hN
    (modePacket d k U Z) hmode f hfΓ y hy n]
  rfl

end

end ImbalancedChen.Part3.ActualCuspPacketPairingSourceOnly
