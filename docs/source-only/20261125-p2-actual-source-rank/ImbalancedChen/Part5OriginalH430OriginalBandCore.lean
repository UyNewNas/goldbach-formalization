import ImbalancedChen.Part5OriginalH430PhysicalRoots
import ImbalancedChen.P2EnhancedLowerPrimeChildCarriers

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.
Mechanical relocation of original declarations from ImbalancedChen.Part5OriginalH430TaggedArithmeticReceivers.
Public namespace and declaration/proof text are preserved. The original
owner postimage imports this module and removes each moved declaration.
Private helpers, if present, acquire this module owner and need a fresh
complete owned audit. No compiler or kernel acceptance is asserted.
-/

namespace ImbalancedChen.Part5OriginalH430TaggedArithmeticReceivers

noncomputable section
open Set
open Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5OriginalH430PhysicalRoots
open scoped Classical BigOperators

/-- The ORIGINAL two selected prime bands, without a disjointification.
If p lies in the overlap, it occurs in both tagged U3 and tagged U4. -/
def originalBand (N : ℕ) : Root → Finset ℕ
  | .U3 => chenSinglePrimeSelector N ((N : ℝ)^a) ((N : ℝ)^(1/3 : ℝ))
  | .U4 => chenSinglePrimeSelector N ((N : ℝ)^a) ((N : ℝ)^(59/250 : ℝ))

/-- The original selector itself supplies primality and coprimality:
they are not arbitrary geometric premises or a count licence. -/
theorem original_band_prime {N p : ℕ} {k : Root}
    (hp : p ∈ originalBand N k) : p.Prime ∧ p.Coprime N := by
  have hc : p ∈ chenAdditivePrimeCarrier N := by
    cases k <;> exact (Finset.mem_filter.mp hp).1
  have h := mem_chenAdditivePrimeCarrier.mp hc
  exact ⟨h.2.1, h.2.2⟩

/-- The actual selected-prime cutoff entails the frozen root band.
The strict source upper endpoint becomes a weak geometric upper bound. -/
theorem original_band_geometry {N p : ℕ} {k : Root}
    (hN : 2 ≤ N) (hp : p ∈ originalBand N k) :
    physicalPrime N p ∈ rootBand k := by
  cases k with
  | U3 =>
      have hc : primeCoordinate N p ∈ Ico a (1/3 : ℝ) :=
        primeCoordinate_mem hN (by simpa only [originalBand] using hp)
      change primeCoordinate N p ∈ Icc a (1/3 : ℝ)
      exact ⟨hc.1, hc.2.le⟩
  | U4 =>
      have hc : primeCoordinate N p ∈ Ico a (59/250 : ℝ) :=
        primeCoordinate_mem hN (by simpa only [originalBand] using hp)
      change primeCoordinate N p ∈ Icc a (59/250 : ℝ)
      exact ⟨hc.1, hc.2.le⟩

end
end ImbalancedChen.Part5OriginalH430TaggedArithmeticReceivers
