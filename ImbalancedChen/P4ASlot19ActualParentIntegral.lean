import ImbalancedChen.P2OriginalThirdMinorantLogDictionary
import ImbalancedChen.P4AAll22OriginalKLedger

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The nineteenth selected upper saving (index zero of finalFourGains) is the
thirteen-cell ascending third-minorant eighth saving. The existing physical
dictionary proves its conservative density is below the actual parent
residual density when the retained seventh history and actual sixth-cap
bound hold. This module moves that comparison to real integrals and
replaces exactly that ledger slot by the actual parent kernel integral.

The selected thirteen-cell domain, its common causal parent, its physical
same-rho signed-density telescope, and the adopted rational enclosure are
not supplied here. Thus the new ledger is not asserted to bound the actual
compiled physical density or to fit currentK.
-/

namespace ImbalancedChen.P4ASlot19ActualParentIntegralSourceOnly

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P4AAll22OriginalKLedger20261024zSourceOnly

def conservativeSaving (D : Set Point) : ℝ :=
  ∫ t in D, conservativeDensity t

def actualParentSaving (D : Set Point) (parent : Point → ℝ) : ℝ :=
  ∫ t in D, parentDensity (parent t) t

theorem slot19_quoted_endpoint :
    finalFourGains 0 = (283388722705335806564439 / 2^96 : ℝ) := by
  rfl

/-- A genuine real-integral saving comparison. The hypotheses are physical
row, history, cap, and integrability facts, not an endpoint or gain bound. -/
theorem conservativeSaving_le_actualParentSaving
    {D : Set Point} (hD : MeasurableSet D)
    (hRows : ∀ t ∈ D, PhysicalRows t) (parent : Point → ℝ)
    (hHistory : ∀ t ∈ D, history7 t < parent t)
    (hCap : ∀ t ∈ D, parent t ≤ comparisonCap t)
    (hCon : IntegrableOn conservativeDensity D)
    (hParent : IntegrableOn (fun t => parentDensity (parent t) t) D) :
    conservativeSaving D ≤ actualParentSaving D parent := by
  unfold conservativeSaving actualParentSaving
  exact setIntegral_mono_on hCon hParent hD
    (fun t ht => conservativeDensity_le_parentDensity (hRows t ht)
      (hHistory t ht) (hCap t ht))

/-- Other 21 quoted savings are unchanged. This expression removes only
finalFourGains 0 and inserts the physical parent-kernel integral. -/
def oneActualSlotLedger (D : Set Point) (parent : Point → ℝ) : ℝ :=
  currentUpperEighteenRaw -
    (actualParentSaving D parent +
      ∑ i : Fin 3, finalFourGains i.succ)

theorem oneActualSlotLedger_replacement_identity
    (D : Set Point) (parent : Point → ℝ) :
    oneActualSlotLedger D parent =
      quotedAll22Raw + finalFourGains 0 - actualParentSaving D parent := by
  unfold oneActualSlotLedger quotedAll22Raw
  simp only [Fin.sum_univ_succ]
  ring

/-- The proved kernel comparison charges the ledger no more than the
literal deficit of the conservative integral against quoted slot 19.
No lower enclosure of that integral is presumed. -/
theorem oneActualSlotLedger_le_quoted_plus_slot19_deficit
    {D : Set Point} (hD : MeasurableSet D)
    (hRows : ∀ t ∈ D, PhysicalRows t) (parent : Point → ℝ)
    (hHistory : ∀ t ∈ D, history7 t < parent t)
    (hCap : ∀ t ∈ D, parent t ≤ comparisonCap t)
    (hCon : IntegrableOn conservativeDensity D)
    (hParent : IntegrableOn (fun t => parentDensity (parent t) t) D) :
    oneActualSlotLedger D parent ≤
      quotedAll22Raw + finalFourGains 0 - conservativeSaving D := by
  rw [oneActualSlotLedger_replacement_identity]
  exact sub_le_sub_left
    (conservativeSaving_le_actualParentSaving hD hRows parent hHistory hCap hCon hParent)
    (quotedAll22Raw + finalFourGains 0)

end
end ImbalancedChen.P4ASlot19ActualParentIntegralSourceOnly
