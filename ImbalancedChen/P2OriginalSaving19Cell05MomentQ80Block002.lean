import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Pilot

/-! Original stored Q80 equalities for four actual Cell05 rows.
No host-computed coefficient or floor is a premise. -/
namespace ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block002
noncomputable section
open P2OriginalSaving19Cell05MomentQ80Pilot

def row (i : Fin 4) : Fin 56 := ⟨8 + i.val, by omega⟩

theorem all_factors : ∀ i : Fin 4, ∀ j : Fin 10,
    computedFactor (row i) j = (originalMomentRow (row i)).factorFloorsQ80[j.val]! := by
  decide +kernel

#print axioms all_factors

end
end ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block002
