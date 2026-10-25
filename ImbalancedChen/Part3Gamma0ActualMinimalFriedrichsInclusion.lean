import ImbalancedChen.Part3Gamma0ActualFriedrichsOperator
import ImbalancedChen.Part3Gamma0ActualMaassClosedOperator

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The actual Gamma0 Friedrichs operator is instantiated from the actual
Gamma0 shifted-energy resolvent R=JJ*, on the SAME canonical quotient
Hilbert space. Its genuine graph equation is R(u+v)=u. The actual completed
energy testing identity already proves R(u+Acore u)=u on the real smooth
compact-seed core. Thus the actual differential core graph lies in this
Friedrichs graph. Closedness of the latter propagates inclusion through
the actual minimal differential graph closure.

The conclusion is actualClosedGammaMaass <= actualGammaFriedrichs, with
the native domain inclusion and exact agreement on that domain. No
essential self-adjointness premise, extension target premise, equality of
the two operators, or equality of their domains is assumed or asserted.
-/

namespace ImbalancedChen.Part3.Gamma0ActualMinimalFriedrichsInclusion20261025a

noncomputable section
open Set MeasureTheory
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
open ImbalancedChen.Part3.Gamma0ActualWeakRieszResolvent20261025a
open ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a

/-- Core compatibility is the actual weak variational identity supplied
by the real energy completion, with no hExtension or hCommute premise. -/
theorem actualGammaResolvent_shift_smoothCore (N : ℕ) [NeZero N] (u : smoothCore N) :
    actualGammaResolvent N ((u : QuotientL2 N)+actualCoreLaplacian N u) = (u : QuotientL2 N) :=
  actualGammaResolvent_shift_core N (u : EnergyCore N)

theorem actual_coreGraph_le_friedrichsGraph (N : ℕ) [NeZero N] :
    coreGraph N ≤ (actualGammaFriedrichs N).graph := by
  rintro ⟨u,v⟩ huv
  have hu : u ∈ smoothCore N := (coreGraph_domain_iff N u).mp ⟨v,huv⟩
  have hv := (coreGraph_iff_operator N ⟨u,hu⟩ v).mp huv
  apply (actualGammaFriedrichs_mem_graph_iff N).mpr
  rw [hv]
  exact actualGammaResolvent_shift_smoothCore N ⟨u,hu⟩

theorem actualPartialGammaMaass_le_friedrichs (N : ℕ) [NeZero N] :
    actualPartialGammaMaass N ≤ actualGammaFriedrichs N := by
  apply LinearPMap.le_of_le_graph
  rw [actualPartialGammaMaass_graph_eq]
  exact actual_coreGraph_le_friedrichsGraph N

/-- The target extension graph is genuinely closed. Consequently it
contains the closure of the original actual differential graph. -/
theorem closedGammaGraph_le_friedrichsGraph (N : ℕ) [NeZero N] :
    closedGammaGraph N ≤ (actualGammaFriedrichs N).graph :=
  closure_minimal (actual_coreGraph_le_friedrichsGraph N) (actualGammaFriedrichs_isClosed N)

/-- Native partial-operator inclusion. Essential self-adjointness would
require the reverse inclusion, which is neither used nor claimed. -/
theorem actualClosedGammaMaass_le_friedrichs (N : ℕ) [NeZero N] :
    actualClosedGammaMaass N ≤ actualGammaFriedrichs N := by
  apply LinearPMap.le_of_le_graph
  rw [actualClosedGammaMaass_graph_eq]
  exact closedGammaGraph_le_friedrichsGraph N

theorem actualClosedGammaMaass_domain_le_friedrichs (N : ℕ) [NeZero N] :
    (actualClosedGammaMaass N).domain ≤ (actualGammaFriedrichs N).domain :=
  (actualClosedGammaMaass_le_friedrichs N).1

/-- Exact output agreement through the proved native domain inclusion. -/
theorem actualClosedGammaMaass_agrees_friedrichs (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).domain) :
    actualClosedGammaMaass N u = actualGammaFriedrichs N
      (Submodule.inclusion (actualClosedGammaMaass_domain_le_friedrichs N) u) :=
  LinearPMap.apply_comp_inclusion (actualClosedGammaMaass_le_friedrichs N) u

/-- The true energy resolvent also inverts the shift on every member of
the actual minimal closed domain. This gives no assertion that every
resolvent output lies in that smaller domain. -/
theorem actualGammaResolvent_shift_minimalClosed (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).domain) :
    actualGammaResolvent N ((u : QuotientL2 N)+actualClosedGammaMaass N u) = (u : QuotientL2 N) :=
  (actualGammaFriedrichs_mem_graph_iff N).mp
    ((closedGammaGraph_le_friedrichsGraph N) (actualClosedGammaMaass_mem_graph N u))

/-- The minimal closed differential graph also satisfies the ACTUAL
completed Dirichlet relation of its Friedrichs extension. -/
theorem actualClosedGammaMaass_Dirichlet (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).domain) :
    actualDirichletRelation N (u : QuotientL2 N) (actualClosedGammaMaass N u) :=
  (actualGammaFriedrichs_mem_graph_iff_Dirichlet N).mp
    ((closedGammaGraph_le_friedrichsGraph N) (actualClosedGammaMaass_mem_graph N u))

end
end ImbalancedChen.Part3.Gamma0ActualMinimalFriedrichsInclusion20261025a
