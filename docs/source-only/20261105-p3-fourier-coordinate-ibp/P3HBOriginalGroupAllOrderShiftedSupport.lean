import ImbalancedChen.P3HBOriginalGroupFinCons
import Mathlib.Tactic

/-!
P3.6, frozen paper @9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F): exact all-order shifted strip support of the
literal product of physical original group occurrences.

The support is at s_{J j}(u) + log(c j), separately for every occurrence
j : Fin g; no fictitious fixed rectangular support is inserted. The
coordinate word can repeat coordinates, and group occurrences with the same
J but different c are not combined. The argument uses the earlier actual
all-order complex Leibniz *candidate* and the literal single-group derivative
support, neither assumed as a new field or external input.

This is manuscript-INTERNAL SOURCE_ONLY; transitive imports, Lean elaboration,
and kernel checking have NOT been completed. No Fourier or arithmetic PP
claim is made. Toolchain v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalGroupAllOrderShiftedSupport
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupJetLeibnizStep
open ImbalancedChen.P3HBOriginalGroupFinCons
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative

/-- Every allocated COMPLEX jet product vanishes if even one genuine
physical group occurrence lies strictly outside its translated strip.
In particular an allocated derivative on that group may have any length. -/
theorem allocatedGroupJetProduct_zero_outside_any_group {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : Fin g → ℝ) (hc : ∀ j, 0 < c j)
    (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) (owner : Fin k → Fin g)
    (u : Fin 6 → ℝ) (j : Fin g)
    (hout : originalGroupSum (J j) u + Real.log (c j) ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    allocatedGroupJetProduct chi c J axes owner u = 0 := by
  classical
  unfold allocatedGroupJetProduct
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact originalGroupOrderedDeriv_zero_outside chi hchi hsmall hlarge
    (c j) (hc j) (J j) (axesAssigned axes owner j) u hout

/-- The FULL complex allocation sum vanishes term by term outside any
one actual shifted group strip. No cancellation or Fourier input is used. -/
theorem allocatedGroupJetSum_zero_outside_any_group {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : Fin g → ℝ) (hc : ∀ j, 0 < c j)
    (J : Fin g → Finset (Fin 6)) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) (j : Fin g)
    (hout : originalGroupSum (J j) u + Real.log (c j) ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    allocatedGroupJetSum chi c J axes u = 0 := by
  classical
  unfold allocatedGroupJetSum
  apply Finset.sum_eq_zero
  intro owner howner
  exact allocatedGroupJetProduct_zero_outside_any_group
    chi hchi hsmall hlarge c hc J axes owner u j hout

/-- Even the nonnegative ORIGINAL allocation norm term vanishes outside
any one shifted group strip; the zero factor is a true group jet. -/
theorem allocationTerm_zero_outside_any_group {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : Fin g → ℝ) (hc : ∀ j, 0 < c j)
    (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) (owner : Fin k → Fin g)
    (u : Fin 6 → ℝ) (j : Fin g)
    (hout : originalGroupSum (J j) u + Real.log (c j) ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    allocationTerm chi c J axes owner u = 0 := by
  classical
  unfold allocationTerm
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  have hz := originalGroupOrderedDeriv_zero_outside chi hchi hsmall hlarge
    (c j) (hc j) (J j) (axesAssigned axes owner j) u hout
  simp only [hz, norm_zero]

/-- The complete nonnegative allocation MASS is zero outside any
one translated strip. It does not merely have a small wall integral. -/
theorem allocationMass_zero_outside_any_group {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : Fin g → ℝ) (hc : ∀ j, 0 < c j)
    (J : Fin g → Finset (Fin 6)) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) (j : Fin g)
    (hout : originalGroupSum (J j) u + Real.log (c j) ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    allocationMass chi c J axes u = 0 := by
  classical
  unfold allocationMass
  apply Finset.sum_eq_zero
  intro owner howner
  exact allocationTerm_zero_outside_any_group
    chi hchi hsmall hlarge c hc J axes owner u j hout

/-- The ACTUAL full original grouped product has no ordered derivative
of any finite order outside ANY one translated occurrence strip. Includes
repeated coordinates, empty derivative words and independent c_j. This
uses the full true derivative/allocation identity as an uncompiled upstream
SOURCE_ONLY theorem candidate, not as a new hypothesis. -/
theorem originalGroupProduct_ordered_zero_outside_any_group {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : Fin g → ℝ) (hc : ∀ j, 0 < c j)
    (J : Fin g → Finset (Fin 6)) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) (j : Fin g)
    (hout : originalGroupSum (J j) u + Real.log (c j) ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    originalOrderedAxisDeriv (List.ofFn axes)
      (originalGroupProduct chi c J) u = 0 := by
  rw [originalGroupProduct_ordered_eq_allocation chi hchi c J k axes u]
  exact allocatedGroupJetSum_zero_outside_any_group
    chi hchi hsmall hlarge c hc J axes u j hout

end
end ImbalancedChen.P3HBOriginalGroupAllOrderShiftedSupport
