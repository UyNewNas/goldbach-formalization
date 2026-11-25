import ImbalancedChen.StoredHistoricalBoxPermit
import ImbalancedChen.P1HistoricalLevelCheckPreservation
import ImbalancedChen.HistoricalFifthJointIntegralSupportP1
import ImbalancedChen.P4AHistoricalCausalSavingsLedger

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Bind a finite selected fifth family to the *historical* fourth parent, not
to the ordinary five-prime parent.  The selected mask and rational ceiling
are fixed for every owned cell before a target is introduced.  The midpoint
cap is the existing rational whole-box selector, and its license uses the
literal manuscript envelope min ((1+s_I)/2) (57/64-3*s_I/2).

The family `J` and its checks must still be instantiated from the original
all22 fifth certificate.  No value, sign, or lower saving bound is inferred
from this binding.  In particular this is not a rational proof of slot 5.
-/

namespace ImbalancedChen.P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly

noncomputable section
open Filter Topology MeasureTheory
open scoped Classical BigOperators

abbrev Label5 (D : HistoricalPrefixCapData) := Fin 5 → Fin (D.m + 1)

/-- The exact two-branch manuscript cap on a selected subproduct. -/
def originalEnvelope (I : Finset (Fin 5)) (t : Fin 5 → ℝ) : ℝ :=
  let s := ∑ i ∈ I, t i
  min ((1 + s) / 2) (57 / 64 - (3 / 2) * s)

/-- Keep the original third and fourth cap tables.  Only selected fifth
owners receive the checked rational midpoint above their *own* old5. -/
def bindFifth (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) : HistoricalPrefixCapData :=
  { D with
    cells5 := D.cells5 ∩ J
    cap5 := fun j => selectedBoxCap (I j) (D.old5 j) (nu j)
      (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) }

/-- The finite whole-box license is the only input to this bridge.  It is
neither a saving estimate nor a claim that a particular numeric table passed. -/
def fifthChecks (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) : Prop :=
  ∀ j ∈ D.cells5 ∩ J,
    selectedBoxCapCheck (I j) (D.old5 j) (nu j)
      (qLogPrimeMeshLo D.a D.b D.m j)
      (qLogPrimeMeshHi D.a D.b D.m j) = true

/-- The direct historical-certificate path retains the stored cap table
verbatim and restricts only the selected fifth cell family. -/
def bindStoredFifth (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) : HistoricalPrefixCapData :=
  D.p1RestrictFifth J

/-- A finite permit for the actual stored cap on the actual inherited old5.
This is a checkable statement about a future concrete certificate table,
not a proposed analytic saving or an assumed target inequality. -/
def storedFifthPermit (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) : Prop :=
  storedMeshCapCheck D.a D.b D.m (D.cells5 ∩ J)
    I D.old5 nu D.cap5 = true

theorem stored_cap_unchanged (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (j : Label5 D) :
    (bindStoredFifth D J).cap5 j = D.cap5 j := rfl

theorem stored_same_historical_parent (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (N : ℝ) :
    (bindStoredFifth D J).upperThirdPolicy N = D.upperThirdPolicy N ∧
    (bindStoredFifth D J).upperFourthPolicy N = D.upperFourthPolicy N ∧
    (bindStoredFifth D J).p1FifthHistoricalParent = D.p1FifthHistoricalParent := by
  exact ⟨rfl, rfl, rfl⟩

/-- Original stored fifth caps retain both strict square licenses and the
literal M_I ceiling throughout every owned half-open cell. -/
theorem stored_cell_license (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (hc : storedFifthPermit D J I nu)
    (j : Label5 D) (hj : j ∈ D.cells5 ∩ J)
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.old5 j : ℝ) < (bindStoredFifth D J).cap5 j ∧
      ((bindStoredFifth D J).cap5 j : ℝ) < originalEnvelope (I j) t ∧
      (∀ k, prefixSquareExpr t k < (bindStoredFifth D J).cap5 j) ∧
      (∀ k ∉ I j,
        selectedSquareExpr (I j) t k < (bindStoredFifth D J).cap5 j) := by
  have h := storedMeshCapCheck_sound D.a D.b D.m (D.cells5 ∩ J)
    I D.old5 nu D.cap5 hc j hj t ht
  rw [stored_cap_unchanged]
  refine ⟨h.1, ?_, h.2.2.2.1, h.2.2.2.2.1⟩
  simpa [originalEnvelope, VariableEnvelope.v_eq_min,
    VariableEnvelope.A, VariableEnvelope.C] using h.2.2.2.2.2

/-- The original certificate's selected fifth family, with every stored
cap preserved, has its own same-carrier finite historical charge. -/
theorem stored_actual_policy_charge (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (hab : D.a ≤ D.b)
    (hD : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) :
    (bindStoredFifth D J).p4aPolicyDensity
        ((bindStoredFifth D J).upperFifthPolicy (N : ℝ)) N cap
        ((N : ℝ) ^ (D.b : ℝ)) =
      D.p4aPolicyDensity (D.upperThirdPolicy (N : ℝ)) N cap
          ((N : ℝ) ^ (D.b : ℝ)) -
        D.p4aFourthEntry N cap ((N : ℝ) ^ (D.b : ℝ)) -
          ∑ j ∈ D.cells5 ∩ J,
            (bindStoredFifth D J).fifthCellPrimeCorrection N cap j := by
  have h := (bindStoredFifth D J).p4a_fifth_density_eq_causal_cell_ledger
    hab (D.p1RestrictFifth_levelCheck J hD) N cap hN
  exact h

theorem stored_integral_is_original_cell_sum (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (ha : 0 < D.a) (hab : D.a < D.b) :
    (bindStoredFifth D J).fifthCorrectionIntegral =
      ∑ j ∈ D.cells5 ∩ J,
        ∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
            primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j),
          (primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
            primeOwnCubeGatedProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i := by
  exact (bindStoredFifth D J).fifthCorrectionIntegral_eq_integrals ha hab

/-- No selected endpoint or positivity is used in the real limit. -/
theorem stored_actual_saving_limit (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hD : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ))
        ((bindStoredFifth D J).level5 (N : ℝ))
        N (cap N) ((N : ℝ) ^ (D.b : ℝ)) *
          Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (bindStoredFifth D J).fifthCorrectionIntegral) := by
  exact (bindStoredFifth D J).tendsto_actualHistoricalFifthSaving
    ha hab hold (D.p1RestrictFifth_levelCheck J hD) cap hcap

theorem bound_cells5 (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) :
    (bindFifth D J I nu).cells5 = D.cells5 ∩ J := rfl

theorem bound_old5 (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (j : Label5 D) :
    (bindFifth D J I nu).old5 j = D.old5 j := rfl

theorem bound_cap5 (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (j : Label5 D) :
    (bindFifth D J I nu).cap5 j =
      selectedBoxCap (I j) (D.old5 j) (nu j)
        (qLogPrimeMeshLo D.a D.b D.m j)
        (qLogPrimeMeshHi D.a D.b D.m j) := rfl

/-- The inherited third level, complete fourth cap, and fourth policy are
definitionally the same objects on the same target-deleted carrier. -/
theorem same_historical_parent (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (N : ℝ) :
    (bindFifth D J I nu).upperThirdPolicy N = D.upperThirdPolicy N ∧
    (bindFifth D J I nu).upperFourthPolicy N = D.upperFourthPolicy N ∧
    (bindFifth D J I nu).p1FifthHistoricalParent = D.p1FifthHistoricalParent := by
  exact ⟨rfl, rfl, rfl⟩

theorem same_fourth_old_gate (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (j : Label5 D) :
    (bindFifth D J I nu).fifthParentGateBounds j =
      D.fifthParentGateBounds j := rfl

/-- Checked midpoint caps stay strictly below the literal M_I at every
point of their half-open owned cells; full and complement squares retain
their separate strict tests. -/
theorem bound_cell_license (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (hc : fifthChecks D J I nu)
    (j : Label5 D) (hj : j ∈ D.cells5 ∩ J)
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.old5 j : ℝ) < (bindFifth D J I nu).cap5 j ∧
      ((bindFifth D J I nu).cap5 j : ℝ) < originalEnvelope (I j) t ∧
      (∀ k, prefixSquareExpr t k < (bindFifth D J I nu).cap5 j) ∧
      (∀ k ∉ I j,
        selectedSquareExpr (I j) t k < (bindFifth D J I nu).cap5 j) := by
  have hbox := selectedBoxCapCheck_sound (I j) (D.old5 j) (nu j)
    (qLogPrimeMeshLo D.a D.b D.m j)
    (qLogPrimeMeshHi D.a D.b D.m j) (hc j hj) t
    (by
      intro k
      rw [congrFun (cast_qLogPrimeMeshLo D.a D.b D.m j) k]
      exact (mem_logPrimeMeshCell.mp ht k).1)
    (by
      intro k
      rw [congrFun (cast_qLogPrimeMeshHi D.a D.b D.m j) k]
      exact (mem_logPrimeMeshCell.mp ht k).2.le)
  rw [bound_cap5]
  refine ⟨hbox.1, ?_, hbox.2.2.2.1, hbox.2.2.2.2.1⟩
  simpa [originalEnvelope, VariableEnvelope.v_eq_min,
    VariableEnvelope.A, VariableEnvelope.C] using hbox.2.2.2.2.2

/-- Existing first/fourth checks plus the new fifth box checks yield the
literal nested level check; no density or saving premise is added. -/
theorem bound_levelCheck (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (hD : D.levelCheck = true)
    (hc : fifthChecks D J I nu) :
    (bindFifth D J I nu).levelCheck = true := by
  have hprior := D.levelCheck_sound hD
  simp only [HistoricalPrefixCapData.levelCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hD ⊢
  refine ⟨hprior.1, hprior.2.1, ?_⟩
  intro j hj
  change j ∈ D.cells5 ∩ J at hj
  change D.old5 j ≤ selectedBoxCap (I j) (D.old5 j) (nu j)
    (qLogPrimeMeshLo D.a D.b D.m j)
    (qLogPrimeMeshHi D.a D.b D.m j)
  exact (selectedCapLower_old_le (I j) (D.old5 j) _).trans
    (selectedBoxCap_between (I j) (D.old5 j) (nu j) _ _ (hc j hj)).1.le

/-- Same historical fifth policy and same actual correction integral.  Both
own-cube profiles remain inside the inherited parent gate. -/
theorem bound_integral_is_original_cell_sum (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (ha : 0 < D.a) (hab : D.a < D.b) :
    (bindFifth D J I nu).fifthCorrectionIntegral =
      ∑ j ∈ D.cells5 ∩ J,
        ∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
            primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j),
          (primeOwnCubeGatedProfile ((bindFifth D J I nu).cap5 j : ℝ) t -
            primeOwnCubeGatedProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i := by
  simpa only [bound_cells5, bound_old5, same_fourth_old_gate] using
    (bindFifth D J I nu).fifthCorrectionIntegral_eq_integrals ha hab

/-- The actual fourth-to-fifth finite density charge is this cell sum,
once, on the original historical third parent and rough carrier. -/
theorem bound_actual_policy_charge (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (hab : D.a ≤ D.b)
    (hD : D.levelCheck = true) (hc : fifthChecks D J I nu)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) :
    (bindFifth D J I nu).p4aPolicyDensity
        ((bindFifth D J I nu).upperFifthPolicy (N : ℝ)) N cap
        ((N : ℝ) ^ (D.b : ℝ)) =
      D.p4aPolicyDensity (D.upperThirdPolicy (N : ℝ)) N cap
          ((N : ℝ) ^ (D.b : ℝ)) -
        D.p4aFourthEntry N cap ((N : ℝ) ^ (D.b : ℝ)) -
          ∑ j ∈ D.cells5 ∩ J,
            (bindFifth D J I nu).fifthCellPrimeCorrection N cap j := by
  have h := (bindFifth D J I nu).p4a_fifth_density_eq_causal_cell_ledger
    hab (bound_levelCheck D J I nu hD hc) N cap hN
  exact h

/-- The selected actual fifth saving has precisely that integral endpoint.
The only eventual hypothesis covers enumeration of the unchanged carrier. -/
theorem bound_actual_saving_limit (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (nu : Label5 D → ℚ) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hD : D.levelCheck = true)
    (hc : fifthChecks D J I nu) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ))
        ((bindFifth D J I nu).level5 (N : ℝ))
        N (cap N) ((N : ℝ) ^ (D.b : ℝ)) *
          Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (bindFifth D J I nu).fifthCorrectionIntegral) := by
  exact (bindFifth D J I nu).tendsto_actualHistoricalFifthSaving
    ha hab hold (bound_levelCheck D J I nu hD hc) cap hcap

end
end ImbalancedChen.P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly
