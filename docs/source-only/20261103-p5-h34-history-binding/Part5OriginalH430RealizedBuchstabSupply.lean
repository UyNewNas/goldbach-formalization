import ImbalancedChen.Part5OriginalH430SameQHistoryCells

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Apply the existing interior+ceiling estimates to the constructed finite
integer Member catalog. ParentWindow, residual/word dictionary, common
positive floor and same-Q grouping are supplied by the preceding modules.
No new limit or error estimate is assumed. The actual count-source identity,
ordinary/switched bases and common smooth 441 realization remain open.
-/
namespace ImbalancedChen.Part5OriginalH430RealizedBuchstabSupply

noncomputable section
open Set
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry P2OriginalChildPhysicalNormalization
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430BuchstabArithmeticRows Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalBuchstabImmutable430Budget Part5OriginalBuchstabRowMass

/-- Every old-array read is one of the literal seed-only predecessors.
Assigning its ORIGINAL causal generation remains the count-source task. -/
def cellError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (sigma : Label N mesh → ℝ) (g : Label N mesh → Fin 430) : ℝ :=
  ∑ h ∈ cellFamily N n mesh tau c, sigma h *
    strictAbsoluteError (labelNode n tau h).upper N (cellQ N n c)
      (labelNode n tau h).physical.ceiling (labelWord h) (labelNode n tau h).physical
      (precedingH (g h)) (precedingh (g h))

def cellMass (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (sigma : Label N mesh → ℝ) : ℝ :=
  ∑ h ∈ cellFamily N n mesh tau c, sigma h *
    ∑ b : RowAtom, strictRow (labelNode n tau h).upper N (cellQ N n c)
      (labelNode n tau h).physical.ceiling (labelWord h) (labelNode n tau h).physical b

def cellTheta (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (sigma : Label N mesh → ℝ) : ℝ :=
  parentTheta N (cellQ N n c) (cellFamily N n mesh tau c)
    (fun h => parentProduct (labelWord h)) sigma

theorem cellError_nonneg {N n mesh : ℕ} (tau : ℝ) (c : RootCode n)
    (sigma : Label N mesh → ℝ) (g : Label N mesh → Fin 430)
    (hsigma : ∀ h ∈ cellFamily N n mesh tau c, 0 ≤ sigma h) :
    0 ≤ cellError N n mesh tau c sigma g :=
  Finset.sum_nonneg (fun h hh => mul_nonneg (hsigma h hh)
    (strictAbsoluteError_nonneg _ _ _ _ _ _ _ _))

/-- One threshold BEFORE N, root precision n, physical mesh, cell,
positive marks and all430 predecessor assignments. Local arithmetic
uniformity is NOT a proof of the required nested smooth refinement. -/
theorem uniform_realized_cells {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ sigma : Label N mesh → ℝ,
      ∀ g : Label N mesh → Fin 430,
      (∀ h ∈ cellFamily N n mesh tau c, 0 ≤ sigma h) →
      cellError N n mesh tau c sigma g ≤ epsilon*cellTheta N n mesh tau c sigma ∧
      (0 ≤ cellMass N n mesh tau c sigma ∧
        cellMass N n mesh tau c sigma ≤ 5*cellTheta N n mesh tau c sigma) ∧
      (cellTheta N n mesh tau c sigma = 0 →
        cellError N n mesh tau c sigma g = 0 ∧ cellMass N n mesh tau c sigma = 0) := by
  obtain ⟨Te, hTe⟩ := immutable430_uniform_buchstab_rows frozenResidualFloor_pos he
  obtain ⟨Tm, hTm⟩ := uniform_labelled_row_mass frozenResidualFloor_pos
  refine ⟨max 4 (max Te Tm), ?_⟩
  intro N hN n mesh tau htau htauhi hn c sigma g hsigma
  have hN1 : 1 < N := by omega
  have hf (h : Label N mesh) (hh : h ∈ cellFamily N n mesh tau c) :=
    cell_history_support hN1 htau htauhi hn hh
  have hg (h : Label N mesh) (hh : h ∈ cellFamily N n mesh tau c) :
      directionGuard (labelNode n tau h).upper (labelNode n tau h).physical :=
    (mem_cellFamily.mp hh).1.2
  have herr := hTe N (by omega) (cellQ N n c) (cellFamily N n mesh tau c)
    labelWord (fun h => (labelNode n tau h).physical)
    (fun h => (labelNode n tau h).physical.ceiling) sigma
    (fun h => (labelNode n tau h).upper) g
    (fun h hh => (hf h hh).1)
    (fun h hh => (hf h hh).2.1) (fun _ _ => rfl)
    (fun h hh => (hf h hh).2.2.2.1.1) hg hsigma
    (fun h hh => (hf h hh).2.2.1)
  have hmass := hTm N (by omega) (cellQ N n c) (cellFamily N n mesh tau c)
    labelWord (fun h => (labelNode n tau h).physical)
    (fun h => (labelNode n tau h).physical.ceiling) sigma
    (fun h => (labelNode n tau h).upper)
    (fun h hh => (hf h hh).1)
    (fun h hh => (hf h hh).2.1) (fun _ _ => rfl)
    (fun h hh => (hf h hh).2.2.2.1.1) hg hsigma
    (fun h hh => (hf h hh).2.2.1)
  change cellError N n mesh tau c sigma g ≤ epsilon*cellTheta N n mesh tau c sigma at herr
  change 0 ≤ cellMass N n mesh tau c sigma ∧
    cellMass N n mesh tau c sigma ≤ 5*cellTheta N n mesh tau c sigma at hmass
  refine ⟨herr, hmass, ?_⟩
  intro hz
  constructor
  · exact le_antisymm (by simpa only [hz, mul_zero] using herr)
      (cellError_nonneg tau c sigma g hsigma)
  · exact le_antisymm (by simpa only [hz, mul_zero] using hmass.2) hmass.1

/-- This is a sum of DIFFERENT cell normalizers, not a false single-Q
Theta for every root prime. It is exactly the original labelled sum. -/
def totalCellTheta (N n mesh : ℕ) (tau : ℝ) (sigma : Label N mesh → ℝ) : ℝ :=
  ∑ h ∈ readyCatalog N n mesh tau, sigma h *
    thetaAtom N (rootQ N n h.2.1 tau h.2.2.1.val) (parentProduct (labelWord h))

theorem sum_cellTheta (N n mesh : ℕ) (tau : ℝ) (sigma : Label N mesh → ℝ) :
    (∑ c : RootCode n, cellTheta N n mesh tau c sigma) =
      totalCellTheta N n mesh tau sigma := by
  unfold cellTheta
  simp_rw [cell_Theta_exact]
  exact sum_cellFamily N n mesh tau _

/-- Finite outer aggregation keeps the same pre-N threshold and pays
absolute errors before cancellation. This is not the missing native
outer integral / count-source identification. -/
theorem uniform_outer_buchstab_supply {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ sigma : Label N mesh → ℝ, ∀ g : Label N mesh → Fin 430,
      (∀ h ∈ readyCatalog N n mesh tau, 0 ≤ sigma h) →
      (∑ c : RootCode n, cellError N n mesh tau c sigma g) ≤
        epsilon*totalCellTheta N n mesh tau sigma ∧
      (∑ c : RootCode n, cellMass N n mesh tau c sigma) ≤
        5*totalCellTheta N n mesh tau sigma := by
  obtain ⟨T, hT⟩ := uniform_realized_cells he
  refine ⟨T, ?_⟩
  intro N hN n mesh tau htau htauhi hn sigma g hsigma
  have hs (c : RootCode n) (h : Label N mesh)
      (hh : h ∈ cellFamily N n mesh tau c) : 0 ≤ sigma h :=
    hsigma h (Finset.mem_filter.mp hh).1
  have hc (c : RootCode n) := hT N hN n mesh tau htau htauhi hn c sigma g (hs c)
  constructor
  · calc
      _ ≤ ∑ c : RootCode n, epsilon*cellTheta N n mesh tau c sigma :=
        Finset.sum_le_sum (fun c _ => (hc c).1)
      _ = _ := by rw [← Finset.mul_sum, sum_cellTheta]
  · calc
      _ ≤ ∑ c : RootCode n, 5*cellTheta N n mesh tau c sigma :=
        Finset.sum_le_sum (fun c _ => (hc c).2.1.2)
      _ = _ := by rw [← Finset.mul_sum, sum_cellTheta]

end
end ImbalancedChen.Part5OriginalH430RealizedBuchstabSupply
