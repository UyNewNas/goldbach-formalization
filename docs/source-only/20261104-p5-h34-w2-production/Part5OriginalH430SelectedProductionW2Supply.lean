import ImbalancedChen.Part5OriginalH430W2ProductionRows
import ImbalancedChen.Part5OriginalH430SelectedFreshW2Supply

/-!
SOURCE ONLY / UNCOMPILED.

Transport the already-paid W2 fresh-tuple estimates along EXACT production
row equalities. The selected owner and frozen Member supply all geometric
premises. There is no additional epsilon charge, row-norm inflation, new
external analytic proof, or assumption of a count defect. Full original
selected-count generation/mark/filter assignment and common441 remain open.
-/
namespace ImbalancedChen.Part5OriginalH430SelectedProductionW2Supply

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430SameQHistoryCells
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles Part5OriginalH430LiteralBankBudget
open Part5OriginalH430BankSlotTargets Part5OriginalH430SelectedBankGeometry
open Part5OriginalH430SelectedBankCarrierSupply Part5OriginalH430SelectedFreshW2Supply
open Part5OriginalH430W2DiscardedCarriers Part5OriginalH430W2ProductionRows

/-- The formerly independent target/ceiling premise is now derived from
the actual selected owner, not assumed on a generic marked source. -/
theorem selected_production_geometry {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {j : Fin 36} {h : Label N mesh}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ w2Family N n mesh tau c g j) :
    parentWindow N (cellQ N n c) (labelWord h) (labelNode n tau h).physical.ceiling ∧
    residual (labelNode n tau h).physical = labelResidual n c h ∧
    labelResidual n c h/(originalW2At j).s ≤ (labelNode n tau h).physical.ceiling := by
  have hs := cell_history_support hN ht ht' hn (mem_bankFamily.mp hh).1
  have hp := selected_parent_tests hN ht ht' hn hh
  have hceil : residual (labelNode n tau h).physical/(originalW2At j).s ≤
      (labelNode n tau h).physical.ceiling := by
    simpa only [action_slot, actionTarget] using hp.2.2
  rw [hs.2.1] at hceil
  exact ⟨hs.1,hs.2.1,hceil⟩

theorem selected_productionRow_eq {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {j : Fin 36} {h : Label N mesh}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ w2Family N n mesh tau c g j) (a : RowAtom) :
    productionRow N (cellQ N n c) (labelWord h) (labelNode n tau h).physical j a =
      freshRow N (cellQ N n c) (labelResidual n c h) (labelPrefix h) j a := by
  have hs := selected_production_geometry hN ht ht' hn hh
  exact productionRow_eq_freshRow hs.1 hs.2.1 j hs.2.2 a

def productionPointError (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (j : Fin 36) (g : Fin 430) : ℝ :=
  ∑ a : RowAtom, |productionRow N Q old p j a-
      thetaAtom N Q (parentProduct old)*idealRow (.inr j) a| *
    |oldAtomValue (precedingH g) (precedingh g) a|

def w2ProductionError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (j : Fin 36) : ℝ :=
  ∑ h ∈ w2Family N n mesh tau c g j, sigma h *
    productionPointError N (cellQ N n c) (labelWord h) (labelNode n tau h).physical j (g h)

def w2ProductionRow (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (j : Fin 36) (a : RowAtom) : ℝ :=
  ∑ h ∈ w2Family N n mesh tau c g j, sigma h *
    productionRow N (cellQ N n c) (labelWord h) (labelNode n tau h).physical j a

theorem w2ProductionError_eq {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {sigma : Label N mesh → ℝ} {j : Fin 36}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    w2ProductionError N n mesh tau c g sigma j = w2FreshError N n mesh tau c g sigma j := by
  unfold w2ProductionError w2FreshError
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun e : ℝ => sigma h*e)
  unfold productionPointError freshPointError
  apply Finset.sum_congr rfl
  intro a _
  rw [selected_productionRow_eq hN ht ht' hn hh]

theorem w2ProductionRow_eq {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {sigma : Label N mesh → ℝ} {j : Fin 36}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (a : RowAtom) :
    w2ProductionRow N n mesh tau c g sigma j a = w2FreshRow N n mesh tau c g sigma j a := by
  unfold w2ProductionRow w2FreshRow
  apply Finset.sum_congr rfl
  intro h hh
  rw [selected_productionRow_eq hN ht ht' hn hh]

/-- One threshold before N and every later finite choice. Exact transport
uses the preceding error budget unchanged, including zero Theta. -/
theorem uniform_selected_W2_production {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ g : Label N mesh → Fin 430,
      ∀ sigma : Label N mesh → ℝ, ∀ j : Fin 36,
      (∀ h ∈ w2Family N n mesh tau c g j, 0 ≤ sigma h) →
      w2ProductionError N n mesh tau c g sigma j ≤ epsilon*w2Theta N n mesh tau c g sigma j ∧
      (∀ a, 0 ≤ w2ProductionRow N n mesh tau c g sigma j a) ∧
      (∑ a : RowAtom, w2ProductionRow N n mesh tau c g sigma j a) ≤
        12*w2Theta N n mesh tau c g sigma j ∧
      (w2Theta N n mesh tau c g sigma j = 0 →
        w2ProductionError N n mesh tau c g sigma j = 0 ∧
        ∀ a, w2ProductionRow N n mesh tau c g sigma j a = 0) := by
  obtain ⟨T,hT⟩ := uniform_selected_W2_freshTuples he
  refine ⟨max 2 T, ?_⟩
  intro N hN n mesh tau ht ht' hn c g sigma j hs
  have hN1 : 1 < N := by omega
  simpa only [w2ProductionError_eq hN1 ht ht' hn,
    w2ProductionRow_eq hN1 ht ht' hn] using
    hT N (by omega) n mesh tau ht ht' hn c g sigma j hs

/-- Signed profile error follows FROM coefficientwise absolute control;
no cancellation between different old-table atoms is used in reverse. -/
theorem production_profile_error_le (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (j : Fin 36) (g : Fin 430) :
    |productionProfile N Q old p j (precedingH g) (precedingh g) -
      thetaAtom N Q (parentProduct old)*idealProfile (precedingH g) (precedingh g) (.inr j)| ≤
      productionPointError N Q old p j g := by
  rw [← productionRow_value, ← Part5OriginalH430LiteralBankBudget.idealRow_value,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro a _
  have he : productionRow N Q old p j a*oldAtomValue (precedingH g) (precedingh g) a -
      thetaAtom N Q (parentProduct old)*
        (idealRow (.inr j) a*oldAtomValue (precedingH g) (precedingh g) a) =
      (productionRow N Q old p j a-thetaAtom N Q (parentProduct old)*idealRow (.inr j) a)*
        oldAtomValue (precedingH g) (precedingh g) a := by ring
  rw [he, abs_mul]

def w2ProductionAppliedError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (j : Fin 36) : ℝ :=
  ∑ h ∈ w2Family N n mesh tau c g j, sigma h *
    |productionProfile N (cellQ N n c) (labelWord h) (labelNode n tau h).physical j
        (precedingH (g h)) (precedingh (g h)) -
      thetaAtom N (cellQ N n c) (labelPrefix h)*
        idealProfile (precedingH (g h)) (precedingh (g h)) (.inr j)|

theorem w2ProductionAppliedError_le {N n mesh : ℕ} (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (j : Fin 36)
    (hs : ∀ h ∈ w2Family N n mesh tau c g j, 0 ≤ sigma h) :
    w2ProductionAppliedError N n mesh tau c g sigma j ≤
      w2ProductionError N n mesh tau c g sigma j := by
  apply Finset.sum_le_sum
  intro h hh
  exact mul_le_mul_of_nonneg_left (production_profile_error_le _ _ _ _ _ _) (hs h hh)

theorem uniform_selected_W2_production_applied {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ g : Label N mesh → Fin 430,
      ∀ sigma : Label N mesh → ℝ, ∀ j : Fin 36,
      (∀ h ∈ w2Family N n mesh tau c g j, 0 ≤ sigma h) →
      w2ProductionAppliedError N n mesh tau c g sigma j ≤
        epsilon*w2Theta N n mesh tau c g sigma j := by
  obtain ⟨T,hT⟩ := uniform_selected_W2_production he
  refine ⟨T, ?_⟩
  intro N hN n mesh tau ht ht' hn c g sigma j hs
  exact (w2ProductionAppliedError_le tau c g sigma j hs).trans
    (hT N hN n mesh tau ht ht' hn c g sigma j hs).1

/-- Only selected W2 alternatives are aggregated, and each root cell
retains its own Q. This is not the full native outer integral/count step. -/
theorem uniform_selected_outer_W2_production {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ g : Label N mesh → Fin 430, ∀ sigma : Label N mesh → ℝ,
      (∀ h ∈ readyCatalog N n mesh tau, 0 ≤ sigma h) →
      (∑ c : RootCode n, ∑ j : Fin 36, w2ProductionError N n mesh tau c g sigma j) ≤
        epsilon*(∑ c : RootCode n, ∑ j : Fin 36, w2Theta N n mesh tau c g sigma j) := by
  obtain ⟨T,hT⟩ := uniform_selected_W2_production he
  refine ⟨T, ?_⟩
  intro N hN n mesh tau ht ht' hn g sigma hs
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact (hT N hN n mesh tau ht ht' hn c g sigma j
    (fun h hh => hs h (Finset.mem_filter.mp (mem_bankFamily.mp hh).1).1)).1

end
end ImbalancedChen.Part5OriginalH430SelectedProductionW2Supply
