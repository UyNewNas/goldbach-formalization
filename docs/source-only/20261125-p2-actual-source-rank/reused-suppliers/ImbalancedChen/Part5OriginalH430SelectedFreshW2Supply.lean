import ImbalancedChen.Part5OriginalH430W2DiscardedMass
import ImbalancedChen.Part5OriginalH430SelectedBankCarrierSupply

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Apply the elementary W2 deletion to the concrete selected Member families.
The old bank error and the deletion each use epsilon/2. No 12+epsilon
mass bound is introduced: nonnegative coefficients are only removed.
The output concerns strict fresh TUPLE rows, not yet a production-child
reindexing, a selected-count identity, a scalar bank/base licence or h34.
-/
namespace ImbalancedChen.Part5OriginalH430SelectedFreshW2Supply

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalBuchstabActualRowLimits
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles Part5OriginalH430LiteralBankBudget
open Part5OriginalH430BankSlotTargets Part5OriginalH430SelectedBankGeometry
open Part5OriginalH430SelectedBankCarrierSupply
open Part5OriginalH430W2DiscardedCarriers Part5OriginalH430W2DiscardedMass

abbrev w2Family (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (j : Fin 36) :=
  bankFamily N n mesh tau c g (slotOfAction (.inr j))

abbrev w2Theta (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (j : Fin 36) :=
  bankTheta N n mesh tau c g sigma (slotOfAction (.inr j))

def freshPointError (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (g : Fin 430) : ℝ :=
  ∑ b : RowAtom, |freshRow N Q L d j b-thetaAtom N Q d*idealRow (.inr j) b| *
    |oldAtomValue (precedingH g) (precedingh g) b|

theorem freshPointError_nonneg (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (g : Fin 430) :
    0 ≤ freshPointError N Q L d j g :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem freshPointError_le (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (g : Fin 430) :
    freshPointError N Q L d j g ≤ rowGap N Q L d j g + pointError N Q L d g (.inr j) := by
  unfold freshPointError rowGap pointError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  have hh := abs_sub_le (freshRow N Q L d j b) (arithmeticRow N Q L d (.inr j) b)
    (thetaAtom N Q d*idealRow (.inr j) b)
  rw [abs_sub_comm (freshRow N Q L d j b) (arithmeticRow N Q L d (.inr j) b)] at hh
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hh
    (abs_nonneg (oldAtomValue (precedingH g) (precedingh g) b))

def w2FreshError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (j : Fin 36) : ℝ :=
  ∑ h ∈ w2Family N n mesh tau c g j, sigma h *
    freshPointError N (cellQ N n c) (labelResidual n c h) (labelPrefix h) j (g h)

def w2FreshRow (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (j : Fin 36) (b : RowAtom) : ℝ :=
  ∑ h ∈ w2Family N n mesh tau c g j, sigma h *
    freshRow N (cellQ N n c) (labelResidual n c h) (labelPrefix h) j b

/-- Parent support is taken from the existing U3/U4 Member constructor;
no new caller-supplied analytic error bound or arbitrary floor is added. -/
theorem uniform_selected_W2_freshTuples {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ g : Label N mesh → Fin 430,
      ∀ sigma : Label N mesh → ℝ, ∀ j : Fin 36,
      (∀ h ∈ w2Family N n mesh tau c g j, 0 ≤ sigma h) →
      w2FreshError N n mesh tau c g sigma j ≤ epsilon*w2Theta N n mesh tau c g sigma j ∧
      (∀ b, 0 ≤ w2FreshRow N n mesh tau c g sigma j b) ∧
      (∑ b : RowAtom, w2FreshRow N n mesh tau c g sigma j b) ≤
        12*w2Theta N n mesh tau c g sigma j ∧
      (w2Theta N n mesh tau c g sigma j = 0 →
        w2FreshError N n mesh tau c g sigma j = 0 ∧
        ∀ b, w2FreshRow N n mesh tau c g sigma j b = 0) := by
  obtain ⟨Tr,hTr⟩ := uniform_selected_bank_carriers (by positivity : (0:ℝ) < epsilon/2)
  obtain ⟨Te,hTe4,hTe⟩ := uniform_W2_rowGap frozenResidualFloor_pos
    (by positivity : (0:ℝ) < epsilon/2)
  refine ⟨max 4 (max Tr Te), ?_⟩
  intro N hN n mesh tau ht ht' hn c g sigma j hsigma
  let S := w2Family N n mesh tau c g j
  let Q := cellQ N n c
  let k := slotOfAction (.inr j)
  have hN1 : 1 < N := by omega
  have hf (h : Label N mesh) (hh : h ∈ S) :=
    cell_history_support hN1 ht ht' hn (mem_bankFamily.mp hh).1
  have hdN (h : Label N mesh) (hh : h ∈ S) : labelPrefix h ≤ N := by
    have hw := (hf h hh).1
    exact_mod_cast hw.2.2.1.le.trans hw.2.2.2.1
  have hg (h : Label N mesh) (hh : h ∈ S) :=
    hTe N (by omega) Q (labelResidual n c h) (labelPrefix h)
      (hf h hh).2.2.1 (parent_level_le_one (hf h hh).1)
      (hf h hh).1.2.1 (hdN h hh) (hf h hh).2.2.2.2.2 j (g h)
  have hraw := hTr N (by omega) n mesh tau ht ht' hn c g sigma k hsigma
  have hgap : (∑ h ∈ S, sigma h * rowGap N Q (labelResidual n c h) (labelPrefix h) j (g h)) ≤
      (epsilon/2)*w2Theta N n mesh tau c g sigma j := by
    calc
      _ ≤ ∑ h ∈ S, sigma h*((epsilon/2)*thetaAtom N Q (labelPrefix h)) :=
        Finset.sum_le_sum (fun h hh => mul_le_mul_of_nonneg_left (hg h hh).1 (hsigma h hh))
      _ = _ := by
        change _ = (epsilon/2)*parentTheta N Q S labelPrefix sigma
        rw [parentTheta, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        ring
  have herr : w2FreshError N n mesh tau c g sigma j ≤ epsilon*w2Theta N n mesh tau c g sigma j := by
    have hc : w2FreshError N n mesh tau c g sigma j ≤
        (∑ h ∈ S, sigma h * rowGap N Q (labelResidual n c h) (labelPrefix h) j (g h)) +
        bankError N n mesh tau c g sigma k := by
      change (∑ h ∈ S, _) ≤ _ + ∑ h ∈ S, _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro h hh
      simpa only [k, action_slot, mul_add] using mul_le_mul_of_nonneg_left
        (freshPointError_le N Q (labelResidual n c h) (labelPrefix h) j (g h)) (hsigma h hh)
    have hr := hraw.1
    change bankError N n mesh tau c g sigma k ≤ (epsilon/2)*w2Theta N n mesh tau c g sigma j at hr
    linarith
  have hrow (b : RowAtom) : 0 ≤ w2FreshRow N n mesh tau c g sigma j b ∧
      w2FreshRow N n mesh tau c g sigma j b ≤ bankRow N n mesh tau c g sigma k b := by
    constructor
    · exact Finset.sum_nonneg (fun h hh => mul_nonneg (hsigma h hh) ((hg h hh).2 b).1)
    · change (∑ h ∈ S, _) ≤ ∑ h ∈ S, _
      apply Finset.sum_le_sum
      intro h hh
      simpa only [k, action_slot] using mul_le_mul_of_nonneg_left ((hg h hh).2 b).2 (hsigma h hh)
  have hmass : (∑ b : RowAtom, w2FreshRow N n mesh tau c g sigma j b) ≤
      12*w2Theta N n mesh tau c g sigma j :=
    (Finset.sum_le_sum (fun b _ => (hrow b).2)).trans hraw.2.2.2.1
  refine ⟨herr, fun b => (hrow b).1, hmass, ?_⟩
  intro hz
  constructor
  · apply le_antisymm (by simpa only [hz, mul_zero] using herr)
    exact Finset.sum_nonneg (fun h hh => mul_nonneg (hsigma h hh) (freshPointError_nonneg _ _ _ _ _ _))
  · intro b
    have hb := Finset.single_le_sum (fun a _ => (hrow a).1) (Finset.mem_univ b)
    exact le_antisymm ((hb.trans hmass).trans_eq (by rw [hz, mul_zero])) (hrow b).1

/-- Aggregate only selected W2 slots and preserve each root cell's own Q. -/
theorem uniform_selected_outer_W2_freshTuples {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ g : Label N mesh → Fin 430, ∀ sigma : Label N mesh → ℝ,
      (∀ h ∈ readyCatalog N n mesh tau, 0 ≤ sigma h) →
      (∑ c : RootCode n, ∑ j : Fin 36, w2FreshError N n mesh tau c g sigma j) ≤
      epsilon*(∑ c : RootCode n, ∑ j : Fin 36, w2Theta N n mesh tau c g sigma j) := by
  obtain ⟨T,hT⟩ := uniform_selected_W2_freshTuples he
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
end ImbalancedChen.Part5OriginalH430SelectedFreshW2Supply
