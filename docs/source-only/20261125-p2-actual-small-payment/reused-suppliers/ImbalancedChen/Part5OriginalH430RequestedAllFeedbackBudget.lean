import ImbalancedChen.Part5OriginalH430RequestedAllChoice

/-!
Manuscript-local uniform selected-feedback level supplier.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The 106 possible bank actions, two Buchstab polarities and retention are
NOT alternative charges for the same occurrence. The exact selected-choice
partition in RequestedAllChoice prevents this: this supplier sums only
selected bank and Buchstab positions; retention is paid by the exact old
cell identity. Its row mass is bounded by 12*Theta (not 12+5).
No U3/U4 count-source identity, base/seed comparison or h34 is assumed.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedAllFeedbackBudget

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPrimeChildCarriers P2OriginalChildPhysicalNormalization
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLocalBankSupply
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedNonbankLevel
open Part5OriginalH430RequestedAllChoice

/-- Only actual bank winners and actual Buchstab winners have
coefficientwise feedback errors. Retention is an exact old-cell read. -/
def combinedTheta (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  (∑ a : Original106Action, levelTheta N n root tau p g a) +
    buchstabLevelTheta N n root tau p g

def combinedError (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  (∑ a : Original106Action, levelError N n root tau p g a) +
    buchstabLevelError N n root tau p g

def combinedRow (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (b : RowAtom) : ℝ :=
  (∑ a : Original106Action, levelRow N n root tau p g a b) +
    buchstabLevelRow N n root tau p g b

/-- Nonnegative error is a sum of absolute coefficient errors with the
actual positive path marks, never a signed cancellation estimate. -/
theorem combinedError_nonneg (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : 0 ≤ combinedError N n root tau p g := by
  unfold combinedError
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro a _
    unfold levelError
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (mark_pos _).le (requestError_nonneg _ _ _ _ _)
  · unfold buchstabLevelError
    apply Finset.sum_nonneg
    intro l _
    apply mul_nonneg (mark_pos _).le
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- The same pre-N threshold covers every root kind, precision, prime,
generation and actual winner. No 106-fold or 17-Theta loss: the same list
position cannot be selected by two different choices. The conclusion
remains a coefficient-row statement, not a closed-cell count inequality. -/
theorem uniform_combined_feedback {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ n : ℕ, ∀ root : Root,
      ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
      physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        combinedError N n root tau p g ≤
          epsilon * combinedTheta N n root tau p g ∧
        (∀ b : RowAtom, 0 ≤ combinedRow N n root tau p g b) ∧
        (∑ b : RowAtom, combinedRow N n root tau p g b) ≤
          12 * combinedTheta N n root tau p g ∧
        (combinedTheta N n root tau p g = 0 →
          combinedError N n root tau p g = 0 ∧
          ∀ b : RowAtom, combinedRow N n root tau p g b = 0) := by
  obtain ⟨Tb,hTb,hBank⟩ := uniform_level_bank_supply he
  obtain ⟨Tu,hTu,hBuch⟩ := uniform_level_buchstab_supply he
  refine ⟨max Tb Tu,hTb.trans (le_max_left _ _),?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have hNbank : Tb ≤ N := (le_max_left _ _).trans hN
  have hNb : Tu ≤ N := (le_max_right _ _).trans hN
  have hbank (a : Original106Action) :=
    hBank N hNbank n root tau ht ht' hn p hp hband g a
  have hbuch := hBuch N hNb n root tau ht ht' hn p hp hband g
  have hbankErr :
      (∑ a : Original106Action, levelError N n root tau p g a) ≤
        epsilon * (∑ a : Original106Action, levelTheta N n root tau p g a) := by
    calc
      _ ≤ ∑ a : Original106Action, epsilon * levelTheta N n root tau p g a :=
        Finset.sum_le_sum (fun a _ => (hbank a).1)
      _ = _ := by rw [Finset.mul_sum]
  have hbankMass :
      (∑ b : RowAtom, ∑ a : Original106Action, levelRow N n root tau p g a b) ≤
        12 * (∑ a : Original106Action, levelTheta N n root tau p g a) := by
    calc
      _ = ∑ a : Original106Action, ∑ b : RowAtom, levelRow N n root tau p g a b :=
        Finset.sum_comm
      _ ≤ ∑ a : Original106Action, 12 * levelTheta N n root tau p g a :=
        Finset.sum_le_sum (fun a _ => (hbank a).2.2.2.1)
      _ = _ := by rw [Finset.mul_sum]
  have hbuchTheta : 0 ≤ buchstabLevelTheta N n root tau p g := by
    have hm0 : 0 ≤ ∑ b : RowAtom, buchstabLevelRow N n root tau p g b :=
      Finset.sum_nonneg (fun b _ => hbuch.2.1 b)
    have hm5 := hbuch.2.2.1
    linarith
  have heAll : combinedError N n root tau p g ≤
      epsilon * combinedTheta N n root tau p g := by
    change (∑ a : Original106Action, levelError N n root tau p g a) +
        buchstabLevelError N n root tau p g ≤
      epsilon * ((∑ a : Original106Action, levelTheta N n root tau p g a) +
        buchstabLevelTheta N n root tau p g)
    calc
      _ ≤ epsilon * (∑ a : Original106Action, levelTheta N n root tau p g a) +
          epsilon * buchstabLevelTheta N n root tau p g :=
        add_le_add hbankErr hbuch.1
      _ = _ := by ring
  have hrow (b : RowAtom) : 0 ≤ combinedRow N n root tau p g b := by
    change 0 ≤ (∑ a : Original106Action, levelRow N n root tau p g a b) +
      buchstabLevelRow N n root tau p g b
    exact add_nonneg
      (Finset.sum_nonneg (fun a _ => (hbank a).2.2.1 b)) (hbuch.2.1 b)
  have hmAll : (∑ b : RowAtom, combinedRow N n root tau p g b) ≤
      12 * combinedTheta N n root tau p g := by
    change (∑ b : RowAtom,
      (∑ a : Original106Action, levelRow N n root tau p g a b) +
        buchstabLevelRow N n root tau p g b) ≤
      12 * ((∑ a : Original106Action, levelTheta N n root tau p g a) +
        buchstabLevelTheta N n root tau p g)
    rw [Finset.sum_add_distrib]
    calc
      _ ≤ 12 * (∑ a : Original106Action, levelTheta N n root tau p g a) +
        5 * buchstabLevelTheta N n root tau p g :=
          add_le_add hbankMass hbuch.2.2.1
      _ ≤ _ := by linarith [hbuchTheta]
  refine ⟨heAll,hrow,hmAll,?_⟩
  intro hz
  constructor
  · exact le_antisymm (by simpa only [hz,mul_zero] using heAll)
      (combinedError_nonneg N n root tau p g)
  · intro b
    have hb := Finset.single_le_sum (fun c _ => hrow c) (Finset.mem_univ b)
    exact le_antisymm (by simpa only [hz,mul_zero] using hb.trans hmAll) (hrow b)

end
end ImbalancedChen.Part5OriginalH430RequestedAllFeedbackBudget
