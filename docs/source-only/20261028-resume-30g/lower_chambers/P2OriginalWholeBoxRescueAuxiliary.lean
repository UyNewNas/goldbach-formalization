import ImbalancedChen.P2OriginalIdealTentCanonicalScreen
import ImbalancedChen.ActualSelectedSubproductParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original Gamma_B rescue is max(A,W), with physical level Gamma_B-2e.
Its arithmetic auxiliary level is a different, larger number. A whole-box
dichotomy chooses ONE source and ONE auxiliary level before any fine tuple.
In the W case the designated gate may exceed the physical cap. It is the
auxiliary level, not an invented tent support mask, which pays that gate.
The repaired greedy allocation and distribution theorem are not asserted.
-/

namespace ImbalancedChen.P2OriginalWholeBoxRescueAuxiliary

noncomputable section
open scoped Classical
open P2OriginalLowerSelectedCapConstructor (Code)
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalPairSourceReceiver

def A (t : ℝ) : ℝ := (1 + t) / 2
def W (t : ℝ) : ℝ := 153 / 256 - 3 * t / 8

-- The independent coordinates attaining these two infima can be used
-- simultaneously. Hence this really is the closed-box infimum of max(A,W).
def rescueFloor (R : PairRange) {mesh : ℕ} (code : Code mesh) : ℚ :=
  max ((1 + qLo R mesh (code 0).1) / 2)
    (153 / 256 - 3 * qHi R mesh (code 2).1 / 8)

def physical (R : PairRange) {mesh : ℕ} (code : Code mesh) (e : ℚ) : ℚ :=
  rescueFloor R code - 2 * e

theorem rescueFloor_cast (R : PairRange) {mesh : ℕ} (code : Code mesh) :
    (rescueFloor R code : ℝ) =
      max (A (qLo R mesh (code 0).1)) (W (qHi R mesh (code 2).1)) := by
  unfold rescueFloor A W
  push_cast <;> rfl

theorem rescueFloor_le_endpoint (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (x : Fin 5 → ℝ) (hx : inBox (box R code) x) :
    (rescueFloor R code : ℝ) ≤ max (A (x 0)) (W (x 2)) := by
  rw [rescueFloor_cast]
  apply max_le_max
  · have h := (hx 0).1
    dsimp [box, A] at *
    linarith
  · have h := (hx 2).2
    dsimp [box, W] at *
    linarith

theorem rescueFloor_attained (R : PairRange) {mesh : ℕ}
    (code : Code mesh)
    (hne : ∀ i, (qLo R mesh (code i).1 : ℝ) ≤ qHi R mesh (code i).1) :
    ∃ x : Fin 5 → ℝ, inBox (box R code) x ∧
      max (A (x 0)) (W (x 2)) = (rescueFloor R code : ℝ) := by
  let x : Fin 5 → ℝ := fun i =>
    if i = 2 then qHi R mesh (code i).1 else qLo R mesh (code i).1
  refine ⟨x, ?_, ?_⟩
  · intro i
    by_cases hi : i = 2
    · simpa [x, hi, box] using And.intro (hne i) (le_refl (qHi R mesh (code i).1 : ℝ))
    · simpa [x, hi, box] using And.intro (le_refl (qLo R mesh (code i).1 : ℝ)) (hne i)
  · simp [x, rescueFloor_cast]

-- These are the TWO original u-v constraints, with the moving residue
-- alpha=1+3*kappa and spectral exponent 7/32. Both are retained in the min.
theorem W_third_slot_reserve (z theta e kappa : ℝ)
    (hz : 0 ≤ z) (he : 0 ≤ e) (hk : kappa ≤ e)
    (hend : theta + e ≤ W z) :
    (235 / 96 : ℝ) * e ≤
      actualSelectedSubproductUpper (1 + 3 * kappa) theta - (2 * theta - 1) - z := by
  have hfirst : (235 / 96 : ℝ) * e ≤
      (32 - 39 * theta) / 34 - (2 * theta - 1) - z := by
    dsimp [W] at hend
    linarith
  have hsecond : (235 / 96 : ℝ) * e ≤
      (2 - 2 * theta - 7 * (1 + 3 * kappa) / 32) / 3 - (2 * theta - 1) - z := by
    dsimp [W] at hend
    linarith
  unfold actualSelectedSubproductUpper
  have hm : (235 / 96 : ℝ) * e + (2 * theta - 1) + z ≤
      min ((32 - 39 * theta) / 34)
        ((2 - 2 * theta - 7 * (1 + 3 * kappa) / 32) / 3) :=
    le_min (by linarith) (by linarith)
  linarith

theorem W_other_initial_square_reserve (b theta : ℝ)
    (hb : b ≤ 25 / 128) (htheta : theta ≤ 153 / 256) :
    (3 / 256 : ℝ) ≤ 1 - theta - 2 * b := by linarith

private theorem singleton_tent_eq_A (t : ℝ) (ht : t ≤ 25 / 128) :
    VariableEnvelope.v t = A t := by
  rw [VariableEnvelope.v_eq_min]
  change min ((1 + t) / 2) (57 / 64 - 3 * t / 2) = (1 + t) / 2
  apply min_eq_left
  linarith

-- This is the precise original case(ii) estimate. The one box-wide
-- decision uses only A at its lower endpoint, never the individual tuple.
theorem W_case_whole_box (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (e : ℚ) (he : 0 < e)
    (hwidth : (qHi R mesh (code 0).1 : ℝ) - qLo R mesh (code 0).1 < (e : ℝ) / 10)
    (hcase : A (qLo R mesh (code 0).1) < (physical R code e : ℝ) + e / 2)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x) :
    (9 : ℝ) * e / 20 ≤ (physical R code e : ℝ) + e - A (x 0) ∧
      (physical R code e : ℝ) + 2 * e ≤ W (x 2) := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hphys : (physical R code e : ℝ) = (rescueFloor R code : ℝ) - 2 * e := by
    unfold physical
    push_cast <;> rfl
  have hA : A (x 0) < (physical R code e : ℝ) + 11 * e / 20 := by
    have hxhi := (hx 0).2
    dsimp [box, A] at hxhi hcase ⊢
    linarith
  have hrescue := rescueFloor_le_endpoint R code x hx
  have hW : (physical R code e : ℝ) + 2 * e ≤ W (x 2) := by
    rw [hphys] at *
    rcases le_max_iff.mp hrescue with hleft | hright
    · exfalso
      linarith
    · linarith
  exact ⟨by linarith, hW⟩

-- One source for the ENTIRE actual box. The output is a parameter licence
-- at an explicitly chosen rational auxiliary level, not a successful
-- selector, an arithmetic factorization or full adopted-bank coverage.
theorem original_rescue_auxiliary_dichotomy (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (e : ℚ) (he : 0 < e)
    (hwidth : (qHi R mesh (code 0).1 : ℝ) - qLo R mesh (code 0).1 < (e : ℝ) / 10)
    (hfirst : (qHi R mesh (code 0).1 : ℝ) ≤ 25 / 128)
    (hthird : (0 : ℝ) ≤ qLo R mesh (code 2).1)
    (kappa : ℝ) (hkappa : kappa ≤ (e : ℝ) / 4) :
    (∀ x : Fin 5 → ℝ, inBox (box R code) x →
      (physical R code e : ℝ) + e / 4 + e / 8 ≤
        actualSelectedSubproductV (1 + 3 * kappa) (x 0)) ∨
    (∀ x : Fin 5 → ℝ, inBox (box R code) x → x 1 ≤ 25 / 128 →
      (9 : ℝ) * e / 20 ≤ (physical R code e : ℝ) + e - A (x 0) ∧
      (3 / 256 : ℝ) ≤ 1 - ((physical R code e : ℝ) + e) - 2 * x 1 ∧
      (235 / 96 : ℝ) * e ≤
        actualSelectedSubproductUpper (1 + 3 * kappa) ((physical R code e : ℝ) + e) -
          (2 * ((physical R code e : ℝ) + e) - 1) - x 2) := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  by_cases hcase : (physical R code e : ℝ) + e / 2 ≤ A (qLo R mesh (code 0).1)
  · left
    intro x hx
    have hx0 : x 0 ≤ 25 / 128 := (hx 0).2.trans hfirst
    have hAlo : A (qLo R mesh (code 0).1) ≤ A (x 0) := by
      have h := (hx 0).1
      dsimp [box, A] at *
      linarith
    apply actualSelectedSubproductV_residue_margin heR.le hkappa
    rw [singleton_tent_eq_A _ hx0]
    linarith
  · right
    intro x hx hx1
    obtain ⟨hgate, hend⟩ := W_case_whole_box R code e he hwidth (lt_of_not_ge hcase) x hx
    have hx2 : 0 ≤ x 2 := hthird.trans (hx 2).1
    have htheta : (physical R code e : ℝ) + e ≤ 153 / 256 := by
      dsimp [W] at hend
      linarith
    exact ⟨hgate, W_other_initial_square_reserve _ _ hx1 htheta,
      W_third_slot_reserve _ _ _ _ hx2 heR.le (by linarith) (by linarith)⟩

end
end ImbalancedChen.P2OriginalWholeBoxRescueAuxiliary
