import ImbalancedChen.P5ZU11CanonicalSwitchedIntegrable
import ImbalancedChen.Part5U11H248MeasurableAdapter
import Mathlib.Tactic.FinCases

/-!
Actual adopted H248 range and the original U11 ordinary-kernel supplier.

The finite integer bounds below are source proofs about the serialized
200-entry table. They do not certify its feedback recurrence or any
averaged Rosser meaning. The closed-cell knot value is the adjacent
minimum. The proof retains those singleton seams and proves that at most
one scalar atom contributes. U11 uses H248 throughout; H430 is absent.

The remaining eligible-policy premise is the numerical consequence
L >= 2w. No square license or physical gate is invented or inferred from
this bound. Analytic source means and numerical quadrature remain open.
Status: source_written / uncompiled; no numeric replay was executed.
-/

namespace ImbalancedChen.P5Z.U11H248

open Set MeasureTheory
open Part5OriginalUpsilon5CausalDictionary
open Part5UpperTables
open U11Integral U11Canonical
open scoped BigOperators

noncomputable section

theorem grid_lt_iff (i j : ℕ) : floorGrid i < floorGrid j ↔ i < j := by
  constructor
  · intro h
    have hh : (i : ℝ) < (j : ℝ) := by dsimp [floorGrid] at h; linarith
    exact_mod_cast hh
  · intro h
    have hh : (i : ℝ) < (j : ℝ) := by exact_mod_cast h
    dsimp [floorGrid]
    linarith

theorem grid_injective : Function.Injective floorGrid := by
  intro i j hij
  have hh : (i : ℝ) = (j : ℝ) := by dsimp [floorGrid] at hij; linarith
  exact_mod_cast hh

/-- Open-cell atoms and singleton-knot atoms never double count a scalar
argument, including at the two guarded interval endpoints. -/
theorem upperAtom_unique {s : ℝ} {b c : FloorAtom}
    (hb : s ∈ upperAtomSet b) (hc : s ∈ upperAtomSet c) : b = c := by
  cases b with
  | inl i =>
    cases c with
    | inl j =>
      have hij : i.val < j.val + 1 := (grid_lt_iff _ _).mp (hb.2.1.trans hc.2.2)
      have hji : j.val < i.val + 1 := (grid_lt_iff _ _).mp (hc.2.1.trans hb.2.2)
      have heq : i.val = j.val := by omega
      exact congrArg Sum.inl (Fin.ext heq)
    | inr j =>
      have hs : s = floorGrid j.val := hc.2
      have hij : i.val < j.val := (grid_lt_iff _ _).mp (hb.2.1.trans_eq hs)
      have hji : j.val < i.val + 1 := (grid_lt_iff _ _).mp (hs.symm.trans_lt hb.2.2)
      omega
  | inr i =>
    cases c with
    | inl j =>
      have hs : s = floorGrid i.val := hb.2
      have hji : j.val < i.val := (grid_lt_iff _ _).mp (hc.2.1.trans_eq hs)
      have hij : i.val < j.val + 1 := (grid_lt_iff _ _).mp (hs.symm.trans_lt hc.2.2)
      omega
    | inr j =>
      have hi : s = floorGrid i.val := hb.2
      have hj : s = floorGrid j.val := hc.2
      exact congrArg Sum.inr (Fin.ext (grid_injective (hi.symm.trans hj)))

/-- This is finite literal data checking, without evaluation of any
analytic recurrence or use of a decision procedure as a trusted oracle. -/
theorem H248_numerator_bounds (i : Fin 200) :
    (0 : ℤ) ≤ H248Numerators i ∧ H248Numerators i ≤ (2 : ℤ) ^ 80 := by
  fin_cases i <;> norm_num [H248Numerators]

theorem H248_value_bounds (i : Fin 200) :
    (0 : ℝ) ≤ floorValue H248Numerators i ∧ floorValue H248Numerators i ≤ 1 := by
  have hl : (0 : ℝ) ≤ (H248Numerators i : ℝ) := by
    exact_mod_cast (H248_numerator_bounds i).1
  have hu : (H248Numerators i : ℝ) ≤ (2 ^ 80 : ℝ) := by
    exact_mod_cast (H248_numerator_bounds i).2
  have hd : (0 : ℝ) < 2 ^ 80 := by positivity
  refine ⟨div_nonneg hl hd.le, ?_⟩
  exact (div_le_iff₀ hd).2 (by simpa only [one_mul] using hu)

theorem H248_knot_bounds (j : Fin 201) :
    (0 : ℝ) ≤ floorKnotValue H248Numerators j ∧
      floorKnotValue H248Numerators j ≤ 1 := by
  unfold floorKnotValue
  split_ifs
  · exact H248_value_bounds _
  · exact H248_value_bounds _
  · exact ⟨le_min (H248_value_bounds _).1 (H248_value_bounds _).1,
      (min_le_left _ _).trans (H248_value_bounds _).2⟩

theorem H248_atom_bounds (b : FloorAtom) :
    (0 : ℝ) ≤ floorAtomValue H248Numerators b ∧
      floorAtomValue H248Numerators b ≤ 1 := by
  cases b with
  | inl i => exact H248_value_bounds i
  | inr j => exact H248_knot_bounds j

/-- Exact global range, including exterior zero values and all singleton
knots; no almost-everywhere seam deletion is needed. -/
theorem H248_bounds (s : ℝ) : 0 ≤ H248 s ∧ H248 s ≤ 1 := by
  by_cases hex : ∃ b : FloorAtom, s ∈ upperAtomSet b
  · obtain ⟨b, hb⟩ := hex
    have heq : H248 s = floorAtomValue H248Numerators b := by
      unfold H248 upperFloor
      calc
        _ = (upperAtomSet b).indicator (fun _ => floorAtomValue H248Numerators b) s := by
          apply Finset.sum_eq_single b
          · intro c hc hcb
            exact indicator_of_notMem (fun h => hcb (upperAtom_unique h hb)) _
          · intro h
            exact (h (Finset.mem_univ b)).elim
        _ = _ := indicator_of_mem hb _
    rw [heq]
    exact H248_atom_bounds b
  · have heq : H248 s = 0 := by
      unfold H248 upperFloor
      apply Finset.sum_eq_zero
      intro b hb
      exact indicator_of_notMem (fun h => hex ⟨b, h⟩) _
    rw [heq]
    exact ⟨le_rfl, zero_le_one⟩

theorem measurable_H248_max_two : Measurable (fun s : ℝ => H248 (max 2 s)) :=
  measurable_H248.comp (measurable_const.max measurable_id)

theorem H248_max_two_bounds (s : ℝ) :
    0 ≤ H248 (max 2 s) ∧ H248 (max 2 s) ≤ 1 := H248_bounds _

/-- The ordinary residual lower wall follows the actual eligible policy;
it is not used to define or enlarge the eligibility predicate. -/
theorem ordinary_H248_bounds (mask : Set (ℝ × ℝ)) (L : ℕ → LogFour → ℝ)
    (j : ℕ) (v : LogFour) (hv : v ∈ originalDomain mask)
    (hL : 2 * v 3 ≤ L j v) :
    0 ≤ ordinaryKernel H248 L j v ∧ ordinaryKernel H248 L j v ≤ (10000 / 417 : ℝ) := by
  have hw := (originalDomain_denominators_pos mask v hv).1
  have hLpos : 0 < L j v := lt_of_lt_of_le (mul_pos (by norm_num) hw) hL
  have hH := H248_max_two_bounds (L j v / v 3)
  have ha : (417 / 5000 : ℝ) ≤ v 3 := hv.1
  have hLa : (834 / 5000 : ℝ) ≤ L j v := by linarith
  unfold ordinaryKernel
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hH.2)) hLpos.le
  · apply (div_le_iff₀ hLpos).2
    nlinarith [hH.1]

/-- The table measurability and ordinary nonnegative supplier slots are
both discharged concretely, leaving only genuine residual/gate data. -/
theorem integrableOn_actual_H248_envelope (mask : Set (ℝ × ℝ))
    (hm : MeasurableSet mask) (bank : Finset ℕ)
    (eligible : ℕ → LogFour → Prop) (L : ℕ → LogFour → ℝ)
    (he : ∀ j ∈ bank, MeasurableSet {v | eligible j v})
    (hL : ∀ j ∈ bank, Measurable (L j))
    (hres : ∀ j ∈ bank, ∀ v ∈ originalDomain mask,
      eligible j v → 2 * v 3 ≤ L j v) :
    IntegrableOn (envelope bank
      (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
        (ordinaryKernel H248 L))) (originalDomain mask) volume := by
  apply integrableOn_original_canonical_envelope mask hm bank eligible currentK
    (by norm_num [currentK]) H248 L he measurable_H248 hL
  intro j hj v hv helig
  exact (ordinary_H248_bounds mask L j v hv (hres j hj v hv helig)).1

theorem integral_actual_H248_envelope_eq_sum (mask : Set (ℝ × ℝ))
    (hm : MeasurableSet mask) (bank : Finset ℕ)
    (eligible : ℕ → LogFour → Prop) (L : ℕ → LogFour → ℝ)
    (he : ∀ j ∈ bank, MeasurableSet {v | eligible j v})
    (hL : ∀ j ∈ bank, Measurable (L j))
    (hres : ∀ j ∈ bank, ∀ v ∈ originalDomain mask,
      eligible j v → 2 * v 3 ≤ L j v) :
    (∫ v in originalDomain mask,
      envelope bank (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
        (ordinaryKernel H248 L)) v) =
      ∑ c ∈ tags bank,
        ∫ v in winner (originalDomain mask) bank
            (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
              (ordinaryKernel H248 L)) c,
          (if c = 0 then switchedKernel currentK LiLiuPrereqBuchstab.buchstab v
            else ordinaryKernel H248 L c.pred v) := by
  apply integral_original_current_envelope_eq_sum mask hm bank eligible H248 L
    he measurable_H248 hL
  intro j hj v hv helig
  exact (ordinary_H248_bounds mask L j v hv (hres j hj v hv helig)).1

end

end ImbalancedChen.P5Z.U11H248
