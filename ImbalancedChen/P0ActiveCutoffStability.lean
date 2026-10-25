import ImbalancedChen.P0ActivePrimeShellBudget

/-!
Exact stability of the original active retained third-prime source under
raising its rough activation cutoff. Above the raised cutoff both actual
raw-Q3 levels coincide, including every original firstStop/cube test.
The lost active source is exactly the original lower-cutoff shell; the
quantitative decrement therefore uses the proved shell budget directly.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P0ActiveCutoffStability

noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse HistoricalThirdCoarse.P1ActualTuple
open P0ActivePrimeShellBudget

local notation "ρ" => (19 / 96 : ℝ)

/-- The complete original active retained prime-product mass. -/
def activeMass (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) : ℝ :=
  ∑ p ∈ activeRetainedTuples e chi m omega N cap ((N : ℝ) ^ ρ),
    ∏ i, 1 / ((p i : ℝ) - 1)

private theorem retained_iff_of_both_active
    (e chi : ℝ) (m : ℕ) (omega omega' : ℝ) (N cap : ℕ) (z : ℝ)
    (p : Fin 3 → ℕ)
    (ha : active omega (N : ℝ) (history p))
    (hb : active omega' (N : ℝ) (history p)) :
    p ∈ retainedTuples e chi m omega N cap z ↔
      p ∈ retainedTuples e chi m omega' N cap z := by
  have hraw : rawLevel e chi m omega (N : ℝ) (history p) =
      rawLevel e chi m omega' (N : ℝ) (history p) := by
    simp only [rawLevel, if_pos ha, if_pos hb]
  have hself : rosserAncestor 3 (history p) = history p := by
    simp [rosserAncestor, history]
  have hthird : policy e chi m omega (N : ℝ) false (history p) =
      policy e chi m omega' (N : ℝ) false (history p) := by
    change ordinaryParityRosserPolicy false
        (rawLevel e chi m omega (N : ℝ) (rosserAncestor 3 (history p)))
        false (history p) =
      ordinaryParityRosserPolicy false
        (rawLevel e chi m omega' (N : ℝ) (rosserAncestor 3 (history p)))
        false (history p)
    rw [hself, hraw]
  have hfirst : policy e chi m omega (N : ℝ) false [p 0] =
      policy e chi m omega' (N : ℝ) false [p 0] := by
    rw [policy_through_two e chi m omega (N : ℝ) false [p 0] (by simp),
      policy_through_two e chi m omega' (N : ℝ) false [p 0] (by simp)]
  have hof : List.ofFn p = [p 0, p 1, p 2] := by simp [List.ofFn_succ]
  rw [mem_retainedTuples_iff, mem_retainedTuples_iff]
  apply and_congr_right
  intro _hsub
  simp only [hof, FirstExitValidSelection, Bool.not_true, Bool.not_false,
    policy_even, true_and, and_true]
  change (policy e chi m omega (N : ℝ) false [p 0] = true ∧
      policy e chi m omega (N : ℝ) false (history p) = true) ↔
    (policy e chi m omega' (N : ℝ) false [p 0] = true ∧
      policy e chi m omega' (N : ℝ) false (history p) = true)
  rw [hfirst, hthird]

/-- Above a larger rough cutoff, both actual policies make identical
retention decisions. The original firstStop is part of each decision. -/
theorem mem_active_higher_iff (e chi : ℝ) (m : ℕ)
    (omega omega' : ℝ) (hcut : omega ≤ omega')
    (N cap : ℕ) (hN : 1 ≤ N) (z : ℝ) (p : Fin 3 → ℕ) :
    p ∈ activeRetainedTuples e chi m omega' N cap z ↔
      p ∈ activeRetainedTuples e chi m omega N cap z ∧
        (N : ℝ) ^ omega' ≤ (p 2 : ℝ) := by
  have hpower : (N : ℝ) ^ omega ≤ (N : ℝ) ^ omega' :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hcut
  constructor
  · intro hp
    obtain ⟨hret, hb⟩ := Finset.mem_filter.mp hp
    have hbound := (active_triple omega' (N : ℝ) (p 0) (p 1) (p 2)).mp hb
    have ha : active omega (N : ℝ) (history p) :=
      (active_triple omega (N : ℝ) (p 0) (p 1) (p 2)).mpr (hpower.trans hbound)
    exact ⟨Finset.mem_filter.mpr
      ⟨(retained_iff_of_both_active e chi m omega omega' N cap z p ha hb).mpr hret, ha⟩,
        hbound⟩
  · rintro ⟨hp, hbound⟩
    obtain ⟨hret, ha⟩ := Finset.mem_filter.mp hp
    have hb : active omega' (N : ℝ) (history p) :=
      (active_triple omega' (N : ℝ) (p 0) (p 1) (p 2)).mpr hbound
    exact Finset.mem_filter.mpr
      ⟨(retained_iff_of_both_active e chi m omega omega' N cap z p ha hb).mp hret, hb⟩

/-- The exact lost source is the original active shell, with strict upper
and inclusive lower faces. This identity asserts no monotonicity of the
full retained support outside activation. -/
theorem active_partition (e chi : ℝ) (m : ℕ) (omega delta : ℝ)
    (hdelta : 0 ≤ delta) (N cap : ℕ) (hN : 1 ≤ N) :
    activeRetainedTuples e chi m omega N cap ((N : ℝ) ^ ρ) =
      activeRetainedTuples e chi m (omega + delta) N cap ((N : ℝ) ^ ρ) ∪
        shellTuples e chi m omega delta N cap := by
  ext p
  rw [Finset.mem_union,
    mem_active_higher_iff e chi m omega (omega + delta) (by linarith)
      N cap hN ((N : ℝ) ^ ρ) p]
  simp only [shellTuples, Finset.mem_filter]
  constructor
  · intro hp
    rcases le_or_gt ((N : ℝ) ^ (omega + delta)) (p 2 : ℝ) with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp

theorem higher_disjoint_shell (e chi : ℝ) (m : ℕ) (omega delta : ℝ)
    (N cap : ℕ) :
    Disjoint (activeRetainedTuples e chi m (omega + delta) N cap ((N : ℝ) ^ ρ))
      (shellTuples e chi m omega delta N cap) := by
  apply Finset.disjoint_left.mpr
  intro p hp hs
  have hactive := (Finset.mem_filter.mp hp).2
  have hbound := (active_triple (omega + delta) (N : ℝ) (p 0) (p 1) (p 2)).mp hactive
  exact (not_lt_of_ge hbound) (Finset.mem_filter.mp hs).2

/-- Exact conservation of the actual weighted source across the raised
cutoff. Every summand keeps the same target-deleted prime product. -/
theorem activeMass_eq_higher_add_shell (e chi : ℝ) (m : ℕ)
    (omega delta : ℝ) (hdelta : 0 ≤ delta)
    (N cap : ℕ) (hN : 1 ≤ N) :
    activeMass e chi m omega N cap =
      activeMass e chi m (omega + delta) N cap +
        shellMass e chi m omega delta N cap := by
  unfold activeMass
  rw [active_partition e chi m omega delta hdelta N cap hN,
    Finset.sum_union (higher_disjoint_shell e chi m omega delta N cap)]
  rfl

/-- Raising the activation cutoff removes nonnegative mass from the exact
active source. No assumed ordering between Theta and Gamma is needed. -/
theorem activeMass_sub_higher_nonneg (e chi : ℝ) (m : ℕ)
    (omega delta : ℝ) (hdelta : 0 ≤ delta)
    (N cap : ℕ) (hN : 1 ≤ N) :
    0 ≤ activeMass e chi m omega N cap -
      activeMass e chi m (omega + delta) N cap := by
  rw [activeMass_eq_higher_add_shell e chi m omega delta hdelta N cap hN,
    add_sub_cancel_left]
  unfold shellMass
  apply Finset.sum_nonneg
  intro p hp
  exact actualPrimeBoxWeight_nonneg
    (shellTuples_subset_box e chi m omega delta N cap hp)

/-- Quantitative continuity of the original active retained mass in its
rough exponent. The absolute K is supplied by the proved prime estimate,
and the remaining size condition is purely scalar and explicit. -/
theorem exists_uniform_active_cutoff_stability :
    ∃ K : ℝ, 1 < K ∧
      ∀ (e chi : ℝ) (m : ℕ) (omega delta : ℝ),
        0 < omega → 0 < delta → omega + delta ≤ ρ →
      ∀ (N cap : ℕ), 1 < N → Even N →
        K * ρ ≤ delta * omega * Real.log (N : ℝ) →
        |activeMass e chi m omega N cap -
          activeMass e chi m (omega + delta) N cap| ≤
            (8 * ρ ^ 2 / omega ^ 3) * delta := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_active_shell_bound
  refine ⟨K, hK, ?_⟩
  intro e chi m omega delta homega hdelta hwidth N cap hN hEven hscale
  rw [abs_of_nonneg (activeMass_sub_higher_nonneg
    e chi m omega delta hdelta.le N cap hN.le),
    activeMass_eq_higher_add_shell e chi m omega delta hdelta.le N cap hN.le,
    add_sub_cancel_left]
  exact hbound e chi m omega delta homega hdelta hwidth N cap hN hEven hscale

end
end ImbalancedChen.P0ActiveCutoffStability