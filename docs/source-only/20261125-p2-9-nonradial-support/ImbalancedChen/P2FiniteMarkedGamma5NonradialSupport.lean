import ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension

/-!
Pointwise location of the nonradial excess of the original physical
Gamma5 profile. The original complete product gate is separated exactly.
Inside M <= N, a supported point failing the original sharp program lies
in a one-sided strip of an original nonproduct gate.

This is a support statement only. It gives no arithmetic strip-count
estimate, history-selection smoothing, source-mass equality or PP licence.
All old, fresh and tail coordinate tags, including repeated values and
empty old/tail blocks, are unchanged.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5NonradialSupport

noncomputable section
open Real
open P2FiniteMarkedGamma5LogExtension
open P2FiniteMarkedGamma5PhysicalExtension
open scoped Classical BigOperators

/-- One of the original nonproduct gates lies on or just outside its
sharp boundary. The zero margin is retained for the strict faces. -/
def properStrip {r : ℕ} (logQ logN width : ℝ) (v : Point r) : Prop :=
  ∃ g ∈ program r, g ≠ Gate.product ∧
    -width < margin logQ logN v g ∧ margin logQ logN v g ≤ 0

theorem product_passed_of_physicalProduct_le {k r : ℕ}
    {logQ N : ℝ} {x : PhysicalPoint k r}
    (hx : ∀ i, 0 < x i) (hcap : physicalProduct x ≤ N) :
    passed logQ (log N) (logPoint x) Gate.product := by
  change 0 ≤ log N - ((logPoint x).1 + (logPoint x).2.1 0 +
    (logPoint x).2.1 1 + ∑ i, (logPoint x).2.2 i)
  rw [← log_physicalProduct hx]
  exact sub_nonneg.mpr (log_le_log (physicalProduct_pos hx) hcap)

/-- This is the exact support-level alternative for the inner profile.
The radial gate cannot witness failure when the complete product is <=N. -/
theorem inner_nonzero_failure_mem_properStrip {k r : ℕ}
    {logQ N width b : ℝ} {x : PhysicalPoint k r}
    (hb : 0 < b) (hw : 0 < width)
    (hne : physicalProfile logQ N width b x ≠ 0)
    (hcap : physicalProduct x ≤ N)
    (hfail : ¬ accepted logQ (log N) (logPoint x)) :
    properStrip logQ (log N) width (logPoint x) := by
  have hx (i : Slot k r) : 0 < x i :=
    (half_pos hb).trans (physicalProfile_nonzero_lower hb hne i)
  have hp := hne
  rw [physicalProfile_eq_floor_mul_original logQ N width hb x] at hp
  have hprofile := (mul_ne_zero_iff.mp hp).2
  unfold accepted at hfail
  push Not at hfail
  obtain ⟨g, hg, hnot⟩ := hfail
  have hneProduct : g ≠ Gate.product := by
    intro heq
    subst g
    exact hnot (product_passed_of_physicalProduct_le hx hcap)
  have hmargin : margin logQ (log N) (logPoint x) g ≤ 0 := by
    unfold passed at hnot
    split at hnot
    · exact le_of_not_gt hnot
    · exact (lt_of_not_ge hnot).le
  exact ⟨g, hg, hneProduct, profile_nonzero_margin hw hprofile g hg, hmargin⟩

/-- Every supported point is either in the already separated radial
excess, in the original sharp program, or in a nonradial boundary strip. -/
theorem nonzero_support_trichotomy {k r : ℕ}
    {logQ N width b : ℝ} {x : PhysicalPoint k r}
    (hb : 0 < b) (hw : 0 < width)
    (hne : physicalProfile logQ N width b x ≠ 0) :
    N < physicalProduct x ∨ accepted logQ (log N) (logPoint x) ∨
      properStrip logQ (log N) width (logPoint x) := by
  by_cases hcap : physicalProduct x ≤ N
  · right
    by_cases hsharp : accepted logQ (log N) (logPoint x)
    · exact Or.inl hsharp
    · exact Or.inr (inner_nonzero_failure_mem_properStrip hb hw hne hcap hsharp)
  · exact Or.inl (lt_of_not_ge hcap)

/-- Unit indicators dominate the inner smooth profile pointwise. This
does not identify the accepted geometry with an arithmetic source. -/
theorem inner_profile_le_sharp_add_strip {k r : ℕ}
    {logQ N width b : ℝ} {x : PhysicalPoint k r}
    (hb : 0 < b) (hw : 0 < width) (hcap : physicalProduct x ≤ N) :
    physicalProfile logQ N width b x ≤
      (if accepted logQ (log N) (logPoint x) then (1 : ℝ) else 0) +
      (if properStrip logQ (log N) width (logPoint x) then (1 : ℝ) else 0) := by
  by_cases hzero : physicalProfile logQ N width b x = 0
  · rw [hzero]
    positivity
  by_cases hsharp : accepted logQ (log N) (logPoint x)
  · rw [if_pos hsharp]
    exact (physicalProfile_bounds logQ N width b x).2.trans
      (le_add_of_nonneg_right (by positivity))
  · have hstrip := inner_nonzero_failure_mem_properStrip hb hw hzero hcap hsharp
    simpa only [if_neg hsharp, if_pos hstrip, zero_add] using
      (physicalProfile_bounds logQ N width b x).2

/-- Passing from physical logarithms to log-N coordinates preserves the
original gate witness, including all strict-face equality points. -/
theorem properStrip_scaled {r : ℕ} {logQ logN width : ℝ} {v : Point r}
    (hlogN : 0 < logN) (hstrip : properStrip logQ logN width v) :
    ∃ g ∈ program r, g ≠ Gate.product ∧
      |margin logQ logN v g / logN| ≤ width / logN := by
  obtain ⟨g, hg, hp, hlo, hhi⟩ := hstrip
  refine ⟨g, hg, hp, ?_⟩
  rw [abs_div, abs_of_pos hlogN]
  exact div_le_div_of_nonneg_right
    ((abs_le.mpr ⟨hlo.le, hhi.trans (by linarith only [hlo, hhi])⟩)) hlogN.le

end
end ImbalancedChen.P2FiniteMarkedGamma5NonradialSupport
