import ImbalancedChen.CurrentChenBuchstabRefinement
import Lean.Elab.Tactic.Omega

/-!
SOURCE ONLY / UNCOMPILED / no Lean, lake, evaluator, or numerical replay.

This file supplies the missing *semantic form* of an elementary rational
method-of-steps certificate for the actual pinned Buchstab function.  It does
not create a second Buchstab function.  `weighted` is literally `s * buchstab s`,
and the proof of each step uses `buchstab_weighted_sub_eq_integral`.

The existing `Part5OriginalOmegaGridCore` already has a different non-circular
whole-cell supplier: its checked integer Bernstein identity is combined with
the actual-function theorem `all_cells`.  Its `OriginalGridRecord.Valid`, by
itself, only records ceil/max arithmetic.  In particular, its `hiLeft` and
`hiRight` fields have no semantic link to the Buchstab function merely because
that predicate holds.  This file supplies an independent rational recurrence
whose finite checks do have that semantic meaning.  No P5 row, coordinate
certificate, original table value, or final saved gain is duplicated here.

The remaining gap is concrete data: no claim is made that the old rounded
`hiLeft`/`hiRight` arrays satisfy this recurrence, or that these elementary
rectangle bounds are sharp enough for every original table entry.  The
original table's complete analytic/numerical coverage remains separate.  The
finite checker and the proofs below have not been run.
-/

namespace ImbalancedChen.Certificates.P2BuchstabRationalSemantics

open Set MeasureTheory LiLiuPrereqBuchstab
open scoped Interval

noncomputable section

/-- The actual weighted Buchstab function, with no approximation involved. -/
def weighted (s : ℝ) : ℝ := s * LiLiuPrereqBuchstab.buchstab s

private theorem approx_positive (n : ℕ) (u : ℝ) : 0 < approx n u := by
  induction n generalizing u with
  | zero =>
      change 0 < 1 / max 1 u
      exact div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left 1 u))
  | succ n ih =>
      have hc : Continuous (fun t : ℝ => approx n (t - 1)) :=
        (continuous_approx n).comp (continuous_id.sub continuous_const)
      have hi := intervalIntegral.integral_mono_on (le_max_left (2 : ℝ) u)
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 2 (max 2 u))
        (hc.intervalIntegrable 2 (max 2 u)) (fun t _ => (ih (t - 1)).le)
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hi
      change 0 < (1 + ∫ t in (2 : ℝ)..max 2 u, approx n (t - 1)) / max 1 u
      exact div_pos (by linarith only [hi])
        (lt_of_lt_of_le (by norm_num) (le_max_left 1 u))

/-- Positivity comes directly from the actual stabilized approximants.
In particular the recurrence semantics does not require a pre-assumed
positive omega barrier, even as an intermediate analytic hypothesis. -/
theorem buchstab_positive (u : ℝ) : 0 < LiLiuPrereqBuchstab.buchstab u := by
  change 0 < approx ⌈u⌉₊ u
  exact approx_positive ⌈u⌉₊ u

theorem weighted_initial {s : ℝ} (hs : 1 ≤ s) (hs₂ : s ≤ 2) :
    weighted s = 1 := by
  rw [weighted, buchstab_eq_one_div hs hs₂]
  have hs₀ : s ≠ 0 := by linarith
  field_simp [hs₀]

private theorem delayed_integral_nonneg {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, buchstab (t - 1) := by
  have hc : Continuous (fun t : ℝ => buchstab (t - 1)) :=
    continuous_buchstab.comp (continuous_id.sub continuous_const)
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b)
    (hc.intervalIntegrable a b) (fun t _ => (buchstab_positive (t - 1)).le)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] using h

/-- The *weighted* function is monotone.  No monotonicity of `buchstab`
itself is asserted or used. -/
theorem weighted_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    weighted a ≤ weighted b := by
  by_cases hb₂ : b ≤ 2
  · rw [weighted_initial ha (hab.trans hb₂),
      weighted_initial (ha.trans hab) hb₂]
  · have hb₂' : 2 ≤ b := (lt_of_not_ge hb₂).le
    by_cases ha₂ : a ≤ 2
    · rw [weighted_initial ha ha₂]
      have hi := delayed_integral_nonneg (a := 2) (b := b) (by norm_num) hb₂'
      have he := mul_buchstab_eq_integral hb₂'
      dsimp only [weighted]
      linarith only [hi, he]
    · have ha₂' : 2 ≤ a := (lt_of_not_ge ha₂).le
      have hi := delayed_integral_nonneg ha₂' hab
      have he := buchstab_weighted_sub_eq_integral (a := a) ha₂' hab
      dsimp only [weighted]
      linarith only [hi, he]

/-- A genuine one-step enclosure.  The input weighted enclosures concern
only the anchor `a` and the delayed endpoints `a - 1`, `b - 1`.  The factors
`1 / (b - 1)` and `1 / (a - 1)` come from the whole delayed interval, not
from evaluating the integrand at one sample point. -/
theorem weighted_step {a b l₀ u₀ l₁ u₁ : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hl₀ : l₀ ≤ weighted a) (hu₀ : weighted a ≤ u₀)
    (hl₁ : l₁ ≤ weighted (a - 1)) (hu₁ : weighted (b - 1) ≤ u₁) :
    l₀ + (b - a) * (l₁ / (b - 1)) ≤ weighted b ∧
      weighted b ≤ u₀ + (b - a) * (u₁ / (a - 1)) := by
  have ha₁ : 0 < a - 1 := by linarith
  have hb₁ : 0 < b - 1 := by linarith
  have hc : Continuous (fun t : ℝ => buchstab (t - 1)) :=
    continuous_buchstab.comp (continuous_id.sub continuous_const)
  have hpoint : ∀ t ∈ Icc a b,
      l₁ / (b - 1) ≤ buchstab (t - 1) ∧
        buchstab (t - 1) ≤ u₁ / (a - 1) := by
    intro t ht
    have htnonneg : 0 ≤ buchstab (t - 1) := (buchstab_positive (t - 1)).le
    have hlo : l₁ ≤ weighted (t - 1) := hl₁.trans
      (weighted_mono (by linarith) (by linarith [ht.1]))
    have hhi : weighted (t - 1) ≤ u₁ :=
      (weighted_mono (by linarith [ht.1]) (by linarith [ht.2])).trans hu₁
    constructor
    · apply (div_le_iff₀ hb₁).mpr
      calc
        l₁ ≤ (t - 1) * buchstab (t - 1) := hlo
        _ ≤ (b - 1) * buchstab (t - 1) :=
          mul_le_mul_of_nonneg_right (by linarith [ht.2]) htnonneg
        _ = buchstab (t - 1) * (b - 1) := mul_comm _ _
    · apply (le_div_iff₀ ha₁).mpr
      calc
        buchstab (t - 1) * (a - 1) = (a - 1) * buchstab (t - 1) := mul_comm _ _
        _ ≤ (t - 1) * buchstab (t - 1) :=
          mul_le_mul_of_nonneg_right (by linarith [ht.1]) htnonneg
        _ ≤ u₁ := hhi
  have hloInt := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => l₁ / (b - 1)) volume a b)
    (hc.intervalIntegrable a b) (fun t ht => (hpoint t ht).1)
  have hhiInt := intervalIntegral.integral_mono_on hab
    (hc.intervalIntegrable a b)
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => u₁ / (a - 1)) volume a b)
    (fun t ht => (hpoint t ht).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hloInt hhiInt
  have he := buchstab_weighted_sub_eq_integral (a := a) ha hab
  dsimp only [weighted] at hl₀ hu₀ ⊢
  constructor <;> linarith only [hl₀, hu₀, hloInt, hhiInt, he]

/-- Rational arithmetic version of the analytic step.  This theorem has
no hypothesis about a desired current-cell enclosure. -/
theorem weighted_rational_step {a b l₀ u₀ l₁ u₁ : ℚ}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hl₀ : (l₀ : ℝ) ≤ weighted a) (hu₀ : weighted a ≤ (u₀ : ℝ))
    (hl₁ : (l₁ : ℝ) ≤ weighted ((a : ℝ) - 1))
    (hu₁ : weighted ((b : ℝ) - 1) ≤ (u₁ : ℝ)) :
    ((l₀ + (b - a) * (l₁ / (b - 1)) : ℚ) : ℝ) ≤ weighted b ∧
      weighted b ≤ ((u₀ + (b - a) * (u₁ / (a - 1)) : ℚ) : ℝ) := by
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_one]
    using weighted_step haR habR hl₀ hu₀ hl₁ hu₁

end

/-- Original rational grid coordinate, starting at `1`. -/
def grid (m k : ℕ) : ℚ := 1 + (k : ℚ) / (m : ℚ)

private theorem grid_step (m k : ℕ) :
    grid m (k + 1) - grid m k = 1 / (m : ℚ) := by
  simp only [grid, Nat.cast_add, Nat.cast_one]
  ring

private theorem grid_delay {m k : ℕ} (hm : 0 < m) (hkm : m ≤ k) :
    grid m (k - m) = grid m k - 1 := by
  have hm₀ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [grid, grid, Nat.cast_sub hkm]
  field_simp
  ring

private theorem grid_delay_succ {m k : ℕ} (hm : 0 < m) (hkm : m ≤ k) :
    grid m (k - m + 1) = grid m (k + 1) - 1 := by
  have he : k - m + 1 = (k + 1) - m := by omega
  rw [he]
  exact grid_delay hm (by omega)

private theorem grid_initial_range {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) :
    (1 : ℚ) ≤ grid m k ∧ grid m k ≤ 2 := by
  have hmR : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hkR : (k : ℚ) ≤ (m : ℚ) := by exact_mod_cast hk
  constructor
  · dsimp [grid]
    have hdiv : (0 : ℚ) ≤ (k : ℚ) / (m : ℚ) :=
      div_nonneg (Nat.cast_nonneg k) hmR.le
    linarith
  · dsimp [grid]
    have hdiv : (k : ℚ) / (m : ℚ) ≤ 1 :=
      (div_le_iff₀ hmR).mpr (by simpa only [one_mul] using hkR)
    linarith

private theorem grid_recursive_range {m k : ℕ} (hm : 0 < m) (hk : m ≤ k) :
    (2 : ℚ) ≤ grid m k ∧ grid m k ≤ grid m (k + 1) := by
  have hmR : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hkR : (m : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hdiv : (1 : ℚ) ≤ (k : ℚ) / (m : ℚ) :=
    (le_div_iff₀ hmR).mpr (by simpa only [one_mul] using hkR)
  have hstep := grid_step m k
  have hp : (0 : ℚ) ≤ 1 / (m : ℚ) := by positivity
  constructor
  · dsimp [grid]
    linarith
  · linarith

/-- One row of a completely rational certificate: bounds on the actual
weighted function at one original rational grid node. -/
structure NodeEnclosure where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

def entry (cs : List NodeEnclosure) (k : ℕ) : NodeEnclosure :=
  (cs[k]?).getD ⟨0, 0⟩

/-- All checks are finite rational arithmetic.  For node `k > m`, the
anchor is node `k - 1`; the delayed endpoints are `k - 1 - m` and
`k - 1 - m + 1`, both strictly earlier than `k` because `0 < m`.
No predicate here contains `ℝ`, `buchstab`, an integral, or a final gain. -/
def Valid (m : ℕ) (cs : List NodeEnclosure) : Prop :=
  0 < m ∧ ∀ k : Fin cs.length,
    if k.val ≤ m then
      (entry cs k.val).lower ≤ 1 ∧ 1 ≤ (entry cs k.val).upper
    else
      (entry cs k.val).lower ≤
          (entry cs (k.val - 1)).lower + (1 / (m : ℚ)) *
            ((entry cs (k.val - 1 - m)).lower / (grid m k.val - 1)) ∧
        (entry cs (k.val - 1)).upper + (1 / (m : ℚ)) *
            ((entry cs (k.val - 1 - m + 1)).upper / (grid m (k.val - 1) - 1)) ≤
          (entry cs k.val).upper

instance (m : ℕ) (cs : List NodeEnclosure) : Decidable (Valid m cs) := by
  unfold Valid
  infer_instance

def check (m : ℕ) (cs : List NodeEnclosure) : Bool := decide (Valid m cs)

/-- A small nonvacuous certificate on the half-mesh from `1` through `3`.
The last two enclosures are obtained by the delayed rectangle recurrence,
not by sampled Buchstab values.  These are seed semantics, not P5 row data. -/
def halfMeshSeed : List NodeEnclosure :=
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4 / 3, 3 / 2⟩, ⟨19 / 12, 11 / 6⟩]

theorem halfMeshSeed_checked : check 2 halfMeshSeed = true := by
  decide

noncomputable section

/-- Soundness by strict induction on the grid index.  The only initial
function fact is the actual condition `s * buchstab s = 1` on `[1,2]`.
Every recursive input comes from a strictly smaller index. -/
theorem valid_sound {m : ℕ} {cs : List NodeEnclosure} (hc : Valid m cs) :
    ∀ k : ℕ, k < cs.length →
      ((entry cs k).lower : ℝ) ≤ weighted (grid m k) ∧
        weighted (grid m k) ≤ ((entry cs k).upper : ℝ) := by
  rcases hc with ⟨hm, hchecks⟩
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      have hrow := hchecks ⟨k, hk⟩
      by_cases hbase : k ≤ m
      · simp only [hbase, if_true] at hrow
        have hrange := grid_initial_range hm hbase
        have hlo : (1 : ℝ) ≤ (grid m k : ℝ) := by exact_mod_cast hrange.1
        have hhi : (grid m k : ℝ) ≤ (2 : ℝ) := by exact_mod_cast hrange.2
        rw [weighted_initial hlo hhi]
        exact ⟨by exact_mod_cast hrow.1, by exact_mod_cast hrow.2⟩
      · simp only [hbase, if_false] at hrow
        cases k with
        | zero => omega
        | succ j =>
            have hjm : m ≤ j := by omega
            have hj : j < cs.length := by omega
            have hd₀ : j - m < j + 1 := by omega
            have hd₁ : j - m + 1 < j + 1 := by omega
            have hjbounds := ih j (by omega) hj
            have hd₀bounds := ih (j - m) hd₀ (by omega)
            have hd₁bounds := ih (j - m + 1) hd₁ (by omega)
            have hrange := grid_recursive_range hm hjm
            have hdelay₀ : (grid m (j - m) : ℝ) = (grid m j : ℝ) - 1 := by
              exact_mod_cast grid_delay hm hjm
            have hdelay₁ : (grid m (j - m + 1) : ℝ) =
                (grid m (j + 1) : ℝ) - 1 := by
              exact_mod_cast grid_delay_succ hm hjm
            rw [hdelay₀] at hd₀bounds
            rw [hdelay₁] at hd₁bounds
            have hstep := weighted_rational_step hrange.1 hrange.2
              hjbounds.1 hjbounds.2 hd₀bounds.1 hd₁bounds.2
            rw [grid_step] at hstep
            have hloQ : (entry cs (j + 1)).lower ≤
                (entry cs j).lower + (1 / (m : ℚ)) *
                  ((entry cs (j - m)).lower / (grid m (j + 1) - 1)) := by
              simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hrow.1
            have hhiQ : (entry cs j).upper + (1 / (m : ℚ)) *
                ((entry cs (j - m + 1)).upper / (grid m j - 1)) ≤
                  (entry cs (j + 1)).upper := by
              simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hrow.2
            have hloR : ((entry cs (j + 1)).lower : ℝ) ≤
                (((entry cs j).lower + (1 / (m : ℚ)) *
                  ((entry cs (j - m)).lower / (grid m (j + 1) - 1)) : ℚ) : ℝ) := by
              exact_mod_cast hloQ
            have hhiR :
                (((entry cs j).upper + (1 / (m : ℚ)) *
                  ((entry cs (j - m + 1)).upper / (grid m j - 1)) : ℚ) : ℝ) ≤
                  ((entry cs (j + 1)).upper : ℝ) := by
              exact_mod_cast hhiQ
            exact ⟨hloR.trans hstep.1, hstep.2.trans hhiR⟩

theorem check_sound {m : ℕ} {cs : List NodeEnclosure} (hc : check m cs = true)
    {k : ℕ} (hk : k < cs.length) :
    ((entry cs k).lower : ℝ) ≤ weighted (grid m k) ∧
      weighted (grid m k) ≤ ((entry cs k).upper : ℝ) := by
  exact valid_sound (of_decide_eq_true hc) k hk

/-- An actual-function consequence of the explicit finite seed.  This
does not appeal to either a desired omega barrier or a saved-gain theorem. -/
theorem weighted_three_seed_enclosure :
    (19 : ℝ) / 12 ≤ weighted 3 ∧ weighted 3 ≤ (11 : ℝ) / 6 := by
  have h := check_sound halfMeshSeed_checked (k := 4) (by decide)
  norm_num [entry, halfMeshSeed, grid] at h
  exact h

/-- A node certificate licenses the entire closed cell between consecutive
nodes.  Division is by the actual positive real argument, so a node upper
bound is never silently interpreted as a pointwise Buchstab upper bound. -/
theorem check_cell_sound {m : ℕ} {cs : List NodeEnclosure}
    (hc : check m cs = true) {k : ℕ} (hk : k + 1 < cs.length) {s : ℝ}
    (hs : s ∈ Icc (grid m k : ℝ) (grid m (k + 1) : ℝ)) :
    ((entry cs k).lower : ℝ) / s ≤ buchstab s ∧
      buchstab s ≤ ((entry cs (k + 1)).upper : ℝ) / s := by
  have hv : Valid m cs := of_decide_eq_true hc
  have hmR : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hv.1
  have hgrid : (1 : ℚ) ≤ grid m k := by
    have hdiv : (0 : ℚ) ≤ (k : ℚ) / (m : ℚ) :=
      div_nonneg (Nat.cast_nonneg k) hmR.le
    dsimp [grid]
    linarith
  have hgridR : (1 : ℝ) ≤ (grid m k : ℝ) := by exact_mod_cast hgrid
  have hs₀ : 0 < s := by linarith [hs.1]
  have hleft := check_sound hc (k := k) (by omega)
  have hright := check_sound hc (k := k + 1) hk
  constructor
  · apply (div_le_iff₀ hs₀).mpr
    have h := hleft.1.trans (weighted_mono hgridR hs.1)
    simpa only [weighted, mul_comm] using h
  · apply (le_div_iff₀ hs₀).mpr
    have h := (weighted_mono (by linarith [hs.1]) hs.2).trans hright.2
    simpa only [weighted, mul_comm] using h

/-- Explicit original-normalization output from a certificate.  `S` can
be `2^80`; the finite premise is the exact multiplication inequality
needed at the *left* endpoint of the cell. -/
theorem check_cell_upper_scaled {m : ℕ} {cs : List NodeEnclosure}
    (hc : check m cs = true) {k : ℕ} (hk : k + 1 < cs.length)
    {S num : ℚ} (hS : 0 < S) (hnum : 0 ≤ num)
    (hcap : S * (entry cs (k + 1)).upper ≤ num * grid m k)
    {s : ℝ} (hs : s ∈ Icc (grid m k : ℝ) (grid m (k + 1) : ℝ)) :
    buchstab s ≤ (num : ℝ) / (S : ℝ) := by
  have hcell := (check_cell_sound hc hk hs).2
  have hv : Valid m cs := of_decide_eq_true hc
  have hmR : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hv.1
  have hg : (1 : ℚ) ≤ grid m k := by
    have hdiv : (0 : ℚ) ≤ (k : ℚ) / (m : ℚ) :=
      div_nonneg (Nat.cast_nonneg k) hmR.le
    dsimp [grid]
    linarith
  have hgR : (1 : ℝ) ≤ (grid m k : ℝ) := by exact_mod_cast hg
  have hs₀ : 0 < s := by linarith [hs.1]
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hnumR : (0 : ℝ) ≤ (num : ℝ) := by exact_mod_cast hnum
  have hcapR : (S : ℝ) * ((entry cs (k + 1)).upper : ℝ) ≤
      (num : ℝ) * (grid m k : ℝ) := by exact_mod_cast hcap
  have hcapS : (S : ℝ) * ((entry cs (k + 1)).upper : ℝ) ≤
      (num : ℝ) * s := hcapR.trans
        (mul_le_mul_of_nonneg_left hs.1 hnumR)
  have hscaled : (S : ℝ) * buchstab s ≤ (num : ℝ) := by
    have hmul := (le_div_iff₀ hs₀).mp hcell
    have hp := mul_le_mul_of_nonneg_left hmul hSR.le
    apply (mul_le_mul_iff_right₀ hs₀).mp
    calc
      (S : ℝ) * buchstab s * s = (S : ℝ) * (buchstab s * s) := by ring
      _ ≤ (S : ℝ) * ((entry cs (k + 1)).upper : ℝ) := hp
      _ ≤ (num : ℝ) * s := hcapS
  exact (le_div_iff₀ hSR).mpr (by simpa only [mul_comm] using hscaled)

end

end ImbalancedChen.Certificates.P2BuchstabRationalSemantics
