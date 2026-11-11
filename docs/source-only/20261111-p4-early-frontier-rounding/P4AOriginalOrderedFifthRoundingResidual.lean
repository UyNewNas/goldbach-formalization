import ImbalancedChen.P4AOriginalOrderedThirdFullPolicy
import ImbalancedChen.P1VariableOwnCubeResidualUniformity
import ImbalancedChen.P4AOriginalFiniteFifthCompactProfile

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The literal ordered-third policy's raw fifth level and its protected
finite cap use the same Root, OriginalData, history and eligible predicates.
The cap loss is less than 2 * width n; no width n versus omega condition
is introduced. The current-root range is proved only in its lower mode.
These are compact arithmetic estimates, not whole-frontier early payments.
-/
namespace ImbalancedChen.P4AOriginalOrderedFifthRoundingResidual
noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open VariableEnvelope
open P5OriginalCommonRefinedConstructor (OriginalData)
open P1OriginalVariableFourthContinuation
  (finiteMax finiteMax_seed_le finiteMax_le)
open P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalOrderedThirdFullPolicy

theorem third_range
    (R : Root) (N : ℝ) (pre : List ℕ)
    (hR : R.scalar ≤ VariableEnvelope.cap) :
    R.scalar ≤ third R N pre ∧
      third R N pre ≤ VariableEnvelope.cap := by
  unfold third
  constructor
  · exact le_max_left _ _
  · refine max_le hR ?_
    split_ifs <;> first
      | exact v_le_cap _
      | exact hR

theorem fourth_range
    (R : Root) (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (he : 0 ≤ (d.e : ℝ))
    (hR : R.scalar ≤ VariableEnvelope.cap) :
    R.scalar ≤ fourth R d N pre ∧
      fourth R d N pre ≤ VariableEnvelope.cap := by
  have ht := third_range R N pre hR
  unfold fourth
  split_ifs
  · constructor
    · exact ht.1.trans (finiteMax_seed_le _ _ _ _)
    · apply finiteMax_le
      · exact ht.2
      · intro r _hr _heligible
        rw [r.bufferedCandidate_eq]
        have hv := v_le_cap
          (∑ i ∈ r.selected, primeHistoryLogCoordinates N 4 pre i)
        linarith
  · exact ht

theorem fourth_le_fifth
    (R : Root) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    fourth R d N (rosserAncestor 4 pre) ≤ fifth R d N pre := by
  unfold fifth
  split_ifs
  · exact finiteMax_seed_le _ _ _ _
  · exact le_rfl

theorem fifth_range
    (R : Root) (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (he : 0 ≤ (d.e : ℝ))
    (hR : R.scalar ≤ VariableEnvelope.cap) :
    R.scalar ≤ fifth R d N pre ∧
      fifth R d N pre ≤ VariableEnvelope.cap := by
  have h4 := fourth_range R d N (rosserAncestor 4 pre) he hR
  constructor
  · exact h4.1.trans (fourth_le_fifth R d N pre)
  · unfold fifth
    split_ifs
    · apply finiteMax_le
      · exact h4.2
      · intro r _hr _heligible
        exact
          P1OriginalVariableFifthContinuation.candidate_le_global_cap
            (d.e : ℝ) he r.selected
            (primeHistoryLogCoordinates N 5 pre)
    · exact h4.2

/-- One rounding debt on the same grid, without reselecting the fourth ancestor. -/
theorem cap5_eq_protect
    (R : Root) (d : OriginalData) (N : ℝ)
    (n : ℕ) (pre : List ℕ) :
    cap5 R d N n pre =
      protect n R.scalar (fifth R d N pre) := by
  unfold cap5
  exact protect_nested n R.scalar
    (fourth R d N (rosserAncestor 4 pre))
    (fifth R d N pre)
    (fourth_le_fifth R d N pre)

theorem cap5_bounds
    (R : Root) (d : OriginalData) (N : ℝ)
    (n : ℕ) (pre : List ℕ)
    (he : 0 ≤ (d.e : ℝ))
    (hs : 0 ≤ R.scalar)
    (hc : R.scalar ≤ VariableEnvelope.cap) :
    R.scalar ≤ cap5 R d N n pre ∧
      fifth R d N pre - 2 * width n < cap5 R d N n pre ∧
      cap5 R d N n pre ≤ fifth R d N pre := by
  rw [cap5_eq_protect]
  have hf := fifth_range R d N pre he hc
  exact protect_error n R.scalar (fifth R d N pre) hs hf.1 hf.2

theorem cap5_abs_error
    (R : Root) (d : OriginalData) (N : ℝ)
    (n : ℕ) (pre : List ℕ)
    (he : 0 ≤ (d.e : ℝ))
    (hs : 0 ≤ R.scalar)
    (hc : R.scalar ≤ VariableEnvelope.cap) :
    |fifth R d N pre - cap5 R d N n pre| < 2 * width n := by
  have h := cap5_bounds R d N n pre he hs hc
  rw [abs_of_nonneg (sub_nonneg.mpr h.2.2)]
  linarith [h.2.1]

theorem retained_capValue_range
    {e : ℝ} {m : ℕ} {j : HistoricalThirdCoarse.Cell m}
    (he : 0 < e) (hecap : e ≤ 1 / 384)
    (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ e / 2)
    (hj : j ∈ P4AOriginalOrderedThirdTable.retained e m) :
    0 ≤ P4AOriginalOrderedThirdTable.capValue e m j ∧
      P4AOriginalOrderedThirdTable.capValue e m j ≤
        VariableEnvelope.cap := by
  rcases (Finset.mem_filter.mp hj).2 with ⟨hne, hstop⟩
  obtain ⟨t, ht⟩ := hne
  have hx : 0 ≤ t 0 :=
    ht.2.1.trans (ht.2.2.1.trans ht.2.2.2)
  have hfirst :=
    P4AOriginalOrderedThirdTable.first_cube he hecap hstep ht hstop
  have hupper :=
    P4AOriginalOrderedThirdTable.cap_on_ordered he.le ht
  constructor <;> linarith

/-- Only the selected lower mode requires this quantizer range.
The distinct inactive initial exponent may exceed VariableEnvelope.cap. -/
theorem current_scalar_range_of_lower
    (d : OriginalData) (omega N : ℝ) (pre : List ℕ)
    (he : 0 < (d.e : ℝ))
    (hecap : (d.e : ℝ) ≤ 1 / 384)
    (hstep :
      logPrimeMeshStep 0 (19 / 96) d.m ≤ (d.e : ℝ) / 2)
    (hlower : (current d omega N pre).lower) :
    0 ≤ (current d omega N pre).scalar ∧
      (current d omega N pre).scalar ≤ VariableEnvelope.cap := by
  let h3 := rosserAncestor 3 pre
  let t := primeHistoryLogCoordinates N 3 h3
  have hinfo :
      t 0 ≤ mu ∧ HistoricalThirdCoarse.active omega N h3 ∧
        ∃ j ∈ P4AOriginalOrderedThirdTable.retained (d.e : ℝ) d.m,
          t ∈ logPrimeMeshCell 0 (19 / 96) d.m j := hlower
  obtain ⟨_hmu, hactive, j, hj, ht⟩ := hinfo
  have hscalar :
      (current d omega N pre).scalar =
        P4AOriginalOrderedThirdTable.capValue (d.e : ℝ) d.m j := by
    change
      P4AOriginalOrderedThirdTable.rawExponent
        (d.e : ℝ) d.m omega N h3 =
          P4AOriginalOrderedThirdTable.capValue (d.e : ℝ) d.m j
    rw [P4AOriginalOrderedThirdTable.rawExponent,
      if_pos hactive,
      P4AOriginalOrderedThirdTable.atPoint_on_cell hj ht]
  rw [hscalar]
  exact retained_capValue_range he hecap hstep hj

/-- Exactly the conditional exponent used by ordered five. -/
def effectiveFifth
    (R : Root) (d : OriginalData) (N : ℝ)
    (n : ℕ) (pre : List ℕ) : ℝ :=
  if R.lower then cap5 R d N n pre else fifth R d N pre

theorem effectiveFifth_abs_error
    (R : Root) (d : OriginalData) (N : ℝ)
    (n : ℕ) (pre : List ℕ)
    (he : 0 ≤ (d.e : ℝ))
    (hR : R.lower →
      0 ≤ R.scalar ∧ R.scalar ≤ VariableEnvelope.cap) :
    |fifth R d N pre - effectiveFifth R d N n pre| <
      2 * width n := by
  by_cases hlower : R.lower
  · simpa only [effectiveFifth, if_pos hlower] using
      cap5_abs_error R d N n pre he (hR hlower).1 (hR hlower).2
  · simp only [effectiveFifth, if_neg hlower, sub_self, abs_zero]
    exact mul_pos (by norm_num : (0 : ℝ) < 2) (width_pos n)

def ownCubeProfile {k : ℕ}
    (lambda : ℝ) (t : Fin (k + 1) → ℝ) : ℝ :=
  if primeTupleOwnCubeForm t < lambda then
    primeTupleMinusProfile lambda t else 0

/-- One actual prime-mean threshold precedes n, all row banks, root and history.
The last inequality controls the signed arithmetic replacement error. -/
theorem exists_actual_fifth_cap5_residual_uniform_threshold
    (a b eta : ℝ) (ha : 0 < a) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N
          (fun _ : Fin 5 => a) (fun _ => b),
      ∀ (n : ℕ) (d : OriginalData) (R : Root) (pre : List ℕ),
        0 ≤ (d.e : ℝ) →
        0 ≤ R.scalar →
        R.scalar ≤ VariableEnvelope.cap →
        let raw := fifth R d (N : ℝ) pre
        let finite := cap5 R d (N : ℝ) n pre
        let t := actualPrimeTupleLog N p
        |actualPrimeTupleOwnCubeMinus N cap raw p -
            ownCubeProfile raw t| < eta / 2 ∧
          |actualPrimeTupleOwnCubeMinus N cap finite p -
            ownCubeProfile finite t| < eta / 2 ∧
          |(actualPrimeTupleOwnCubeMinus N cap raw p -
              actualPrimeTupleOwnCubeMinus N cap finite p) -
            (ownCubeProfile raw t - ownCubeProfile finite t)| < eta := by
  obtain ⟨N₀, hN₀, hmean⟩ :=
    P1VariableOwnCubeResidualUniformity.
      exists_actualPrimeTupleOwnCubeMinus_uniform_levels_threshold
        4 a b 0 VariableEnvelope.cap ha
        (eta / 2) (half_pos heta)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcover p hp n d R pre he hs hc
  dsimp only
  have hf := fifth_range R d (N : ℝ) pre he hc
  have hq := cap5_bounds R d (N : ℝ) n pre he hs hc
  have hraw :
      |actualPrimeTupleOwnCubeMinus N cap
          (fifth R d (N : ℝ) pre) p -
        ownCubeProfile (fifth R d (N : ℝ) pre)
          (actualPrimeTupleLog N p)| < eta / 2 := by
    simpa only [ownCubeProfile] using
      hmean N hN hEven cap hcover p hp
        (fifth R d (N : ℝ) pre)
        ⟨hs.trans hf.1, hf.2⟩
  have hfinite :
      |actualPrimeTupleOwnCubeMinus N cap
          (cap5 R d (N : ℝ) n pre) p -
        ownCubeProfile (cap5 R d (N : ℝ) n pre)
          (actualPrimeTupleLog N p)| < eta / 2 := by
    simpa only [ownCubeProfile] using
      hmean N hN hEven cap hcover p hp
        (cap5 R d (N : ℝ) n pre)
        ⟨hs.trans hq.1, hq.2.2.trans hf.2⟩
  refine ⟨hraw, hfinite, ?_⟩
  let A := actualPrimeTupleOwnCubeMinus N cap
    (fifth R d (N : ℝ) pre) p
  let B := actualPrimeTupleOwnCubeMinus N cap
    (cap5 R d (N : ℝ) n pre) p
  let F := ownCubeProfile (fifth R d (N : ℝ) pre)
    (actualPrimeTupleLog N p)
  let G := ownCubeProfile (cap5 R d (N : ℝ) n pre)
    (actualPrimeTupleLog N p)
  change |(A - B) - (F - G)| < eta
  have hA : |A - F| < eta / 2 := hraw
  have hB : |B - G| < eta / 2 := hfinite
  calc
    |(A - B) - (F - G)| =
        |(A - F) + (-(B - G))| := by
          congr 1
          ring
    _ ≤ |A - F| + |B - G| := by
      simpa only [abs_neg] using
        (abs_add (A - F) (-(B - G)))
    _ < eta := by linarith

/-- The actual conditional mode is retained; outside lower mode both differences vanish. -/
theorem exists_current_effectiveFifth_residual_uniform_threshold
    (a b eta : ℝ) (ha : 0 < a) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N
          (fun _ : Fin 5 => a) (fun _ => b),
      ∀ d : OriginalData,
        0 < (d.e : ℝ) →
        (d.e : ℝ) ≤ 1 / 384 →
        logPrimeMeshStep 0 (19 / 96) d.m ≤ (d.e : ℝ) / 2 →
      ∀ (omega : ℝ) (n : ℕ) (pre : List ℕ),
        let R := current d omega (N : ℝ) pre
        let raw := fifth R d (N : ℝ) pre
        let finite := effectiveFifth R d (N : ℝ) n pre
        let t := actualPrimeTupleLog N p
        |(actualPrimeTupleOwnCubeMinus N cap raw p -
            actualPrimeTupleOwnCubeMinus N cap finite p) -
          (ownCubeProfile raw t - ownCubeProfile finite t)| < eta := by
  obtain ⟨N₀, hN₀, hmean⟩ :=
    exists_actual_fifth_cap5_residual_uniform_threshold a b eta ha heta
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcover p hp d he hecap hstep omega n pre
  dsimp only
  by_cases hlower : (current d omega (N : ℝ) pre).lower
  · obtain ⟨hs, hc⟩ :=
      current_scalar_range_of_lower
        d omega (N : ℝ) pre he hecap hstep hlower
    have hh := hmean N hN hEven cap hcover p hp n d
      (current d omega (N : ℝ) pre) pre he.le hs hc
    simpa only [effectiveFifth, if_pos hlower] using hh.2.2
  · simp only [effectiveFifth, if_neg hlower, sub_self, abs_zero]
    exact heta

/-- The literal current policy's two fifth levels have close actual
normalized own-cube residuals on one fixed positive prime box.
The grid threshold does not depend on the later physical cutoff. -/
theorem exists_current_effectiveFifth_residual_small
    (a b eta : ℝ) (ha : 0 < a) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N
          (fun _ : Fin 5 => a) (fun _ => b),
      ∀ d : OriginalData,
        0 < (d.e : ℝ) → (d.e : ℝ) ≤ 1 / 384 →
        logPrimeMeshStep 0 (19 / 96) d.m ≤ (d.e : ℝ) / 2 →
      ∀ (omega : ℝ) (n : ℕ) (pre : List ℕ),
        2 * width n ≤ delta →
        let R := current d omega (N : ℝ) pre
        |actualPrimeTupleOwnCubeMinus N cap
            (fifth R d (N : ℝ) pre) p -
          actualPrimeTupleOwnCubeMinus N cap
            (effectiveFifth R d (N : ℝ) n pre) p| < eta := by
  obtain ⟨delta, hdelta, N₀, hN₀, hclose⟩ :=
    P4AOriginalFiniteFifthCompactProfile.exists_actual_levels_close_threshold
      4 a b 0 VariableEnvelope.cap eta ha heta
  refine ⟨delta, hdelta, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcover p hp d he hecap hstep omega n pre hn
  dsimp only
  by_cases hlower : (current d omega (N : ℝ) pre).lower
  · obtain ⟨hs, hc⟩ := current_scalar_range_of_lower
      d omega (N : ℝ) pre he hecap hstep hlower
    have hf := fifth_range (current d omega (N : ℝ) pre)
      d (N : ℝ) pre he.le hc
    have hq := cap5_bounds (current d omega (N : ℝ) pre)
      d (N : ℝ) n pre he.le hs hc
    have hd := cap5_abs_error (current d omega (N : ℝ) pre)
      d (N : ℝ) n pre he.le hs hc
    have hh := hclose N hN hEven cap hcover p hp
      (fifth (current d omega (N : ℝ) pre) d (N : ℝ) pre)
      (cap5 (current d omega (N : ℝ) pre) d (N : ℝ) n pre)
      ⟨hs.trans hf.1, hf.2⟩
      ⟨hs.trans hq.1, hq.2.2.trans hf.2⟩
      (hd.le.trans hn)
    simpa only [effectiveFifth, if_pos hlower] using hh
  · simp only [effectiveFifth, if_neg hlower, sub_self, abs_zero]
    exact heta

/-- One cofinal resolution works for every actual row bank and current root,
before omega and the target N are chosen. -/
theorem exists_cofinal_current_effectiveFifth_residual_small
    (a b eta : ℝ) (ha : 0 < a) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
      ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N
          (fun _ : Fin 5 => a) (fun _ => b),
      ∀ d : OriginalData,
        0 < (d.e : ℝ) → (d.e : ℝ) ≤ 1 / 384 →
        logPrimeMeshStep 0 (19 / 96) d.m ≤ (d.e : ℝ) / 2 →
      ∀ (omega : ℝ) (pre : List ℕ),
        let R := current d omega (N : ℝ) pre
        |actualPrimeTupleOwnCubeMinus N cap
            (fifth R d (N : ℝ) pre) p -
          actualPrimeTupleOwnCubeMinus N cap
            (effectiveFifth R d (N : ℝ) n pre) p| < eta := by
  obtain ⟨delta, hdelta, N₀, hN₀, hsmall⟩ :=
    exists_current_effectiveFifth_residual_small a b eta ha heta
  obtain ⟨n₀, hn₀⟩ :=
    P4AOriginalFull87FiniteEighthCap.exists_uniform_cap_resolution delta hdelta
  refine ⟨n₀, N₀, hN₀, ?_⟩
  intro n hn N hN hEven cap hcover p hp d he hecap hstep omega pre
  have hgrid : 2 * width n ≤ delta := by
    have hh := hn₀ n hn
    have hwpos := width_pos n
    linarith
  exact hsmall N hN hEven cap hcover p hp d he hecap hstep omega n pre hgrid

end
end ImbalancedChen.P4AOriginalOrderedFifthRoundingResidual
