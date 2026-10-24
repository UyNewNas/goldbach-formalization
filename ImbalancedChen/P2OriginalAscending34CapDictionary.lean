import ImbalancedChen.ActualSelectedPrefixCapSelector
import ImbalancedChen.FirstExitHistoricalLevels
import ImbalancedChen.ActualRosserInitialResidualSaving

/-!
# Original saving 9: ascending34 geometry and actual residual dictionary

Read-only original sources in the release cache:
* replay_public_full.py, ninth saving: ascending34_actual_parent;
* sixth-tent34-ascending-independent-20261009.py, scalar semantics;
  SHA256 e7235a849c4144db845c537206e62ac9f38fdf3e36f7b97cd38f2ff52f107564;
* sixth-tent34-ascending-upgrade-20261009.tex, actual-parent comparison;
  SHA256 4d25e04d09ea569ef3c95a6c2b5e6e84380c6126e6f0963daa9034b05a411cf4.

Here mask34 is zero-based {1,5} = the physical slots {2,6}. The proposed
cap is M=(1+t2+t6)/2-10^-6. Its comparison parent is R=max(R0,D33), not
R0 on the second chart. These are six selected primes, so the concrete
policy below freezes at rank 6. Relabelling it as the rank-4/rank-5
historical policies would be incorrect.

The source's old-subset branch inequalities exclude previous clipped
actions, and exclude the previous ascending33 action. The surviving
descending33 cap is bounded by the explicit comparison envelope. The
actual quotient-density theorem below proves the conservative incremental
gain against that envelope, with the original coefficient 4.

Still open: identify the complete existing previous-policy implementation
and original adopted cells with these source guards, verify all saved
polytope/branch data, and integrate the resulting actual parent frontier.
No 621-term numerical certificate, original total, or final gain is assumed.
-/

namespace ImbalancedChen.P2OriginalAscending34CapDictionary

noncomputable section

open Set VariableEnvelope
open scoped Classical BigOperators

def eta : ℝ := 1 / 1000000
def mask34 : Finset (Fin 6) := {1, 5}
def S (t : Fin 6 → ℝ) : ℝ := ∑ i, t i
def R0 (t : Fin 6 → ℝ) : ℝ := (1 + t 0) / 2
def A33 (t : Fin 6 → ℝ) : ℝ := (1 + t 0 + t 5) / 2
def D33 (t : Fin 6 → ℝ) : ℝ := 57 / 64 - 3 / 2 * (t 0 + t 5)
def A34 (t : Fin 6 → ℝ) : ℝ := (1 + t 1 + t 5) / 2
def D34 (t : Fin 6 → ℝ) : ℝ := 57 / 64 - 3 / 2 * (t 1 + t 5)
def M (t : Fin 6 → ℝ) : ℝ := A34 t - eta
def clippedC (t : Fin 6 → ℝ) : ℝ := S t + 3 * t 5 - eta
def comparisonR (t : Fin 6 → ℝ) : ℝ := max (R0 t) (D33 t)
def previousBufferedEnvelope (t : Fin 6 → ℝ) : ℝ := max (R0 t) (D33 t - eta)

/-- Exact affine map used by both frozen source producers; q3=R0-S5 and
q4=R0-H5, in zero-based coordinate notation. -/
def physical (q : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![q 0, q 1, q 2, (1 - q 0) / 2 - q 1 - q 2 + (q 4 - 3 * q 3) / 2,
    (q 3 - q 4) / 2, q 5]

theorem physical_sum_dictionary (q : Fin 6 → ℝ) :
    S (physical q) = R0 (physical q) - q 3 + q 5 := by
  norm_num [S, physical, R0, Fin.sum_univ_succ] <;> ring

theorem physical_fifth_history_dictionary (q : Fin 6 → ℝ) :
    physical q 0 + physical q 1 + physical q 2 + physical q 3 + 3 * physical q 4 =
      R0 (physical q) - q 4 := by
  norm_num [physical, R0] <;> ring

theorem physical_M_dictionary (q : Fin 6 → ℝ) :
    M (physical q) = (1 + q 1 + q 5) / 2 - 1 / 1000000 := by
  norm_num [M, A34, physical, eta]

theorem mask34_sum (t : Fin 6 → ℝ) : (∑ i ∈ mask34, t i) = t 1 + t 5 := by
  norm_num [mask34]

theorem ascending34_tent_license (t : Fin 6 → ℝ) (hbranch : A34 t < D34 t) :
    M t < v (∑ i ∈ mask34, t i) := by
  rw [mask34_sum, v_eq_min]
  have hA : A (t 1 + t 5) = A34 t := by unfold A A34; ring
  have hD : C (t 1 + t 5) = D34 t := by unfold C D34; ring
  rw [hA, hD, min_eq_left hbranch.le]
  unfold M eta
  linarith

theorem comparisonR_chart0 (t : Fin 6 → ℝ) (h : D33 t ≤ R0 t) :
    comparisonR t = R0 t := max_eq_left h

theorem comparisonR_chart1 (t : Fin 6 → ℝ) (h : R0 t ≤ D33 t) :
    comparisonR t = D33 t := max_eq_right h

/-- Each of the producer's 31 old-subset branch rows has exactly this
semantic implication, before any pattern classification or vertex claim. -/
theorem old_subset_cap_le_R0 (t : Fin 6 → ℝ) (B : ℝ)
    (hbranch : B ≤ t 0 ∨ 25 / 64 ≤ 3 / 2 * B + t 0 / 2) : v B ≤ R0 t := by
  rw [v_eq_min]
  rcases hbranch with h | h
  · apply (min_le_left _ _).trans
    dsimp [A, R0]
    linarith
  · apply (min_le_right _ _).trans
    dsimp [C, R0]
    linarith

/-- Literal C>A33 excludes a previous clipped action for either recorded
old-subset branch. The proof uses the source's tent, including its min. -/
theorem old_selected_clipped_excluded (t : Fin 6 → ℝ) (B : ℝ)
    (hr : 0 < t 5) (hclip : A33 t < clippedC t)
    (hbranch : B ≤ t 0 ∨ 25 / 64 ≤ 3 / 2 * B + t 0 / 2) :
    v (B + t 5) < clippedC t := by
  rw [v_eq_min]
  rcases hbranch with h | h
  · have hA : A (B + t 5) ≤ A33 t := by dsimp [A, A33]; linarith
    exact (min_le_left _ _).trans_lt (hA.trans_lt hclip)
  · have hD : C (B + t 5) < R0 t := by dsimp [C, R0]; linarith
    have h0A : R0 t < A33 t := by dsimp [R0, A33]; linarith
    exact (min_le_right _ _).trans_lt (hD.trans (h0A.trans hclip))

theorem previous_ascending33_excluded (t : Fin 6 → ℝ) (horder : t 1 ≤ t 0)
    (hupgrade : comparisonR t < M t) : ¬ A33 t - eta < D33 t := by
  intro hprior
  have hM : M t ≤ A33 t - eta := by dsimp [M, A34, A33]; linarith
  have hD : D33 t ≤ comparisonR t := le_max_right _ _
  linarith

/-- The remaining old descending33 option, even when active, stays below
the comparison cap used by saving 9. This is not an equality with R0. -/
theorem previousBufferedEnvelope_bounds (t : Fin 6 → ℝ) :
    R0 t ≤ previousBufferedEnvelope t ∧ previousBufferedEnvelope t ≤ comparisonR t := by
  refine ⟨le_max_left _ _, max_le_max le_rfl ?_⟩
  dsimp [eta]
  linarith

/-- These are exactly the four strict residual rows in the original
ascending34 producer, with the actual comparison parent retained. -/
def ResidualGuard (t : Fin 6 → ℝ) : Prop :=
  0 < t 5 ∧ S t + t 5 < R0 t ∧ comparisonR t < M t ∧ M t < S t + 3 * t 5

/-- The producer's remaining geometric/support rows. The finite old subset
branch alternatives are retained; their saved pattern1371 specialization
and the polytope vertex verification are separate binding obligations. -/
def SupportGuard (t : Fin 6 → ℝ) : Prop :=
  StrictAnti t ∧ t 0 < 25 / 128 ∧ t 5 < 1 / 50 ∧ 53 / 4608 < t 5 ∧
    t 0 + t 1 + 3 * t 2 < R0 t ∧
    t 0 + t 1 + t 2 + t 3 + 3 * t 4 < R0 t ∧
    153 / 256 - 3 * t 2 / 8 ≤ R0 t ∧
    (∀ I : Finset (Fin 5), I.Nonempty →
      (∑ i ∈ I, t i.castSucc) ≤ t 0 ∨
        25 / 64 ≤ 3 / 2 * (∑ i ∈ I, t i.castSucc) + t 0 / 2) ∧
    A33 t < clippedC t ∧ A34 t < D34 t ∧ 1 / 2 < M t ∧
    (∀ i, prefixSquareExpr t i < M t) ∧
    (∀ i ∉ mask34, selectedSquareExpr mask34 t i < M t)

def SourceGuard (t : Fin 6 → ℝ) : Prop :=
  ResidualGuard t ∧ SupportGuard t ∧ (R0 t < D33 t ∨ D33 t < R0 t)

theorem sourceGuard_support_license (t : Fin 6 → ℝ) (h : SourceGuard t) :
    1 / 2 < M t ∧ (∀ i, prefixSquareExpr t i < M t) ∧
      (∀ i ∉ mask34, selectedSquareExpr mask34 t i < M t) ∧
      M t < v (∑ i ∈ mask34, t i) := by
  rcases h.2.1 with ⟨_hord, _hx, _hru, _hrl, _h3, _h5, _hw, _hsub,
    _hclip, hbranch, hhalf, hfull, hselected⟩
  exact ⟨hhalf, hfull, hselected, ascending34_tent_license t hbranch⟩

theorem sourceGuard_old_subsets_dominated (t : Fin 6 → ℝ) (h : SourceGuard t)
    (I : Finset (Fin 5)) (hI : I.Nonempty) :
    v (∑ i ∈ I, t i.castSucc) ≤ R0 t := by
  rcases h.2.1 with ⟨_hord, _hx, _hru, _hrl, _h3, _h5, _hw, hsub, _hrest⟩
  exact old_subset_cap_le_R0 t _ (hsub I hI)

theorem residual_parameter_range (t : Fin 6 → ℝ) (h : ResidualGuard t)
    (current : ℝ) (hlo : R0 t ≤ current) (hhi : current ≤ comparisonR t) :
    0 < t 5 ∧ t 5 < current - S t ∧ current - S t ≤ 3 * t 5 ∧
      t 5 < M t - S t ∧ M t - S t ≤ 3 * t 5 := by
  have hR0 : R0 t ≤ comparisonR t := le_max_left _ _
  rcases h with ⟨hr, hlow, hgain, htop⟩
  refine ⟨hr, ?_, ?_, ?_, ?_⟩ <;> linarith

def sourceGain (old new : ℝ) (t : Fin 6 → ℝ) : ℝ :=
  4 * (new - old) / ((old - S t) * (new - S t))

theorem sourceGain_eq_difference (old new : ℝ) (t : Fin 6 → ℝ)
    (ho : 0 < old - S t) (hn : 0 < new - S t) :
    sourceGain old new t = 4 / (old - S t) - 4 / (new - S t) := by
  unfold sourceGain
  field_simp [ho.ne', hn.ne'] <;> ring

/-- Replacing the true old parent by its larger comparison envelope lowers
the incremental gain. The previous descending33 gain is paid only once. -/
theorem comparison_gain_le_actual_parent (t : Fin 6 → ℝ) (h : ResidualGuard t)
    (current : ℝ) (hlo : R0 t ≤ current) (hhi : current ≤ comparisonR t) :
    sourceGain (comparisonR t) (M t) t ≤ sourceGain current (M t) t := by
  have hc := residual_parameter_range t h current hlo hhi
  have hR := residual_parameter_range t h (comparisonR t) (le_max_left _ _) le_rfl
  have hcp : 0 < current - S t := hc.1.trans hc.2.1
  have hRp : 0 < comparisonR t - S t := hR.1.trans hR.2.1
  have hMp : 0 < M t - S t := hc.1.trans hc.2.2.2.1
  have hi := one_div_le_one_div_of_le hcp (sub_le_sub_right hhi (S t))
  have h4 : 4 / (comparisonR t - S t) ≤ 4 / (current - S t) := by
    convert mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
  rw [sourceGain_eq_difference _ _ t hRp hMp, sourceGain_eq_difference _ _ t hcp hMp]
  exact sub_le_sub_right h4 _

/-- Actual ordinary residuals at the literal quotient levels realize the
source's conservative same-node profile, with a proved uniform threshold.
The current cap is permitted to be any actual parent between R0 and R.
No finite coefficientwise monotonicity or final integral gain is assumed. -/
theorem exists_actual_ascending34_increment_threshold (t : Fin 6 → ℝ)
    (h : ResidualGuard t) (current : ℝ) (hlo : R0 t ≤ current)
    (hhi : current ≤ comparisonR t) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y : ℝ, 0 < P → 0 < y →
        Real.log P / Real.log (N : ℝ) = S t →
        Real.log y / Real.log (N : ℝ) = t 5 →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          sourceGain (comparisonR t) (M t) t - epsilon <
            (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current / P) -
              actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P)) *
                Real.log (N : ℝ) / singularSeries N := by
  let T : Set (ℝ × ℝ) := {(current - S t, t 5)} ∪ {(M t - S t, t 5)}
  have hT : IsCompact T := isCompact_singleton.union isCompact_singleton
  have hc := residual_parameter_range t h current hlo hhi
  have hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2 := by
    intro p hp
    rcases hp with hp | hp
    · have heq := Set.mem_singleton_iff.mp hp
      subst p
      exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
    · have heq := Set.mem_singleton_iff.mp hp
      subst p
      exact ⟨hc.1, hc.2.2.2.1, hc.2.2.2.2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold T hT hparam epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y hP hy hlogP hlogy cap hcap
  have hOld : actualRosserQuotientParameters (N : ℝ) P y current ∈ T := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
    exact Or.inl (Set.mem_singleton _)
  have hNew : actualRosserQuotientParameters (N : ℝ) P y (M t) ∈ T := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
    exact Or.inr (Set.mem_singleton _)
  have hb := abs_lt.mp (hbound N hN hEven P y current (M t) hP hy hOld hNew cap hcap)
  rw [hlogP] at hb
  have hcomp := comparison_gain_le_actual_parent t h current hlo hhi
  unfold sourceGain at hcomp ⊢
  linarith [hb.1]

/-- On a fixed compact original cell, one threshold precedes every target
and every tuple. This is the required quantifier order for applying the
dictionary on continuously labelled parent-cap cells. -/
theorem exists_actual_ascending34_compact_increment_threshold
    (K : Set (Fin 6 → ℝ)) (hK : IsCompact K)
    (hguard : ∀ t ∈ K, ResidualGuard t) (current : (Fin 6 → ℝ) → ℝ)
    (hcurrent : ContinuousOn current K)
    (hparent : ∀ t ∈ K, R0 t ≤ current t ∧ current t ≤ comparisonR t)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ t ∈ K, ∀ P y : ℝ, 0 < P → 0 < y →
        Real.log P / Real.log (N : ℝ) = S t →
        Real.log y / Real.log (N : ℝ) = t 5 →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          sourceGain (comparisonR t) (M t) t - epsilon <
            (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current t / P) -
              actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P)) *
                Real.log (N : ℝ) / singularSeries N := by
  let Fc (t : Fin 6 → ℝ) := (current t - S t, t 5)
  let Fm (t : Fin 6 → ℝ) := (M t - S t, t 5)
  let T : Set (ℝ × ℝ) := Fc '' K ∪ Fm '' K
  have hS : Continuous S := by unfold S; fun_prop
  have hM : Continuous M := by unfold M A34 eta; fun_prop
  have hFc : ContinuousOn Fc K :=
    (hcurrent.sub hS.continuousOn).prodMk (continuous_apply 5).continuousOn
  have hFm : ContinuousOn Fm K :=
    (hM.continuousOn.sub hS.continuousOn).prodMk (continuous_apply 5).continuousOn
  have hT : IsCompact T := (hK.image_of_continuousOn hFc).union (hK.image_of_continuousOn hFm)
  have hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2 := by
    intro p hp
    rcases hp with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · have h := residual_parameter_range t (hguard t ht) (current t)
        (hparent t ht).1 (hparent t ht).2
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    · have h := residual_parameter_range t (hguard t ht) (current t)
        (hparent t ht).1 (hparent t ht).2
      exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold T hT hparam epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven t ht P y hP hy hlogP hlogy cap hcap
  have hOld : actualRosserQuotientParameters (N : ℝ) P y (current t) ∈ T := by
    apply Or.inl
    refine ⟨t, ht, ?_⟩
    simp only [Fc, actualRosserQuotientParameters, hlogP, hlogy]
  have hNew : actualRosserQuotientParameters (N : ℝ) P y (M t) ∈ T := by
    apply Or.inr
    refine ⟨t, ht, ?_⟩
    simp only [Fm, actualRosserQuotientParameters, hlogP, hlogy]
  have hb := abs_lt.mp (hbound N hN hEven P y (current t) (M t) hP hy hOld hNew cap hcap)
  rw [hlogP] at hb
  have hcomp := comparison_gain_le_actual_parent t (hguard t ht) (current t)
    (hparent t ht).1 (hparent t ht).2
  unfold sourceGain at hcomp ⊢
  linarith [hb.1]

/-- Literal source formula used as a level function on actual histories. -/
def sourceLevel (N : ℝ) (history : List ℕ) : ℝ :=
  N ^ M (primeHistoryLogCoordinates N 6 history)

theorem sourceLevel_literal_formula (N : ℝ) (history : List ℕ) :
    sourceLevel N history = N ^ ((1 + primeHistoryLogCoordinates N 6 history 1 +
      primeHistoryLogCoordinates N 6 history 5) / 2 - 1 / 1000000) := rfl

/-- The source's full and mask34 exponent rows imply the existing literal
natural-history support gates, using the exact log/rpow dictionary. -/
theorem sourceLevel_actual_square_gates (N : ℝ) (hN : 1 < N)
    (history : List ℕ) (hlen : history.length = 6) (hpos : ∀ p ∈ history, 0 < p)
    (hguard : SourceGuard (primeHistoryLogCoordinates N 6 history)) :
    (∀ i, ((∏ k ∈ Finset.univ.filter (fun k => k < i),
        primeHistoryTuple 6 history k : ℕ) : ℝ) *
      (primeHistoryTuple 6 history i : ℝ) ^ 2 < sourceLevel N history) ∧
    (∀ i ∉ mask34, ((∏ k ∈ mask34, primeHistoryTuple 6 history k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k => k < i ∧ k ∉ mask34),
        primeHistoryTuple 6 history k : ℕ) : ℝ) *
      (primeHistoryTuple 6 history i : ℝ) ^ 2 < sourceLevel N history) := by
  have hs := sourceGuard_support_license _ hguard
  have hp : ∀ i, (primeHistoryTuple 6 history i : ℝ) ≤
      N ^ primeHistoryLogCoordinates N 6 history i := by
    intro i
    rw [rpow_primeHistoryLogCoordinates N hN hlen hpos i]
  exact ⟨fun i => prefixSquareExpr_actual_gate N hN _ _ hp i (hs.2.1 i),
    fun i hi => selectedSquareExpr_actual_gate mask34 N hN _ _ hp i (hs.2.2.1 i hi)⟩

def comparisonLevel (N : ℝ) (history : List ℕ) : ℝ :=
  N ^ comparisonR (primeHistoryLogCoordinates N 6 history)

/-- The source row guard fixes where this local action is used; equality
faces and points outside its strict region keep the comparison action. -/
def guardedSourceLevel (N : ℝ) (history : List ℕ) : ℝ :=
  if SourceGuard (primeHistoryLogCoordinates N 6 history) then sourceLevel N history
  else comparisonLevel N history

theorem comparisonLevel_le_guardedSourceLevel (N : ℝ) (hN : 1 ≤ N) (history : List ℕ) :
    comparisonLevel N history ≤ guardedSourceLevel N history := by
  unfold guardedSourceLevel
  split_ifs with h
  · apply Real.rpow_le_rpow_of_exponent_le hN
    exact h.1.2.2.1.le
  · exact le_rfl

def sourcePolicy (N : ℝ) (parent : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 parent (frozenParityRosserPolicy false 6 (guardedSourceLevel N))

theorem sourcePolicy_after_six (N : ℝ) (parent : Bool → List ℕ → Bool)
    (positive : Bool) (history : List ℕ) (hlen : 6 < history.length) :
    sourcePolicy N parent positive history =
      ordinaryParityRosserPolicy false (guardedSourceLevel N (rosserAncestor 6 history))
        positive history := by
  simp only [sourcePolicy, firstExitDepthSplicePolicy, if_neg (by omega : ¬history.length ≤ 6),
    frozenParityRosserPolicy, ancestorFrozenPolicy]

theorem sourceFrozenLevel_append (N : ℝ) (later history : List ℕ)
    (hlen : 6 ≤ history.length) :
    guardedSourceLevel N (rosserAncestor 6 (later ++ history)) =
      guardedSourceLevel N (rosserAncestor 6 history) := by
  rw [rosserAncestor_append 6 later history hlen]

theorem sourcePolicy_frontier_six (N : ℝ) (parent : Bool → List ℕ → Bool)
    (weight : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 6 (sourcePolicy N parent) weight pre positive mass carrier =
      firstExitDepthFrontier 6 parent weight pre positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 6 6 le_rfl parent _ weight pre carrier positive mass

/-- The existing generic frozen-density theorem binds this concrete sixth
level to the same actual parent frontier. Old admission is the only parent
obligation; new admission follows from the proved level comparison. -/
theorem actual_sixth_source_splice_saving (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ)
    (parent : Bool → List ℕ → Bool)
    (hold : ∀ state ∈ firstExitDepthFrontier 6 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ordinaryRosserPrefixAdmissible false (comparisonLevel (N : ℝ) state.selectedPrefix)
        state.selectedPrefix) :
    firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy 6 parent (frozenParityRosserPolicy false 6 (comparisonLevel (N : ℝ))))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (sourcePolicy (N : ℝ) parent)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier 6 parent (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 z)).map (fun state =>
          actualFrozenFrontierDensityTerm false N cap (comparisonLevel (N : ℝ)) state.selectedPrefix -
            actualFrozenFrontierDensityTerm false N cap (guardedSourceLevel (N : ℝ)) state.selectedPrefix)).sum := by
  apply firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum false 6 (by omega)
    parent (guardedSourceLevel (N : ℝ)) (comparisonLevel (N : ℝ)) N cap z
  · intro state hstate
    exact ordinaryRosserPrefixAdmissible_mono false state.selectedPrefix
      (comparisonLevel_le_guardedSourceLevel (N : ℝ) hN state.selectedPrefix) (hold state hstate)
  · exact hold

end

end ImbalancedChen.P2OriginalAscending34CapDictionary
