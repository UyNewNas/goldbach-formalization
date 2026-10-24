import ImbalancedChen.HistoricalPrefixCertificate
import ImbalancedChen.SelectedPrefixBoxCap
import ImbalancedChen.P1AdoptedPairMaskAncestorSupport

/-!
# Original saving 10: descending34 on the actual inherited parent

SOURCE ONLY, uncompiled.  Saving identifier: `descending34_actual_parent`.
Frozen sources read as text, never executed:
* `sixth-tent34-descending-independent-20261009.py`, SHA256
  35453e30c1e05e30e67a5253de87b67bb8cc8772306288b38bff267193898862;
* `sixth-tent34-descending-upgrade-20261009.tex`, SHA256
  6f449a0f047928f647507ed4c2c47fd06d8f4d4a13333cff91bacd50f44ea48c.
They were read in the complete local publication-20261010 release cache.

The producer uses a retained EVEN SIXTH node.  Its new mask is decimal34,
namely processing slots {2,6}; its new cap is D34-eta and its conservative
comparison is max(R0,D33).  The historical third/fourth/fifth ancestors
are NOT relabelled with this comparison.  The actual fourth/fifth policies
are passed intact to the post-sixth splice below, with their complete
frontiers preserved through rank six.  This rank distinction is essential:
this six-coordinate family is not an `actualHistoricalFifthSaving` value.

The branch vector is the literal pattern1371 old31 vector from both selected
charts.  The parameter-to-physical map and old-envelope branch slacks are
literal producer formulas.  No geometry mass, 558-simplex floor total,
final gain, cap-freezing theorem or arithmetic distribution is assumed.

The adopted E0/E1 and ancestor pair-mask suppliers are reused through the
P1 import.  Its future installation requires the two owned P1 drafts
`P1AdoptedE0E1ActualSupport.lean.txt` and
`P1AdoptedPairMaskAncestorSupport.lean`, together with the latter's declared
P1AdoptedMaskAncestors dependency.  No P1 source is modified here.

Remaining: prove the finite ancestor-refined compact freezing for this exact
support and its connection to ALL earlier merged sixth actions, then the
signed ordinary-density passage and exact geometrical floor certificate.
The conservative old33 ceiling proved here is an upper ceiling, not an
assertion that an old33 action is licensed at every point of a new cell.
-/

namespace ImbalancedChen.P2OriginalDescending34CapDictionary

noncomputable section

open scoped Classical BigOperators
open Set

def eta : ℝ := 1 / 1000000

def R0 (t : Fin 6 → ℝ) : ℝ := (1 + t 0) / 2

def A33 (t : Fin 6 → ℝ) : ℝ := (1 + t 0 + t 5) / 2

def A34 (t : Fin 6 → ℝ) : ℝ := (1 + t 1 + t 5) / 2

def D33 (t : Fin 6 → ℝ) : ℝ := 57 / 64 - 3 * (t 0 + t 5) / 2

def D34 (t : Fin 6 → ℝ) : ℝ := 57 / 64 - 3 * (t 1 + t 5) / 2

def sum5 (t : Fin 6 → ℝ) : ℝ := t 0 + t 1 + t 2 + t 3 + t 4

def sum6 (t : Fin 6 → ℝ) : ℝ := sum5 t + t 5

def H3 (t : Fin 6 → ℝ) : ℝ := t 0 + t 1 + 3 * t 2

def H5 (t : Fin 6 → ℝ) : ℝ := t 0 + t 1 + t 2 + t 3 + 3 * t 4

def oldW (t : Fin 6 → ℝ) : ℝ := 153 / 256 - 3 * t 2 / 8

def clippedC (t : Fin 6 → ℝ) : ℝ := sum5 t + 4 * t 5 - eta

/-- Conservative comparison only; it is not sent back to a history. -/
def currentParent (t : Fin 6 → ℝ) : ℝ := max (R0 t) (D33 t)

def newM (t : Fin 6 → ℝ) : ℝ := D34 t - eta

/-- The tent minimum whose descending branch is selected in this family. -/
def newTentMinimum (t : Fin 6 → ℝ) : ℝ := min (A34 t) (D34 t)

def selected34 : Finset (Fin 6) := {1, 5}

theorem selected34_decimal_mask : (∑ i ∈ selected34, (2 : ℕ) ^ i.val) = 34 := by
  norm_num [selected34]

theorem selected34_sum (t : Fin 6 → ℝ) : (∑ i ∈ selected34, t i) = t 1 + t 5 := by
  simp [selected34]

theorem selected34_product (p : Fin 6 → ℕ) : (∏ i ∈ selected34, p i) = p 1 * p 5 := by
  simp [selected34]

/-- Literal parameter coordinates q=(x,y,z,a,c,r), with the original
physical order (x,y,z,t4,t5,r). -/
def physical (q : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![q 0, q 1, q 2,
    (1 - q 0) / 2 - q 1 - q 2 - 3 * q 3 / 2 + q 4 / 2,
    (q 3 - q 4) / 2, q 5]

theorem physical_old_residual_coordinates (q : Fin 6 → ℝ) :
    R0 (physical q) - sum5 (physical q) = q 3 ∧
      R0 (physical q) - H5 (physical q) = q 4 := by
  dsimp [R0, sum5, H5, physical]
  constructor <;> ring

theorem physical_inverse (q : Fin 6 → ℝ) :
    ![(physical q) 0, (physical q) 1, (physical q) 2,
      R0 (physical q) - sum5 (physical q),
      R0 (physical q) - H5 (physical q), (physical q) 5] = q := by
  rw [(physical_old_residual_coordinates q).1, (physical_old_residual_coordinates q).2]
  funext i
  fin_cases i <;> rfl

theorem physical_injective : Function.Injective physical := by
  intro q p hqp
  calc
    q = ![(physical q) 0, (physical q) 1, (physical q) 2,
        R0 (physical q) - sum5 (physical q),
        R0 (physical q) - H5 (physical q), (physical q) 5] := (physical_inverse q).symm
    _ = ![(physical p) 0, (physical p) 1, (physical p) 2,
        R0 (physical p) - sum5 (physical p),
        R0 (physical p) - H5 (physical p), (physical p) 5] := by rw [hqp]
    _ = p := physical_inverse p

/-- Literal old branch bits, in mask order 1,...,31, in both charts. -/
def branch1371 : Fin 31 → Bool :=
  ![false, false, true, false, true, true, true, false,
    true, true, true, false, true, true, true, false,
    true, true, true, false, true, true, true, false,
    true, true, true, false, true, true, true]

def oldMask (m : Fin 31) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => Nat.testBit (m.val + 1) i.val)

def oldSubsetSum (m : Fin 31) (t : Fin 6 → ℝ) : ℝ :=
  ∑ i ∈ oldMask m, t i.castSucc

theorem oldMask_one : oldMask (0 : Fin 31) = {0} := by
  ext i
  fin_cases i <;> decide

theorem oldSubsetSum_one (t : Fin 6 → ℝ) : oldSubsetSum (0 : Fin 31) t = t 0 := by
  simp only [oldSubsetSum, oldMask_one, Finset.sum_singleton]

def oldTent (m : Fin 31) (t : Fin 6 → ℝ) : ℝ :=
  min ((1 + oldSubsetSum m t) / 2) (57 / 64 - 3 * oldSubsetSum m t / 2)

/-- R0 is already an old31 member on the actual below-mu support, so its
explicit occurrence in the max assembly does not add a new candidate. -/
theorem oldTent_one_eq_R0 {t : Fin 6 → ℝ} (hmu : t 0 ≤ (25 / 128 : ℝ)) :
    oldTent (0 : Fin 31) t = R0 t := by
  rw [oldTent, oldSubsetSum_one, min_eq_left (show (1 + t 0) / 2 ≤
    57 / 64 - 3 * t 0 / 2 by linarith)]
  rfl

/-- The producer tent is the existing variable-envelope license, rather
than a newly assumed license function. -/
theorem oldTent_eq_actual_v (m : Fin 31) (t : Fin 6 → ℝ) :
    oldTent m t = VariableEnvelope.v (oldSubsetSum m t) := by
  rw [VariableEnvelope.v_eq_min]
  unfold oldTent VariableEnvelope.A VariableEnvelope.C
  congr 1 <;> ring

theorem newTentMinimum_eq_actual_v (t : Fin 6 → ℝ) :
    newTentMinimum t = VariableEnvelope.v (∑ i ∈ selected34, t i) := by
  rw [selected34_sum, VariableEnvelope.v_eq_min]
  unfold newTentMinimum A34 D34 VariableEnvelope.A VariableEnvelope.C
  congr 1 <;> ring

def oldBranchSlack (m : Fin 31) (t : Fin 6 → ℝ) : ℝ :=
  if branch1371 m then
    3 * oldSubsetSum m t / 2 + t 0 / 2 - 25 / 64
  else t 0 - oldSubsetSum m t

/-- The mask1 constant identity is retained; every other producer branch
row uses its strict affine inequality. -/
def oldBranches1371 (t : Fin 6 → ℝ) : Prop :=
  ∀ m : Fin 31, if m.val = 0 then 0 ≤ oldBranchSlack m t else 0 < oldBranchSlack m t

theorem oldTent_le_R0_of_branch {t : Fin 6 → ℝ} (h : oldBranches1371 t) (m : Fin 31) :
    oldTent m t ≤ R0 t := by
  have hs : 0 ≤ oldBranchSlack m t := by
    by_cases hm : m.val = 0
    · simpa only [if_pos hm] using h m
    · exact (show 0 < oldBranchSlack m t by simpa only [if_neg hm] using h m).le
  by_cases hb : branch1371 m = true
  · have hslack : 0 ≤ 3 * oldSubsetSum m t / 2 + t 0 / 2 - 25 / 64 := by
      simpa [oldBranchSlack, hb] using hs
    exact (min_le_right _ _).trans (by dsimp [R0]; linarith)
  · have hslack : 0 ≤ t 0 - oldSubsetSum m t := by
      simpa [oldBranchSlack, hb] using hs
    exact (min_le_left _ _).trans (by dsimp [R0]; linarith)

/-- Explicit max assembly of all 31 old tent caps and W; R0 is included
as the singleton-one cap which is already selected by this source domain. -/
def rawOldEnvelope (t : Fin 6 → ℝ) : ℝ :=
  (List.ofFn (fun m : Fin 31 => oldTent m t)).foldr max (max (R0 t) (oldW t))

private theorem foldr_max_eq_of_le (b : ℝ) (l : List ℝ) (h : ∀ x ∈ l, x ≤ b) :
    l.foldr max b = b := by
  revert h
  induction l with
  | nil => intro h; rfl
  | cons x xs ih =>
    intro h
    rw [List.foldr_cons, ih (fun y hy => h y (List.mem_cons_of_mem x hy)),
      max_eq_right (h x (by simp))]

theorem rawOldEnvelope_eq_R0 {t : Fin 6 → ℝ}
    (hbranches : oldBranches1371 t) (hW : oldW t ≤ R0 t) : rawOldEnvelope t = R0 t := by
  unfold rawOldEnvelope
  rw [max_eq_left hW]
  apply foldr_max_eq_of_le
  intro x hx
  obtain ⟨m, rfl⟩ := List.mem_ofFn.mp hx
  exact oldTent_le_R0_of_branch hbranches m

/-- Literal physical support of the selected descending34 family.  The
old31 branches, both old histories, full squares and selected squares are
all read from the same six processing coordinates. -/
def descendingSupport (t : Fin 6 → ℝ) : Prop :=
  StrictAnti t ∧ 0 < t 5 ∧ t 0 < (25 / 128 : ℝ) ∧
  (53 / 4608 : ℝ) < t 5 ∧ t 5 < (1 / 50 : ℝ) ∧
  oldBranches1371 t ∧ oldW t ≤ R0 t ∧ H3 t < R0 t ∧ H5 t < R0 t ∧
  A33 t < clippedC t ∧ D34 t < A34 t ∧ currentParent t < newM t ∧
  (1 / 2 : ℝ) < newM t ∧
  (∀ j : Fin 6, prefixSquareExpr t j < newM t) ∧
  (∀ j : Fin 6, j ∉ selected34 → selectedSquareExpr selected34 t j < newM t) ∧
  newM t - sum6 t < 3 * t 5 ∧ t 5 < R0 t - sum6 t

theorem support_rawOldEnvelope {t : Fin 6 → ℝ} (hs : descendingSupport t) :
    rawOldEnvelope t = R0 t :=
  rawOldEnvelope_eq_R0 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1

theorem descending_min_cap {t : Fin 6 → ℝ} (hdesc : D34 t < A34 t) :
    newM t = newTentMinimum t - eta := by
  simp only [newM, newTentMinimum, min_eq_right hdesc.le]

theorem descending_licenses {t : Fin 6 → ℝ} (hdesc : D34 t < A34 t) :
    newM t < A34 t ∧ newM t < D34 t ∧ D34 t - newM t = eta := by
  have he : 0 < eta := by norm_num [eta]
  dsimp [newM]
  constructor
  · linarith
  constructor <;> linarith

/-- On the actual descending support the min/new-cap merge is exact. -/
theorem descending_merge_eq {t : Fin 6 → ℝ}
    (hdesc : D34 t < A34 t) (hnew : currentParent t < newM t) :
    max (currentParent t) (newTentMinimum t - eta) = newM t := by
  rw [← descending_min_cap hdesc]
  exact max_eq_right hnew.le

/-- Both frozen old33 formulas are bounded by D33 even when their
membership selectors are omitted.  This is a conservative comparison. -/
theorem old33_candidates_le_currentParent (t : Fin 6 → ℝ) :
    max (R0 t) (max (min (A33 t - eta) (D33 t)) (D33 t - eta)) ≤ currentParent t := by
  have he : 0 ≤ eta := by norm_num [eta]
  apply max_le (le_max_left _ _)
  apply max_le
  · exact (min_le_right _ _).trans (le_max_right _ _)
  · exact (sub_le_self _ he).trans (le_max_right _ _)

theorem chart_R0 {t : Fin 6 → ℝ} (h : D33 t ≤ R0 t) : currentParent t = R0 t :=
  max_eq_left h

theorem chart_D33 {t : Fin 6 → ℝ} (h : R0 t ≤ D33 t) : currentParent t = D33 t :=
  max_eq_right h

/-- The comparison range is the literal old R0 / conservative parent /
new M range from the frozen note. -/
theorem comparison_residual_range {t : Fin 6 → ℝ}
    (hr : 0 < t 5) (hold : t 5 < R0 t - sum6 t)
    (hnew : currentParent t < newM t) (hupper : newM t - sum6 t < 3 * t 5) :
    1 < (R0 t - sum6 t) / t 5 ∧
      1 < (currentParent t - sum6 t) / t 5 ∧
      (currentParent t - sum6 t) / t 5 < (newM t - sum6 t) / t 5 ∧
      (newM t - sum6 t) / t 5 < 3 := by
  have hR : R0 t ≤ currentParent t := le_max_left _ _
  refine ⟨(lt_div_iff₀ hr).mpr (by linarith),
    (lt_div_iff₀ hr).mpr (by linarith),
    (div_lt_div_iff_of_pos_right hr).mpr (by linarith),
    (div_lt_iff₀ hr).mpr hupper⟩

theorem selected34_remaining_squares (t : Fin 6 → ℝ) :
    selectedSquareExpr selected34 t 0 = t 1 + t 5 + 2 * t 0 ∧
    selectedSquareExpr selected34 t 2 = t 1 + t 5 + t 0 + 2 * t 2 ∧
    selectedSquareExpr selected34 t 3 = t 1 + t 5 + t 0 + t 2 + 2 * t 3 ∧
    selectedSquareExpr selected34 t 4 = t 1 + t 5 + t 0 + t 2 + t 3 + 2 * t 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [selectedSquareExpr, selected34, Finset.sum_filter, Fin.sum_univ_succ] <;> ring

/-- All guards refer to the same actual prime tuple.  The complete and
selected products retain their literal natural-number subproducts. -/
theorem actual_square_guards (N : ℝ) (hN : 1 < N)
    (p : Fin 6 → ℕ) (t : Fin 6 → ℝ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i)
    (hfull : ∀ j, prefixSquareExpr t j < newM t)
    (hselected : ∀ j ∉ selected34, selectedSquareExpr selected34 t j < newM t) :
    (∀ j, ((∏ i ∈ Finset.univ.filter (fun i => i < j), p i : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ newM t) ∧
    (∀ j ∉ selected34, ((∏ i ∈ selected34, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∉ selected34), p i : ℕ) : ℝ) *
        (p j : ℝ) ^ 2 < N ^ newM t) := by
  exact ⟨fun j => prefixSquareExpr_actual_gate N hN p t hp j (hfull j),
    fun j hj => selectedSquareExpr_actual_gate selected34 N hN p t hp j (hselected j hj)⟩

/-- The actual six-coordinate selector reads its own retained ancestor. -/
def historyCoordinates (N : ℝ) (history : List ℕ) : Fin 6 → ℝ :=
  primeHistoryLogCoordinates N 6 (rosserAncestor 6 history)

def selectedLevel (N : ℝ) (history : List ℕ) : ℝ := N ^ newM (historyCoordinates N history)

/-- Correct length removes every tuple default and fixes the exact
six processing coordinates of this retained history. -/
theorem historyCoordinates_eq_of_length (N : ℝ) (history : List ℕ)
    (hlen : history.length = 6) :
    historyCoordinates N history = primeHistoryLogCoordinates N 6 history := by
  unfold historyCoordinates
  rw [rosserAncestor_self_of_length 6 history hlen]

/-- The unbuffered R0 read at the actual earlier third and fifth histories
is the same raw R0 in the six-coordinate source.  Actual finite buffered
D.level3/D.level5 values are deliberately not replaced by this raw bound. -/
theorem raw_ancestor_root_dictionary (N : ℝ) (history : List ℕ)
    (hlen : history.length = 6) :
    (1 + primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) 0) / 2 =
        R0 (historyCoordinates N history) ∧
    (1 + primeHistoryLogCoordinates N 5 (rosserAncestor 5 history) 0) / 2 =
        R0 (historyCoordinates N history) := by
  rw [historyCoordinates_eq_of_length N history hlen]
  constructor
  · exact congrArg (fun x : ℝ => (1 + x) / 2)
      (primeHistoryLogCoordinates_ancestor N hlen (by omega : 3 ≤ 6) (0 : Fin 3))
  · exact congrArg (fun x : ℝ => (1 + x) / 2)
      (primeHistoryLogCoordinates_ancestor N hlen (by omega : 5 ≤ 6) (0 : Fin 5))

/-- The actual natural tuple and source coordinates have exactly the
same full and selected square guards; no integer gate is assumed. -/
theorem actual_history_square_guards (N : ℝ) (hN : 1 < N)
    (history : List ℕ) (hlen : history.length = 6)
    (hpos : ∀ p ∈ history, 0 < p)
    (hfull : ∀ j, prefixSquareExpr (historyCoordinates N history) j <
      newM (historyCoordinates N history))
    (hselected : ∀ j ∉ selected34,
      selectedSquareExpr selected34 (historyCoordinates N history) j <
        newM (historyCoordinates N history)) :
    (∀ j, ((∏ i ∈ Finset.univ.filter (fun i => i < j), primeHistoryTuple 6 history i : ℕ) : ℝ) *
      (primeHistoryTuple 6 history j : ℝ) ^ 2 < selectedLevel N history) ∧
    (∀ j ∉ selected34, ((∏ i ∈ selected34, primeHistoryTuple 6 history i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∉ selected34),
        primeHistoryTuple 6 history i : ℕ) : ℝ) *
        (primeHistoryTuple 6 history j : ℝ) ^ 2 < selectedLevel N history) := by
  apply actual_square_guards N hN (primeHistoryTuple 6 history) (historyCoordinates N history)
  · intro i
    rw [historyCoordinates_eq_of_length N history hlen,
      rpow_primeHistoryLogCoordinates N hN hlen hpos i]
  · exact hfull
  · exact hselected

theorem actual_new_level_above_comparison (N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hnew : currentParent (historyCoordinates N history) < newM (historyCoordinates N history)) :
    N ^ currentParent (historyCoordinates N history) < selectedLevel N history := by
  exact Real.rpow_lt_rpow_of_exponent_lt hN hnew

theorem historyCoordinates_append (N : ℝ) (later history : List ℕ)
    (hlen : 6 ≤ history.length) :
    historyCoordinates N (later ++ history) = historyCoordinates N history := by
  unfold historyCoordinates
  rw [rosserAncestor_append 6 later history hlen]

theorem selectedLevel_append (N : ℝ) (later history : List ℕ)
    (hlen : 6 ≤ history.length) :
    selectedLevel N (later ++ history) = selectedLevel N history := by
  unfold selectedLevel
  rw [historyCoordinates_append N later history hlen]

/-- Retain all actual parent decisions through the sixth admission.  Only
later odd tests read the selected descending34 level on that same ancestor;
outside the literal support the actual current parent is used unchanged. -/
def upgradePolicy (parent : Bool → List ℕ → Bool) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 parent (fun positive history =>
    if descendingSupport (historyCoordinates N history) then
      ordinaryParityRosserPolicy false (selectedLevel N history) positive history
    else parent positive history)

theorem upgradePolicy_through_six (parent : Bool → List ℕ → Bool) (N : ℝ)
    (positive : Bool) (history : List ℕ) (hlen : history.length ≤ 6) :
    upgradePolicy parent N positive history = parent positive history := by
  simp only [upgradePolicy, firstExitDepthSplicePolicy, if_pos hlen]

theorem upgradePolicy_outside (parent : Bool → List ℕ → Bool) (N : ℝ)
    (positive : Bool) (history : List ℕ)
    (hout : ¬ descendingSupport (historyCoordinates N history)) :
    upgradePolicy parent N positive history = parent positive history := by
  by_cases hlen : history.length ≤ 6 <;>
    simp [upgradePolicy, firstExitDepthSplicePolicy, hlen, hout]

theorem upgradePolicy_active_after_six (parent : Bool → List ℕ → Bool) (N : ℝ)
    (positive : Bool) (history : List ℕ) (hlen : 6 < history.length)
    (hs : descendingSupport (historyCoordinates N history)) :
    upgradePolicy parent N positive history =
      ordinaryParityRosserPolicy false (selectedLevel N history) positive history := by
  simp only [upgradePolicy, firstExitDepthSplicePolicy, if_neg (not_le.mpr hlen), if_pos hs]

/-- Concrete reuse of the existing historical fourth policy: the entire
retained frontier, sign, mass and remaining carrier stay unchanged. -/
theorem fourthPolicy_frontier_preserved (D : HistoricalPrefixCapData) (N : ℝ)
    (k : ℕ) (hk : k ≤ 6) (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier k (upgradePolicy (D.upperFourthPolicy N) N)
      h pre positive mass carrier =
      firstExitDepthFrontier k (D.upperFourthPolicy N) h pre positive mass carrier := by
  exact firstExitDepthFrontier_depthSplice_eq k 6 hk _ _ h pre carrier positive mass

/-- The actual fifth policy is likewise not retrospectively upgraded. -/
theorem fifthPolicy_frontier_preserved (D : HistoricalPrefixCapData) (N : ℝ)
    (k : ℕ) (hk : k ≤ 6) (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier k (upgradePolicy (D.upperFifthPolicy N) N)
      h pre positive mass carrier =
      firstExitDepthFrontier k (D.upperFifthPolicy N) h pre positive mass carrier := by
  exact firstExitDepthFrontier_depthSplice_eq k 6 hk _ _ h pre carrier positive mass

/-- Both inherited levels used by actualHistoricalFourth/FifthSaving are
read from exactly the same original ancestors after the six-selector. -/
theorem inherited_levels_preserved (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) :
    D.level3 N (rosserAncestor 3 (rosserAncestor 6 history)) =
        D.level3 N (rosserAncestor 3 history) ∧
    D.level4 N (rosserAncestor 4 (rosserAncestor 6 history)) =
        D.level4 N (rosserAncestor 4 history) ∧
    D.level5 N (rosserAncestor 5 (rosserAncestor 6 history)) =
        D.level5 N (rosserAncestor 5 history) := by
  constructor
  · rw [rosserAncestor_nested 3 6 (by omega)]
  constructor
  · rw [rosserAncestor_nested 4 6 (by omega)]
  · rw [rosserAncestor_nested 5 6 (by omega)]

/-- Reuse the already proved adopted pair-mask ancestor dictionary.  No
E0/E1 label or ownership predicate is reconstructed by this new family. -/
theorem adopted_pair_mask_preserved (N : ℝ) (history : List ℕ) :
    P1AdoptedPairMaskAncestorSupport.historyDeletionMask N (rosserAncestor 6 history) ↔
      P1AdoptedPairMaskAncestorSupport.historyDeletionMask N history := by
  exact P1AdoptedPairMaskAncestorSupport.historyDeletionMask_ancestor N (by omega : 2 ≤ 6) history

end

end ImbalancedChen.P2OriginalDescending34CapDictionary
