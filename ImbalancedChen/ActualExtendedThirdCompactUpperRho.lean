import ImbalancedChen.ActualExtendedThirdCompactCellCutoff
import ImbalancedChen.ActualExtendedThirdFirstCubeMargin
import ImbalancedChen.ActualUpperPolicyDensity
import ImbalancedChen.HistoricalUnorderedThirdGeometry

/-!
# The literal upper coefficient of the compact extended-third policy

The initial rule uses the same old exponent and an actual dyadic first
label stop. At the third selected ancestor the policy reads the already
defined compact-cell level. All later decisions use that same ancestor.
An inactive ancestor restores the complete initial predicate exactly.

The physical coefficient is the existing actualSmallRoughRho applied to
this concrete policy. Its support, signed first-exit coefficient, small
attachment and majorant are identified without choosing a new coefficient
for a particular test integer. These finite identities do not identify its
full density with the harmonic profile or pay a counting remainder.
-/

namespace ImbalancedChen

noncomputable section

open Set
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open scoped Classical

/-- The first coordinate is owned half-open and its label's upper endpoint
passes the original closed first-stop wall. -/
def actualExtendedThirdCompactFirstStop (e : ℝ) (m N : ℕ) (history : List ℕ) : Prop :=
  ∃ i : Fin (2 ^ m),
    actualExtendedThirdDyadicLo m (fun _ => i) 0 ≤
        primeHistoryLogCoordinates (N : ℝ) 1 history 0 ∧
      primeHistoryLogCoordinates (N : ℝ) 1 history 0 <
        actualExtendedThirdDyadicHi m (fun _ => i) 0 ∧
      actualExtendedThirdDyadicHi m (fun _ => i) 0 ≤ thirdPrefixRho - 4 * e

def actualExtendedThirdCompactInitialPolicy (e : ℝ) (m N : ℕ) :
    Bool → List ℕ → Bool :=
  oddFirstExitPolicy fun history => decide
    (ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)) history ∧
      (history.length = 1 → actualExtendedThirdCompactFirstStop e m N history))

def actualExtendedThirdCompactRawLevel (e h : ℝ) (m N : ℕ) (history : List ℕ) : ℝ :=
  (N : ℝ) ^ actualExtendedThirdCompactCellLevel e h m
    (primeHistoryLogCoordinates (N : ℝ) 3 history)

def actualExtendedThirdCompactActive (e h : ℝ) (m N : ℕ) (history : List ℕ) : Prop :=
  ∃ j ∈ actualExtendedThirdCompactCells e h m,
    primeHistoryLogCoordinates (N : ℝ) 3 history ∈ actualExtendedThirdOwnedCell m j

def actualExtendedThirdCompactUpperPolicy (e h : ℝ) (m N : ℕ) :
    Bool → List ℕ → Bool :=
  thirdCappedUpperPolicy (actualExtendedThirdCompactInitialPolicy e m N)
    (actualExtendedThirdCompactRawLevel e h m N)

theorem actualExtendedThirdCompactRawLevel_on_cell {e h : ℝ} {m N : ℕ}
    {history : List ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 history ∈ actualExtendedThirdOwnedCell m j) :
    actualExtendedThirdCompactRawLevel e h m N history =
      (N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j := by
  unfold actualExtendedThirdCompactRawLevel
  rw [actualExtendedThirdCompactCellLevel_on_cell hj ht]

theorem actualExtendedThirdCompactRawLevel_inactive {e h : ℝ} {m N : ℕ}
    {history : List ℕ} (ha : ¬actualExtendedThirdCompactActive e h m N history) :
    actualExtendedThirdCompactRawLevel e h m N history =
      (N : ℝ) ^ (thirdPrefixTheta - 2 * e) := by
  unfold actualExtendedThirdCompactRawLevel
  rw [actualExtendedThirdCompactCellLevel_outside]
  intro j hj ht
  exact ha ⟨j, hj, ht⟩

theorem actualExtendedThirdCompactUpperPolicy_through_two (e h : ℝ) (m N : ℕ)
    (positive : Bool) (history : List ℕ) (hlen : history.length ≤ 2) :
    actualExtendedThirdCompactUpperPolicy e h m N positive history =
      actualExtendedThirdCompactInitialPolicy e m N positive history := by
  simp only [actualExtendedThirdCompactUpperPolicy, thirdCappedUpperPolicy,
    firstExitDepthSplicePolicy, if_pos hlen]

theorem actualExtendedThirdCompactUpperPolicy_even (e h : ℝ) (m N : ℕ)
    (history : List ℕ) : actualExtendedThirdCompactUpperPolicy e h m N true history = true := by
  apply thirdCappedUpperPolicy_even_retained
  intro pre
  simp [actualExtendedThirdCompactInitialPolicy, oddFirstExitPolicy]

/-- Outside the adopted cells the full original first-stop predicate is
restored, rather than only its real exponent. -/
theorem actualExtendedThirdCompactUpperPolicy_inactive (e h : ℝ) (m N : ℕ)
    (positive : Bool) (history : List ℕ)
    (ha : ¬actualExtendedThirdCompactActive e h m N (rosserAncestor 3 history)) :
    actualExtendedThirdCompactUpperPolicy e h m N positive history =
      actualExtendedThirdCompactInitialPolicy e m N positive history := by
  by_cases hlen : history.length ≤ 2
  · exact actualExtendedThirdCompactUpperPolicy_through_two e h m N positive history hlen
  · have hne : history.length ≠ 1 := by omega
    simp [actualExtendedThirdCompactUpperPolicy, thirdCappedUpperPolicy,
      firstExitDepthSplicePolicy, hlen, frozenParityRosserPolicy, ancestorFrozenPolicy,
      actualExtendedThirdCompactRawLevel_inactive ha, ordinaryParityRosserPolicy,
      actualExtendedThirdCompactInitialPolicy, oddFirstExitPolicy, hne]

theorem actualExtendedThirdCompactUpperPolicy_on_cell {e h : ℝ} {m N : ℕ}
    (positive : Bool) (history : List ℕ) (hlen : 3 ≤ history.length)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 history) ∈
      actualExtendedThirdOwnedCell m j) :
    actualExtendedThirdCompactUpperPolicy e h m N positive history =
      ordinaryParityRosserPolicy false ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
        positive history := by
  have hdeep : ¬history.length ≤ 2 := by omega
  simp only [actualExtendedThirdCompactUpperPolicy, thirdCappedUpperPolicy,
    firstExitDepthSplicePolicy, if_neg hdeep, frozenParityRosserPolicy, ancestorFrozenPolicy]
  rw [actualExtendedThirdCompactRawLevel_on_cell hj ht]

/-- Later selections cannot change either the cell lookup or its level. -/
theorem actualExtendedThirdCompactFrozenLevel_append (e h : ℝ) (m N : ℕ)
    (later history : List ℕ) (hlen : 3 ≤ history.length) :
    actualExtendedThirdCompactRawLevel e h m N (rosserAncestor 3 (later ++ history)) =
      actualExtendedThirdCompactRawLevel e h m N (rosserAncestor 3 history) := by
  rw [rosserAncestor_append 3 later history hlen]

theorem actualExtendedThirdCompactUpperPolicy_empty_cells (e h : ℝ) (m N : ℕ)
    (hempty : actualExtendedThirdCompactCells e h m = ∅) :
    actualExtendedThirdCompactUpperPolicy e h m N = actualExtendedThirdCompactInitialPolicy e m N := by
  funext positive history
  apply actualExtendedThirdCompactUpperPolicy_inactive
  rintro ⟨j, hj, _⟩
  rw [hempty] at hj
  exact Finset.notMem_empty j hj

/-- A genuinely adopted third-prime history already passes the same first
dyadic label stop; the first-stop test is not an extra action hypothesis. -/
theorem actualExtendedThirdCompactFirstStop_of_cell {e h : ℝ} {m N : ℕ}
    (p0 p1 p2 : ℕ) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] ∈ actualExtendedThirdOwnedCell m j) :
    actualExtendedThirdCompactFirstStop e m N [p0] := by
  have hcoord : primeHistoryLogCoordinates (N : ℝ) 1 [p0] 0 =
      primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] 0 := by
    simp [primeHistoryLogCoordinates, primeHistoryTuple]
  have hstop := (mem_actualExtendedThirdRetainedCells.mp
    (actualExtendedThirdCompactCells_subset e h m hj)).2
  refine ⟨j 0, ?_, ?_, ?_⟩
  · simpa only [hcoord, actualExtendedThirdDyadicLo] using (ht.1 0 (mem_univ _)).1
  · simpa only [hcoord, actualExtendedThirdDyadicHi] using (ht.1 0 (mem_univ _)).2
  · simpa only [actualExtendedThirdDyadicHi] using hstop

/-- The initial singleton test retains its total-product condition as well
as its first cube and literal dyadic first stop. -/
theorem actualExtendedThirdCompactInitialPolicy_first_iff (e : ℝ) (m N p : ℕ)
    (hp : 0 < p) :
    actualExtendedThirdCompactInitialPolicy e m N false [p] = true ↔
      (p : ℝ) ^ 3 < (N : ℝ) ^ (thirdPrefixTheta - 2 * e) ∧
        actualExtendedThirdCompactFirstStop e m N [p] := by
  have hsq : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hprod : (p : ℝ) ≤ (p : ℝ) ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) p)
    simpa only [mul_one, pow_succ, mul_comm] using hm
  have hc : UpperAdmissibleSet ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)) [p].toFinset ↔
      (p : ℝ) ^ 3 < (N : ℝ) ^ (thirdPrefixTheta - 2 * e) := by
    simp [UpperAdmissibleSet, Finset.filter_singleton, pow_succ, mul_comm]
  change decide (ordinaryRosserPrefixAdmissible false
    ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)) [p] ∧
      (([p] : List ℕ).length = 1 → actualExtendedThirdCompactFirstStop e m N [p])) = true ↔ _
  rw [decide_eq_true_eq]
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
    List.prod_cons, List.prod_nil, mul_one, hc]
  exact ⟨fun h => ⟨h.1.2, h.2 rfl⟩,
    fun h => ⟨⟨hprod.trans_lt h.1, h.1⟩, fun _ => h.2⟩⟩

/-- Positivity of only the selected first prime suffices to read its cube
from the actual cell's logarithmic coordinates. -/
theorem actualExtendedThirdCompactCell_prime_firstCube {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (p0 p1 p2 : ℕ) (hp0 : 0 < p0) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] ∈ actualExtendedThirdOwnedCell m j) :
    (p0 : ℝ) ^ 3 < (N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] 0) = (p0 : ℝ) := by
    simpa [primeHistoryLogCoordinates, primeHistoryTuple, actualPrimeTupleLog] using
      actualPrimeTupleLog_rpow hN (fun _ : Fin 1 => p0) (fun _ => hp0) 0
  exact actualExtendedThirdPhysicalLevel_prime_firstCube p0 hNr he0 he hmesh
    (actualExtendedThirdCompactCells_subset e h m hj)
    (actualExtendedThirdOwnedCell_subset_physicalCell m j ht) hpow.symm.le

/-- Every genuinely adopted triple has already passed the initial first
selection. This obligation is proved from the same cap and same owned cell. -/
theorem actualExtendedThirdCompactInitialPolicy_first_of_cell {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (p0 p1 p2 : ℕ) (hp0 : 0 < p0) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] ∈ actualExtendedThirdOwnedCell m j) :
    actualExtendedThirdCompactInitialPolicy e m N false [p0] = true := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  apply (actualExtendedThirdCompactInitialPolicy_first_iff e m N p0 hp0).mpr
  refine ⟨?_, actualExtendedThirdCompactFirstStop_of_cell p0 p1 p2 hj ht⟩
  exact (actualExtendedThirdCompactCell_prime_firstCube hN he0 he hmesh p0 p1 p2 hp0 hj ht).trans_le
    (Real.rpow_le_rpow_of_exponent_le hNr.le
      (thirdPrefixBufferedCap_le_root e (actualExtendedThirdPhysicalGamma e m j)))

/-- The actual cap's already proved first-cube margin pays that inherited
test at the third admission, even though the new level may be smaller. -/
theorem actualExtendedThirdCompactUpperPolicy_third_iff {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (p0 p1 p2 : ℕ) (hp2 : 0 < p2) (hp21 : p2 < p1) (hp10 : p1 < p0)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] ∈ actualExtendedThirdOwnedCell m j) :
    actualExtendedThirdCompactUpperPolicy e h m N false [p2, p1, p0] = true ↔
      (p0 : ℝ) * p1 * p2 ^ 3 < (N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j := by
  have hfirst := actualExtendedThirdCompactCell_prime_firstCube hN he0 he hmesh
    p0 p1 p2 (by omega) hj ht
  have hself : rosserAncestor 3 [p2, p1, p0] = [p2, p1, p0] := by simp [rosserAncestor]
  have hpolicy := actualExtendedThirdCompactUpperPolicy_on_cell false [p2, p1, p0]
    (by simp) hj (by simpa only [hself] using ht)
  rw [hpolicy]
  change decide (ordinaryRosserPrefixAdmissible false
    ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j) [p2, p1, p0]) = true ↔ _
  rw [decide_eq_true_eq, historicalUnorderedThird_admissible_iff _ p0 p1 p2 hp2 hp21 hp10]
  exact and_iff_right hfirst

/-- The support and coefficient use the existing physical construction,
with one retention predicate fixed before a test integer is supplied. -/
def actualExtendedThirdCompactModuli (e h : ℝ) (m N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  actualSmallRoughModuli (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z

def actualExtendedThirdCompactRho (e h : ℝ) (m N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  actualSmallRoughRho (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z L

theorem actualExtendedThirdCompactRho_eq_firstExitAttachment
    (e h : ℝ) (m N cap : ℕ) (w z L : ℝ) :
    actualExtendedThirdCompactRho e h m N cap w z L =
      smallRoughRho (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli (actualExtendedThirdCompactUpperPolicy e h m N)
          (roughPrimeUniverse N cap w z))
        (fun d => (firstExitRetainedCoefficient (actualExtendedThirdCompactUpperPolicy e h m N)
          (roughPrimeUniverse N cap w z) d : ℝ))
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) := by
  exact actualSmallRoughRho_eq_firstExitAttachment
    (actualExtendedThirdCompactUpperPolicy e h m N)
    (actualExtendedThirdCompactUpperPolicy_even e h m N) N cap w z L

theorem actualExtendedThirdCompactRoughDensity_eq_policy
    (e h : ℝ) (m N cap : ℕ) (w z : ℝ) :
    reciprocalTotientDensity
        (fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z)
        (fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z) =
      firstExitRetainedPolynomial (actualExtendedThirdCompactUpperPolicy e h m N)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) := by
  exact (firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (actualExtendedThirdCompactUpperPolicy e h m N)
    (actualExtendedThirdCompactUpperPolicy_even e h m N) N cap w z).symm

theorem actualExtendedThirdCompactRho_majorant (e h : ℝ) (m N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (actualExtendedThirdCompactModuli e h m N cap w z)
        (actualExtendedThirdCompactRho e h m N cap w z L) n.natAbs := by
  exact actualSmallRoughRho_majorant _ N cap w z L hL hwL hwz hzcap n

theorem actualExtendedThirdCompactRho_abs_le_one (e h : ℝ) (m N cap : ℕ)
    (w z L : ℝ) (q : ℕ) : |actualExtendedThirdCompactRho e h m N cap w z L q| ≤ 1 := by
  exact actualSmallRoughRho_abs_le_one _ N cap w z L q

theorem actualExtendedThirdCompactModuli_squarefree (e h : ℝ) (m N cap : ℕ)
    (w z : ℝ) {q : ℕ} (hq : q ∈ actualExtendedThirdCompactModuli e h m N cap w z) :
    Squarefree q := by
  exact actualSmallRoughModuli_squarefree _ N cap w z hq

theorem actualExtendedThirdCompactModuli_coprime_target (e h : ℝ) (m N cap : ℕ)
    (w z : ℝ) {q : ℕ} (hq : q ∈ actualExtendedThirdCompactModuli e h m N cap w z) :
    q.Coprime N := by
  exact actualSmallRoughModuli_coprime_target _ N cap w z hq

/-- An empty adopted table restores precisely the original initial-policy
coefficient on every modulus, not merely its total density. -/
theorem actualExtendedThirdCompactRho_empty_cells (e h : ℝ) (m N cap : ℕ) (w z L : ℝ)
    (hempty : actualExtendedThirdCompactCells e h m = ∅) :
    actualExtendedThirdCompactRho e h m N cap w z L =
      actualSmallRoughRho (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z L := by
  unfold actualExtendedThirdCompactRho
  rw [actualExtendedThirdCompactUpperPolicy_empty_cells e h m N hempty]

end

end ImbalancedChen
