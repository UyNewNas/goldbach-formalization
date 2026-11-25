import ImbalancedChen.FirstExitDepthSplice
import ImbalancedChen.FirstExitPresieveProjection
import ImbalancedChen.RoughPrimeUniverse
import ImbalancedChen.LogPrimeBoxMesh
import MathlibNt.SieveTheory.LiLiuPrereqWFSmallRosser
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite prime geometry and historical third-level coordinates

This core retains the original arithmetic carriers, the provider's actual
Rosser admissibility predicates, and the exact logarithmic dictionaries.
Declarations are moved with their original names, types and proof bodies;
the heavier supplier modules continue to re-export them by importing this core.
No density limit, numerical certificate, or analytic estimate is asserted here.
-/

namespace ImbalancedChen

/-! Declarations moved verbatim from `ImbalancedChen.OrdinaryRosserFirstExitPolicy`. -/
noncomputable section

open scoped Classical List BigOperators
open MathlibNt.SieveTheory

/-- Total cutoff and the provider's complete parity-sensitive cubic tests. -/
def ordinaryRosserPrefixAdmissible (lower : Bool) (R : ℝ) (pre : List ℕ) : Prop :=
  (pre.prod : ℝ) < R ∧
    if lower then LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet R pre.toFinset
    else LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R pre.toFinset

/-- The globally parity-safe version: only the selected exit parity checks
the full prefix predicate. On reachable histories inherited tests are
already satisfied; the other parity is retained unconditionally. -/
def ordinaryParityRosserPolicy (lower : Bool) (R : ℝ) : Bool → List ℕ → Bool :=
  if lower then evenFirstExitPolicy (fun pre => decide (ordinaryRosserPrefixAdmissible true R pre))
  else oddFirstExitPolicy (fun pre => decide (ordinaryRosserPrefixAdmissible false R pre))


end

/-! Declarations moved verbatim from `ImbalancedChen.FrozenRosserPolicy`. -/
noncomputable section


/-- Selected histories are reversed: the ancestor consists of their last
`k` entries, rather than their first `k` entries. -/
def rosserAncestor {α : Type*} (k : ℕ) (history : List α) : List α :=
  history.drop (history.length - k)

/-- Freeze the level used by an arbitrary literal continuation policy at
the actual rank-`k` ancestor. -/
def ancestorFrozenPolicy {α : Type*} (k : ℕ) (Q : List α → ℝ)
    (policy : ℝ → Bool → List α → Bool) (positive : Bool) (history : List α) : Bool :=
  policy (Q (rosserAncestor k history)) positive history

def frozenParityRosserPolicy (lower : Bool) (k : ℕ) (Q : List ℕ → ℝ) :
    Bool → List ℕ → Bool :=
  ancestorFrozenPolicy k Q (ordinaryParityRosserPolicy lower)


end

/-! Declarations moved verbatim from `ImbalancedChen.PrimeHistoryLogCoordinates`. -/
section

open scoped BigOperators

/-- Total processing-order tuple extracted from a reverse-stored history. -/
def primeHistoryTuple (k : ℕ) (history : List ℕ) : Fin k → ℕ :=
  fun i => history.reverse.getD i.val 0

/-- Logarithmic coordinates at the real target scale. These are total;
the inverse and positivity statements below use their explicit hypotheses. -/
noncomputable def primeHistoryLogCoordinates (N : ℝ) (k : ℕ)
    (history : List ℕ) : Fin k → ℝ :=
  fun i => Real.log (primeHistoryTuple k history i : ℝ) / Real.log N

/-- Correct history length makes the tuple exactly the reversed list. -/
theorem primeHistoryTuple_ofFn {k : ℕ} {history : List ℕ}
    (hlen : history.length = k) :
    List.ofFn (primeHistoryTuple k history) = history.reverse := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i _ hi
    simp only [List.getElem_ofFn, primeHistoryTuple]
    exact List.getD_eq_getElem _ _ hi

/-- The original tree history is recovered without sorting or deduplication. -/
theorem primeHistoryTuple_reverse_ofFn {k : ℕ} {history : List ℕ}
    (hlen : history.length = k) :
    (List.ofFn (primeHistoryTuple k history)).reverse = history := by
  rw [primeHistoryTuple_ofFn hlen, List.reverse_reverse]

/-- The reciprocal-prime mass is also unchanged by the coordinate dictionary. -/
theorem primeHistoryTuple_reciprocal_mass {k : ℕ} {history : List ℕ}
    (hlen : history.length = k) :
    (∏ i, 1 / ((primeHistoryTuple k history i : ℝ) - 1)) =
      (history.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod := by
  rw [← List.prod_ofFn]
  have hmap := congrArg (List.map (fun p : ℕ => 1 / ((p : ℝ) - 1)))
    (primeHistoryTuple_ofFn hlen)
  rw [List.map_ofFn, List.map_reverse] at hmap
  change (List.ofFn ((fun p : ℕ => 1 / ((p : ℝ) - 1)) ∘
    primeHistoryTuple k history)).prod = _
  rw [hmap, List.prod_reverse]


end

/-! Declarations moved verbatim from `ImbalancedChen.FirstExitHistoricalLevels`. -/
noncomputable section

open scoped Classical

/-- An ancestor is the initial processing-order subtuple, even though the
tree stores all histories in reverse order. -/
theorem primeHistoryTuple_ancestor {r k : ℕ} {history : List ℕ}
    (hlen : history.length = k) (hr : r ≤ k) (i : Fin r) :
    primeHistoryTuple r (rosserAncestor r history) i =
      primeHistoryTuple k history (i.castLE hr) := by
  have hrev : (rosserAncestor r history).reverse = history.reverse.take r := by
    simp only [rosserAncestor, List.reverse_drop]
    congr 1
    omega
  unfold primeHistoryTuple
  rw [hrev, List.getD_eq_getElem _ _ (by simp [hlen, hr, i.isLt])]
  rw [List.getD_eq_getElem _ _ (by simpa [hlen] using lt_of_lt_of_le i.isLt hr)]
  simp

theorem primeHistoryLogCoordinates_ancestor (N : ℝ) {r k : ℕ}
    {history : List ℕ} (hlen : history.length = k) (hr : r ≤ k) (i : Fin r) :
    primeHistoryLogCoordinates N r (rosserAncestor r history) i =
      primeHistoryLogCoordinates N k history (i.castLE hr) := by
  simp only [primeHistoryLogCoordinates, primeHistoryTuple_ancestor hlen hr]

/-- All tests through rank two belong to `base`; the active third test and
its subsequent continuation use the level selected by the actual ancestor. -/
def thirdCappedUpperPolicy (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 2 base (frozenParityRosserPolicy false 3 Q3)


end

/-! Declarations moved verbatim from `ImbalancedChen.ActualPrimeBoxMass`. -/
noncomputable section

open scoped BigOperators
open Filter Topology

/-- The actual finite carrier of prime tuples in a logarithmic box. -/
def actualPrimeBoxTuples (N : ℕ) {k : ℕ} (a b : Fin k → ℝ) :
    Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun i =>
    roughPrimeFinset N (Nat.ceil ((N : ℝ) ^ b i))
      ((N : ℝ) ^ a i) ((N : ℝ) ^ b i))

/-- Membership retains primality, the common target exclusion, and both
exact endpoints. Enumeration caps add no truncation. -/
theorem mem_actualPrimeBoxTuples_iff {N k : ℕ} {a b : Fin k → ℝ}
    {p : Fin k → ℕ} :
    p ∈ actualPrimeBoxTuples N a b ↔
      ∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
        (N : ℝ) ^ a i ≤ (p i : ℝ) ∧ (p i : ℝ) < (N : ℝ) ^ b i := by
  simp only [actualPrimeBoxTuples, Fintype.mem_piFinset,
    mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil _)]


end

/-! Declarations moved verbatim from `ImbalancedChen.ActualPrimeBoxTestFunctions`. -/
noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

/-- Logarithmic coordinates of an actual tuple, retaining the target N. -/
def actualPrimeTupleLog {k : ℕ} (N : ℕ) (p : Fin k → ℕ) : Fin k → ℝ :=
  fun i => Real.log (p i : ℝ) / Real.log (N : ℝ)

theorem actualPrimeTupleLog_rpow {k N : ℕ} (hN : 1 < N)
    (p : Fin k → ℕ) (hp : ∀ i, 0 < p i) (i : Fin k) :
    (N : ℝ) ^ (actualPrimeTupleLog N p i) = p i := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  apply (Real.mul_log_eq_log_iff (lt_trans zero_lt_one hN') (by exact_mod_cast hp i)).mp
  exact div_mul_cancel₀ _ (Real.log_pos hN').ne'

/-- The exact power endpoints are equivalent to half-open logarithmic
coordinates. Primality and target exclusion are retained separately. -/
theorem mem_actualPrimeBoxTuples_log_iff {k N : ℕ} (hN : 1 < N)
    (a b : Fin k → ℝ) (p : Fin k → ℕ) :
    p ∈ actualPrimeBoxTuples N a b ↔
      (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N) ∧ actualPrimeTupleLog N p ∈ logPrimeBox a b := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hp
    refine ⟨fun i => ⟨(hi i).1, (hi i).2.1⟩, mem_logPrimeBox.mpr (fun i => ?_)⟩
    have hpow := actualPrimeTupleLog_rpow hN p (fun j => (hi j).1.pos) i
    exact ⟨(Real.rpow_le_rpow_left_iff hN').mp (hpow.symm ▸ (hi i).2.2.1),
      (Real.rpow_lt_rpow_left_iff hN').mp (hpow.symm ▸ (hi i).2.2.2)⟩
  · rintro ⟨hp, hx⟩
    refine mem_actualPrimeBoxTuples_iff.mpr (fun i => ⟨(hp i).1, (hp i).2, ?_, ?_⟩)
    · rw [← actualPrimeTupleLog_rpow hN p (fun j => (hp j).1.pos) i]
      exact (Real.rpow_le_rpow_left_iff hN').mpr (mem_logPrimeBox.mp hx i).1
    · rw [← actualPrimeTupleLog_rpow hN p (fun j => (hp j).1.pos) i]
      exact (Real.rpow_lt_rpow_left_iff hN').mpr (mem_logPrimeBox.mp hx i).2


end

/-! Declarations moved verbatim from `ImbalancedChen.OrdinaryUpperFiveAffineGates`. -/
noncomputable section

open scoped Classical BigOperators
open Set

/-- Strict ordering is preserved in both directions by the actual
target-dependent logarithmic coordinate dictionary. -/
theorem actualPrimeTupleLog_strictAnti_iff {d N : ℕ} (hN : 1 < N)
    (p : Fin d → ℕ) (hp : ∀ i, 0 < p i) :
    StrictAnti (actualPrimeTupleLog N p) ↔ StrictAnti p := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hlt (i j : Fin d) : actualPrimeTupleLog N p i < actualPrimeTupleLog N p j ↔ p i < p j := by
    rw [← Real.rpow_lt_rpow_left_iff hNr,
      actualPrimeTupleLog_rpow hN p hp, actualPrimeTupleLog_rpow hN p hp]
    exact Nat.cast_lt
  exact ⟨fun h i j hij => (hlt j i).mp (h hij),
    fun h i j hij => (hlt j i).mpr (h hij)⟩


end

/-! Declarations moved verbatim from `ImbalancedChen.OrdinaryPrimeFrontierAffineRegion`. -/
noncomputable section

open scoped Classical List BigOperators

/-- The two literal cubic inequalities are exactly their logarithmic
affine inequalities; no rounded power or weak endpoint is substituted. -/
theorem ordinaryUpperFive_cube_tests_iff_log {N : ℕ} (hN : 1 < N)
    (old : ℝ) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ old ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ old) ↔
      3 * actualPrimeTupleLog N p 0 < old ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < old := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN'
  have hc i := actualPrimeTupleLog_rpow hN p hpos i
  have hcub (i : Fin 5) : (N : ℝ) ^ (3 * actualPrimeTupleLog N p i) = (p i : ℝ) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hN0.le, hc]
    norm_num
  have hprod : (N : ℝ) ^ (actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
      3 * actualPrimeTupleLog N p 2) = (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, hc, hc, hcub]
  rw [← hcub 0, ← hprod, Real.rpow_lt_rpow_left_iff hN', Real.rpow_lt_rpow_left_iff hN']


end

/-! Declarations moved verbatim from `ImbalancedChen.HistoricalPrefixCertificate`. -/
noncomputable section

open scoped Classical BigOperators

/-- Initial processing-order coordinates, also used for mesh cell labels. -/
def historicalPrefixProject {α : Type*} {r d : ℕ} (hrd : r ≤ d)
    (t : Fin d → α) : Fin r → α :=
  fun i => t (i.castLE hrd)

/-- The projected label owns precisely the projected ancestor point. -/
theorem mem_logPrimeMeshCell_historicalPrefixProject {r d m : ℕ}
    (hrd : r ≤ d) {a b : ℝ} {j : Fin d → Fin (m + 1)}
    {t : Fin d → ℝ} (ht : t ∈ logPrimeMeshCell a b m j) :
    historicalPrefixProject hrd t ∈
      logPrimeMeshCell a b m (historicalPrefixProject hrd j) := by
  apply mem_logPrimeMeshCell.mpr
  intro i
  simpa only [historicalPrefixProject, logPrimeMeshLo, logPrimeMeshHi]
    using mem_logPrimeMeshCell.mp ht (i.castLE hrd)

theorem primeHistoryLogCoordinates_eq_historicalPrefixProject (N : ℝ)
    {r d : ℕ} (hrd : r ≤ d) {history : List ℕ} (hlen : history.length = d) :
    primeHistoryLogCoordinates N r (rosserAncestor r history) =
      historicalPrefixProject hrd (primeHistoryLogCoordinates N d history) := by
  funext i
  exact primeHistoryLogCoordinates_ancestor N hlen hrd i

/-- A finite cap lookup with an explicit, possibly inherited, fallback. -/
def historicalPrefixLookup {d : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ) : ℚ :=
  fallback + ∑ j ∈ J,
    if t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j then cap j - fallback else 0

theorem historicalPrefixLookup_on_cell {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (j : Fin d → Fin (m + 1)) (hj : j ∈ J)
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t = cap j := by
  unfold historicalPrefixLookup
  rw [Finset.sum_eq_single_of_mem j hj]
  · rw [if_pos ht]
    ring
  · intro q _hq hqj
    apply if_neg
    intro hq
    exact hqj (logPrimeMeshCell_unique (by exact_mod_cast hab) hq ht)

theorem historicalPrefixLookup_outside {d : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (ht : ∀ j ∈ J, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t = fallback := by
  unfold historicalPrefixLookup
  rw [Finset.sum_eq_zero (fun j hj => if_neg (ht j hj)), add_zero]

/-- On every mesh cell, including an unselected one, the effective value
is the stored cap or the exact inherited fallback. -/
theorem historicalPrefixLookup_on_any_cell {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (j : Fin d → Fin (m + 1))
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t =
      if j ∈ J then cap j else fallback := by
  by_cases hj : j ∈ J
  · rw [if_pos hj]
    exact historicalPrefixLookup_on_cell a b hab m J cap fallback t j hj ht
  · rw [if_neg hj]
    apply historicalPrefixLookup_outside
    intro q hq hqt
    have heq : q = j := logPrimeMeshCell_unique (by exact_mod_cast hab) hqt ht
    subst q
    exact hj hq

/-- Every field is finite data independent of the target or tested
integer.  `cap4` and `cap5` are new values only on their adopted cells. -/
structure HistoricalPrefixCapData where
  a : ℚ
  b : ℚ
  m : ℕ
  old : ℚ
  cells3 : Finset (Fin 3 → Fin (m + 1))
  cap3 : (Fin 3 → Fin (m + 1)) → ℚ
  cells4 : Finset (Fin 4 → Fin (m + 1))
  cap4 : (Fin 4 → Fin (m + 1)) → ℚ
  cells5 : Finset (Fin 5 → Fin (m + 1))
  cap5 : (Fin 5 → Fin (m + 1)) → ℚ


namespace HistoricalPrefixCapData

def cell3 (D : HistoricalPrefixCapData) (j : Fin 3 → Fin (D.m + 1)) : ℚ :=
  if j ∈ D.cells3 then D.cap3 j else D.old

def exponent3 (D : HistoricalPrefixCapData) (t : Fin 3 → ℝ) : ℚ :=
  historicalPrefixLookup D.a D.b D.m D.cells3 D.cap3 D.old t

theorem exponent3_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 3 → ℝ) (j : Fin 3 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent3 t = D.cell3 j :=
  historicalPrefixLookup_on_any_cell D.a D.b hab D.m D.cells3 D.cap3 D.old t j ht

/-- The target is introduced only after the finite mesh and cap tables. -/
def level3 (D : HistoricalPrefixCapData) (N : ℝ) (history : List ℕ) : ℝ :=
  N ^ (D.exponent3 (primeHistoryLogCoordinates N 3 history) : ℝ)

/-- The concrete upper policy after selecting the third cap, starting
from the ordinary upper policy at the stored original level. -/
def upperThirdPolicy (D : HistoricalPrefixCapData) (N : ℝ) : Bool → List ℕ → Bool :=
  thirdCappedUpperPolicy (ordinaryParityRosserPolicy false (N ^ (D.old : ℝ))) (D.level3 N)

end HistoricalPrefixCapData

end

/-! Declarations moved verbatim from `ImbalancedChen.HistoricalUpperFiveCellGeometry`. -/
noncomputable section

open scoped Classical List BigOperators
open Set
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser


namespace HistoricalPrefixCapData

/-- A five-prime history fixes its third ancestor's effective level on
the projected owner, whether or not that ancestor cell was selected. -/
theorem level3_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 5)
    (j : Fin 5 → Fin (D.m + 1))
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 N (rosserAncestor 3 history) =
      N ^ (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) := by
  unfold level3
  rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 5) hlen]
  rw [D.exponent3_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) ht)]

/-- The actual processing-order tuple and the reverse-stored third
history select the same projected owner. -/
theorem level3_tuple_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℕ) (p : Fin 5 → ℕ) (j : Fin 5 → Fin (D.m + 1))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 (N : ℝ) [p 2, p 1, p 0] =
      (N : ℝ) ^ (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) := by
  have hcoords :
      primeHistoryLogCoordinates (N : ℝ) 5 [p 4, p 3, p 2, p 1, p 0] =
        actualPrimeTupleLog N p := by
    funext i
    fin_cases i <;> rfl
  have ht' : primeHistoryLogCoordinates (N : ℝ) 5 [p 4, p 3, p 2, p 1, p 0] ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j := by
    rw [hcoords]
    exact ht
  simpa [rosserAncestor] using
    D.level3_on_fifth_cell hab (N : ℝ) [p 4, p 3, p 2, p 1, p 0] (by simp) j ht'

end HistoricalPrefixCapData


/-- The first and third power tests may use different historical levels.
Both logarithmic inequalities retain their strict endpoints. -/
theorem historicalUpperFive_cube_tests_iff_log {N : ℕ} (hN : 1 < N)
    (old third : ℝ) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ old ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ third) ↔
      3 * actualPrimeTupleLog N p 0 < old ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < third := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN'
  have hc i := actualPrimeTupleLog_rpow hN p hpos i
  have hcub (i : Fin 5) :
      (N : ℝ) ^ (3 * actualPrimeTupleLog N p i) = (p i : ℝ) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hN0.le, hc]
    norm_num
  have hprod :
      (N : ℝ) ^ (actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
        3 * actualPrimeTupleLog N p 2) = (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, hc, hc, hcub]
  rw [← hcub 0, ← hprod, Real.rpow_lt_rpow_left_iff hN', Real.rpow_lt_rpow_left_iff hN']


end

end ImbalancedChen
