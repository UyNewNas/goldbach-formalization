import ImbalancedChen.Part5OriginalH430FrozenIntegerSupport
import ImbalancedChen.Part5OriginalBuchstabRowMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A finite catalog of integer-coordinate Members rooted at the original
frozen U3/U4 primes. It is grouped by the ORIGINAL cumulative RootCode,
not by final products. Canonical inactive coordinates prevent artificial
dummy-prime multiplicities. This is a geometric catalog, NOT a declaration
that all alternative Programs are to be added in the original count.
-/
namespace ImbalancedChen.Part5OriginalH430SameQHistoryCells

noncomputable section
open Set
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalH430BuchstabArithmeticRows
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows

/-- A code determines its frozen level even when its fiber is empty.
No representative root is chosen after N and no division by mass occurs. -/
def codeLevel : (n : ℕ) → RootCode n → ℝ
  | 0, c => lowerEndpoint 0 (c ⟨0, by omega⟩)
  | n+1, c => max (codeLevel n (restrictRootCode (Nat.le_succ n) c))
      (lowerEndpoint (n+1) (c ⟨n+1, by omega⟩))

theorem codeLevel_rootCode (n : ℕ) (nu : ℝ) :
    codeLevel n (rootCode n nu) = frozenLevel n nu := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change max (codeLevel n (rootCode n nu)) (rawLower (n+1) nu) = _
      rw [ih]
      rfl

def cellQ (N n : ℕ) (c : RootCode n) : ℝ := (N:ℝ)^(codeLevel n c)

/-- Depths zero through 440; root kind, root prime, Program and active
prime coordinates stay distinct, including equal final products. -/
abbrev Label (N mesh : ℕ) :=
  Sigma (fun d : Fin 441 => Root × Fin (N+1) × Program mesh d.val ×
    (Fin d.val → Fin 2 → Fin (N+1)))

def labelPrimes {N mesh : ℕ} (h : Label N mesh) : IntegerCoordinates h.1.val :=
  fun j i => (h.2.2.2.2 j i).val

def labelNode {N mesh : ℕ} (n : ℕ) (tau : ℝ) (h : Label N mesh) : TypedNode :=
  historyNode N n h.2.1 tau h.2.2.1.val h.2.2.2.1 (labelPrimes h)

def labelWord {N mesh : ℕ} (h : Label N mesh) : List ℕ :=
  historyWord h.2.2.1.val h.2.2.2.1 (labelPrimes h)

def labelLevel {N mesh : ℕ} (tau : ℝ) (h : Label N mesh) : ℝ :=
  (sourceRoot h.2.1 tau (physicalPrime N h.2.2.1.val)).physical.total

def labelCode {N mesh : ℕ} (n : ℕ) (tau : ℝ) (h : Label N mesh) : RootCode n :=
  rootCode n (labelLevel tau h)

def canonicalPoint : StepShape → IntegerPoint → Prop
  | .buchstabUpper, q => q 1 = 1
  | .buchstabLower, q => q 1 = 1
  | .w1Singleton _ _, q => q 1 = 1
  | .w2Singleton _ _, q => q 1 = 1
  | .w2Pair _ _, _ => True
  | _, q => q 0 = 1 ∧ q 1 = 1

/-- All tests are the original geometric/source predicates or literal
primality. No mass, asymptotic estimate, count licence or error bound is data. -/
def Valid {N mesh : ℕ} (n : ℕ) (tau : ℝ) (h : Label N mesh) : Prop :=
  (h.2.2.1.val.Prime ∧ h.2.2.1.val.Coprime N) ∧
  physicalPrime N h.2.2.1.val ∈ rootBand h.2.1 ∧
  PrimeLetters N h.2.2.2.1 (labelPrimes h) ∧
  (∀ j, canonicalPoint (h.2.2.2.1 j).1 (labelPrimes h j)) ∧
  Member 0 1 h.1.val (frozenRoot n h.2.1 tau (physicalPrime N h.2.2.1.val))
    h.2.2.2.1 (physicalCoordinates N (labelPrimes h))

def catalog (N n mesh : ℕ) (tau : ℝ) : Finset (Label N mesh) :=
  Finset.univ.filter (Valid n tau)

def readyCatalog (N n mesh : ℕ) (tau : ℝ) : Finset (Label N mesh) :=
  (catalog N n mesh tau).filter (fun h =>
    directionGuard (labelNode n tau h).upper (labelNode n tau h).physical)

def cellFamily (N n mesh : ℕ) (tau : ℝ) (c : RootCode n) : Finset (Label N mesh) :=
  (readyCatalog N n mesh tau).filter (fun h => labelCode n tau h = c)

theorem mem_catalog {N n mesh : ℕ} {tau : ℝ} {h : Label N mesh} :
    h ∈ catalog N n mesh tau ↔ Valid n tau h := by
  simp only [catalog, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_cellFamily {N n mesh : ℕ} {tau : ℝ} {c : RootCode n} {h : Label N mesh} :
    h ∈ cellFamily N n mesh tau c ↔
      (Valid n tau h ∧ directionGuard (labelNode n tau h).upper
        (labelNode n tau h).physical) ∧ labelCode n tau h = c := by
  simp only [cellFamily, readyCatalog, Finset.mem_filter, mem_catalog]

theorem cellFamily_disjoint {N n mesh : ℕ} (tau : ℝ) {c d : RootCode n}
    (hcd : c ≠ d) : Disjoint (cellFamily N n mesh tau c) (cellFamily N n mesh tau d) := by
  apply Finset.disjoint_left.mpr
  intro h hc hd
  exact hcd ((mem_cellFamily.mp hc).2.symm.trans (mem_cellFamily.mp hd).2)

/-- Exact partition for arbitrary signed tests, so regrouping has no
positivity requirement and introduces no new multiplicity. -/
theorem sum_cellFamily (N n mesh : ℕ) (tau : ℝ) (F : Label N mesh → ℝ) :
    (∑ c : RootCode n, ∑ h ∈ cellFamily N n mesh tau c, F h) =
      ∑ h ∈ readyCatalog N n mesh tau, F h := by
  simp only [cellFamily, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem cell_Q_eq {N n mesh : ℕ} {tau : ℝ} {c : RootCode n} {h : Label N mesh}
    (hh : h ∈ cellFamily N n mesh tau c) :
    rootQ N n h.2.1 tau h.2.2.1.val = cellQ N n c := by
  have hc := (mem_cellFamily.mp hh).2
  change rootCode n (labelLevel tau h) = c at hc
  rw [← hc, cellQ, codeLevel_rootCode]
  rfl

/-- Every stated hypothesis of the preceding local row supplier is now
instantiated on this finite family, including the original residual floor.
The whole family is NOT identified with the selected count interpreter. -/
theorem cell_history_support {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {h : Label N mesh} (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ cellFamily N n mesh tau c) :
    parentWindow N (cellQ N n c) (labelWord h) (labelNode n tau h).physical.ceiling ∧
    residual (labelNode n tau h).physical = physicalLevel N (cellQ N n c) (labelWord h) ∧
    frozenResidualFloor ≤ physicalLevel N (cellQ N n c) (labelWord h) ∧
    (labelNode n tau h).physical.argument ∈ Icc (1:ℝ) 6 ∧
    2 ≤ P2OriginalChildPhysicalNormalization.alpha
      (Real.log (parentProduct (labelWord h):ℝ)/Real.log (N:ℝ))
      (physicalLevel N (cellQ N n c) (labelWord h)) ∧
    cellQ N n c = (parentProduct (labelWord h):ℝ)*
      (N:ℝ)^(physicalLevel N (cellQ N n c) (labelWord h)) := by
  have hv := (mem_cellFamily.mp hh).1.1
  have hs := history_support hN htau htauhi hn
    (show h.1.val ≤ 440 by omega) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.2
  dsimp only at hs
  rw [cell_Q_eq hh] at hs
  exact hs

/-- The actual next action uses the parent's polarity. -/
theorem label_buchstab_incoming {N mesh : ℕ} (n : ℕ) (tau : ℝ) (h : Label N mesh) :
    incomingAllowed (labelNode n tau h).upper
      (buchstabShape (labelNode n tau h).upper) := by
  cases hu : (labelNode n tau h).upper <;> simp [buchstabShape, incomingAllowed, hu]

/-- An inadmissible lower Buchstab action has an empty ORIGINAL integer
carrier. This is not an argument that the whole parent has zero mass. -/
theorem inactive_buchstab_row_zero {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} {up : Bool} (hg : ¬ directionGuard up p) (b : RowAtom) :
    strictRow up N Q chi old p b = 0 := by
  cases up with
  | true => exact False.elim (hg trivial)
  | false =>
      have hempty : singleChildren (.buchstab false p.argument) N Q old chi = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro q hq
        have hs : 2 ≤ p.argument := (mem_singleChildren.mp hq).2.2.1.1
        exact hg hs
      cases b <;> simp [strictRow, rowFrom, hempty]

/-- Same-Q parent Theta is the actual labelled sum. No quotient of
histories by their final product is performed. -/
theorem cell_Theta_exact {N n mesh : ℕ} (tau : ℝ) (c : RootCode n)
    (sigma : Label N mesh → ℝ) :
    parentTheta N (cellQ N n c) (cellFamily N n mesh tau c)
      (fun h => parentProduct (labelWord h)) sigma =
    ∑ h ∈ cellFamily N n mesh tau c, sigma h *
      thetaAtom N (rootQ N n h.2.1 tau h.2.2.1.val) (parentProduct (labelWord h)) := by
  unfold parentTheta
  apply Finset.sum_congr rfl
  intro h hh
  rw [cell_Q_eq hh]

/-- An inactive integer coordinate is exactly one (physical exponent
zero). Thus the finite representation has neither missing active primes
nor arbitrary dummy-coordinate copies. -/
theorem canonical_coordinate_cap {N : ℕ} {shape : StepShape} {q : IntegerPoint}
    (hN : 1 ≤ N) (hq : ∀ r ∈ appendedWord shape q, r ≤ N)
    (hc : canonicalPoint shape q) : ∀ i, q i ≤ N := by
  intro i
  cases shape <;> fin_cases i
  all_goals simp only [canonicalPoint] at hc
  all_goals
    first
    | exact hq _ (by simp [appendedWord])
    | simpa only [hc] using hN
    | simpa only [hc.1] using hN
    | simpa only [hc.2] using hN

/-- Every canonical natural-prime Member of depth<=440 is represented
in the finite catalog. The N+1 bound is proved, not an assumed truncation.
This is completeness for the stated Member class, not for original counts. -/
theorem natural_history_mem_catalog {N n mesh depth : ℕ} {k : Root} {tau : ℝ}
    {p : ℕ} {code : Program mesh depth} {q : IntegerCoordinates depth}
    (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hd : depth ≤ 440)
    (hp : p.Prime ∧ p.Coprime N) (ht : physicalPrime N p ∈ rootBand k)
    (hq : PrimeLetters N code q)
    (hc : ∀ j, canonicalPoint (code j).1 (q j))
    (hz : Member 0 1 depth (frozenRoot n k tau (physicalPrime N p))
      code (physicalCoordinates N q)) :
    ∃ h : Label N mesh, h ∈ catalog N n mesh tau ∧
      labelNode n tau h = historyNode N n k tau p code q ∧
      labelWord h = historyWord p code q ∧
      labelCode n tau h = rootCode n (sourceRoot k tau (physicalPrime N p)).physical.total := by
  have hpN : p ≤ N := prime_le_target hN hp.1.pos
    ((rootBand_subset k ht).2.trans (by norm_num))
  have ht0 : (frozenRoot n k tau (physicalPrime N p)).physical.total ≤ 1 :=
    (frozenLevel_bounds (root_total_bounds htau htauhi ht) n).1.trans
      (root_total_bounds htau htauhi ht).2
  have hw : word (frozenRoot n k tau (physicalPrime N p)).physical =
      [p].map (physicalPrime N) := by simp [word, frozenRoot, sourceRoot]
  have hold : ∀ r ∈ [p], 0 < r := by
    intro r hr
    have he : r = p := List.mem_singleton.mp hr
    subst r
    exact hp.1.pos
  have ha := path_active_cap hN ht0 hw hold hq hz
  have hcoords : ∀ j i, q j i ≤ N :=
    fun j => canonical_coordinate_cap hN.le (ha j) (hc j)
  let h : Label N mesh :=
    ⟨⟨depth, by omega⟩, k, ⟨p, Nat.lt_succ_of_le hpN⟩, code,
      fun j i => ⟨q j i, Nat.lt_succ_of_le (hcoords j i)⟩⟩
  refine ⟨h, ?_, rfl, rfl, rfl⟩
  apply mem_catalog.mpr
  exact ⟨hp, ht, hq, hc, hz⟩

end
end ImbalancedChen.Part5OriginalH430SameQHistoryCells
