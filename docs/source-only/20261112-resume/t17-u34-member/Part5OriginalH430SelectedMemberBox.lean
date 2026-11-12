import ImbalancedChen.Part5OriginalH430OriginalReceiptMemberPullback
import ImbalancedChen.Part5OriginalH430ActualMemberStrictCover
import ImbalancedChen.Part5OriginalH430ActualResolvedPhysicalGates

/-! Selected immutable bank positions on positive, labelled Member boxes.
Partition by actual path/cells, branch and *request* owner, at each one
of the owned root keys. Two additive root tags remain separate throughout.
Theta is a prefix measure; it is not multiplied by the receipt count. -/
namespace ImbalancedChen.Part5OriginalH430SelectedMemberBox
noncomputable section
open scoped Classical BigOperators
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPhysicalNode
open P2Selected430CausalOccurrenceExporter (iterate queryCell)
open P5OriginalActionMassBound (Original106Action)
open P2EnhancedLowerPrimeChildCarriers (parentProduct physicalPrime)
open P2FrozenReceiverCountActions (frozenCount)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430ActualResolvedPhysicalGates Part5OriginalH430ArithmeticParentMass
open Part5OriginalH430RootSourceDictionary Part5OriginalH430OriginalReceiptMemberPullback

abbrev Box (mesh : ℕ) := (GraphVertex mesh 430 × Bool) × Bool × Option (Fin 200)

def atBox {N n p G : ℕ} {k : Root} {t : ℝ}
    (mesh : ℕ) (l : LevelIndex N n k t p G) : Box mesh :=
  let o := levelOccurrence l
  have h := (rootHistory_computed_data (levelOccurrence_source l).1).1
  ((⟨⟨o.path.length,by dsimp only [o]; omega⟩,pathCode mesh o.path⟩,
      decide (o.current.node.physical.argument = 2)),
    decide (rootSource k (physicalPrime N p) = .enhanced),resolve G o.current)

def boxOf {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}
    (mesh : ℕ) (l : Index N n k t p g) : Box mesh := atBox mesh l

def positions (N n mesh : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430)
    (act : Original106Action) (b : Box mesh) : Finset (Index N n k t p g) :=
  (selectedLevel N n k t p g act).filter (fun l => boxOf mesh l = b)

/-- This is exactly the original Member computed on the ordered integer
letters. At knots a specified cell is kept; it is not overwritten by the
scalar owner. This box comes from one and only one requested cell. -/
theorem occupied_member_owner {N n m mesh p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}
    {act : Original106Action} {c : RootKey n m} {b : Box mesh} {l : Index N n k t p g}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p ∈ rootFibre N n m k t c) (hl : l ∈ positions N n mesh k t p g act b) :
    let o := levelOccurrence l
    Member 0 1 o.path.length (frozenRoot n k t (physicalPrime N p))
      (pathCode mesh o.path) (physicalCoordinates N (pathPrimes o.path)) ∧
    (∃! i : Fin 200, b.2.2 = some i ∧ o.current.node.physical.argument ∈ queryCell i) ∧
    b.2.1 = decide (rootSource k (physicalPrime N p) = .enhanced) ∧
    cellQ N n c.1 = rootQ N n k t p := by
  dsimp only
  obtain ⟨ha,hb⟩ := Finset.mem_filter.mp hl
  subst b
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp ha).2
  have hband := (Finset.mem_filter.mp hp).1
  have ho := (levelOccurrence_source l).1
  have hc := rootHistory_coherent (by omega : 1<N) ht hu hn
    (original_band_prime hband) (original_band_geometry hN hband) ho
  refine ⟨rootHistory_member mesh (by omega : 1<N) ht hu hn (original_band_prime hband)
    (original_band_geometry hN hband) ho,⟨i,⟨hi.1,resolve_contains hc.read_valid hi.1⟩,?_⟩,
    rfl,(original_fibre_geometry hN ht hu hn hp).1⟩
  intro j hj
  exact Option.some.inj (hj.1.symm.trans hi.1)

/-- Two independently described finite counts: the frozen additive prime
with inherited root predicate, and the ORIGINAL root quotient that survives
the path. Outer coefficients are products of the actual selected edges. -/
theorem box_count_pullback {N n m mesh : ℕ} (k : Root) {t : ℝ}
    (g : Fin 430) (act : Original106Action) (c : RootKey n m) (b : Box mesh)
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    let Q := cellQ N n c.1
    (∑ p ∈ rootFibre N n m k t c, ∑ l ∈ positions N n mesh k t p g act b,
      levelMark l * (frozenCount N (parentProduct (levelOccurrence l).current.old)
        (rootMask N p) (memberCutoff Q (levelOccurrence l)) : ℝ)) =
    ∑ p ∈ rootFibre N n m k t c, ∑ l ∈ positions N n mesh k t p g act b,
      levelMark l * ((originalReceiptLane N p (tailProduct (levelOccurrence l))
        (memberCutoff Q (levelOccurrence l))).card : ℝ) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro l _
  rw [owned_member_masked_count hN ht hu hn hp (levelOccurrence_source l).1]

/-- Actual incidence coefficient of ONE original receipt q in this selected
box. Its divisibility and residual roughness are fixed by the path, and
every matching history LIST position pays its own positive edge weight. -/
def receiptMark (N n mesh : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430)
    (act : Original106Action) (b : Box mesh) (Q : ℝ) (q : ℕ) : ℝ :=
  ∑ l ∈ positions N n mesh k t p g act b,
    if tailProduct (levelOccurrence l) ∣ q ∧
      ChenPrimeRough (memberCutoff Q (levelOccurrence l)) (q/tailProduct (levelOccurrence l))
    then levelMark l else 0

theorem receiptMark_nonneg (N n mesh : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430)
    (act : Original106Action) (b : Box mesh) (Q : ℝ) (q : ℕ) :
    0 ≤ receiptMark N n mesh k t p g act b Q q := by
  apply Finset.sum_nonneg
  intro l _
  split_ifs <;> first | exact (mark_pos (levelOccurrence l)).le | exact le_rfl

def boxMasked (N n m mesh : ℕ) (k : Root) (t : ℝ) (g : Fin 430)
    (act : Original106Action) (c : RootKey n m) (b : Box mesh) : ℝ :=
  ∑ p ∈ rootFibre N n m k t c, ∑ l ∈ positions N n mesh k t p g act b,
    levelMark l * (frozenCount N (parentProduct (levelOccurrence l).current.old)
      (rootMask N p) (memberCutoff (cellQ N n c.1) (levelOccurrence l)) : ℝ)

/-- Transpose the actual selected count into a sum over the ORIGINAL
root q's. Empty, singly represented and multiply represented receipts
get the computed incidence coefficient (not a unit coefficient). -/
theorem box_count_on_original_receipts {N n m mesh : ℕ} (k : Root) {t : ℝ}
    (g : Fin 430) (act : Original106Action) (c : RootKey n m) (b : Box mesh)
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    boxMasked N n m mesh k t g act c b =
      ∑ p ∈ rootFibre N n m k t c, ∑ q ∈ originalReceiver N p,
        receiptMark N n mesh k t p g act b (cellQ N n c.1) q := by
  unfold boxMasked
  rw [box_count_pullback k g act c b hN ht hu hn]
  apply Finset.sum_congr rfl
  intro p _
  unfold receiptMark
  rw [Finset.sum_comm (s := originalReceiver N p)]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_filter]
  simp only [originalReceiptLane, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Both original tagged populations are summed independently, using
their own path marks. In particular an overlap receipt has BOTH terms. -/
theorem U34_box_original_receipts {N n m mesh : ℕ} {t : ℝ} (g : Fin 430)
    (act : Original106Action) (c : RootKey n m) (b : Box mesh)
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    boxMasked N n m mesh .U3 t g act c b + boxMasked N n m mesh .U4 t g act c b =
      (∑ p ∈ rootFibre N n m .U3 t c, ∑ q ∈ originalReceiver N p,
        receiptMark N n mesh .U3 t p g act b (cellQ N n c.1) q) +
      ∑ p ∈ rootFibre N n m .U4 t c, ∑ q ∈ originalReceiver N p,
        receiptMark N n mesh .U4 t p g act b (cellQ N n c.1) q := by
  rw [box_count_on_original_receipts .U3 g act c b hN ht hu hn,
      box_count_on_original_receipts .U4 g act c b hN ht hu hn]

/-- Original positive normalizer disintegrated on the VERY SAME boxes,
including empty boxes. Physical Q is constant on this owned root fibre.
Prefix marks are summed by list position even if their integer products
coincide; no division by the number of receipts occurs. -/
def boxTheta (N n m mesh : ℕ) (k : Root) (t : ℝ) (g : Fin 430)
    (act : Original106Action) (c : RootKey n m) (b : Box mesh) : ℝ :=
  ∑ p ∈ rootFibre N n m k t c, parentTheta N (cellQ N n c.1)
    (positions N n mesh k t p g act b)
    (fun l => parentProduct (levelOccurrence l).current.old) (fun l => levelMark l)

theorem boxTheta_nonneg {N n m mesh : ℕ} (k : Root) {t : ℝ} (g : Fin 430)
    (act : Original106Action) (c : RootKey n m) (b : Box mesh)
    (hN : 4 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    0 ≤ boxTheta N n m mesh k t g act c b := by
  apply Finset.sum_nonneg
  intro p hp
  have hband := (Finset.mem_filter.mp hp).1
  have hpr := original_band_prime hband
  have htband := original_band_geometry (by omega : 2≤N) hband
  rw [(original_fibre_geometry (by omega : 2≤N) ht hu hn hp).1]
  exact parentTheta_nonneg hN _ _ _ _ (fun l _ =>
    actual_level_parent_product_pos N n k t p g l hN ht hu hn hpr htband)
    (fun l _ => (mark_pos (levelOccurrence l)).le) (fun l _ =>
      actual_level_quotient_gt_one N n k t p g l hN ht hu hn hpr htband)

theorem sum_boxTheta {N n m : ℕ} (mesh : ℕ) (k : Root) {t : ℝ} (g : Fin 430)
    (act : Original106Action) (c : RootKey n m)
    (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    (∑ b : Box mesh, boxTheta N n m mesh k t g act c b) =
      ∑ p ∈ rootFibre N n m k t c, levelTheta N n k t p g act := by
  unfold boxTheta
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  unfold parentTheta levelTheta positions
  rw [(original_fibre_geometry hN ht hu hn hp).1]
  exact Finset.sum_fiberwise_of_maps_to (s := selectedLevel N n k t p g act)
    (t := Finset.univ) (g := boxOf mesh) (fun _ _ => Finset.mem_univ _)
    (fun l => levelMark l * thetaAtom N (rootQ N n k t p)
      (parentProduct (levelOccurrence l).current.old))

/-- The paper adds both labelled occurrences for a prime in the U4
overlap. Regrouping all root and descendant boxes recovers the two
ORIGINAL selected levelTheta sums; no symmetry of tags is needed. -/
theorem U34_selected_theta_exact {N n m : ℕ} (mesh : ℕ) {t : ℝ} (g : Fin 430)
    (act : Original106Action) (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    ((∑ c : RootKey n m, ∑ b : Box mesh, boxTheta N n m mesh .U3 t g act c b) +
     (∑ c : RootKey n m, ∑ b : Box mesh, boxTheta N n m mesh .U4 t g act c b)) =
    (∑ p ∈ originalBand N .U3, levelTheta N n .U3 t p g act) +
      ∑ p ∈ originalBand N .U4, levelTheta N n .U4 t p g act := by
  have h (k : Root) :
      (∑ c : RootKey n m, ∑ b : Box mesh, boxTheta N n m mesh k t g act c b) =
      ∑ p ∈ originalBand N k, levelTheta N n k t p g act := by
    simp_rw [sum_boxTheta mesh k g act _ hN ht hu hn]
    exact Finset.sum_fiberwise_of_maps_to (s := originalBand N k) (t := Finset.univ)
      (g := keyAt N n m k t) (fun _ _ => Finset.mem_univ _)
      (fun p => levelTheta N n k t p g act)
  exact congrArg₂ (· + ·) (h .U3) (h .U4)

end
end ImbalancedChen.Part5OriginalH430SelectedMemberBox
