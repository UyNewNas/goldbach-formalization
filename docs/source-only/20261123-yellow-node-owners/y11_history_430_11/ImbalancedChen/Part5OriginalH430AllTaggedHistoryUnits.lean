import ImbalancedChen.Part5OriginalH430AllOriginalReceiptIncidence
import ImbalancedChen.Part5OriginalH430PresieveOutsideFin
import ImbalancedChen.Part5OriginalH430SignedOriginalFinCapacityGap
import ImbalancedChen.Part5OriginalH430RoughCutoffSelberg

/-! All original quotient receipts with their true multiplicity, for the
classical and nonclassical pieces of U3 and for the whole of U4. -/
namespace ImbalancedChen.Part5OriginalH430AllTaggedHistoryUnits
noncomputable section
open Filter Finset
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers (parentProduct physicalPrime)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions (frozenCount)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430RequestedHistory Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430CompatibleHistoryPayment Part5OriginalH430ZeroFreshReceiverPayment
open Part5OriginalH430RoughCutoffSelberg Part5OriginalH430AllOriginalReceiptIncidence
open Part5OriginalH430MonotoneSieveHeight Part5OriginalH430PresieveOutsideFin
open Part5OriginalH430NegativeQuarterActualPositionDirection
open Part5OriginalH430PhysicalSlotCollisionLedger Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430SequentialTaggedReceiptDebt Part5OriginalH430FullTaggedActualFinPushforward
open Part5OriginalH430SignedOriginalFinCapacityGap Part5OriginalH430OriginalUpperOverlapCount

def units (N n m : ℕ) (k : Root) (t : ℝ) (p : ℕ) : ℝ :=
  compatibleTotal N n m k t (keyAt N n m k t p) p / listBudget (rootHistory N n k t p)

theorem multiplicity_range (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ) :
    1≤listBudget (rootHistory N n k t p) ∧ listBudget (rootHistory N n k t p)≤431 := by
  refine ⟨?_,zeroFresh_rootHistory_budget N n k t p⟩
  have h (os : List (Occurrence N)) : 0≤listBudget os := by
    induction os with
    | nil => exact le_rfl
    | cons o os ih => exact add_nonneg (occurrenceBudget_nonneg o) ih
  change 1≤occurrenceBudget (origin (N:=N) 430 (rootRequest N n k t p))+listBudget _
  rw [occurrenceBudget_origin]
  exact le_add_of_nonneg_right (h _)

theorem units_eq {N n m p : ℕ} {k : Root} {t : ℝ} (hN : 2≤N)
    (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) :
    units N n m k t p=((originalReceiver N p).card:ℝ) := by
  have hf : p∈rootFibre N n m k t (keyAt N n m k t p) := mem_filter.mpr ⟨hp,rfl⟩
  rw [units,compatibleTotal_exact hN ht hu hn hf]
  field_simp [(root_listBudget_pos N n k t p).ne']

/-- On the full manuscript presieve at the physical root, restore EACH
tagged prime separately before applying the original negative quarter. -/
theorem manuscript_signed_all_root_units {N cap n m p : ℕ} {k : Root} {t z0 : ℝ}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k)
    (hz : z0≤cutoff (rootQ N n k t p) p (frozenRoot n k t (physicalPrime N p)).physical.argument)
    (hcap : z0≤(cap:ℝ)) (lower : Bool) :
    originalU34SignedQuarter N = -(1/4:ℝ) *
      ((occupiedFinUnits N cap n t z0 lower+excessFinUnits N cap n t z0 lower)+
        ((∑ u∈originalBand N .U3, units N n m .U3 t u)+
          ∑ u∈originalBand N .U4, units N n m .U4 t u)) := by
  have hsrc := full_tagged_fin_at_manuscript_presieve hN ht hu hn hp hz hcap lower
  have hout : outsideRejectedUnits N cap n t z0 lower =
      ((∑ u∈originalBand N .U3, ((originalReceiver N u).card:ℝ))+
        ∑ u∈originalBand N .U4, ((originalReceiver N u).card:ℝ)) := by
    calc
      _ = ∑ z∈originalTagged N, (1:ℝ) := hsrc.2.2 _
      _ = ((originalTagged N).card:ℝ) := by simp
      _ = _ := by exact_mod_cast original_tagged_card N
  have hroot (j : Root) : (∑ u∈originalBand N j, units N n m j t u) =
      ∑ u∈originalBand N j, ((originalReceiver N u).card:ℝ) :=
    sum_congr rfl (fun u hu' => units_eq hN ht hu hn hu')
  rw [hroot,hroot,original_signed_quarter_three_way N cap n t z0 lower hcap,hout]

/-- Inherited and rejected are kept as different actual unsigned integer
populations. At every post-fresh member the unrestricted count is exactly
the rejected count, irrespective of its later owner or read mode. -/
theorem entire_fresh_count_rejected {N n m p : ℕ} {k : Root} {t : ℝ} {c : RootKey n m}
    {o : Occurrence N} (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (hf : o.path.all zeroFreshEdge ≠ true) :
    let z := memberCutoff (cellQ N n c.1) o
    let B := parentProduct o.current.old
    (frozenCount N B (receiver N) z:ℝ)=((rejectedChild N B (tailProduct o) z).card:ℝ) := by
  have hz := (fresh_rejection_exact hN ht hu hn (mem_filter.mp hp).1 ho hf
    (memberCutoff (cellQ N n c.1) o)).1
  have hr := actual_member_count_split hN ht hu hn hp ho
  simpa only [hz,card_empty,Nat.cast_zero,zero_add] using hr

private theorem full_origin {N n m p : ℕ} {k : Root} {t : ℝ} {c : RootKey n m}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈rootFibre N n m k t c) :
    let o := origin (N:=N) 430 (rootRequest N n k t p)
    ((originalReceiver N p).card:ℝ)≤(frozenCount N p (rootMask N p) (memberCutoff (cellQ N n c.1) o):ℝ) := by
  let o := origin (N:=N) 430 (rootRequest N n k t p)
  have ho : o∈rootHistory N n k t p := List.mem_cons_self
  have hB : parentProduct o.current.old=p := by simp [o,origin,rootRequest,parentProduct]
  have hD : tailProduct o=1 := rfl
  have hf := (mem_filter.mp hp).1
  have hz := member_cutoff_le_original hN ht hu hn hf ho
  rw [←(original_fibre_geometry hN ht hu hn hp).1] at hz
  have hsubset : originalReceiver N p ⊆ originalReceiptLane N p 1 (memberCutoff (cellQ N n c.1) o) := by
    intro q hq
    refine mem_filter.mpr ⟨hq,one_dvd _,?_⟩
    rw [Nat.div_one]
    exact fun u hu hd => hz.trans ((mem_filter.mp hq).2 u hu hd)
  have h := owned_member_masked_count hN ht hu hn hp ho
  dsimp only at h
  rw [hD,hB] at h
  exact h.ge.trans' (by exact_mod_cast card_le_card hsubset)

/-- Every subset of either original prime band, including U4 and the
nonclassical part of U3, has an O(own theta) upper charge. This constant
comes from the same integer Selberg count at its actual occupied origin. -/
theorem all_positive_root_subfamilies :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, Even N →
    ∀ (n m : ℕ) (k : Root) (t : ℝ) (c : RootKey n m) (S : Finset ℕ) (weight : ℕ→ℝ),
    0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → S⊆rootFibre N n m k t c → (∀ p∈S, 0≤weight p) →
    (∑ p∈S, weight p * compatibleTotal N n m k t c p) ≤
      431*C*(∑ p∈S, weight p * thetaAtom N (cellQ N n c.1) p) := by
  obtain ⟨C,hC,rows⟩ := actual_member_count_dominated
  refine ⟨C,hC,?_⟩
  filter_upwards [rows,eventually_ge_atTop (2:ℕ)] with N hrow hN
  intro hev n m k t c S weight ht hu hn hsub hw
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hf := hsub hp
  let o := origin (N:=N) 430 (rootRequest N n k t p)
  have ho : o∈rootHistory N n k t p := List.mem_cons_self
  have hB : parentProduct o.current.old=p := by simp [o,origin,rootRequest,parentProduct]
  have hq := (original_fibre_geometry hN ht hu hn hf).1
  have hc := hrow hev n p k t o (rootMask N p) ht hu hn (mem_filter.mp hf).1 ho (fun _ h => h.1)
  dsimp only at hc
  rw [←hq,hB] at hc
  have hh := (full_origin hN ht hu hn hf).trans hc
  rw [compatibleTotal_exact hN ht hu hn hf]
  have h1 := mul_le_mul_of_nonneg_right (multiplicity_range N n k t p).2 (Nat.cast_nonneg (originalReceiver N p).card)
  have h2 := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤431)
  exact (mul_le_mul_of_nonneg_left (h1.trans h2) (hw p hp)).trans_eq (by ring)

end
end ImbalancedChen.Part5OriginalH430AllTaggedHistoryUnits
