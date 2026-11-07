import ImbalancedChen.Part5OriginalH430RequestedOriginalRowFreeze

/-!
P5.6 / h34: the ACTUAL original U3/U4 prime-receiver occurrences,
tagged by original root band and original selected prime.

SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
The two original root bands overlap.  Hence an arithmetic occurrence
must keep its U3/U4 tag and its full (p,q) labels; neither root prime
nor receiver prime is quotiented.  The frozen source is a genuine
finite superset, not the generated feedback-count history.

This is a set-theoretic arithmetic inclusion, not a closed-cell
count induction, an owner/filter identification, or a new input axiom.
-/

namespace ImbalancedChen.Part5OriginalH430TaggedArithmeticReceivers

noncomputable section
open Set
open scoped Classical BigOperators
open Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedOriginalRowFreeze

/-- The ORIGINAL two selected prime bands, without a disjointification.
If p lies in the overlap, it occurs in both tagged U3 and tagged U4. -/
def originalBand (N : ℕ) : Root → Finset ℕ
  | .U3 => chenSinglePrimeSelector N ((N : ℝ)^a) ((N : ℝ)^(1/3 : ℝ))
  | .U4 => chenSinglePrimeSelector N ((N : ℝ)^a) ((N : ℝ)^(59/250 : ℝ))

/-- Literal original arithmetic receiver, before the root is frozen. -/
def originalReceiver (N p : ℕ) : Finset ℕ :=
  chenSiftedQuotientPrimeSource N p ((N : ℝ)^a)

/-- Literal frozen-root receiver with the ACTUAL frozen Q and the
max-two sieve query. The query is not the true physical alpha. -/
def frozenReceiver (N n : ℕ) (tau : ℝ) (k : Root) (p : ℕ) : Finset ℕ :=
  chenSiftedQuotientPrimeSource N p
    ((rootQ N n k tau p / (p : ℝ)) ^
      (1 / (frozenRoot n k tau (physicalPrime N p)).physical.argument))

/-- The original selector itself supplies primality and coprimality:
they are not arbitrary geometric premises or a count licence. -/
theorem original_band_prime {N p : ℕ} {k : Root}
    (hp : p ∈ originalBand N k) : p.Prime ∧ p.Coprime N := by
  have hc : p ∈ chenAdditivePrimeCarrier N := by
    cases k <;> exact (Finset.mem_filter.mp hp).1
  have h := mem_chenAdditivePrimeCarrier.mp hc
  exact ⟨h.2.1, h.2.2⟩

/-- The actual selected-prime cutoff entails the frozen root band.
The strict source upper endpoint becomes a weak geometric upper bound. -/
theorem original_band_geometry {N p : ℕ} {k : Root}
    (hN : 2 ≤ N) (hp : p ∈ originalBand N k) :
    physicalPrime N p ∈ rootBand k := by
  cases k with
  | U3 =>
      have hc : primeCoordinate N p ∈ Ico a (1/3 : ℝ) :=
        primeCoordinate_mem hN (by simpa only [originalBand] using hp)
      change primeCoordinate N p ∈ Icc a (1/3 : ℝ)
      exact ⟨hc.1, hc.2.le⟩
  | U4 =>
      have hc : primeCoordinate N p ∈ Ico a (59/250 : ℝ) :=
        primeCoordinate_mem hN (by simpa only [originalBand] using hp)
      change primeCoordinate N p ∈ Icc a (59/250 : ℝ)
      exact ⟨hc.1, hc.2.le⟩

/-- Pointwise arithmetic inclusion of the SAME receiver q and prime p.
This is stronger than a comparison of their cardinalities.  Lowering Q
lowers the strict sieve cutoff, which increases the receiver set. -/
theorem original_receiver_subset_frozen (N n : ℕ) (k : Root) (tau : ℝ)
    (p : ℕ) (hN : 2 ≤ N)
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (hp : p ∈ originalBand N k) :
    originalReceiver N p ⊆ frozenReceiver N n tau k p := by
  have hpp : 0 < p := (original_band_prime hp).1.pos
  have hb := original_band_geometry hN hp
  have hQ := frozen_root_sameQ_cutoff_power N n p k tau
    hN hpp htau htauhi hb hn
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hcut :
      (rootQ N n k tau p / (p : ℝ)) ^
        (1 / (frozenRoot n k tau (physicalPrime N p)).physical.argument) ≤
          (N : ℝ)^a := by
    rw [hQ]
    exact Real.rpow_le_rpow_of_exponent_le hNr (min_le_left _ _)
  intro q hq
  change q ∈ chenSiftedQuotientPrimeSource N p ((N : ℝ)^a) at hq
  change q ∈ chenSiftedQuotientPrimeSource N p
    ((rootQ N n k tau p / (p : ℝ)) ^
      (1 / (frozenRoot n k tau (physicalPrime N p)).physical.argument))
  obtain ⟨hbase, hrough⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr
    ⟨hbase, fun ell hell hdiv => hcut.trans (hrough ell hell hdiv)⟩

/-- Each original tagged receiver starts at the ACTUAL frozen U3/U4
root with its original prime p, and keeps its q label in the frozen
finite arithmetic row.  The root occurs ONCE in the feedback history;
this does NOT identify its one mark with the number of receivers q. -/
theorem original_receiver_root_witness (N n : ℕ) (k : Root)
    (tau : ℝ) (p q : ℕ) (hN : 2 ≤ N)
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (hp : p ∈ originalBand N k) (hq : q ∈ originalReceiver N p) :
    q ∈ frozenReceiver N n tau k p ∧
    Coherent N (rootQ N n k tau p) (rootRequest N n k tau p) ∧
    origin 430 (rootRequest N n k tau p) ∈ rootHistory N n k tau p ∧
    mark (origin 430 (rootRequest N n k tau p)) = 1 := by
  have hprime := original_band_prime hp
  have hb := original_band_geometry hN hp
  refine ⟨original_receiver_subset_frozen N n k tau p hN htau htauhi hn hp hq,
    root_coherent (by omega) htau htauhi hn hprime hb, ?_, by simp⟩
  change origin 430 (rootRequest N n k tau p) ∈
    history N (rootQ N n k tau p) 430 (rootRequest N n k tau p)
  exact List.mem_cons_self

/-- A row is indexed by BOTH the original p and receiver q. -/
abbrev TaggedPair := Σ _ : ℕ, ℕ

/-- Sum.inl is U3 and Sum.inr is U4; the tag retains overlap cost. -/
abbrev TaggedReceiver := Sum TaggedPair TaggedPair

def originalPairs (N : ℕ) (k : Root) : Finset TaggedPair :=
  (originalBand N k).sigma (fun p => originalReceiver N p)

def frozenPairs (N n : ℕ) (tau : ℝ) (k : Root) : Finset TaggedPair :=
  (originalBand N k).sigma (fun p => frozenReceiver N n tau k p)

def originalTagged (N : ℕ) : Finset TaggedReceiver :=
  (originalPairs N .U3).disjSum (originalPairs N .U4)

def frozenTagged (N n : ℕ) (tau : ℝ) : Finset TaggedReceiver :=
  (frozenPairs N n tau .U3).disjSum (frozenPairs N n tau .U4)

/-- Every individual original (root,p,q) source position survives, even
when the same p occurs in both original root bands. -/
theorem original_pairs_subset_frozen (N n : ℕ) (k : Root)
    (tau : ℝ) (hN : 2 ≤ N)
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    originalPairs N k ⊆ frozenPairs N n tau k := by
  intro z hz
  obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp hz
  exact Finset.mem_sigma.mpr
    ⟨hp, original_receiver_subset_frozen N n k tau z.1 hN htau htauhi hn hp hq⟩

/-- This is a literal injection of the original tagged arithmetic source
into a larger frozen tagged arithmetic source, NOT into feedback tables. -/
theorem original_tagged_subset_frozen (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    originalTagged N ⊆ frozenTagged N n tau := by
  intro z hz
  cases z with
  | inl v =>
      have hv : v ∈ originalPairs N .U3 := by
        simpa [originalTagged] using hz
      have hf := original_pairs_subset_frozen N n .U3 tau hN htau htauhi hn hv
      simpa [frozenTagged] using hf
  | inr v =>
      have hv : v ∈ originalPairs N .U4 := by
        simpa [originalTagged] using hz
      have hf := original_pairs_subset_frozen N n .U4 tau hN htau htauhi hn hv
      simpa [frozenTagged] using hf

/-- Exact finite source multiplicity: one (p,q) in each original band
for each ORIGINAL contribution.  The overlap occurs twice, not once. -/
theorem original_tagged_card (N : ℕ) :
    (originalTagged N).card =
      (∑ p ∈ originalBand N .U3, (originalReceiver N p).card) +
      ∑ p ∈ originalBand N .U4, (originalReceiver N p).card := by
  simp [originalTagged, originalPairs, Finset.card_disjSum, Finset.card_sigma]

/-- Connect the tagged source to the manuscript's ACTUAL U3+U4 terms,
not to an abstract model count or an arbitrary outer-weighted total. -/
theorem original_U34_eq_tagged_card (N : ℕ) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      ((originalTagged N).card : ℝ) := by
  rw [currentChenUpsilon3_eq_siftedQuotientPrimeSource,
    currentChenUpsilon4_eq_siftedQuotientPrimeSource, original_tagged_card]
  simp [originalBand, originalReceiver, Nat.cast_add, Nat.cast_sum]

/-- The actual source upper bound is now a cardinal inequality obtained
from a genuine tagged subset, rather than only a scalar row estimate.
No total selected-history counting theorem is inferred from this. -/
theorem original_U34_le_frozen_tagged (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    currentChenUpsilon3 N + currentChenUpsilon4 N ≤
      ((frozenTagged N n tau).card : ℝ) := by
  rw [original_U34_eq_tagged_card]
  exact_mod_cast Finset.card_le_card
    (original_tagged_subset_frozen N n tau hN htau htauhi hn)

/-- The extra frozen receivers are exposed as a real finite rejection
lane. No claim bounds its mass or identifies its selected-count owner. -/
def frozenOnly (N n : ℕ) (tau : ℝ) : Finset TaggedReceiver :=
  frozenTagged N n tau \ originalTagged N

theorem frozenOnly_iff (N n : ℕ) (tau : ℝ) (z : TaggedReceiver) :
    z ∈ frozenOnly N n tau ↔
      z ∈ frozenTagged N n tau ∧ z ∉ originalTagged N := by
  simp [frozenOnly]

end
end ImbalancedChen.Part5OriginalH430TaggedArithmeticReceivers
