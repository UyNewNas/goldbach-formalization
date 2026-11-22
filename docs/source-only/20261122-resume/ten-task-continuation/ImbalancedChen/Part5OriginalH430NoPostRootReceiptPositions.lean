import ImbalancedChen.Part5OriginalH430SignedOriginalFinCapacityGap
import ImbalancedChen.Part5OriginalH430PresieveOutsideFin
import ImbalancedChen.Part5OriginalH430CompatibleHistoryPayment
import ImbalancedChen.Part5OriginalH430ZeroFreshReceiverPayment

/-! The p-rough part of the original U3/U4 root-cutoff rejection lane.
At its real root p, a receipt with no prime divisor below p survives
exactly the selected history positions with no appended prime. The
cutoff at a fixed read can change. Its physical root level stays fixed.
SOURCE ONLY / UNCOMPILED. -/

namespace ImbalancedChen.Part5OriginalH430NoPostRootReceiptPositions
noncomputable section
open Finset Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPhysicalTransition (perform_ceiling)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430IntegerItineraries (appendedWord)
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430ActualRootGateCoprime (rootCutoffBlocked)
open Part5OriginalH430OriginalSelectedRootFibres (originalCutoffRoots original_selected_cutoff_signed)
open Part5OriginalH430PresieveOutsideFin (full_tagged_fin_at_manuscript_presieve)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open Part5OriginalH430OriginalSecondFactorWindow
open Part5OriginalH430SignedOriginalFinCapacityGap (outsideRejectedUnits)
open Part5OriginalH430OwnedRootCounts Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430HistoryQuotientCounts (history_integer_roughness)
open Part5OriginalH430FreshBranchIncidence (Allowed)
open Part5OriginalH430CompatibleHistoryPayment
open Part5OriginalH430ZeroFreshReceiverPayment
open Part5OriginalH430ClassicalReceiverSubfamily

theorem no_post_iff_rough (z : TaggedReceiver) :
    ¬ hasPostRootPrimeFactor z ↔
      ChenPrimeRough (arithmeticPrime z : ℝ) (arithmeticQuotientPrime z) := by
  constructor
  · intro h r hr hd
    have hle : arithmeticPrime z ≤ r := le_of_not_gt (fun hlt => h ⟨r,hr,hd,hlt⟩)
    exact_mod_cast hle
  · rintro h ⟨r,hr,hd,hlt⟩
    have hle : arithmeticPrime z ≤ r := by exact_mod_cast h r hr hd
    exact (not_lt_of_ge hle) hlt

/-- Actual cutoff-blocked original quotient receipts with all divisor primes at
least p. Both original tags use this test on their own selected prime bands. -/
def noPostFibre (N : ℕ) (z0 : ℝ) (p : ℕ) : Finset ℕ :=
  if ¬ (p : ℝ) < z0 then (originalReceiver N p).filter (ChenPrimeRough (p : ℝ)) else ∅

private theorem mem_noPostFibre {N p q : ℕ} {z0 : ℝ} :
    q ∈ noPostFibre N z0 p ↔
      ¬ (p : ℝ) < z0 ∧ q ∈ originalReceiver N p ∧ ChenPrimeRough (p : ℝ) q := by
  by_cases hs : (p : ℝ) < z0 <;> simp [noPostFibre,hs]

/-- An original additive prime complementary to p supplies the actual
quotient q=1 throughout the cutoff-blocked part of the p fibre. -/
theorem unit_receipt_of_additive_complement {N p ell : ℕ} {z0 : ℝ}
    (hp : 0 < p) (hz : z0 ≤ (p : ℝ)) (hell : ell ∈ chenAdditivePrimeCarrier N)
    (hadd : p + ell = N) : 1 ∈ noPostFibre N z0 p := by
  have hsub : N - ell = p := by omega
  have hbase : 1 ∈ chenQuotientPrimeSource N p := by
    refine Finset.mem_image.mpr ⟨ell,mem_chenQuotientPrimeCarrier.mpr ⟨hell,?_⟩,?_⟩
    · simpa only [hsub] using (dvd_refl p)
    · simpa only [hsub] using (Nat.div_self (by omega) : p / p = 1)
  have hu (z : ℝ) : ChenPrimeRough z 1 := fun r hr hd =>
    False.elim (hr.ne_one (Nat.dvd_one.mp hd))
  exact mem_noPostFibre.mpr ⟨not_lt_of_ge hz,Finset.mem_filter.mpr ⟨hbase,hu _⟩,hu _⟩

/-- A real fresh child has a prime strictly below its incoming ceiling.
The weak square inequalities alone would leave the equality case. -/
private theorem allowed_child_zeroFresh {N g p q : ℕ} {Q : ℝ} {r : Request} {e : Edge N}
    (hc : Coherent N Q r) (hp : p.Prime) (hq : ChenPrimeRough (p : ℝ) q)
    (hceil : r.node.physical.ceiling ≤ physicalPrime N p) (he : e ∈ children N Q g r)
    (ha : Allowed q.primeFactors e) : zeroFreshEdge e = true := by
  have excluded {u : ℕ} (hu : physicalPrime N u < r.node.physical.ceiling)
      (hm : u ∈ q.primeFactors) : False := by
    have hpu := hq u (Nat.prime_of_mem_primeFactors hm) (Nat.dvd_of_mem_primeFactors hm)
    have hcoord : physicalPrime N p ≤ physicalPrime N u :=
      div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hp.pos) hpu)
        (Real.log_pos (by exact_mod_cast hc.target_gt_one)).le
    exact (not_lt_of_ge (hceil.trans hcoord)) hu
  have single {rule : SingleRule} {u : Fin (N+1)}
      (hu : u ∈ singleChildren rule N Q r.old r.node.physical.ceiling) :
      u.val ∉ q.primeFactors := excluded (mem_singleChildren.mp hu).2.2.2.1
  obtain ⟨i,c,_,he⟩ := child_source he
  cases c with
  | retained =>
      have heq : e = .retained i := by simpa only [branchEdges,List.mem_singleton] using he
      subst e
      rfl
  | buchstab =>
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp he
      exact False.elim (single (Finset.mem_toList.mp hu) (ha u.val (by
        cases hb : r.node.upper <;> simp [edgeShape,edgePrimes,appendedWord,hb])))
  | bank slot =>
      suffices hbank : ∀ (a : P5OriginalActionMassBound.Original106Action) {d : Edge N},
          d ∈ bankEdges N Q r a → Allowed q.primeFactors d → zeroFreshEdge d = true by
        exact hbank _ he ha
      intro act e he ha
      rcases act with ⟨j,l⟩ | j
      · rcases (show e = .w1Fixed j l ∨ e ∈ w1Edges N Q r j l by
          simpa only [bankEdges,List.mem_cons] using he) with rfl | he
        · rfl
        · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp he
          exact False.elim (single (Finset.mem_toList.mp hu)
            (ha u.val (by simp [edgeShape,edgePrimes,appendedWord])))
      · have hsingle (l : Fin 3) {d : Edge N} (hd : d ∈ w2SingleEdges N Q r j l)
            (had : Allowed q.primeFactors d) : zeroFreshEdge d = true := by
          obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hd
          exact False.elim (single (Finset.mem_toList.mp hu)
            (had u.val (by simp [edgeShape,edgePrimes,appendedWord])))
        have hpair (l : Fin 4) {d : Edge N} (hd : d ∈ w2PairEdges N Q r j l)
            (had : Allowed q.primeFactors d) : zeroFreshEdge d = true := by
          obtain ⟨uv,hu,rfl⟩ := List.mem_map.mp hd
          have hsmall := (mem_pairChildren.mp (Finset.mem_toList.mp hu)).2.2.2.2.1
          exact False.elim (excluded hsmall
            (had uv.1.val (by simp [edgeShape,edgePrimes,appendedWord])))
        simp only [bankEdges,List.mem_append,List.mem_cons,List.mem_singleton,
          List.not_mem_nil,or_false] at he
        rcases he with (rfl | rfl) | h0 | h1 | h2 | h0 | h1 | h2 | h3
        · rfl
        · rfl
        · exact hsingle 0 h0 ha
        · exact hsingle 1 h1 ha
        · exact hsingle 2 h2 ha
        · exact hpair 0 h0 ha
        · exact hpair 1 h1 ha
        · exact hpair 2 h2 ha
        · exact hpair 3 h3 ha

private theorem allowed_path_zeroFresh {N g p q : ℕ} {Q : ℝ} {r : Request}
    {es : List (Edge N)} (hp : p.Prime) (hq : ChenPrimeRough (p : ℝ) q)
    (hc : Coherent N Q r) (hceil : r.node.physical.ceiling ≤ physicalPrime N p)
    (hs : ChosenPath N Q g r es) (ha : ∀ e ∈ es, Allowed q.primeFactors e) :
    es.all zeroFreshEdge = true := by
  induction es generalizing g r with
  | nil => rfl
  | cons e es ih =>
      cases g with
      | zero => exact False.elim hs
      | succ g =>
          have he := allowed_child_zeroFresh hc hp hq hceil hs.1 (ha e (List.mem_cons_self ..))
          have hn : (nextRequest r e).node.physical.ceiling ≤ physicalPrime N p :=
            (perform_ceiling (child_admission hc hs.1).2.1).trans hceil
          have ht := ih (child_coherent hc hs.1) hn hs.2
            (fun d hd => ha d (List.mem_cons_of_mem _ hd))
          simp only [List.all_cons,he,ht,Bool.and_self]

/-- Each q has its actual mark at every fixed/retained position, and
zero at every position with a fresh prime. The reverse implication
uses the cutoff at the current request, including changed fixed reads. -/
theorem noPost_receiptPoint {N n m p q : ℕ} {k : Root} {τ z0 : ℝ}
    {c : RootKey n m} {o : Occurrence N}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p ∈ rootFibre N n m k τ c) (hq : q ∈ noPostFibre N z0 p)
    (ho : o ∈ rootHistory N n k τ p) :
    receiptPoint (cellQ N n c.1) q o = occurrenceBudget o := by
  obtain ⟨_,horig,hrough⟩ := mem_noPostFibre.mp hq
  have hb := (Finset.mem_filter.mp hp).1
  have hpr := original_band_prime hb
  have hc := root_coherent (by omega : 1 < N) hτ hτ' hn hpr (original_band_geometry hN hb)
  have iffPath : (tailProduct o ∣ q ∧
      ChenPrimeRough (memberCutoff (cellQ N n c.1) o) (q / tailProduct o)) ↔
      o.path.all zeroFreshEdge = true := by
    constructor
    · rintro ⟨hD,_⟩
      exact allowed_path_zeroFresh hpr.1 hrough hc le_rfl (history_facts ho).1
        (original_receipt_allows_path hN hτ hτ' hn hp ho horig hD)
    · intro hz
      have hw := zeroFresh_original_word ho hz
      have hD : tailProduct o = 1 := by simp [tailProduct,hw]
      have hr := (history_integer_roughness hN hτ hτ' hn hb ho).1
      change ChenPrimeRough (memberCutoff (rootQ N n k τ p) o) (parentProduct o.current.old) at hr
      rw [← (original_fibre_geometry hN hτ hτ' hn hp).1] at hr
      have hcut := hr p hpr.1 (by simp [hw,parentProduct])
      rw [hD,Nat.div_one]
      exact ⟨one_dvd _,fun u hu hd => hcut.trans (hrough u hu hd)⟩
  unfold receiptPoint occurrenceBudget
  rw [iffPath]

/-- The actual list index and its tag/root-key-specific physical Q. -/
theorem noPost_at_position {N n m p q : ℕ} {k : Root} {τ z0 : ℝ}
    {c : RootKey n m} (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k τ c)
    (hq : q ∈ noPostFibre N z0 p)
    (i : Fin (rootHistory N n k τ p).length) :
    let o := (rootHistory N n k τ p).get i
    (N : ℝ)^o.current.node.physical.total = cellQ N n c.1 ∧
      receiptPoint (cellQ N n c.1) q o = occurrenceBudget o := by
  dsimp only
  have ho : (rootHistory N n k τ p).get i ∈ rootHistory N n k τ p := List.get_mem _ _
  exact ⟨(rootHistory_sameQ ho).trans (original_fibre_geometry hN hτ hτ' hn hp).1.symm,
    noPost_receiptPoint hN hτ hτ' hn hp hq ho⟩

private theorem sum_occurrenceBudget {N : ℕ} (os : List (Occurrence N)) :
    (os.map occurrenceBudget).sum = listBudget os := by
  induction os with
  | nil => rfl
  | cons o os ih => simp only [List.map_cons,List.sum_cons,listBudget,ih]

/-- Incidence counts every emitted position separately for this same q. -/
theorem noPost_incidence_exact {N n m p q : ℕ} {k : Root} {τ z0 : ℝ}
    {c : RootKey n m} (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k τ c)
    (hq : q ∈ noPostFibre N z0 p) :
    receiptIncidence (cellQ N n c.1) q (rootHistory N n k τ p) =
      listBudget (rootHistory N n k τ p) := by
  unfold receiptIncidence
  rw [← sum_occurrenceBudget]
  apply congrArg List.sum
  apply List.map_congr_left
  exact fun o ho => noPost_receiptPoint hN hτ hτ' hn hp hq ho

def noPostAtOrigin (N n m : ℕ) (k : Root) (τ z0 : ℝ) (p : ℕ) : ℝ :=
  ∑ q ∈ noPostFibre N z0 p,
    receiptPoint (cellQ N n (keyAt N n m k τ p).1) q
      (origin (N := N) 430 (rootRequest N n k τ p))

private theorem noPost_origin_card {N n m p : ℕ} {k : Root} {τ z0 : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p ∈ originalBand N k) :
    noPostAtOrigin N n m k τ z0 p = ((noPostFibre N z0 p).card : ℝ) := by
  have hf : p ∈ rootFibre N n m k τ (keyAt N n m k τ p) := Finset.mem_filter.mpr ⟨hp,rfl⟩
  have ho : origin 430 (rootRequest N n k τ p) ∈ rootHistory N n k τ p := List.mem_cons_self
  unfold noPostAtOrigin
  calc
    _ = ∑ q ∈ noPostFibre N z0 p, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (noPost_receiptPoint hN hτ hτ' hn hf hq ho).trans
        (occurrenceBudget_origin (N := N) 430 (rootRequest N n k τ p))
    _ = _ := by simp

/-- The p-rough part of the literal cutoff-blocked R4 entry is counted once
per original q at the first actual PATH position, for each tag separately. -/
theorem cutoff_noPost_source_at_origins (N n m : ℕ) (τ z0 : ℝ)
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    (∑ z ∈ rootCutoffBlocked (originalTagged N) z0,
      if ¬ hasPostRootPrimeFactor z then (1 : ℝ) else 0) =
      (∑ p ∈ originalBand N .U3, noPostAtOrigin N n m .U3 τ z0 p) +
       ∑ p ∈ originalBand N .U4, noPostAtOrigin N n m .U4 τ z0 p := by
  have hsum (k : Root) :
      (∑ p ∈ originalCutoffRoots N k z0, ∑ q ∈ originalReceiver N p,
        if ChenPrimeRough (p:ℝ) q then (1:ℝ) else 0) =
      ∑ p ∈ originalBand N k, noPostAtOrigin N n m k τ z0 p := by
    rw [originalCutoffRoots,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    rw [noPost_origin_card hN hτ hτ' hn hp]
    by_cases hs : (p : ℝ) < z0
    · simp [noPostFibre,hs]
    · simp only [noPostFibre,if_pos hs,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [original_selected_cutoff_signed]
  simp_rw [no_post_iff_rough]
  exact congrArg₂ (·+·) (hsum .U3) (hsum .U4)

/-- At the manuscript presieve the whole original R4 lies at the root
cutoff. The remaining q with a prime strictly below p stay in the bill. -/
theorem manuscript_outside_noPost_split {N cap n m p : ℕ} {k : Root} {τ z0 : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p ∈ originalBand N k)
    (hz : z0 ≤ cutoff (rootQ N n k τ p) p (frozenRoot n k τ (physicalPrime N p)).physical.argument)
    (hcap : z0 ≤ (cap : ℝ)) (lower : Bool) :
    outsideRejectedUnits N cap n τ z0 lower =
      ((∑ p ∈ originalBand N .U3, noPostAtOrigin N n m .U3 τ z0 p) +
        ∑ p ∈ originalBand N .U4, noPostAtOrigin N n m .U4 τ z0 p) +
      ∑ z ∈ rootCutoffBlocked (originalTagged N) z0,
        if hasPostRootPrimeFactor z then (1 : ℝ) else 0 := by
  have h := full_tagged_fin_at_manuscript_presieve hN hτ hτ' hn hp hz hcap lower
  rw [← cutoff_noPost_source_at_origins N n m τ z0 hN hτ hτ' hn,
    ← Finset.sum_add_distrib,h.2.1]
  unfold outsideRejectedUnits
  rw [h.2.2 (fun _ => (1 : ℝ))]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hfac : hasPostRootPrimeFactor z <;> simp [hfac]

def noPostHistoryCharge (N n m : ℕ) (k : Root) (τ z0 : ℝ)
    (c : RootKey n m) (p : ℕ) : ℝ :=
  ∑ q ∈ noPostFibre N z0 p,
    receiptIncidence (cellQ N n c.1) q (rootHistory N n k τ p)

theorem noPost_history_charge_exact {N n m p : ℕ} {k : Root} {τ z0 : ℝ}
    {c : RootKey n m} (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k τ c) :
    noPostHistoryCharge N n m k τ z0 c p =
      ((noPostFibre N z0 p).card : ℝ) * listBudget (rootHistory N n k τ p) := by
  unfold noPostHistoryCharge
  calc
    _ = ∑ q ∈ noPostFibre N z0 p, listBudget (rootHistory N n k τ p) :=
      Finset.sum_congr rfl (fun q hq => noPost_incidence_exact hN hτ hτ' hn hp hq)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

theorem noPost_history_charge_le {N n m p : ℕ} {k : Root} {τ z0 : ℝ}
    {c : RootKey n m} (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k τ c) :
    noPostHistoryCharge N n m k τ z0 c p ≤ 431 * ((noPostFibre N z0 p).card : ℝ) := by
  rw [noPost_history_charge_exact hN hτ hτ' hn hp,mul_comm (431 : ℝ)]
  exact mul_le_mul_of_nonneg_left (zeroFresh_rootHistory_budget N n k τ p) (Nat.cast_nonneg _)

/-- Classical U3 only. The complement of this exact lane stays on
the original root-card account. The history coefficient 431 includes
the origin and all 430 possible feedback levels. -/
theorem classical_noPost_history_paid {τ ε : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1/12)
    (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ z0 : ℝ,
      (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        noPostHistoryCharge N n m .U3 τ z0 c p) ≤
      431 * ((1+ε)*classicalOwnTheta N n m τ -
        ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
          (((originalReceiver N p) \ noPostFibre N z0 p).card : ℝ)) := by
  filter_upwards [classical_original_card_bound hτ hτ' he, eventually_ge_atTop (2:ℕ)] with N hd hN
  intro hEven n m hn z0
  have hsum : (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
      (noPostHistoryCharge N n m .U3 τ z0 c p +
        431 * (((originalReceiver N p) \ noPostFibre N z0 p).card : ℝ))) ≤
      ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        431 * ((originalReceiver N p).card : ℝ) := by
    apply Finset.sum_le_sum
    intro c _
    apply Finset.sum_le_sum
    intro p hp
    let S := noPostFibre N z0 p
    have hsub : S ⊆ originalReceiver N p := fun _ h => (mem_noPostFibre.mp h).2.1
    have hcard : (((originalReceiver N p) \ S).card : ℝ) + (S.card : ℝ) =
        ((originalReceiver N p).card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
    have hcoef : noPostHistoryCharge N n m .U3 τ z0 c p ≤ 431 * (S.card : ℝ) :=
      noPost_history_charge_le hN hτ.le hτ' hn (classicalFibre_subset_rootFibre c hp)
    change noPostHistoryCharge N n m .U3 τ z0 c p +
      431 * (((originalReceiver N p) \ S).card : ℝ) ≤ _
    linarith only [hcoef,hcard]
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  rw [sum_classicalFibre N n m τ (fun p => ((originalReceiver N p).card : ℝ))] at hsum
  rw [classicalOwnTheta_eq hN hτ.le hτ' hn]
  linarith only [hsum,hd hEven n hn]

end
end ImbalancedChen.Part5OriginalH430NoPostRootReceiptPositions
