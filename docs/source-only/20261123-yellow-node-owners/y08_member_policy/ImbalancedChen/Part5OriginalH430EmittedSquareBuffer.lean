import ImbalancedChen.Part5OriginalH430AllLaneMemberQuery
import ImbalancedChen.Part5OriginalH430SquareStripPrimeMass
import ImbalancedChen.Part5OriginalH430EmittedWordBox

/-! Both square lists at a U3/U4 Member have the same chronological tests after
the first selected root. One width therefore suffices. The removed ordered prime
words are charged with their actual emitted marks and their own physical theta.
The scale of the bound here is the manuscript's absolute H_N. -/
namespace ImbalancedChen.Part5OriginalH430EmittedSquareBuffer

noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization (thetaAtom)
open Wu2008DoubleSieve
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430IntegerItineraries
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RootSourceDictionary Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430SameQHistoryCells
open Part5OriginalH430EnhancedPhysicalGrid Part5OriginalH430OwnedPrimeBoxWeight
open Part5OriginalH430EmittedWordBox Part5OriginalH430SquareStripPrimeMass

private theorem consecutive (nu T : ℝ) {r : ℕ} (x : Fin r → ℝ) :
    SquareGates nu T (List.ofFn x) ↔ ∀ i, T + prefix x i + 2*x i ≤ nu := by
  induction r generalizing T with
  | zero => simp [SquareGates]
  | succ r ih =>
    rw [List.ofFn_succ,SquareGates,ih,Fin.forall_fin_succ]
    have hz : prefix x 0 = 0 := by simp [prefix]
    have hs (i : Fin r) : prefix x i.succ = x 0 + prefix (fun j => x j.succ) i := by
      unfold prefix
      simp only [Finset.sum_filter]
      rw [Fin.sum_univ_succ]
      simp
    simp only [hs,hz,add_zero,add_assoc]

private theorem remaining_if_unselected (xs : List Slot) (h : selectedWord xs = []) :
    remainingWord xs = xs.map Slot.exponent := by
  induction xs with
  | nil => rfl
  | cons u xs ih =>
    cases hs : u.selected with
    | true => simp [selectedWord,hs] at h
    | false =>
      have ht : selectedWord xs = [] := by simpa [selectedWord,hs] using h
      simp [remainingWord,hs,ih ht]

/-- The selected-complement square starts *after* the actual selected root,
on the unchanged chronological suffix. This also covers a word of length one. -/
theorem remaining_is_tail {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (ho : o ∈ rootHistory N n k t p) :
    word o.current.node.physical =
      physicalPrime N p :: remainingWord o.current.node.physical.slots := by
  have hpre := replay_slots_prefix (rootRequest N n k t p) o.path
  rw [← (history_facts ho).2.2] at hpre
  obtain ⟨xs,hxs⟩ := hpre
  change o.current.node.physical.slots = ⟨physicalPrime N p,true⟩ :: xs at hxs
  have hs := rootHistory_selected_root ho
  rw [hxs] at hs
  have ht : selectedWord xs = [] := by simpa [selectedWord] using hs
  simp [word,hxs,remainingWord,remaining_if_unselected xs ht]

/-- The good part uses the original physical total minus the preselected width in
each square *test*. Its arithmetic Q, old word and resolver are unchanged. -/
theorem emitted_two_square_buffers {N n m r p : ℕ} {k : Root} {t : ℝ}
    {o : Occurrence N} {v : Fin (r+1) → ℕ} (j : ℕ)
    (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p ∈ originalBand N k) (ho : o ∈ rootHistory N n k t p)
    (he : rootSource k (physicalPrime N p) = .enhanced)
    (hv : List.ofFn v = o.current.old)
    (good : ¬thin n j (actualPrimeTupleLog N v)) :
    let z := o.current.node.physical
    SquareGates (z.total - width j) 0 (word z) ∧
    SquareGates (z.total - width j) (selectedWord z.slots).sum (remainingWord z.slots) := by
  dsimp only
  let x := actualPrimeTupleLog N v
  let z := o.current.node.physical
  let c := keyAt N n m k t p
  have hf : p ∈ rootFibre N n m k t c := Finset.mem_filter.mpr ⟨hp,rfl⟩
  have htotal : codeLevel n c.1 = z.total := by
    apply (Real.strictMono_rpow_of_base_gt_one (by exact_mod_cast (show 1<N by omega) : (1:ℝ)<N)).injective
    exact (original_fibre_geometry hN ht hu (precision_error hn) hf).1.trans (rootHistory_sameQ ho).symm
  have hword : word z = List.ofFn x := by
    rw [show word z = o.current.old.map (physicalPrime N) from rootHistory_integer_word ho,←hv]
    simp [List.map_ofFn,x,actualPrimeTupleLog,physicalPrime,Function.comp_def]
  have hfull : SquareGates z.total 0 (List.ofFn x) := by
    rw [←hword]
    exact (enhanced_history_physical_gates hn hN ht hu hp he ho).1
  have hmargin : SquareGates (z.total-width j) 0 (word z) := by
    rw [hword,consecutive]
    intro i
    have hs := (consecutive z.total 0 x).mp hfull i
    have hw : ¬ |wall (c.1,i) x| ≤ width j := fun h => good ⟨(c.1,i),h⟩
    have hneg : wall (c.1,i) x ≤ 0 := by
      change prefix x i + 2*x i - codeLevel n c.1 ≤ 0
      rw [htotal]
      linarith
    rw [abs_of_nonpos hneg] at hw
    change ¬ -(prefix x i + 2*x i - codeLevel n c.1) ≤ width j at hw
    rw [htotal] at hw
    linarith
  refine ⟨hmargin,?_⟩
  rw [rootHistory_selected_root ho]
  rw [remaining_is_tail ho] at hmargin
  simpa only [List.sum_cons,List.sum_nil,add_zero,zero_add] using hmargin.2

private theorem wordMark_nonneg {N : ℕ} (ss : List StepShape) (w : List ℕ)
    (os : List (Occurrence N)) : 0 ≤ selectedWordMark ss w os := by
  induction os with
  | nil => exact le_rfl
  | cons o os ih =>
    unfold selectedWordMark
    split_ifs <;> first | exact add_nonneg (mark_pos o).le ih | simpa using ih

private theorem wordMark_empty {N : ℕ} (ss : List StepShape) (w : List ℕ)
    (os : List (Occurrence N)) (h : ∀ o ∈ os, o.current.old ≠ w) :
    selectedWordMark ss w os = 0 := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    rw [selectedWordMark,if_neg (fun h' => h o (List.mem_cons_self ..) h'.2),zero_add]
    exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- True path marks for a fixed chronological shape and word; summing them
retains all repeated positions. Its normalizer uses this root's own cellQ. -/
def thetaCharge {r : ℕ} (N n m : ℕ) (k : Root) (t : ℝ) (ss : List StepShape)
    (v : Fin (r+1) → ℕ) : ℝ :=
  if v 0 ∈ originalBand N k then
    selectedWordMark ss (List.ofFn v) (rootHistory N n k t (v 0)) *
      |thetaAtom N (cellQ N n (keyAt N n m k t (v 0)).1) (List.ofFn v).prod /
        singularNormalization N|
  else 0

private theorem point_price {r N n m : ℕ} (k : Root) {t : ℝ} (ss : List StepShape)
    {a : ℝ} {v : Fin (r+1) → ℕ} (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hv : v ∈ actualPrimeBoxTuples N (fun _ => a) (fun _ => 1)) :
    thetaCharge N n m k t ss v ≤ emittedTerm N n m k t ss v +
      (4/frozenResidualFloor) * (∏ i, 1/((v i:ℝ)-1)) := by
  let p := v 0
  let w := List.ofFn v
  let c := keyAt N n m k t p
  let Q := cellQ N n c.1
  let L := physicalLevel N Q w
  let M := selectedWordMark ss w (rootHistory N n k t p)
  let A := thetaAtom N Q w.prod / singularNormalization N
  let H := primeBoxWord w
  have hM : 0 ≤ M := wordMark_nonneg _ _ _
  have hM' : M ≤ 1 := (le_abs_self M).trans (actual_shape_word_mark k t p ss w)
  have heq : H = ∏ i, 1/((v i:ℝ)-1) := primeBoxWord_ofFn v
  have hH : 0≤H := (actualPrimeBoxWeight_nonneg hv).trans_eq heq.symm
  have floor := frozenResidualFloor_pos
  by_cases hp : p ∈ originalBand N k
  · change (if p ∈ originalBand N k then M*|A| else 0) ≤
      (if p ∈ originalBand N k then M*|A-4/L*H| else 0) + _
    rw [if_pos hp,if_pos hp,←heq]
    by_cases hw : ∃ o ∈ rootHistory N n k t p, o.current.old = w
    · obtain ⟨o,ho,how⟩ := hw
      have hf : p ∈ rootFibre N n m k t c := Finset.mem_filter.mpr ⟨hp,rfl⟩
      have hQ := (original_fibre_geometry hN ht hu hn hf).1
      have hL : frozenResidualFloor ≤ L := by
        dsimp only [L,Q]
        rw [hQ,←how]
        exact (rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp)
          (original_band_geometry hN hp) ho).2.2.1
      have hl := floor.trans_le hL
      have hb := mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤4) hl.le) hH
      have ha := abs_sub_le A (4/L*H) 0
      simp only [sub_zero,abs_of_nonneg hb] at ha
      have h1 := mul_le_mul_of_nonneg_left ha hM
      have h2 := (mul_le_mul_of_nonneg_right hM' hb).trans_eq (one_mul _)
      have h3 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) floor hL) hH
      rw [mul_add] at h1
      exact h1.trans (add_le_add_left (h2.trans h3) _)
    · have h0 : M = 0 := wordMark_empty _ _ _ (fun o ho he => hw ⟨o,ho,he⟩)
      rw [h0,zero_mul,zero_mul,zero_add]
      exact mul_nonneg (div_nonneg (by norm_num) floor.le) hH
  · simp only [thetaCharge,emittedTerm,show v 0 ∉ originalBand N k from hp,if_false,zero_add]
    exact mul_nonneg (div_nonneg (by norm_num) floor.le) (actualPrimeBoxWeight_nonneg hv)

def removed {r : ℕ} (N n m j : ℕ) (a : ℝ) (k : Root) (t : ℝ) (ss : List StepShape) :
    ℝ :=
  ∑ v ∈ actualPrimeBoxTuples N (fun _ : Fin (r+1) => a) (fun _ => 1),
    if thin n j (actualPrimeTupleLog N v) then thetaCharge N n m k t ss v else 0

/-- First fix the original level mesh n and the positive word floor a.
The same width then works for both roots, every allowed tau, every query mesh,
every original path of the given rank and its entire emitted multiplicity. -/
theorem square_strip_theta {r : ℕ} (n : ℕ) (hn : 111≤n)
    {a eps : ℝ} (ha : 0<a) (hb : a<1) (he : 0<eps) :
    ∀ᶠ j : ℕ in atTop, ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (m : ℕ) (k : Root) (t : ℝ), 0≤t → t≤1/12 → ∀ ss : List StepShape,
        removed (r:=r) N n m j a k t ss < eps := by
  let C : ℝ := 4/frozenResidualFloor
  have hC : 0<C := div_pos (by norm_num) frozenResidualFloor_pos
  let lo := fun _ : Fin (r+1) => a
  let hi := fun _ : Fin (r+1) => (1:ℝ)
  obtain ⟨T,hT⟩ := uniform_emitted_box lo hi (fun _ => ha) (fun _ => hb) (half_pos he)
  filter_upwards [prime_square_strip (r+1) n ha hb (div_pos (half_pos he) hC)] with j hj
  filter_upwards [hj,eventually_ge_atTop T,eventually_ge_atTop (2:ℕ)] with N hS hNT hN
  intro hE m k t ht hu ss
  let test := fun v : Fin (r+1) → ℕ => if thin n j (actualPrimeTupleLog N v) then (1:ℝ) else 0
  have htest v : |test v| ≤ 1 := by unfold test; split_ifs <;> norm_num
  have hbudget := hT N hNT hE n m k t ht hu (precision_error hn) ss test (fun v _ => htest v)
  have hid : removed (r:=r) N n m j a k t ss ≤
      (∑ v ∈ actualPrimeBoxTuples N lo hi, |test v|*emittedTerm N n m k t ss v) +
      C * stripMass (r+1) n j N a := by
    unfold removed stripMass actualPrimeBoxTestSum
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v hv
    by_cases ht' : thin n j (actualPrimeTupleLog N v)
    · simpa only [C,test,if_pos ht',abs_one,one_mul,mul_one] using
        point_price (n:=n) (m:=m) k ss hN ht hu (precision_error hn) hv
    · simp [test,ht']
  have hcost : C * stripMass (r+1) n j N a < eps/2 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hC).mp hS
  linarith only [hid,hbudget,hcost]

/-- Rank 1..881 covers the manuscript's 440-step horizon. All ranks and
all their chronological tests use a single width and arithmetic threshold. -/
theorem all_rank_square_strip_theta (n : ℕ) (hn : 111≤n)
    {a eps : ℝ} (ha : 0<a) (hb : a<1) (he : 0<eps) :
    ∀ᶠ j : ℕ in atTop, ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r : Fin 881) (m : ℕ) (k : Root) (t : ℝ), 0≤t → t≤1/12 →
      ∀ ss : List StepShape, removed (r:=r.val) N n m j a k t ss < eps := by
  have H (r : Fin 881) := square_strip_theta (r:=r.val) n hn ha hb he
  filter_upwards [Filter.eventually_all.mpr H] with j hj
  filter_upwards [Filter.eventually_all.mpr hj] with N hN
  exact fun he r => hN r he

def letterFloor : ℝ := min (1/2) frozenLeafCutoffFloor

theorem word_in_paid_box {N n r p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    {v : Fin (r+1) → ℕ} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p ∈ originalBand N k) (ho : o ∈ rootHistory N n k t p)
    (hv : List.ofFn v = o.current.old) :
    v ∈ actualPrimeBoxTuples N (fun _ => letterFloor) (fun _ => 1) := by
  have hd := precision_error hn
  have hs := (rootHistory_support (by omega : 1<N) ht hu hd (original_band_prime hp)
    (original_band_geometry hN hp) ho).1
  have hco := rootHistory_coherent (by omega : 1<N) ht hu hd (original_band_prime hp)
    (original_band_geometry hN hp) ho
  have hrough := Part5OriginalH430HistoryQuotientCounts.history_integer_roughness hN ht hu hd hp ho
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  have hm : v i ∈ o.current.old := hv ▸ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hq := hco.letters _ hm
  have hdiv : v i ∣ parentProduct o.current.old := List.dvd_prod hm
  have hpf := (Nat.mem_primeFactors_of_ne_zero hs.2.1.ne').mpr ⟨hq.1,hdiv⟩
  have hup : (v i : ℝ) < N := by
    have hh : (v i : ℝ) ≤ parentProduct o.current.old :=
      Nat.cast_le.mpr (Nat.le_of_dvd hs.2.1 hdiv)
    exact hh.trans_lt (hs.2.2.1.trans_le hs.2.2.2.1)
  refine ⟨hq.1,hq.1.coprime_iff_not_dvd.mp hq.2,?_,by simpa using hup⟩
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
    (min_le_right _ _)).trans (hrough.2.2.1 _ hpf)

abbrev PathShape := (d : Fin 431) × (Fin d.val → StepShape)
abbrev Scope := Root × PathShape × Fin 881

/-- Aggregate absolute wall mass, including both overlapping root tags and every
possible chronological shape through depth 430. A zero or varying owner mask can
only decrease this positive sum. The cutoff floor contains every actual word. -/
theorem entire_emitted_square_strip (n : ℕ) (hn : 111 ≤ n) {eps : ℝ} (he : 0 < eps) :
    ∀ᶠ j : ℕ in atTop, ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (m : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1/12 →
        (∑ b : Scope, removed (r:=b.2.2.val) N n m j letterFloor b.1 t
          (List.ofFn b.2.1.2)) < eps := by
  let M : ℝ := Fintype.card Scope
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hD : 0 < M+1 := by linarith
  let share := eps/(M+1)
  have hshare : 0 < share := div_pos he hD
  have hlo : 0 < letterFloor := lt_min (by norm_num) frozenLeafCutoffFloor_pos
  have hhi : letterFloor < 1 := (min_le_left _ _).trans_lt (by norm_num)
  filter_upwards [all_rank_square_strip_theta n hn hlo hhi hshare] with j hj
  filter_upwards [hj] with N hN
  intro hE m t ht hu
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (b : Scope) _ =>
    (hN hE b.2.2 m b.1 t ht hu (List.ofFn b.2.1.2)).le)
  have hval : (∑ _b : Scope, share) = M*share := by simp [M]
  rw [hval] at hsum
  apply hsum.trans_lt
  have heq : share*(M+1) = eps := div_mul_cancel₀ eps hD.ne'
  nlinarith only [hshare,heq]

end
end ImbalancedChen.Part5OriginalH430EmittedSquareBuffer
