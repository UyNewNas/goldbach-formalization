import ImbalancedChen.Part5OriginalH430RootTentScreen

/-! A single collar index is used by the counted descendants, both tagged
root prices, all chronological shapes and all own-theta word charges. -/
namespace ImbalancedChen.Part5OriginalH430RootTentOwnTheta
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430RootTentScreen Part5OriginalH430EmittedSquareBuffer
open Part5OriginalH430EmittedWordBox
open Part5OriginalH430SquareStripPrimeMass (width width_pos)
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430EnhancedPhysicalGrid
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SelectedBankCarrierSupply
open Part5OriginalH430OwnedRootCounts Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedPrimeBoxWeight
open Part5OriginalH430OwnedThetaWord Part5OriginalH430AbsoluteWordBox
open Part5OriginalH430OwnedMemberMass Part5OriginalH430SharpPrimeBox

/-- Original path position, including identical repeated integer words.
The weight can distinguish the actual owner, generation or action. -/
def weighted {N : ℕ} (ss : List StepShape) (w : List ℕ) (f : Occurrence N→ℝ) :
    List (Occurrence N)→ℝ
  | [] => 0
  | o::os => (if o.path.map edgeShape=ss ∧ o.current.old=w then mark o*f o else 0)+weighted ss w f os

private theorem weighted_bound {N : ℕ} (ss : List StepShape) (w : List ℕ)
    (f : Occurrence N→ℝ) (hf : ∀ o, |f o|≤1) (os : List (Occurrence N)) :
    |weighted ss w f os| ≤ selectedWordMark ss w os := by
  induction os with
  | nil => simp [weighted,selectedWordMark]
  | cons o os ih =>
    rw [weighted,selectedWordMark]
    split_ifs with h
    · apply (abs_add_le ..).trans (add_le_add _ ih)
      rw [abs_mul,abs_of_pos (mark_pos o)]
      exact (mul_le_mul_of_nonneg_left (hf o) (mark_pos o).le).trans_eq (mul_one _)
    · simpa only [zero_add] using ih

private theorem no_word {N : ℕ} (ss : List StepShape) (w : List ℕ) (f : Occurrence N→ℝ)
    (os : List (Occurrence N)) (h : ∀ o∈os,o.current.old≠w) : weighted ss w f os=0 := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    rw [weighted,if_neg (fun hm => h o (List.mem_cons_self ..) hm.2),zero_add]
    exact ih (fun u hu => h u (List.mem_cons_of_mem _ hu))

def wordCharge {r : ℕ} (N n m : ℕ) (k : Root) (t : ℝ) (ss : List StepShape)
    (f : Occurrence N→ℝ) (v : Fin (r+1)→ℕ) : ℝ :=
  if v 0∈originalBand N k then
    |weighted ss (List.ofFn v) f (rootHistory N n k t (v 0)) *
      (thetaAtom N (cellQ N n (keyAt N n m k t (v 0)).1) (List.ofFn v).prod / singularNormalization N)|
  else 0

/-- The constant mask returns the prior chronological theta charge
exactly, including its true coefficient at every emitted integer word. -/
theorem unmasked_eq {r : ℕ} (N n m : ℕ) (k : Root) (t : ℝ) (ss : List StepShape) (v : Fin (r+1)→ℕ) :
    wordCharge N n m k t ss (fun _ => 1) v = thetaCharge N n m k t ss v := by
  have H (os : List (Occurrence N)) : weighted ss (List.ofFn v) (fun _=>1) os = selectedWordMark ss (List.ofFn v) os := by
    induction os with
    | nil => rfl
    | cons o os ih => simp only [weighted,selectedWordMark,mul_one,ih]
  unfold wordCharge thetaCharge
  split_ifs
  · rw [abs_mul,H,abs_of_nonneg]
    exact (abs_nonneg _).trans (weighted_bound ss (List.ofFn v) (fun _=>1) (fun _=>by norm_num) _)
  · rfl

private def rate : ℝ := 1+4/frozenResidualFloor

private theorem rate_pos : 0<rate := add_pos zero_lt_one (div_pos (by norm_num) frozenResidualFloor_pos)

private theorem point {r N n m : ℕ} {k : Root} {t : ℝ} (ss : List StepShape) (f : Occurrence N→ℝ)
    (hN : 2≤N) (hev : Even N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hA : 4≤primeFloor N) (hprice : price N≤1) (hf : ∀ o, |f o|≤1) {v : Fin (r+1)→ℕ}
    (hv : v ∈ actualPrimeBoxTuples N (fun _ => letterFloor) (fun _ => 1)) :
    wordCharge N n m k t ss f v ≤ rate*atomWeight v := by
  let p := v 0
  let w := List.ofFn v
  let c := keyAt N n m k t p
  let os := rootHistory N n k t p
  have hpos : 0≤atomWeight v := actualPrimeBoxWeight_nonneg hv
  have hr := mul_nonneg rate_pos.le hpos
  by_cases hb : p∈originalBand N k
  · rw [wordCharge,if_pos hb,abs_mul]
    by_cases hm : ∃ o∈os,o.current.old=w
    · obtain ⟨o,ho,how⟩ := hm
      obtain ⟨u,hu',huw⟩ := emitted_owned_word (m:=m) 0 hN ht hu (precision_error hn) hb ho
      have hL := (owned_support hN ht hu (precision_error hn) hu').2.2.1.1
      have H := owned_primeBox_price hN hev ht hu (precision_error hn) hA hu'
      change |thetaAtom N (cellQ N n c.1) (labelWord u).prod / singularNormalization N -
        (4/Lkey c u)*primeBoxWord (labelWord u)| ≤ price N * primeBoxWord (labelWord u) at H
      have hw : labelWord u=List.ofFn v := huw.trans how
      rw [hw,primeBoxWord_ofFn] at H
      let A := thetaAtom N (cellQ N n c.1) (List.ofFn v).prod / singularNormalization N
      let b := (4/Lkey c u)*atomWeight v
      have hb0 : 0≤b := mul_nonneg (div_nonneg (by norm_num) (frozenResidualFloor_pos.trans_le hL).le) hpos
      have HH : |A-b| ≤ price N * atomWeight v := H
      have hA' : |A| ≤ rate*atomWeight v := by
        calc
          |A| ≤ |A-b|+|b| := by simpa only [sub_zero] using abs_sub_le A b 0
          _ ≤ price N*atomWeight v + b := by rw [abs_of_nonneg hb0]; exact add_le_add_right HH _
          _ ≤ _ := by
            rw [show b=(4/Lkey c u)*atomWeight v from rfl,←add_mul]
            exact mul_le_mul_of_nonneg_right (add_le_add hprice
              (div_le_div_of_nonneg_left (by norm_num) frozenResidualFloor_pos hL)) hpos
      have hM := (weighted_bound ss w f hf os).trans ((le_abs_self _).trans (actual_shape_word_mark k t p ss w))
      exact ((mul_le_mul_of_nonneg_right hM (abs_nonneg A)).trans_eq (one_mul _)).trans hA'
    · have hz := no_word ss w f os (fun o ho h => hm ⟨o,ho,h⟩)
      rw [show weighted ss (List.ofFn v) f (rootHistory N n k t (v 0))=0 from hz,abs_zero,zero_mul]
      exact hr
  · simpa only [wordCharge,if_neg hb] using hr

def removed {r : ℕ} (N n m : ℕ) (k : Root) (t : ℝ) (ss : List StepShape)
    (f : Occurrence N→ℝ) : ℝ :=
  ∑ v ∈ actualPrimeBoxTuples N (fun _ : Fin (r+1) => letterFloor) (fun _ => 1),
    if collar n (collarIndex n) (actualPrimeTupleLog N v 0) then wordCharge N n m k t ss f v else 0

/-- Total normalized removed own-theta, including both roots, every
chronological length and shape, with masks and assignments chosen after N.
The root screen is the very same one as for the additive-prime estimate. -/
theorem entire_tent_ownTheta {eps : ℝ} (he : 0<eps) :
    ∃ T : ℕ, ∀ n≥T, ∃ N₀ : ℕ, ∀ N≥N₀, Even N →
      ∀ (m : ℕ) (t : ℝ), 0≤t → t≤1/12 → ∀ f : Scope→Occurrence N→ℝ, (∀ s o, |f s o|≤1) →
      (∑ s : Scope, removed (r:=s.2.2.val) N n m s.1 t (List.ofFn s.2.1.2) (f s))<eps := by
  let M : ℝ := Fintype.card Scope
  have hM : 0≤M := Nat.cast_nonneg _
  have hD : 0<(M+1)*rate := mul_pos (by linarith) rate_pos
  have hw : Tendsto width atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply eventually_atTop.1
  filter_upwards [hw.eventually (eventually_lt_nhds (div_pos he hD)),eventually_ge_atTop (111:ℕ)] with n hsmall hn
  apply eventually_atTop.1
  filter_upwards [all_word_mass n,eventually_ge_atTop (2:ℕ),primeFloor_tendsto.eventually_ge_atTop 4,
    price_tendsto.eventually_le_const (by norm_num : (0:ℝ)<1)] with N hbox hN hA hprice
  intro hev m t ht hu f hf
  have each (s : Scope) : removed (r:=s.2.2.val) N n m s.1 t (List.ofFn s.2.1.2) (f s) ≤ rate*width n := by
    apply le_trans _ (mul_le_mul_of_nonneg_left (hbox s.2.2).le rate_pos.le)
    unfold removed badMass actualPrimeBoxTestSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    by_cases hh : collar n (collarIndex n) (actualPrimeTupleLog N v 0)
    · simpa only [if_pos hh,Set.indicator_of_mem hh,mul_one,atomWeight] using
        point (List.ofFn s.2.1.2) (f s) hN hev hn ht hu hA hprice (hf s) hv
    · simp only [if_neg hh,Set.indicator_of_notMem hh,mul_zero,le_refl]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (s : Scope) _ => each s)
  have hcard : (∑ _s : Scope,rate*width n)=M*(rate*width n) := by simp [M]
  rw [hcard] at hsum
  apply hsum.trans_lt
  have hsmall' := (lt_div_iff₀ hD).mp hsmall
  have hpos := mul_pos rate_pos (width_pos n)
  nlinarith only [hsmall',hpos]

end
end ImbalancedChen.Part5OriginalH430RootTentOwnTheta
