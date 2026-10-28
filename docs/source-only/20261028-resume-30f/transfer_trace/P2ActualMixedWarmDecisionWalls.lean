import ImbalancedChen.P2ActualWarmDecisionDivergence
import ImbalancedChen.P2ActualLowerCanonicalWallDensity

/-!
# Actual mixed warm decisions meet coarse or frozen-admission walls

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is a constructive first-disagreement cover for the actual computed
run, not an input coverage hypothesis. It retains its true frozen parent.
Coarse walls are literal logarithmic mesh boundaries, including the top
singleton. Admissions are the original full even-rank cubes. The present
file does not replace their varying actual cap/root offsets by a fixed
pre-N finite arithmetic wall catalogue, nor claim full-W adoption.
-/

namespace ImbalancedChen.P2ActualMixedWarmDecisionWalls

noncomputable section
open scoped Classical
open Set P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer P2ActualWarmDecisionDivergence
open P2LowerFiniteCellRounding P2RoundedCausalFibreLossAndLevel

def FineClose (tau : ℝ) (xs ys : List ℝ) : Prop :=
  List.Forall₂ (fun x y => |x - y| ≤ tau) xs ys

theorem fineClose_of_floor_labels {tau : ℝ} (htau : 0 < tau)
    (xs ys : List ℝ)
    (h : xs.map (fun x => (⌊x / tau⌋ : ℤ)) =
      ys.map (fun y => (⌊y / tau⌋ : ℤ))) : FineClose tau xs ys := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := by simpa using h.symm
      subst ys
      exact .nil
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          have hc := (List.cons.inj h).1
          have hxlo := (le_div_iff₀ htau).mp (Int.floor_le (x / tau))
          have hylo := (le_div_iff₀ htau).mp (Int.floor_le (y / tau))
          have hxhi := (div_lt_iff₀ htau).mp (Int.lt_floor_add_one (x / tau))
          have hyhi := (div_lt_iff₀ htau).mp (Int.lt_floor_add_one (y / tau))
          rw [hc] at hxlo hxhi
          exact .cons (abs_le.mpr (by constructor <;> linarith))
            (ih ys (List.cons.inj h).2)

theorem fineClose_length {tau : ℝ} {xs ys : List ℝ} (h : FineClose tau xs ys) :
    xs.length = ys.length := h.length_eq

theorem fineClose_take {tau : ℝ} {xs ys : List ℝ} (h : FineClose tau xs ys) (j : ℕ) :
    FineClose tau (xs.take j) (ys.take j) := by
  induction h generalizing j with
  | nil => exact .nil
  | @cons x y xs ys hxy htail ih =>
      cases j with
      | zero => exact .nil
      | succ j => exact .cons hxy (ih j)

theorem fineClose_getD {tau : ℝ} (htau : 0 ≤ tau) {xs ys : List ℝ}
    (h : FineClose tau xs ys) (j : ℕ) : |xs.getD j 0 - ys.getD j 0| ≤ tau := by
  induction h generalizing j with
  | nil => simpa using htau
  | @cons x y xs ys hxy htail ih =>
      cases j with
      | zero => simpa only [List.getD_cons_zero] using hxy
      | succ j => simpa only [List.getD_cons_succ] using ih j

theorem fineClose_sum {tau : ℝ} {xs ys : List ℝ} (h : FineClose tau xs ys) :
    |xs.sum - ys.sum| ≤ (xs.length : ℝ) * tau := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy htail ih =>
      obtain ⟨hxl, hxu⟩ := abs_le.mp hxy
      obtain ⟨hsl, hsu⟩ := abs_le.mp ih
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      apply abs_le.mpr
      constructor <;> nlinarith

/-- A changed actual half-open coarse code crosses a literal mesh wall.
The top singleton is retained; no almost-everywhere deletion is used. -/
theorem exponentCode_ne_near_mesh_boundary {a b x y tau : ℝ} (hab : a < b)
    (mesh : ℕ) (htau : 0 ≤ tau) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : |x - y| ≤ tau)
    (hne : exponentCode a b mesh x ≠ exponentCode a b mesh y) :
    ∃ q : Fin (mesh + 2), |x - logPrimeMeshPoint a b mesh q.val| ≤ tau := by
  have hcx := exponentCode_membership (m := mesh) hx
  have hcy := exponentCode_membership (m := mesh) hy
  cases hxc : exponentCode a b mesh x with
  | none =>
      have hxb : x = b := by simpa only [hxc, exponentCell] using hcx
      refine ⟨⟨mesh + 1, by omega⟩, ?_⟩
      simpa only [hxb, logPrimeMeshPoint_last, sub_self, abs_zero] using htau
  | some i =>
      cases hyc : exponentCode a b mesh y with
      | none =>
          have hyb : y = b := by simpa only [hyc, exponentCell] using hcy
          refine ⟨⟨mesh + 1, by omega⟩, ?_⟩
          simpa only [logPrimeMeshPoint_last, ← hyb] using hxy
      | some q =>
          have hx' : logPrimeMeshPoint a b mesh i.val ≤ x ∧
              x < logPrimeMeshPoint a b mesh (i.val + 1) := by
            simpa only [hxc, exponentCell, mem_Ico] using hcx
          have hy' : logPrimeMeshPoint a b mesh q.val ≤ y ∧
              y < logPrimeMeshPoint a b mesh (q.val + 1) := by
            simpa only [hyc, exponentCell, mem_Ico] using hcy
          have hiq : i ≠ q := by
            intro heq
            exact hne (by rw [hxc, hyc, heq])
          obtain ⟨hlo, hhi⟩ := abs_le.mp hxy
          rcases lt_or_gt_of_ne hiq with hij | hji
          · have hsep : logPrimeMeshPoint a b mesh (i.val + 1) ≤
                logPrimeMeshPoint a b mesh q.val :=
              logPrimeMeshPoint_mono hab.le mesh (by omega)
            refine ⟨⟨i.val + 1, by omega⟩, abs_le.mpr ?_⟩
            constructor <;> linarith [hx'.2, hy'.1]
          · have hsep : logPrimeMeshPoint a b mesh (q.val + 1) ≤
                logPrimeMeshPoint a b mesh i.val :=
              logPrimeMeshPoint_mono hab.le mesh (by omega)
            refine ⟨⟨i.val, by omega⟩, abs_le.mpr ?_⟩
            constructor <;> linarith [hx'.1, hy'.2]

theorem coordinate_code_maps_ne_wall {a b tau : ℝ} (hab : a < b) (mesh : ℕ)
    (htau : 0 ≤ tau) {xs ys : List ℝ} (hf : FineClose tau xs ys)
    (hx : ∀ x ∈ xs, x ∈ Icc a b) (hy : ∀ y ∈ ys, y ∈ Icc a b)
    (hne : xs.map (exponentCode a b mesh) ≠ ys.map (exponentCode a b mesh)) :
    ∃ x ∈ xs, ∃ q : Fin (mesh + 2), |x - logPrimeMeshPoint a b mesh q.val| ≤ tau := by
  revert hx hy hne
  induction hf with
  | nil => intro _ _ hne; exact (hne rfl).elim
  | @cons x y xs ys hxy htail ih =>
      intro hx hy hne
      by_cases hc : exponentCode a b mesh x = exponentCode a b mesh y
      · have ht : xs.map (exponentCode a b mesh) ≠ ys.map (exponentCode a b mesh) := by
          intro heq
          exact hne (by simp only [List.map_cons, hc, heq])
        obtain ⟨z, hz, q, hq⟩ := ih
          (fun z hz => hx z (List.mem_cons_of_mem x hz))
          (fun z hz => hy z (List.mem_cons_of_mem y hz)) ht
        exact ⟨z, List.mem_cons_of_mem x hz, q, hq⟩
      · obtain ⟨q, hq⟩ := exponentCode_ne_near_mesh_boundary hab mesh htau
          (hx x (List.mem_cons_self x xs)) (hy y (List.mem_cons_self y ys)) hxy hc
        exact ⟨x, List.mem_cons_self x xs, q, hq⟩

private theorem take_succ_getD (xs : List ℝ) (j : ℕ) (hj : j < xs.length) :
    xs.take (j + 1) = xs.take j ++ [xs.getD j 0] := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
      cases j with
      | zero => simp
      | succ j =>
          simpa only [List.take_succ_cons, List.getD_cons_succ, List.cons_append] using
            congrArg (List.cons x) (ih j (by simpa using hj))

/-- Every different actual warm acceptance has a genuine coarse-coordinate
wall or its true incoming even-cube wall. Rank4/5 parent caps are the run's
own caps, not independently selected maxima or reset ideal values. -/
theorem actual_run_disagreement_wall_cover {depth mesh : ℕ}
    (P : CapPlan depth mesh) {a b tau : ℝ} (hab : a < b) (htau : 0 ≤ tau)
    (base : Trace) (hbase : 0 < base.word.length) {xs ys : List ℝ}
    (hf : FineClose tau xs ys)
    (hx : ∀ x ∈ xs, x ∈ Icc a b) (hy : ∀ y ∈ ys, y ∈ Icc a b)
    (hne : (run P a b base xs).accepted ≠ (run P a b base ys).accepted) :
    ∃ j : ℕ, j < xs.length ∧
      ((∃ x ∈ xs.take (j + 1), ∃ q : Fin (mesh + 2),
          |x - logPrimeMeshPoint a b mesh q.val| ≤ tau) ∨
        let A := run P a b base (xs.take j)
        (A.word.length + 1) % 2 = 0 ∧
          |A.word.sum + 3 * xs.getD j 0 - A.cap| ≤ ((j : ℝ) + 3) * tau) := by
  have hlen := fineClose_length hf
  obtain ⟨j, hj, hcap, hacc, hd⟩ :=
    run_disagreement_first_decision P a b xs ys hlen base base rfl rfl hne
  refine ⟨j, hj, ?_⟩
  rcases hd with hc | ha
  · left
    have htakeLen : (xs.take (j + 1)).length = (ys.take (j + 1)).length :=
      fineClose_length (fineClose_take hf (j + 1))
    have hcodes : (xs.take (j + 1)).map (exponentCode a b mesh) ≠
        (ys.take (j + 1)).map (exponentCode a b mesh) := by
      intro heq
      apply hc
      rw [run_word, run_word, List.append_assoc, List.append_assoc,
        ← take_succ_getD xs j hj,
        ← take_succ_getD ys j (by omega)]
      apply planChoice_eq_of_coordinate_codes
      · simp only [List.length_append, htakeLen]
      · simp only [List.map_append, heq]
    exact coordinate_code_maps_ne_wall hab mesh htau (fineClose_take hf (j + 1))
      (fun x hx' => hx x (List.mem_of_mem_take hx'))
      (fun y hy' => hy y (List.mem_of_mem_take hy')) hcodes
  · right
    have hs := fineClose_sum (fineClose_take hf j)
    have hsum :
        |(run P a b base (xs.take j)).word.sum -
          (run P a b base (ys.take j)).word.sum| ≤ (j : ℝ) * tau := by
      simpa only [run_word, List.sum_append, add_sub_add_left_eq_sub,
        List.length_take, Nat.min_eq_left hj.le] using hs
    apply admission_disagreement_wall _ _ _ _ tau j htau ?_ ?_ hcap hsum
      (fineClose_getD htau hf j) ha
    · simp only [run_word, List.length_append, List.length_take, hlen]
    · simp only [run_word, List.length_append]
      omega

/-- Actual canonical rough coordinate words inherit closeness directly
from the very labels used by the ALL/ANY compiler. -/
theorem canonical_words_fineClose {N : ℕ} {tau : ℝ} (htau : 0 < tau)
    {d r : ℕ} (h : label N tau d = label N tau r) :
    FineClose tau (physicalWord N d.primeFactorsList) (physicalWord N r.primeFactorsList) := by
  apply fineClose_of_floor_labels htau
  simpa only [physicalWord, coordinate, label, primeLabel, List.map_map,
    Function.comp_def] using h

/-- The actual mixed cell supplies an opposite canonical warm acceptance
for d ITSELF, rather than merely a wall around an unrelated retained witness. -/
theorem mixed_opposite_canonical_word {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ) (N enum : ℕ) (p : ℕ × ℕ)
    (w z tau : ℝ) {d : ℕ} (hd : d ∈ universe N enum w z)
    (hm : mixed (pairPolicy P a b seed N p) N enum w z tau d) :
    ∃ r ∈ cell N enum w z tau d,
      pairPolicy P a b seed N p d.primeFactorsList ≠
        pairPolicy P a b seed N p r.primeFactorsList := by
  have hself := self_mem_cell N enum w z tau hd
  by_cases hraw : d ∈ rawSupport (pairPolicy P a b seed N p) N enum w z
  · obtain ⟨r, hr, hnr⟩ := hm.2
    refine ⟨r, hr, ?_⟩
    have hdt := (P2ActualPairPlanRawSupport.pair_raw_iff_canonical_warm
      P a b seed N enum p w z d).mp hraw
    intro heq
    exact hnr ((P2ActualPairPlanRawSupport.pair_raw_iff_canonical_warm
      P a b seed N enum p w z r).mpr ⟨(Finset.mem_filter.mp hr).1, heq ▸ hdt.2⟩)
  · obtain ⟨r, hr, hrr⟩ := hm.1
    refine ⟨r, hr, ?_⟩
    have hrt := (P2ActualPairPlanRawSupport.pair_raw_iff_canonical_warm
      P a b seed N enum p w z r).mp hrr
    intro heq
    exact hraw ((P2ActualPairPlanRawSupport.pair_raw_iff_canonical_warm
      P a b seed N enum p w z d).mpr ⟨hd, heq.symm ▸ hrt.2⟩)

/-- Receiver membership is derived from the actual rough carrier and its
cutoffs; it is not an assumed geometric box for an arithmetic word. -/
theorem canonicalWord_in_receiver {N enum d : ℕ} (hN : 1 < (N : ℝ))
    {omega v a b : ℝ} (ha : a ≤ omega) (hb : v ≤ b)
    (hd : d ∈ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ v)) :
    ∀ x ∈ physicalWord N d.primeFactorsList, x ∈ Icc a b := by
  obtain ⟨hsub, hprod⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe
    N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ v) hd
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  have hp := mem_roughPrimeUniverse.mp (hsub.subset hq)
  have heq := coordinate_power hN hp.2.1.pos
  have hlo : omega ≤ coordinate N q := by
    apply (Real.rpow_le_rpow_left_iff hN).mp
    simpa only [heq] using hp.2.2.2.1
  have hhi : coordinate N q < v := by
    apply (Real.rpow_lt_rpow_left_iff hN).mp
    simpa only [heq] using hp.2.2.2.2
  exact ⟨ha.trans hlo, hhi.le.trans hb⟩

/-- ALL mixed fibres of this actual warm compiler, measured at d itself,
are covered by a true coarse mesh wall or true frozen admission wall.
No coverage, success equality or retained-witness wall is a premise. -/
theorem all_actual_mixed_warm_decision_walls {depth mesh : ℕ}
    (P : CapPlan depth mesh) {a b omega v tau : ℝ}
    (hab : a < b) (ha : a ≤ omega) (hb : v ≤ b) (htau : 0 < tau)
    {N : ℕ} (hN : 1 < (N : ℝ)) (enum : ℕ) (p : ℕ × ℕ) (seed : ℝ)
    {d : ℕ} (hd : d ∈ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ v))
    (hm : mixed (pairPolicy P a b seed N p)
      N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau d) :
    ∃ j : ℕ, j < d.primeFactorsList.length ∧
      ((∃ x ∈ (physicalWord N d.primeFactorsList).take (j + 1),
          ∃ q : Fin (mesh + 2), |x - logPrimeMeshPoint a b mesh q.val| ≤ tau) ∨
        let A := run P a b (pairRoot N p seed)
          ((physicalWord N d.primeFactorsList).take j)
        (A.word.length + 1) % 2 = 0 ∧
          |A.word.sum + 3 * (physicalWord N d.primeFactorsList).getD j 0 - A.cap| ≤
            ((j : ℝ) + 3) * tau) := by
  obtain ⟨r, hr, hneq⟩ := mixed_opposite_canonical_word
    P a b seed N enum p ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau hd hm
  have hrU := (Finset.mem_filter.mp hr).1
  have hlabel := (Finset.mem_filter.mp hr).2
  have hf := canonical_words_fineClose htau hlabel.symm
  have hx := canonicalWord_in_receiver hN ha hb hd
  have hy := canonicalWord_in_receiver hN ha hb hrU
  have hrun : (run P a b (pairRoot N p seed) (physicalWord N d.primeFactorsList)).accepted ≠
      (run P a b (pairRoot N p seed) (physicalWord N r.primeFactorsList)).accepted := by
    simpa only [pairPolicy, warmRetain, warmTrace] using hneq
  obtain ⟨j, hj, hw⟩ := actual_run_disagreement_wall_cover P hab htau.le
    (pairRoot N p seed) (by simp [pairRoot]) hf hx hy hrun
  exact ⟨j, by simpa only [physicalWord, List.length_map, List.length_reverse] using hj, hw⟩

/-- The real canonical tent constructor supplies the plan and the actual
raw rank supplier. This is a concrete application, not an arbitrary bank
whose adopted identity has been asserted. The full-W target stays separate. -/
theorem canonical_tent_mixed_rank_and_walls
    (R : P2OriginalPairSourceReceiver.PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (hseed : (seed : ℝ) ≤ P2OriginalLowerCompactStartCapConstructor.topCap)
    (omega tau : ℝ) (homega : 0 < omega) (heps : (R.epsilon : ℝ) ≤ omega)
    (htau : 0 < tau) {N : ℕ} (hN : 1 < (N : ℝ)) (enum : ℕ)
    {p : ℕ × ℕ} (hp : p ∈ P5SelectedMaskTransport.sixthSupport N)
    {d : ℕ} (hd : d ∈ universe N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ (417 / 5000 : ℝ)))
    (hm : mixed (pairPolicy (P2OriginalCanonicalPairTentBank.plan R mesh buffer seed)
      R.epsilon P2OriginalPairSourceReceiver.ceiling seed N p)
      N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ (417 / 5000 : ℝ)) tau d) :
    d.primeFactorsList.length ≤
      Nat.ceil (P2OriginalLowerCompactStartCapConstructor.topCap / omega) ∧
    ∃ j : ℕ, j < d.primeFactorsList.length ∧
      ((∃ x ∈ (physicalWord N d.primeFactorsList).take (j + 1),
          ∃ q : Fin (mesh + 2),
            |x - logPrimeMeshPoint (R.epsilon : ℝ)
              (P2OriginalPairSourceReceiver.ceiling : ℝ) mesh q.val| ≤ tau) ∨
        let P := P2OriginalCanonicalPairTentBank.plan R mesh buffer seed
        let A := run P R.epsilon P2OriginalPairSourceReceiver.ceiling
          (pairRoot N p seed) ((physicalWord N d.primeFactorsList).take j)
        (A.word.length + 1) % 2 = 0 ∧
          |A.word.sum + 3 * (physicalWord N d.primeFactorsList).getD j 0 - A.cap| ≤
            ((j : ℝ) + 3) * tau) := by
  obtain ⟨r, hr, hraw⟩ := hm.1
  have hrank := (P2SourceFormPairRoundedSigmaLevel.sourceform_pair_raw_support R
    (P2OriginalCanonicalPairTentBank.bank R mesh buffer seed) buffer seed hseed hN enum
    hp omega homega hraw).2
  have hlen : d.primeFactorsList.length = r.primeFactorsList.length := by
    have h := congrArg List.length (Finset.mem_filter.mp hr).2
    simpa only [label, List.length_map, List.length_reverse] using h.symm
  have hdRank : d.primeFactorsList.length ≤
      Nat.ceil (P2OriginalLowerCompactStartCapConstructor.topCap / omega) := by
    rw [hlen]
    exact hrank
  refine ⟨hdRank, ?_⟩
  apply all_actual_mixed_warm_decision_walls _ ?_ heps ?_ htau hN enum p seed hd hm
  · exact_mod_cast R.epsilon_lt_a.trans (by norm_num : (417/5000 : ℚ) < 59/250)
  · norm_num [P2OriginalPairSourceReceiver.ceiling]

end
end ImbalancedChen.P2ActualMixedWarmDecisionWalls
