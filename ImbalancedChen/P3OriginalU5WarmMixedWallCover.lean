import ImbalancedChen.P3OriginalU5WarmWordWalls
import ImbalancedChen.P3OriginalU5RoundedModulusCap

/-!
# Actual U5 mixed fibres meet a finite proper wall catalogue

SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE.

The selected policy, its pointwise original root seed, and the external
pair stay literal. The cap alphabet has a fixed finite address space even
when its real values depend on N and the pair. A mixed fibre supplies an
opposite word, but the resulting wall is at the charged d itself.

This is a coverage statement. It neither assumes nor proves smallness of
mixedMass, density, auxiliary admission, a common Q, or PP. All wall forms
are fixed coordinate/cube rows; the seed and external pair affect only
the finite list of centres. The small beta divisor is not a rough slot.
-/

namespace ImbalancedChen.P3OriginalU5WarmMixedWallCover

noncomputable section
open scoped Classical BigOperators List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer
open P3OriginalU5WarmCapCodeStability P3OriginalU5WarmAdmissionView
open P3OriginalU5WarmWordWalls
open P4AUpperTaggedFrozenAdmissionCatalogue (strict_row_disagreement_proper_wall)

/-- Coordinate-grid walls or an actual incoming cap address and cube row. -/
abbrev WallIndex (depth mesh rank : ℕ) :=
  (Fin rank × Fin (mesh + 2)) ⊕ (Fin rank × CapAddress depth mesh)

/-- One finite address type for every allowed rough rank, before N/pair. -/
abbrev BoundedWallIndex (depth mesh bound : ℕ) :=
  Σ rank : Fin (bound + 1), WallIndex depth mesh rank.val

def wallForm {depth mesh rank : ℕ} :
    WallIndex depth mesh rank → (Fin rank → ℝ) →L[ℝ] ℝ
  | .inl w => ContinuousLinearMap.proj w.1
  | .inr w => P5Z.PresievedRoughSlotAffineGates.cubeRow w.1

def wallCenter {depth mesh rank : ℕ} (P : CapPlan depth mesh)
    (a b seed externalSum : ℝ) : WallIndex depth mesh rank → ℝ
  | .inl w => logPrimeMeshPoint a b mesh w.2.val
  | .inr w => addressedCap P seed w.2 - externalSum

/-- The full catalogue size depends only on coarse mesh/depth and rank. -/
theorem wallIndex_card (depth mesh rank : ℕ) :
    Fintype.card (WallIndex depth mesh rank) =
      rank * (mesh + 2) + rank * Fintype.card (CapAddress depth mesh) := by
  simp only [WallIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

/-- A whole trace disagreement is covered at the first word, with no
coarse code, ancestor test, or inherited-cap region removed. -/
theorem warm_words_disagreement_wall {depth mesh rank : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ) (hab : a < b)
    (base : Trace) (hbase : base.accepted = true)
    (hbasecap : base.cap = seed) (hbaselen : base.word.length = 2)
    {tau : ℝ} (htau : 0 < tau) (xs ys : List ℝ)
    (hx : xs.length = rank) (hy : ys.length = rank)
    (hfine : xs.map (fun x => (⌊x / tau⌋ : ℤ)) =
      ys.map (fun y => (⌊y / tau⌋ : ℤ)))
    (hdiff : ¬((run P a b base xs).accepted = true ↔
      (run P a b base ys).accepted = true)) :
    ∃ w : WallIndex depth mesh rank, wallForm w ≠ 0 ∧
      |wallForm w (wordPoint rank xs) - wallCenter P a b seed base.word.sum w| ≤
        max 1 ‖wallForm w‖ * tau := by
  have hlen : xs.length = ys.length := hx.trans hy.symm
  by_cases hcoarse : coarseWord a b mesh xs = coarseWord a b mesh ys
  · obtain ⟨k, hk, htest, _hbefore⟩ :=
      first_actual_admission_difference P a b base hbase xs ys hlen hdiff
    let i : Fin rank := ⟨k, by omega⟩
    have hky : k < ys.length := by omega
    have hxl : (run P a b base (xs.take k)).word.length = 2 + k := by
      rw [run_word, List.length_append, hbaselen, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hk)]
    have hyl : (run P a b base (ys.take k)).word.length = 2 + k := by
      rw [run_word, List.length_append, hbaselen, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hky)]
    have hnonzero : 2 + k ≠ 0 := by omega
    have heven : (2 + k + 1) % 2 = 0 := by
      by_contra hodd
      apply htest
      simp only [admission, hxl, hyl, if_neg hnonzero, if_neg hodd]
    have hcaps := run_prefix_cap_eq_of_coarseWord P a b base xs ys hcoarse k
    let c := (run P a b base (xs.take k)).cap - base.word.sum
    have hxgate : admission (run P a b base (xs.take k)) xs[k] ↔
        (xs.take k).sum + 3 * xs[k] < c := by
      simp only [admission]
      rw [hxl, if_neg hnonzero, if_pos heven, run_word, List.sum_append]
      dsimp only [c]
      constructor <;> intro h <;> linarith
    have hygate : admission (run P a b base (ys.take k)) ys[k] ↔
        (ys.take k).sum + 3 * ys[k] < c := by
      simp only [admission]
      rw [hyl, if_neg hnonzero, if_pos heven, run_word, List.sum_append]
      dsimp only [c]
      rw [← hcaps]
      constructor <;> intro h <;> linarith
    have hrow : ¬(P5Z.PresievedRoughSlotAffineGates.cubeRow i (wordPoint rank xs) < c ↔
        P5Z.PresievedRoughSlotAffineGates.cubeRow i (wordPoint rank ys) < c) := by
      rw [cubeRow_wordPoint xs hx i, cubeRow_wordPoint ys hy i]
      intro h
      exact htest (hxgate.trans (h.trans hygate.symm))
    obtain ⟨hproper, hwall⟩ := strict_row_disagreement_proper_wall
      (P5Z.PresievedRoughSlotAffineGates.cubeRow i) c tau
      (wordPoint rank xs) (wordPoint rank ys)
      (same_floor_wordPoint_norm_le htau xs ys hx hy hfine) hrow
    have hcap : (run P a b base (xs.take k)).cap ∈ capAlphabet P seed := by
      apply run_cap_mem_capAlphabet
      simpa only [hbasecap] using seed_mem_capAlphabet P seed
    obtain ⟨address, _haddress, hvalue⟩ := Finset.mem_image.mp hcap
    refine ⟨Sum.inr (i, address), hproper, ?_⟩
    change |P5Z.PresievedRoughSlotAffineGates.cubeRow i (wordPoint rank xs) -
      (addressedCap P seed address - base.word.sum)| ≤
        max 1 ‖P5Z.PresievedRoughSlotAffineGates.cubeRow i‖ * tau
    rw [hvalue]
    exact hwall.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) htau.le)
  · obtain ⟨i, hi⟩ := coarseWord_disagreement_coordinate hlen hcoarse
    have hclose := same_floor_coordinate_le htau xs ys hfine i.val i.isLt
    obtain ⟨j, hj⟩ := exponentCode_disagreement_boundary hab hclose hi
    let i' : Fin rank := ⟨i.val, by omega⟩
    have hproper : (ContinuousLinearMap.proj i' : (Fin rank → ℝ) →L[ℝ] ℝ) ≠ 0 := by
      intro hz
      have h := congrArg (fun L : (Fin rank → ℝ) →L[ℝ] ℝ => L (fun _ => 1)) hz
      simp at h
    refine ⟨Sum.inl (i', j), hproper, ?_⟩
    change |wordPoint rank xs i' - logPrimeMeshPoint a b mesh j.val| ≤
      max 1 ‖(ContinuousLinearMap.proj i' : (Fin rank → ℝ) →L[ℝ] ℝ)‖ * tau
    rw [wordPoint_getElem xs hx i']
    exact hj.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (le_max_left (1 : ℝ) ‖(ContinuousLinearMap.proj i' : (Fin rank → ℝ) →L[ℝ] ℝ)‖)
        htau.le)

/-- Choose an opposite witness relative to d, including when d is itself
rejected. The good raw witness is never substituted for the charged d. -/
theorem mixed_has_opposite_warm_word {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seed : ℝ) (N enum : ℕ) (p : ℕ × ℕ) (z0 z tau : ℝ) (d : ℕ)
    (hm : P2RoundedCausalFibreLossAndLevel.mixed (pairPolicy P a b seed N p)
      N enum z0 z tau d) :
    ∃ e ∈ P2LowerFiniteCellRounding.cell N enum z0 z tau d,
      ¬(pairPolicy P a b seed N p d.primeFactorsList = true ↔
        pairPolicy P a b seed N p e.primeFactorsList = true) := by
  obtain ⟨r, hr, s, hs, hyes, hno⟩ :=
    (P2ActualPairPlanRawSupport.mixed_pair_iff_canonical_warm
      P a b seed N enum p z0 z tau d).mp hm
  by_cases hd : pairPolicy P a b seed N p d.primeFactorsList = true
  · exact ⟨s, hs, fun h => hno (h.mp hd)⟩
  · exact ⟨r, hr, fun h => hd (h.mpr hyes)⟩

theorem mixed_pair_wall_cover {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seed : ℝ) (hab : a < b) (N enum : ℕ) (p : ℕ × ℕ)
    (z0 z : ℝ) {tau : ℝ} (htau : 0 < tau) {d : ℕ}
    (hd : d ∈ P2LowerFiniteCellRounding.«universe» N enum z0 z)
    (hm : P2RoundedCausalFibreLossAndLevel.mixed (pairPolicy P a b seed N p)
      N enum z0 z tau d) :
    ∃ w : WallIndex depth mesh d.primeFactorsList.length, wallForm w ≠ 0 ∧
      |wallForm w (wordPoint d.primeFactorsList.length (physicalWord N d.primeFactorsList)) -
        wallCenter P a b seed (pairRoot N p seed).word.sum w| ≤
          max 1 ‖wallForm w‖ * tau := by
  obtain ⟨e, he, hopposite⟩ :=
    mixed_has_opposite_warm_word P a b seed N enum p z0 z tau d hm
  have hdcell := P2LowerFiniteCellRounding.self_mem_cell N enum z0 z tau hd
  have hlabel := (Finset.mem_filter.mp hdcell).2.trans (Finset.mem_filter.mp he).2.symm
  have hfine : (physicalWord N d.primeFactorsList).map (fun x => (⌊x / tau⌋ : ℤ)) =
      (physicalWord N e.primeFactorsList).map (fun y => (⌊y / tau⌋ : ℤ)) := by
    unfold P2LowerFiniteCellRounding.label P2LowerFiniteCellRounding.primeLabel at hlabel
    simpa only [physicalWord, coordinate, List.map_map, Function.comp_def] using hlabel
  have hx : (physicalWord N d.primeFactorsList).length = d.primeFactorsList.length := by
    simp only [physicalWord, List.length_map, List.length_reverse]
  have hy : (physicalWord N e.primeFactorsList).length = d.primeFactorsList.length := by
    have h := congrArg List.length hfine
    simpa only [List.length_map, hx] using h.symm
  have hdiff : ¬((run P a b (pairRoot N p seed)
        (physicalWord N d.primeFactorsList)).accepted = true ↔
      (run P a b (pairRoot N p seed)
        (physicalWord N e.primeFactorsList)).accepted = true) := hopposite
  exact warm_words_disagreement_wall P a b seed hab (pairRoot N p seed) rfl rfl rfl
    htau _ _ hx hy hfine hdiff

open P2OriginalPairSourceReceiver (PairRange pairPlan ceiling)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy rootSeed)
open P3OriginalU5RoundedModulusCap (rawRank selected_U5_raw_level_and_rank)
open P5OriginalU5CausalFinite (smallCutoff cutoff pairSupport)

/-- The actual U5 raw-rank supplier bounds the charged word through its
same-label good witness. There is no raw-retention assumption on d. -/
theorem selected_U5_mixed_rank
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum : ℕ) (tau : ℝ) {d : ℕ}
    (hm : P2RoundedCausalFibreLossAndLevel.mixed
      (selectedPolicy R bank buffer false N t) N enum
      (smallCutoff N epsilon) (cutoff N) tau d) :
    d.primeFactorsList.length ≤ rawRank epsilon := by
  obtain ⟨⟨r, hr, hraw⟩, _⟩ := hm
  have hbound := (selected_U5_raw_level_and_rank R bank buffer hb hb'
    epsilon hepsilon hN ht enum hraw).2
  have hsame := congrArg List.length (Finset.mem_filter.mp hr).2
  simp only [P2LowerFiniteCellRounding.label, List.length_map, List.length_reverse] at hsame
  simpa only [hsame] using hbound

/-- Finite proper-wall coverage for the literal selected U5 policy and
the literal rounded universe. The external pair and pointwise root seed
are fixed during each fibre comparison; they are not frozen across N. -/
theorem selected_U5_mixed_wall_cover
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum : ℕ) {tau : ℝ} (htau : 0 < tau) {d : ℕ}
    (hd : d ∈ P2LowerFiniteCellRounding.«universe» N enum
      (smallCutoff N epsilon) (cutoff N))
    (hm : P2RoundedCausalFibreLossAndLevel.mixed
      (selectedPolicy R bank buffer false N t) N enum
      (smallCutoff N epsilon) (cutoff N) tau d) :
    d.primeFactorsList.length ≤ rawRank epsilon ∧
      ∃ w : WallIndex 5 mesh d.primeFactorsList.length, wallForm w ≠ 0 ∧
        |wallForm w (wordPoint d.primeFactorsList.length
            (physicalWord N d.primeFactorsList)) -
          wallCenter (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
            (R.epsilon : ℝ) (ceiling : ℝ) (rootSeed false buffer N t)
            (pairRoot N t (rootSeed false buffer N t)).word.sum w| ≤
              max 1 ‖wallForm w‖ * tau := by
  refine ⟨selected_U5_mixed_rank R bank buffer hb hb' epsilon hepsilon hN ht enum tau hm, ?_⟩
  have hab : (R.epsilon : ℝ) < (ceiling : ℝ) := by
    exact_mod_cast R.epsilon_lt_a.trans (show (417 / 5000 : ℚ) < ceiling by
      norm_num [ceiling])
  exact mixed_pair_wall_cover
    (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
    (R.epsilon : ℝ) (ceiling : ℝ) (rootSeed false buffer N t) hab
    N enum t (smallCutoff N epsilon) (cutoff N) htau hd hm

/-- The address TYPE is fixed by epsilon and the coarse mesh, before N,
bank and pair. Only the numerical centres vary with those later inputs. -/
theorem selected_U5_mixed_bounded_catalogue
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum : ℕ) {tau : ℝ} (htau : 0 < tau) {d : ℕ}
    (hd : d ∈ P2LowerFiniteCellRounding.«universe» N enum
      (smallCutoff N epsilon) (cutoff N))
    (hm : P2RoundedCausalFibreLossAndLevel.mixed
      (selectedPolicy R bank buffer false N t) N enum
      (smallCutoff N epsilon) (cutoff N) tau d) :
    ∃ q : BoundedWallIndex 5 mesh (rawRank epsilon),
      q.1.val = d.primeFactorsList.length ∧ wallForm q.2 ≠ 0 ∧
        |wallForm q.2 (wordPoint q.1.val (physicalWord N d.primeFactorsList)) -
          wallCenter (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
            (R.epsilon : ℝ) (ceiling : ℝ) (rootSeed false buffer N t)
            (pairRoot N t (rootSeed false buffer N t)).word.sum q.2| ≤
              max 1 ‖wallForm q.2‖ * tau := by
  obtain ⟨hrank, w, hproper, hwall⟩ := selected_U5_mixed_wall_cover
    R bank buffer hb hb' epsilon hepsilon hN ht enum htau hd hm
  exact ⟨⟨⟨d.primeFactorsList.length, by omega⟩, w⟩, rfl, hproper, hwall⟩

end
end ImbalancedChen.P3OriginalU5WarmMixedWallCover
