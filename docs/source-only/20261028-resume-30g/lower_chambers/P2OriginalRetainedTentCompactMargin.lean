import ImbalancedChen.P2OriginalCanonicalTentFrozenChambers

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Strict original full and selected-complement tests, without a supplied
positive margin, give an open retained source region. Every compact part
of that region has one positive rational margin. The finite physical
prefix alphabet then gives an actual finite box cover and screened rows
on ONE common mesh. This concerns the literal tent actions; W has its
different auxiliary-level source and is never declared a tent mask.
-/

namespace ImbalancedChen.P2OriginalRetainedTentCompactMargin

noncomputable section
open scoped Classical Topology
open Set
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code strictSquareGates)
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerAffineTieSelector
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalPairSourceReceiver
open P2OriginalCanonicalPairTentBank
open P2OriginalIdealTentCanonicalScreen
open P2OriginalCanonicalTentFrozenChambers

abbrev Point := Fin 5 → ℝ

def indices (rank : Fin 6) : List (Fin 5) := [0,1,2,3,4].take rank.val
def fullFunctions (rank : Fin 6) : List (Point → ℝ) :=
  (indices rank).map (fun i x => x i)
def selectedFunctions (rank : Fin 6) (mask : Finset (Fin 5)) : List (Point → ℝ) :=
  ((indices rank).filter (fun i => decide (i ∈ mask))).map (fun i x => x i)
def remainingFunctions (rank : Fin 6) (mask : Finset (Fin 5)) : List (Point → ℝ) :=
  ((indices rank).filter (fun i => !decide (i ∈ mask))).map (fun i x => x i)
def evaluate (fs : List (Point → ℝ)) (x : Point) : List ℝ := fs.map (fun f => f x)

def tentForm (mask : Finset (Fin 5)) (right : Bool) : SourceForm :=
  if right then .tentRight mask else .tentLeft mask
def endpoint (mask : Finset (Fin 5)) (right : Bool) (x : Point) : ℝ :=
  (tentForm mask right).affine.eval x

-- A strict active gate that is identically equal to its endpoint cannot
-- lie here. This is distinct from the preserved parent-inherit label.
def region (rank : Fin 6) (mask : Finset (Fin 5)) (right : Bool) (m : ℝ) : Set Point :=
  {x | m < endpoint mask (!right) x - endpoint mask right x ∧
    strictSquareGates (endpoint mask right x - m) 0 (evaluate (fullFunctions rank) x) ∧
    strictSquareGates (endpoint mask right x - m)
      (evaluate (selectedFunctions rank mask) x).sum
      (evaluate (remainingFunctions rank mask) x)}

theorem strict_squares_mono {a b T : ℝ} {xs : List ℝ}
    (hab : a ≤ b) (h : strictSquareGates a T xs) : strictSquareGates b T xs := by
  induction xs generalizing T with
  | nil => trivial
  | cons x xs ih => exact ⟨h.1.trans_le hab, ih h.2⟩

theorem strict_squares_have_margin {cap T : ℝ} {xs : List ℝ}
    (h : strictSquareGates cap T xs) :
    ∃ d : ℝ, 0 < d ∧ strictSquareGates (cap - d) T xs := by
  induction xs generalizing T with
  | nil => exact ⟨1, by norm_num, trivial⟩
  | cons x xs ih =>
      obtain ⟨d, hd, ht⟩ := ih h.2
      let r := min ((cap - T - 2*x)/2) d
      have hr : 0 < r := lt_min (by linarith [h.1]) hd
      refine ⟨r, hr, ?_, ?_⟩
      · have hh := min_le_left ((cap-T-2*x)/2) d
        dsimp [r] at *
        linarith [h.1]
      · apply strict_squares_mono _ ht
        dsimp [r]
        linarith [min_le_right ((cap-T-2*x)/2) d]

private theorem continuous_evaluate_sum (fs : List (Point → ℝ))
    (hfs : ∀ f ∈ fs, Continuous f) : Continuous (fun x => (evaluate fs x).sum) := by
  revert hfs
  induction fs with
  | nil =>
      intro hfs
      simpa [evaluate] using (continuous_const : Continuous (fun _ : Point => (0 : ℝ)))
  | cons f fs ih =>
      intro hfs
      simpa [evaluate] using (hfs f (by simp)).add
        (ih (fun g hg => hfs g (by simp [hg])))

private theorem squares_isOpen (fs : List (Point → ℝ))
    (hfs : ∀ f ∈ fs, Continuous f) (cap T : Point → ℝ)
    (hcap : Continuous cap) (hT : Continuous T) :
    IsOpen {x | strictSquareGates (cap x) (T x) (evaluate fs x)} := by
  revert hfs
  induction fs generalizing T with
  | nil =>
      intro hfs
      simpa [strictSquareGates, evaluate] using isOpen_univ
  | cons f fs ih =>
      intro hfs
      have hf := hfs f (by simp)
      have hrest := ih (fun x => T x + f x) (hT.add hf)
        (fun g hg => hfs g (by simp [hg]))
      have hhead : IsOpen {x | T x + 2*f x < cap x} :=
        isOpen_lt (hT.add (continuous_const.mul hf)) hcap
      simpa [evaluate, strictSquareGates] using hhead.inter hrest

private theorem endpoint_continuous (mask : Finset (Fin 5)) (right : Bool) :
    Continuous (endpoint mask right) := by
  unfold endpoint AffineBranch.eval
  fun_prop

private theorem functions_continuous (rank : Fin 6) (mask : Finset (Fin 5)) :
    (∀ f ∈ fullFunctions rank, Continuous f) ∧
      (∀ f ∈ selectedFunctions rank mask, Continuous f) ∧
      (∀ f ∈ remainingFunctions rank mask, Continuous f) := by
  constructor
  · intro f hf
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
    exact continuous_apply i
  constructor <;> intro f hf <;>
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf <;> exact continuous_apply i

theorem region_isOpen (rank : Fin 6) (mask : Finset (Fin 5)) (right : Bool) (m : ℝ) :
    IsOpen (region rank mask right m) := by
  obtain ⟨hfull, hsel, hrem⟩ := functions_continuous rank mask
  have hcap : Continuous (fun x => endpoint mask right x - m) :=
    (endpoint_continuous mask right).sub continuous_const
  have hside : IsOpen {x | m < endpoint mask (!right) x - endpoint mask right x} :=
    isOpen_lt continuous_const
      ((endpoint_continuous mask (!right)).sub (endpoint_continuous mask right))
  exact hside.inter ((squares_isOpen _ hfull _ _ hcap continuous_const).inter
    (squares_isOpen _ hrem _ _ hcap (continuous_evaluate_sum _ hsel)))

theorem region_mono (rank : Fin 6) (mask : Finset (Fin 5)) (right : Bool)
    {m n : ℝ} (hmn : m ≤ n) : region rank mask right n ⊆ region rank mask right m := by
  intro x hx
  exact ⟨hmn.trans_lt hx.1,
    strict_squares_mono (by linarith) hx.2.1,
    strict_squares_mono (by linarith) hx.2.2⟩

theorem original_strict_point_has_rational_margin
    (rank : Fin 6) (mask : Finset (Fin 5)) (right : Bool)
    (x : Point) (hx : x ∈ region rank mask right 0) :
    ∃ m : ℚ, 0 < m ∧ x ∈ region rank mask right m := by
  obtain ⟨dF, hF0, hF⟩ := strict_squares_have_margin (by simpa using hx.2.1)
  obtain ⟨dS, hS0, hS⟩ := strict_squares_have_margin (by simpa using hx.2.2)
  have hg : 0 < endpoint mask (!right) x - endpoint mask right x := hx.1
  obtain ⟨m, hm0, hms⟩ := exists_rat_btwn
    (lt_min (half_pos hg) (lt_min hF0 hS0))
  have hmSide := hms.trans_le (min_le_left _ _)
  have hmF := hms.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hmS := hms.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨m, by exact_mod_cast hm0, ?_, ?_, ?_⟩
  · linarith
  · exact strict_squares_mono (by linarith) hF
  · exact strict_squares_mono (by linarith) hS

private theorem finite_margin (F : Finset {m : ℚ // 0 < m}) :
    ∃ m : ℚ, 0 < m ∧ ∀ q ∈ F, m ≤ q.val := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert q F hnot ih =>
      obtain ⟨m, hm, hF⟩ := ih
      refine ⟨min m q.val, lt_min hm q.property, ?_⟩
      intro r hr
      rcases Finset.mem_insert.mp hr with heq | hmem
      · subst r
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (hF r hmem)

-- No uniform point margin is an input. It is obtained from the exact
-- original strict gate system and compactness, with an empty K allowed.
theorem compact_original_tent_has_common_margin
    (rank : Fin 6) (mask : Finset (Fin 5)) (right : Bool)
    (K : Set Point) (hK : IsCompact K) (hsource : K ⊆ region rank mask right 0) :
    ∃ m : ℚ, 0 < m ∧ K ⊆ region rank mask right m := by
  have hcover : K ⊆ ⋃ q : {m : ℚ // 0 < m}, region rank mask right q.val := by
    intro x hx
    obtain ⟨m, hm, hxm⟩ := original_strict_point_has_rational_margin rank mask right x (hsource hx)
    exact Set.mem_iUnion.mpr ⟨⟨m, hm⟩, hxm⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover
    (fun q : {m : ℚ // 0 < m} => region rank mask right q.val)
    (fun q => region_isOpen rank mask right q.val) hcover
  obtain ⟨m, hm, hmF⟩ := finite_margin F
  refine ⟨m, hm, ?_⟩
  intro x hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (hF hx)
  exact region_mono rank mask right (by exact_mod_cast hmF q hq) hxq

-- Literal physical words: all original incoming bits of codeAt are
-- false; each source supplies its OWN selected mask, once and unchanged.
theorem actual_point_words (R : PairRange) (mesh : ℕ) (rank : Fin 6)
    (mask : Finset (Fin 5)) (x : Point) :
    ((pointSlots rank (actualCode R mesh rank x) mask x).map Slot.exponent =
        evaluate (fullFunctions rank) x) ∧
      (selectedWord (pointSlots rank (actualCode R mesh rank x) mask x) =
        evaluate (selectedFunctions rank mask) x) ∧
      (remainingWord (pointSlots rank (actualCode R mesh rank x) mask x) =
        evaluate (remainingFunctions rank mask) x) := by
  fin_cases rank <;>
    simp [pointSlots, pointSlot, actualCode_at, evaluate, fullFunctions,
      selectedFunctions, remainingFunctions, indices, selectedWord, remainingWord]

theorem chosen_endpoint (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) (right : Bool) (x : Point) :
    (chosenRow R code mask right).cap.eval x = endpoint mask right x := by
  cases right <;> rfl

-- The actual finite code type is the finite cover. No arbitrary bank or
-- checker is supplied. Padding is merely the causal embedding of rank-r
-- prefixes in five coordinates; it is not a restriction on later primes.
theorem compact_original_tent_enters_common_actual_mesh
    (R : PairRange) (rank : Fin 6) (mask : Finset (Fin 5))
    (hmask : mask ∈ P2OriginalFiniteTentBankSelectorMargins.tentMasks rank)
    (right : Bool) (K : Set Point) (hK : IsCompact K)
    (hsource : K ⊆ region rank mask right 0)
    (hrange : ∀ x ∈ K, ∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (hpadding : ∀ x ∈ K, ∀ i : Fin 5, rank.val ≤ i.val → x i = (ceiling : ℝ)) :
    ∃ buffer : ℚ, 0 < buffer ∧ ∃ M : ℕ, ∀ mesh : ℕ, M ≤ mesh →
      ∀ floor : ℚ, ∀ x ∈ K,
        sourceCheck R rank (actualCode R mesh rank x) buffer
          (chosenRow R (actualCode R mesh rank x) mask right) ∧
        chosenRow R (actualCode R mesh rank x) mask right ∈
          (bank R mesh buffer floor).alternatives rank (actualCode R mesh rank x) := by
  obtain ⟨m, hm, hKm⟩ := compact_original_tent_has_common_margin rank mask right K hK hsource
  let buffer : ℚ := m/2
  have hb : 0 < buffer := by dsimp [buffer]; positivity
  have hbmargin : (buffer : ℝ) < m := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    dsimp [buffer]
    push_cast
    linarith
  obtain ⟨M, hM⟩ := exists_uniform_canonical_tent_mesh R buffer hb.le m hbmargin
  refine ⟨buffer, hb, M, ?_⟩
  intro mesh hmesh floor x hx
  have hpoint : actualPoint rank x = x := by
    funext i
    by_cases hi : i.val < rank.val
    · simp [actualPoint, hi]
    · simp [actualPoint, hi, hpadding x hx i (Nat.le_of_not_gt hi)]
  have hbox : inBox (box R (actualCode R mesh rank x)) x := by
    simpa [hpoint] using actualCode_point_in_box R mesh rank x (hrange x hx)
  have hmX := hKm hx
  obtain ⟨hw, hs, hr⟩ := actual_point_words R mesh rank mask x
  have hscreen := ideal_tent_enters_concrete_screen R _ rank x hbox mask hmask
    right buffer hb.le m (by exact_mod_cast hm) (hM mesh hmesh)
    (by simpa [otherRow, chosen_endpoint] using hmX.1.le)
    (by simpa [chosen_endpoint, hw] using hmX.2.1)
    (by simpa [chosen_endpoint, hs, hr] using hmX.2.2)
  exact ⟨hscreen.2, every_screened_original_action_occurs R mesh buffer floor rank _
    mask hmask _ hscreen.1 hscreen.2⟩

-- Explicit finite source-box cover, not merely a pointwise existence
-- statement. Only actual codes attained by K enter F; later child walls
-- have not been projected onto or used to discard any parent space.
theorem compact_original_tent_finite_actual_cover
    (R : PairRange) (rank : Fin 6) (mask : Finset (Fin 5))
    (hmask : mask ∈ P2OriginalFiniteTentBankSelectorMargins.tentMasks rank)
    (right : Bool) (K : Set Point) (hK : IsCompact K)
    (hsource : K ⊆ region rank mask right 0)
    (hrange : ∀ x ∈ K, ∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (hpadding : ∀ x ∈ K, ∀ i : Fin 5, rank.val ≤ i.val → x i = (ceiling : ℝ)) :
    ∃ buffer : ℚ, 0 < buffer ∧ ∃ M : ℕ, ∀ mesh : ℕ, M ≤ mesh →
      ∀ floor : ℚ, ∃ F : Finset (Code mesh),
        K ⊆ ⋃ code ∈ F, {x | inBox (box R code) x} ∧
        ∀ code ∈ F,
          sourceCheck R rank code buffer (chosenRow R code mask right) ∧
          chosenRow R code mask right ∈ (bank R mesh buffer floor).alternatives rank code := by
  obtain ⟨buffer, hb, M, hM⟩ := compact_original_tent_enters_common_actual_mesh
    R rank mask hmask right K hK hsource hrange hpadding
  refine ⟨buffer, hb, M, ?_⟩
  intro mesh hmesh floor
  let F : Finset (Code mesh) := Finset.univ.filter
    (fun code => ∃ x ∈ K, actualCode R mesh rank x = code)
  refine ⟨F, ?_, ?_⟩
  · intro x hx
    have hmem : actualCode R mesh rank x ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hx, rfl⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨actualCode R mesh rank x, hmem, ?_⟩
    have hpoint : actualPoint rank x = x := by
      funext i
      by_cases hi : i.val < rank.val
      · simp [actualPoint, hi]
      · simp [actualPoint, hi, hpadding x hx i (Nat.le_of_not_gt hi)]
    simpa [hpoint] using actualCode_point_in_box R mesh rank x (hrange x hx)
  · intro code hcode
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ K, actualCode R mesh rank x = code :=
      (Finset.mem_filter.mp hcode).2
    exact hM mesh hmesh floor x hx

end
end ImbalancedChen.P2OriginalRetainedTentCompactMargin
