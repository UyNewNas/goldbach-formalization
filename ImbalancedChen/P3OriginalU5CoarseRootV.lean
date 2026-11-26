import ImbalancedChen.P3OriginalU5AllSignedSquares
import ImbalancedChen.VariableEnvelopeRegularity

/-!
# A fixed auxiliary PairRange cover for actual U5 root sources

SOURCE ONLY / UNCOMPILED / NO KERNEL ACCEPTANCE.

The auxiliary mesh, its finite family of original rank-two codes, and
each geometric representative precede N.  The original CandidateBank
has its own independent mesh.  No seed or policy is replaced.

The representative chooses a singleton, pair, or W winner of the same
real maximum.  Equality ties only choose an auxiliary route.  A V route
has a fixed positive margin throughout the original code's closed hull,
even when it is not the pointwise winner elsewhere in that hull.

Actual root-origin SignedSupply is transported monotonically to this
fixed auxiliary cover, retaining the complete canonical word and the
original selected mask.  Small beta is not assigned a fixed prime rank.
Endpoint atomization, the W factorization, physical common Q, exact
tensor identity, and family admission remain separate obligations.

Compatibility: public-qpoint-cast.patch only exposes the existing
qPoint_cast declaration; its statement and proof are unchanged.
-/

namespace ImbalancedChen.P3OriginalU5CoarseRootV

noncomputable section
open scoped Classical Topology
open Set Filter
open P2PhysicalIncomingPrefixCells
open P2LowerCapPlanIntegerRetention (coordinate marked)
open P2OriginalPairSourceReceiver
open P2OriginalLowerSelectedCapConstructor (Code)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData
open P2OriginalSelectedIntegerPrefixSquares
open P2OriginalSelectedNativeSmallExtension
open P3OriginalU5AllSourceSquares
open P3OriginalU5AllSignedSquares
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV (fullModulus)
open Part5OriginalUpsilon5CausalDictionary (triangle level a h mem_triangle level_bounds)
open VariableEnvelope (v B)

/-- This resolution is auxiliary and never replaces the bank's mesh. -/
abbrev meshStep (R : PairRange) (m_aux : ℕ) : ℝ :=
  logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) m_aux

theorem meshStep_pos (R : PairRange) (m_aux : ℕ) : 0 < meshStep R m_aux := by
  apply logPrimeMeshStep_pos
  exact_mod_cast R.epsilon_lt_a.trans (by norm_num [ceiling] :
    (417 / 5000 : ℚ) < ceiling)

/-- The mesh is chosen before any arithmetic scale or prime pair. -/
theorem exists_auxiliary_mesh (R : PairRange) {buffer : ℝ} (hb : 0 < buffer) :
    ∃ m_aux : ℕ, meshStep R m_aux ≤ buffer / 32 := by
  obtain ⟨m_aux, hm⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ)).eventually
      (gt_mem_nhds (by linarith : 0 < buffer / 32)))
  exact ⟨m_aux, (hm m_aux le_rfl).le⟩

private theorem triangle_in_receiver (R : PairRange) {x : Fin 2 → ℝ}
    (hx : x ∈ triangle) :
    x 0 ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ) ∧
      x 1 ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ) := by
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp hx
  have he : (R.epsilon : ℝ) < a := by
    change (R.epsilon : ℝ) < (417 / 5000 : ℝ)
    have hcast : (R.epsilon : ℝ) < ((417 / 5000 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr R.epsilon_lt_a
    norm_num at hcast ⊢
    exact hcast
  have hh : h < (ceiling : ℝ) := by norm_num [h, ceiling]
  exact ⟨⟨he.le.trans hu, hut.le.trans (ht.le.trans hh.le)⟩,
    ⟨he.le.trans (hu.trans hut.le), ht.le.trans hh.le⟩⟩

/-- The missing lower half of the existing exponent_upper interface. -/
theorem exponent_lower (R : PairRange) (m_aux : ℕ) {x : ℝ}
    (hx : x ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ)) :
    (qLo R m_aux (exponentCode (R.epsilon : ℝ) (ceiling : ℝ) m_aux x) : ℝ) ≤ x := by
  have hm := exponentCode_membership (m := m_aux) hx
  cases hc : exponentCode (R.epsilon : ℝ) (ceiling : ℝ) m_aux x with
  | none =>
      have heq : x = (ceiling : ℝ) := by simpa [hc, exponentCell] using hm
      simpa [hc, qLo] using heq.ge
  | some j =>
      have hm' : x ∈ Ico
          (logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) m_aux j.val)
          (logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) m_aux (j.val + 1)) := by
        simpa only [hc, exponentCell] using hm
      simpa only [qLo, qPoint_cast] using hm'.1

/-- Reuse the original adjacent-endpoint identity, including top padding. -/
theorem code_width_le (R : PairRange) (m_aux : ℕ) (c : CellCode m_aux) :
    (qHi R m_aux c : ℝ) - (qLo R m_aux c : ℝ) ≤ meshStep R m_aux := by
  cases c with
  | none => simpa only [qHi, qLo, sub_self] using (meshStep_pos R m_aux).le
  | some j =>
      simp only [qHi, qLo, qPoint_cast]
      rw [logPrimeMeshPoint_succ]
      simp only [add_sub_cancel_left, le_refl]

/-- Exact ownership uses codeAt, with its original marks and padding.
    Coordinates are (u,t); the chronological prefix is [t,u]. -/
def ownedCell (R : PairRange) (m_aux : ℕ) (code : Code m_aux) : Set (Fin 2 → ℝ) :=
  {x | x ∈ triangle ∧ codeAt R m_aux 2 [x 1, x 0] = code}

/-- The first two coordinates of the existing rational box, intersected
    with the original triangle.  No new box representation is introduced. -/
def closedCell (R : PairRange) {m_aux : ℕ} (code : Code m_aux) : Set (Fin 2 → ℝ) :=
  {x | x ∈ triangle ∧
    ((box R code).lo 0 : ℝ) ≤ x 1 ∧ x 1 ≤ ((box R code).hi 0 : ℝ) ∧
    ((box R code).lo 1 : ℝ) ≤ x 0 ∧ x 0 ≤ ((box R code).hi 1 : ℝ)}

/-- Finiteness is fixed by m_aux; this predicate contains no N or prime. -/
def family (R : PairRange) (m_aux : ℕ) : Finset (Code m_aux) :=
  Finset.univ.filter (fun code => (ownedCell R m_aux code).Nonempty)

abbrev Label (R : PairRange) (m_aux : ℕ) :=
  {code : Code m_aux // code ∈ family R m_aux}

def representative (R : PairRange) {m_aux : ℕ} (j : Label R m_aux) : Fin 2 → ℝ :=
  Classical.choose (Finset.mem_filter.mp j.property).2

theorem representative_mem (R : PairRange) {m_aux : ℕ} (j : Label R m_aux) :
    representative R j ∈ ownedCell R m_aux j.val :=
  Classical.choose_spec (Finset.mem_filter.mp j.property).2

theorem ownedCell_subset_closedCell (R : PairRange) (m_aux : ℕ) (code : Code m_aux) :
    ownedCell R m_aux code ⊆ closedCell R code := by
  rintro x ⟨hx, rfl⟩
  obtain ⟨hu, ht⟩ := triangle_in_receiver R hx
  refine ⟨hx, ?_, ?_, ?_, ?_⟩
  · simpa [box, codeAt, incomingCode, physicalCode, marked] using exponent_lower R m_aux ht
  · simpa [box, codeAt, incomingCode, physicalCode, marked] using exponent_upper R m_aux ht
  · simpa [box, codeAt, incomingCode, physicalCode, marked] using exponent_lower R m_aux hu
  · simpa [box, codeAt, incomingCode, physicalCode, marked] using exponent_upper R m_aux hu

/-- After the finite geometry is fixed, an actual point reads its old code. -/
def labelAt (R : PairRange) (m_aux : ℕ) (x : Fin 2 → ℝ) (hx : x ∈ triangle) :
    Label R m_aux :=
  ⟨codeAt R m_aux 2 [x 1, x 0], Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨x, hx, rfl⟩⟩⟩

theorem labelAt_closed (R : PairRange) (m_aux : ℕ) (x : Fin 2 → ℝ)
    (hx : x ∈ triangle) : x ∈ closedCell R (labelAt R m_aux x hx).val :=
  ownedCell_subset_closedCell R m_aux _ ⟨hx, rfl⟩

/-- PairRange's actual first-two-slot hull has one mesh-width diameter. -/
theorem closedCell_coordinate_error (R : PairRange) {m_aux : ℕ}
    {code : Code m_aux} {x y : Fin 2 → ℝ}
    (hx : x ∈ closedCell R code) (hy : y ∈ closedCell R code) (i : Fin 2) :
    |x i - y i| ≤ meshStep R m_aux := by
  have h0 := code_width_le R m_aux (code 0).1
  have h1 := code_width_le R m_aux (code 1).1
  change (qHi R m_aux (code 0).1 : ℝ) - (qLo R m_aux (code 0).1 : ℝ) ≤ _ at h0
  change (qHi R m_aux (code 1).1 : ℝ) - (qLo R m_aux (code 1).1 : ℝ) ≤ _ at h1
  have hxt := hx.2.1
  have hxt' := hx.2.2.1
  have hxu := hx.2.2.2.1
  have hxu' := hx.2.2.2.2
  have hyt := hy.2.1
  have hyt' := hy.2.2.1
  have hyu := hy.2.2.2.1
  have hyu' := hy.2.2.2.2
  dsimp [box] at hxt hxt' hxu hxu' hyt hyt' hyu hyu'
  fin_cases i
  · change |x 0 - y 0| ≤ meshStep R m_aux
    exact abs_le.mpr ⟨by linarith only [hxu, hyu', h1], by linarith only [hxu', hyu, h1]⟩
  · change |x 1 - y 1| ≤ meshStep R m_aux
    exact abs_le.mpr ⟨by linarith only [hxt, hyt', h0], by linarith only [hxt', hyt, h0]⟩

def vArgument (x : Fin 2 → ℝ) (both : Bool) : ℝ :=
  if both then x 1 + x 0 else x 1

theorem v_argument_variation (R : PairRange) {m_aux : ℕ}
    {code : Code m_aux} {x y : Fin 2 → ℝ}
    (hx : x ∈ closedCell R code) (hy : y ∈ closedCell R code) (both : Bool) :
    |v (vArgument x both) - v (vArgument y both)| ≤ 3 * meshStep R m_aux := by
  have h0 := closedCell_coordinate_error R hx hy 0
  have h1 := closedCell_coordinate_error R hx hy 1
  have hstep := (meshStep_pos R m_aux).le
  cases both
  · have hv := VariableEnvelope.v_abs_sub_le_of_le h1
    dsimp [vArgument]
    linarith
  · have hsum : |(x 1 + x 0) - (y 1 + y 0)| ≤ 2 * meshStep R m_aux := by
      calc
        _ = |(x 1 - y 1) + (x 0 - y 0)| := by congr 1; ring
        _ ≤ |x 1 - y 1| + |x 0 - y 0| := abs_add_le _ _
        _ ≤ 2 * meshStep R m_aux := by linarith
    have hv := VariableEnvelope.v_abs_sub_le_of_le hsum
    dsimp [vArgument]
    linarith

theorem root_level_variation (R : PairRange) {m_aux : ℕ}
    {code : Code m_aux} {x y : Fin 2 → ℝ}
    (hx : x ∈ closedCell R code) (hy : y ∈ closedCell R code) :
    |level (x 0) (x 1) - level (y 0) (y 1)| ≤ 3 * meshStep R m_aux := by
  have hs := v_argument_variation R hx hy false
  have hp := v_argument_variation R hx hy true
  dsimp [vArgument] at hs hp
  have hw : |VariableEnvelope.B a - VariableEnvelope.B a| ≤ 3 * meshStep R m_aux := by
    simpa only [sub_self, abs_zero] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (meshStep_pos R m_aux).le
  unfold level
  exact (abs_max_sub_max_le_max _ _ _ _).trans
    (max_le hs ((abs_max_sub_max_le_max _ _ _ _).trans (max_le hp hw)))

/-- An auxiliary equality tie chooses singleton, then pair, then W.
    This does not read or modify the original arithmetic policy. -/
def representativeRoute (R : PairRange) {m_aux : ℕ} (j : Label R m_aux) : Option Bool :=
  let r := representative R j
  if level (r 0) (r 1) = v (r 1) then some false
  else if level (r 0) (r 1) = v (r 1 + r 0) then some true
  else none

theorem representative_route_sound (R : PairRange) {m_aux : ℕ} (j : Label R m_aux) :
    match representativeRoute R j with
    | none => level (representative R j 0) (representative R j 1) = VariableEnvelope.B a
    | some both => level (representative R j 0) (representative R j 1) =
        v (vArgument (representative R j) both) := by
  unfold representativeRoute
  dsimp only
  split_ifs with hs hp
  · simpa [vArgument] using hs
  · simpa [vArgument] using hp
  · dsimp only [level] at hs hp ⊢
    rcases le_total (v (representative R j 1))
        (max (v (representative R j 1 + representative R j 0)) (VariableEnvelope.B a)) with ht | ht
    · rw [max_eq_right ht] at hp ⊢
      rcases le_total (v (representative R j 1 + representative R j 0)) (VariableEnvelope.B a) with hw | hw
      · exact max_eq_right hw
      · exact (hp (max_eq_left hw)).elim
    · exact (hs (max_eq_left ht)).elim

/-- This is an auxiliary covering exponent, never a replacement physical seed. -/
def auxCover (R : PairRange) {m_aux : ℕ} (buffer : ℝ) (j : Label R m_aux) : ℝ :=
  level (representative R j 0) (representative R j 1) +
    3 * meshStep R m_aux - buffer / 2

theorem auxiliary_cover_range (R : PairRange) {m_aux : ℕ}
    {buffer : ℝ} (hb : 0 < buffer) (hb' : buffer ≤ 1 / 1000)
    (hmesh : meshStep R m_aux ≤ buffer / 32) (j : Label R m_aux) :
    (1 / 2 : ℝ) < auxCover R buffer j ∧ auxCover R buffer j < (153 / 256 : ℝ) := by
  obtain ⟨hu, hut, ht⟩ := mem_triangle.mp (representative_mem R j).1
  have hlo := (level_bounds hu hut.le ht.le).1
  have hhi := P5CausalPrimeCorrectionPayment.original_U5_level_le_cap (representative R j)
  have hstep := (meshStep_pos R m_aux).le
  dsimp only [auxCover]
  dsimp only [a] at hu
  constructor <;> linarith

/-- Every original signed root cover is dominated with half a buffer to spare. -/
theorem whole_cell_cover (R : PairRange) {m_aux : ℕ} (buffer : ℝ)
    (j : Label R m_aux) {x : Fin 2 → ℝ} (hx : x ∈ closedCell R j.val) :
    level (x 0) (x 1) - buffer ≤ auxCover R buffer j - buffer / 2 := by
  have hr := ownedCell_subset_closedCell R m_aux j.val (representative_mem R j)
  have herr := (abs_le.mp (root_level_variation R hx hr)).2
  dsimp only [auxCover]
  linarith

/-- The representative's V route has one uniform whole-cell license.
    The W alternative deliberately has no factorization output. -/
theorem whole_cell_V_margin (R : PairRange) {m_aux : ℕ}
    {buffer : ℝ} (hb : 0 ≤ buffer) (hmesh : meshStep R m_aux ≤ buffer / 32)
    (j : Label R m_aux) :
    match representativeRoute R j with
    | none => level (representative R j 0) (representative R j 1) = VariableEnvelope.B a
    | some both => ∀ x ∈ closedCell R j.val,
        auxCover R buffer j + buffer / 4 ≤ v (vArgument x both) := by
  have hroute := representative_route_sound R j
  cases hr : representativeRoute R j with
  | none => simpa only [hr] using hroute
  | some both =>
      rw [hr] at hroute
      intro x hx
      have hrep := ownedCell_subset_closedCell R m_aux j.val (representative_mem R j)
      have herr := (abs_le.mp (v_argument_variation R hx hrep both)).1
      dsimp only [auxCover]
      rw [hroute]
      linarith

/-- Existential geometry precedes every possible arithmetic target.
    No family cardinality, representative, route or cover depends on N. -/
theorem exists_fixed_auxiliary_geometry (R : PairRange) {buffer : ℝ}
    (hb : 0 < buffer) (hb' : buffer ≤ 1 / 1000) :
    ∃ m_aux : ℕ, meshStep R m_aux ≤ buffer / 32 ∧
      ∀ j : Label R m_aux,
        ((1 / 2 : ℝ) < auxCover R buffer j ∧ auxCover R buffer j < (153 / 256 : ℝ)) ∧
        (∀ x ∈ closedCell R j.val,
          level (x 0) (x 1) - buffer ≤ auxCover R buffer j - buffer / 2) ∧
        (match representativeRoute R j with
        | none => level (representative R j 0) (representative R j 1) = VariableEnvelope.B a
        | some both => ∀ x ∈ closedCell R j.val,
            auxCover R buffer j + buffer / 4 ≤ v (vArgument x both)) := by
  obtain ⟨m_aux, hmesh⟩ := exists_auxiliary_mesh R hb
  exact ⟨m_aux, hmesh, fun j => ⟨auxiliary_cover_range R hb hb' hmesh j,
    fun _ hx => whole_cell_cover R buffer j hx, whole_cell_V_margin R hb.le hmesh j⟩⟩

/-- The same actual complete word and original selected mask use the
    fixed auxiliary cover.  There is no rank bound on the appended beta. -/
theorem root_signed_auxiliary_support
    (R : PairRange) {mesh m_aux : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (epsilon : ℝ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {k s : ℕ} {chosen : List ℕ} {slots : List (ℕ × Bool)}
    (hsigned : SignedSupply R bank buffer epsilon N t k s chosen .root slots) :
    let j := labelAt R m_aux (coordinates N t) (coordinates_mem_triangle hN ht)
    IntegerSquareGates N (auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2) 1
        (fullModulus t k).primeFactorsList.reverse ∧
      IntegerSquareGates N (auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2)
        (selectedPrimes (appendUnselected slots s.primeFactorsList.reverse)).prod
        (remainingPrimes (appendUnselected slots s.primeFactorsList.reverse)) := by
  let j := labelAt R m_aux (coordinates N t) (coordinates_mem_triangle hN ht)
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hcover := whole_cell_cover R (buffer : ℝ) j
    (labelAt_closed R m_aux (coordinates N t) (coordinates_mem_triangle hN ht))
  have hcap : sourceCover R buffer N t (.root : Origin mesh) ≤
      auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2 := by
    simpa [sourceCover, rootLevel, coordinates, actualPrimeTupleLog, coordinate] using hcover
  constructor
  · have hfull := P3OriginalU5FreshFifthSquareSupplier.integer_gates_mono
      hNr hcap _ hsigned.full
    rwa [hsigned.canonical] at hfull
  · exact P3OriginalU5FreshFifthSquareSupplier.integer_gates_mono
      hNr hcap _ hsigned.selected

/-- Both possible auxiliary V prefixes consume the existing exact append
    dictionary.  These complements do not change the source's S-mask. -/
theorem root_signed_initial_complements
    (R : PairRange) {mesh m_aux : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (epsilon : ℝ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {k s : ℕ} {chosen : List ℕ} {slots : List (ℕ × Bool)}
    (hsigned : SignedSupply R bank buffer epsilon N t k s chosen .root slots) :
    let j := labelAt R m_aux (coordinates N t) (coordinates_mem_triangle hN ht)
    IntegerSquareGates N (auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2) t.2
        (t.1 :: (chosen ++ s.primeFactorsList.reverse)) ∧
      IntegerSquareGates N (auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2) (t.2 * t.1)
        (chosen ++ s.primeFactorsList.reverse) := by
  let j := labelAt R m_aux (coordinates N t) (coordinates_mem_triangle hN ht)
  let c := auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2
  have hfull := (root_signed_auxiliary_support R bank buffer epsilon hN ht
    (m_aux := m_aux) hsigned).1
  rw [← hsigned.canonical, appendUnselected_values, hsigned.rough.values] at hfull
  constructor
  · simpa using ((integerSquareGates_append_iff N 1 c [t.2]
      (t.1 :: (chosen ++ s.primeFactorsList.reverse))).mp hfull).2
  · simpa using ((integerSquareGates_append_iff N 1 c [t.2, t.1]
      (chosen ++ s.primeFactorsList.reverse)).mp hfull).2

/-- Nonzero literal rho supplies its own witnesses before this root-only
    cover conclusion is used.  Fresh-row origins are retained, not relabeled.
    m_aux is independent of the bank mesh and is fixed before N. -/
theorem native_U5_coarse_root_support
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    (m_aux : ℕ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k : ℕ}
    (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0) :
    let j := labelAt R m_aux (coordinates N t) (coordinates_mem_triangle hN ht)
    ∃ s ∈ actualSmallRosserSupport N (Nat.ceil (cutoff N)) (smallCutoff N epsilon),
      ∃ chosen : List ℕ,
        List.Sublist chosen (roughPrimeUniverse N (Nat.ceil (cutoff N))
          (smallCutoff N epsilon) (cutoff N)) ∧ k = s * chosen.prod ∧
        (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t chosen).accepted = true ∧
        ∃ source slots, SignedSupply R bank buffer epsilon N t k s chosen source slots ∧
          (source = .root →
            IntegerSquareGates N (auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2) 1
                (fullModulus t k).primeFactorsList.reverse ∧
              IntegerSquareGates N (auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2)
                (selectedPrimes (appendUnselected slots s.primeFactorsList.reverse)).prod
                (remainingPrimes (appendUnselected slots s.primeFactorsList.reverse)) ∧
              IntegerSquareGates N (auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2) t.2
                (t.1 :: (chosen ++ s.primeFactorsList.reverse)) ∧
              IntegerSquareGates N (auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2) (t.2 * t.1)
                (chosen ++ s.primeFactorsList.reverse)) := by
  obtain ⟨s, hs, chosen, hsub, hkprod, haccept, source, slots, hsigned⟩ :=
    native_U5_nonzero_all_signed_squares R bank buffer hb hb' epsilon
      hepsilon hepsilon8 hgrid halloc hN ht hk
  refine ⟨s, hs, chosen, hsub, hkprod, haccept, source, slots, hsigned, ?_⟩
  intro hsource
  subst source
  have hcover := root_signed_auxiliary_support R bank buffer epsilon hN ht
    (m_aux := m_aux) hsigned
  exact ⟨hcover.1, hcover.2,
    root_signed_initial_complements R bank buffer epsilon hN ht (m_aux := m_aux) hsigned⟩

end
end ImbalancedChen.P3OriginalU5CoarseRootV
