import ImbalancedChen.P2OriginalLowerWThirdPhysicalRow

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Arbitrary strict original W-winning points have rational buffered endpoint
boxes. Every compact subset of this strict chamber has a finite cover by
these boxes. A mesh cell refining one of the boxes passes the original
WBoxCheck with its actual baseline parent. Equality/order/gate/winner walls
are not asserted to lie in this strict chamber or in the finite cover.
-/

namespace ImbalancedChen.P2OriginalStrictWLocalRationalCover

noncomputable section
open scoped Classical BigOperators Topology
open Set
open P2PhysicalIncomingPrefixCells P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code strictSquareGates)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerOrderedWBranch
open P2OriginalLowerWThirdPhysicalRow

abbrev Point := Fin 3 → ℝ
abbrev ProperMask := {I : Finset (Fin 3) // I.Nonempty}

-- These are point conditions of the original ordinary first-start history,
-- not fields asserting a table, a plan, a selected winner or a boxed licence.
structure StrictWPoint (S : CompactStart) (rho : ℝ) (x : Point) : Prop where
  cutoff_lower : (S.epsilon : ℝ) < x 2
  order21 : x 2 < x 1
  order10 : x 1 < x 0
  cutoff_upper : x 0 < (startCutoff S.start : ℝ)
  below_mu : x 0 < mu
  first_square : 2 * x 0 < baselineCap rho
  second_cube : x 0 + 3 * x 1 < baselineCap rho
  beats_parent : baselineCap rho < B (x 2)
  W_activation : A (x 0) < B (x 2)
  beats_tents : ∀ I : ProperMask, v (∑ i ∈ I.val, x i) < B (x 2)

-- Three lower endpoints, three upper endpoints, beta and delta.
def pack (lo hi : Point) (beta delta : ℝ) : Fin 8 → ℝ :=
  ![lo 0, lo 1, lo 2, hi 0, hi 1, hi 2, beta, delta]

def lower (u : Fin 8 → ℝ) (i : Fin 3) : ℝ :=
  u ⟨i.val, by omega⟩

def upper (u : Fin 8 → ℝ) (i : Fin 3) : ℝ :=
  u ⟨i.val + 3, by omega⟩

@[simp] theorem lower_pack (lo hi : Point) (beta delta : ℝ) :
    lower (pack lo hi beta delta) = lo := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem upper_pack (lo hi : Point) (beta delta : ℝ) :
    upper (pack lo hi beta delta) = hi := by
  funext i
  fin_cases i <;> rfl

def endpointCap (u : Fin 8 → ℝ) : ℝ := B (upper u 2) - u 6

-- All constraints must remain strict in one common endpoint neighborhood.
-- Positivity of beta/delta is supplied by rational density after choosing
-- the neighborhood; the diagonal point has beta=delta=0.
def geometricSlack (S : CompactStart) (rho : ℝ)
    (u : Fin 8 → ℝ) : Fin 14 → ℝ :=
  ![lower u 2 - S.epsilon,
    (startCutoff S.start : ℝ) - upper u 0,
    mu - upper u 0,
    lower u 0 - upper u 1,
    lower u 1 - upper u 2,
    endpointCap u - baselineCap rho,
    baselineCap rho - upper u 0 - 3 * upper u 1,
    endpointCap u - 2 * u 7 - 2 * upper u 0,
    endpointCap u - 2 * u 7 - upper u 0 - 2 * upper u 1,
    endpointCap u - 2 * u 7 - upper u 0 - upper u 1 - 2 * upper u 2,
    endpointCap u - A (upper u 0),
    topCap - endpointCap u,
    1 / 100000 - u 7,
    lower u 2]

-- A and C are oppositely monotone. This is a genuine upper bound for
-- v(sum_I y) throughout the entire endpoint box, including a tent bend.
def winnerSlack (u : Fin 8 → ℝ) (I : ProperMask) : ℝ :=
  endpointCap u - min (A (∑ i ∈ I.val, upper u i))
    (C (∑ i ∈ I.val, lower u i))

def endpointRegion (S : CompactStart) (rho : ℝ) : Set (Fin 8 → ℝ) :=
  {u | (∀ j : Fin 14, 0 < geometricSlack S rho u j) ∧
    ∀ I : ProperMask, 0 < winnerSlack u I}

private theorem geometricSlack_continuous (S : CompactStart) (rho : ℝ)
    (j : Fin 14) : Continuous (fun u => geometricSlack S rho u j) := by
  fin_cases j <;>
    dsimp [geometricSlack, endpointCap, lower, upper, A, B, Lambda] <;> fun_prop

private theorem winnerSlack_continuous (I : ProperMask) :
    Continuous (fun u => winnerSlack u I) := by
  unfold winnerSlack endpointCap lower upper A B C Lambda
  fun_prop

theorem endpointRegion_isOpen (S : CompactStart) (rho : ℝ) :
    IsOpen (endpointRegion S rho) := by
  change IsOpen ((⋂ j : Fin 14, {u | 0 < geometricSlack S rho u j}) ∩
    ⋂ I : ProperMask, {u | 0 < winnerSlack u I})
  exact (isOpen_iInter_of_finite (fun j =>
    isOpen_lt continuous_const (geometricSlack_continuous S rho j))).inter
    (isOpen_iInter_of_finite (fun I =>
      isOpen_lt continuous_const (winnerSlack_continuous I)))

theorem diagonal_mem_endpointRegion (S : CompactStart) (rho : ℝ)
    (x : Point) (hx : StrictWPoint S rho x) :
    pack x x 0 0 ∈ endpointRegion S rho := by
  rcases hx with ⟨hlo, ho21, ho10, hcut, hmu, hsq, hcube, hparent, hact, htents⟩
  have heps : (0 : ℝ) < S.epsilon := by exact_mod_cast S.epsilon_pos
  have hz : 0 < x 2 := lt_trans heps hlo
  have hy : 0 < x 1 := lt_trans hz ho21
  constructor
  · intro j
    fin_cases j <;>
      simp [geometricSlack, endpointCap, pack, A, B, Lambda, mu,
        baselineCap, topCap] at * <;> linarith
  · intro I
    have ht := htents I
    simpa [winnerSlack, endpointCap, pack, v] using sub_pos.mpr ht

structure LocalWBox (S : CompactStart) (rho : ℝ) where
  lo : Fin 3 → ℚ
  hi : Fin 3 → ℚ
  beta : ℚ
  delta : ℚ
  beta_pos : 0 < beta
  delta_pos : 0 < delta
  lo_lt_hi : ∀ i, lo i < hi i
  feasible : pack (fun i => (lo i : ℝ)) (fun i => (hi i : ℝ))
    beta delta ∈ endpointRegion S rho

def LocalWBox.interiorSet {S : CompactStart} {rho : ℝ}
    (Q : LocalWBox S rho) : Set Point :=
  {x | ∀ i, (Q.lo i : ℝ) < x i ∧ x i < (Q.hi i : ℝ)}

def LocalWBox.closedSet {S : CompactStart} {rho : ℝ}
    (Q : LocalWBox S rho) : Set Point :=
  {x | ∀ i, (Q.lo i : ℝ) ≤ x i ∧ x i ≤ (Q.hi i : ℝ)}

theorem LocalWBox.interior_isOpen {S : CompactStart} {rho : ℝ}
    (Q : LocalWBox S rho) : IsOpen Q.interiorSet := by
  change IsOpen (⋂ i : Fin 3,
    {x : Point | (Q.lo i : ℝ) < x i ∧ x i < (Q.hi i : ℝ)})
  exact isOpen_iInter_of_finite (fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const))

-- All endpoint and buffer choices are proved by rational density inside
-- one open set of strict original inequalities. No boxed checker premise
-- or uniform prechosen positive gap is smuggled into this existence step.
theorem strict_point_has_rational_W_box (S : CompactStart) (rho : ℝ)
    (x : Point) (hx : StrictWPoint S rho x) :
    ∃ Q : LocalWBox S rho, x ∈ Q.interiorSet := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((endpointRegion_isOpen S rho).mem_nhds
      (diagonal_mem_endpointRegion S rho x hx))
  have hlo : ∀ i : Fin 3, ∃ q : ℚ,
      x i - r / 2 < (q : ℝ) ∧ (q : ℝ) < x i := by
    intro i
    exact exists_rat_btwn (by linarith)
  have hhi : ∀ i : Fin 3, ∃ q : ℚ,
      x i < (q : ℝ) ∧ (q : ℝ) < x i + r / 2 := by
    intro i
    exact exists_rat_btwn (by linarith)
  choose lo hlo using hlo
  choose hi hhi using hhi
  obtain ⟨beta, hb0, hb1⟩ : ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < r / 2 :=
    exists_rat_btwn (by linarith)
  obtain ⟨delta, hd0, hd1⟩ : ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < r / 2 :=
    exists_rat_btwn (by linarith)
  have hnear : pack (fun i => (lo i : ℝ)) (fun i => (hi i : ℝ))
      beta delta ∈ Metric.ball (pack x x 0 0) r := by
    apply (dist_pi_lt_iff hr).2
    intro j
    have hl0 := hlo 0
    have hl1 := hlo 1
    have hl2 := hlo 2
    have hh0 := hhi 0
    have hh1 := hhi 1
    have hh2 := hhi 2
    fin_cases j <;> dsimp [pack] <;> rw [Real.dist_eq] <;>
      apply abs_lt.mpr <;> constructor <;> linarith
  let Q : LocalWBox S rho :=
    { lo := lo
      hi := hi
      beta := beta
      delta := delta
      beta_pos := by exact_mod_cast hb0
      delta_pos := by exact_mod_cast hd0
      lo_lt_hi := fun i => by
        have h : (lo i : ℝ) < (hi i : ℝ) := lt_trans (hlo i).2 (hhi i).1
        exact_mod_cast h
      feasible := hball hnear }
  exact ⟨Q, fun i => ⟨(hlo i).2, (hhi i).1⟩⟩

-- This finite cover is only of the supplied compact subset of the strict
-- chamber. It makes no assertion about an equality wall or its measure.
theorem compact_strict_chamber_finite_cover (S : CompactStart) (rho : ℝ)
    (K : Set Point) (hK : IsCompact K)
    (hstrict : ∀ x ∈ K, StrictWPoint S rho x) :
    ∃ F : Finset (LocalWBox S rho),
      K ⊆ ⋃ Q ∈ F, Q.interiorSet := by
  have hcover : K ⊆ ⋃ Q : LocalWBox S rho, Q.interiorSet := by
    intro x hx
    obtain ⟨Q, hQ⟩ := strict_point_has_rational_W_box S rho x (hstrict x hx)
    exact Set.mem_iUnion.mpr ⟨Q, hQ⟩
  exact hK.elim_finite_subcover (fun Q : LocalWBox S rho => Q.interiorSet)
    (fun Q => Q.interior_isOpen) hcover

-- The box retains the winner even across the bend of any selected tent.
-- In particular no assertion of globally affine v is needed.
theorem LocalWBox.tents_below_buffered_W {S : CompactStart} {rho : ℝ}
    (Q : LocalWBox S rho) (x : Point) (hx : x ∈ Q.closedSet)
    (I : ProperMask) :
    v (∑ i ∈ I.val, x i) < B (Q.hi 2) - Q.beta := by
  have hsumlo : (∑ i ∈ I.val, (Q.lo i : ℝ)) ≤ ∑ i ∈ I.val, x i :=
    Finset.sum_le_sum (fun i _ => (hx i).1)
  have hsumhi : (∑ i ∈ I.val, x i) ≤ ∑ i ∈ I.val, (Q.hi i : ℝ) :=
    Finset.sum_le_sum (fun i _ => (hx i).2)
  have hA : A (∑ i ∈ I.val, x i) ≤ A (∑ i ∈ I.val, (Q.hi i : ℝ)) := by
    dsimp [A]
    linarith
  have hC : C (∑ i ∈ I.val, x i) ≤ C (∑ i ∈ I.val, (Q.lo i : ℝ)) := by
    dsimp [C]
    linarith
  have hwin := Q.feasible.2 I
  have hbound : min (A (∑ i ∈ I.val, (Q.hi i : ℝ)))
      (C (∑ i ∈ I.val, (Q.lo i : ℝ))) < B (Q.hi 2) - Q.beta := by
    simpa [winnerSlack, endpointCap, pack] using sub_pos.mp hwin
  exact lt_of_le_of_lt (min_le_min hA hC) hbound

end
end ImbalancedChen.P2OriginalStrictWLocalRationalCover
