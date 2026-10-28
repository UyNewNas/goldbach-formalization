import ImbalancedChen.P4AOriginalCell0AffineChronology
import ImbalancedChen.PrimeHistoryLogCoordinates
import ImbalancedChen.FirstExitFrontierAdmission
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A source-owned inner-box compiler for literal ascending cell0. Its finite
rational box bank is fixed before N. Exact N-power half-open prime boxes
select actual retained frontier states. All 96 strict affine conditions and
the genuine coarse-label firstStop follow from those arithmetic memberships.
Affine equality walls inherit the preceding slot15 action. No actual sixth
parent guard, full58/full87 identity, density convergence or K is assumed
closed by this local construction.
-/
namespace ImbalancedChen.P4AOriginalCell0HalfOpenPrimeCarrier
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open P4AOriginalCell0AffineChronology
open P2OriginalAscendingEighthCapDictionary

abbrev BoxIndex (m : ℕ) := Fin 8 → Fin (m + 1)

def qPoint (m i : ℕ) : ℚ := (i : ℚ) * (19 / 96) / ((m : ℚ) + 1)
def qLo (m : ℕ) (j : BoxIndex m) (i : Fin 8) : ℚ := qPoint m (j i).val
def qHi (m : ℕ) (j : BoxIndex m) (i : Fin 8) : ℚ := qPoint m ((j i).val + 1)

private theorem qPoint_cast (m i : ℕ) :
    (qPoint m i : ℝ) = logPrimeMeshPoint 0 (19 / 96) m i := by
  norm_num [qPoint, logPrimeMeshPoint, logPrimeMeshStep]
  push_cast
  ring

private theorem qLo_cast (m : ℕ) (j : BoxIndex m) (i : Fin 8) :
    (qLo m j i : ℝ) = logPrimeMeshLo 0 (19 / 96) m j i :=
  qPoint_cast m (j i).val

private theorem qHi_cast (m : ℕ) (j : BoxIndex m) (i : Fin 8) :
    (qHi m j i : ℝ) = logPrimeMeshHi 0 (19 / 96) m j i :=
  qPoint_cast m ((j i).val + 1)

/-- The lower affine endpoint uses lo for nonnegative slopes and hi for
negative slopes. This checks the complete closed box, so every point of
its half-open arithmetic carrier satisfies the same strict source row. -/
def rowLowerQ (m : ℕ) (j : BoxIndex m) (k : Fin 96) : ℚ :=
  (sourceRow k).2 0 + ∑ i : Fin 8,
    (sourceRow k).2 i.succ *
      (if 0 ≤ (sourceRow k).2 i.succ then qLo m j i else qHi m j i)

/-- Finite rational tests only; no N or arithmetic variable occurs. -/
def InnerBox (e : ℚ) (m : ℕ) (j : BoxIndex m) : Prop :=
  qHi m j 0 ≤ 19 / 96 - 4 * e ∧ ∀ k : Fin 96, 0 < rowLowerQ m j k

def innerBoxes (e : ℚ) (m : ℕ) : Finset (BoxIndex m) :=
  Finset.univ.filter (InnerBox e m)

@[simp] theorem mem_innerBoxes (e : ℚ) (m : ℕ) (j : BoxIndex m) :
    j ∈ innerBoxes e m ↔ InnerBox e m j := by simp [innerBoxes]

private theorem rowLowerQ_cast (m : ℕ) (j : BoxIndex m) (k : Fin 96) :
    (rowLowerQ m j k : ℝ) =
      ((sourceRow k).2 0 : ℝ) + ∑ i : Fin 8,
        ((sourceRow k).2 i.succ : ℝ) *
          (if 0 ≤ (sourceRow k).2 i.succ then
            logPrimeMeshLo 0 (19 / 96) m j i
           else logPrimeMeshHi 0 (19 / 96) m j i) := by
  simp only [rowLowerQ, Rat.cast_add, Rat.cast_sum, Rat.cast_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [qLo_cast, qHi_cast]

/-- Exact box lower bound for one recorded affine row. -/
theorem rowLower_le_eval (m : ℕ) (j : BoxIndex m) (k : Fin 96)
    (t : Fin 8 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    (rowLowerQ m j k : ℝ) ≤ evalRow (sourceRow k).2 t := by
  rw [rowLowerQ_cast]
  unfold evalRow P4AOriginalSeed7Unequal15Literal.evalAffine
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  have hi := mem_logPrimeMeshCell.mp ht i
  split_ifs with hc
  · exact mul_le_mul_of_nonneg_left hi.1 (by exact_mod_cast hc)
  · exact mul_le_mul_of_nonpos_left hi.2.le (by exact_mod_cast (le_of_not_ge hc))

/-- This theorem derives all source rows, rather than requesting them
from the arithmetic caller. -/
theorem innerBox_literalRows (e : ℚ) (m : ℕ) (j : BoxIndex m)
    (hj : j ∈ innerBoxes e m) (t : Fin 8 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) : literalRows t := by
  intro k
  have hk : (0 : ℝ) < (rowLowerQ m j k : ℝ) := by
    have hq := ((mem_innerBoxes e m j).mp hj).2 k
    exact_mod_cast hq
  exact hk.trans_le (rowLower_le_eval m j k t ht)

/-- Genuine N-dependent arithmetic carrier with exact lower-closed,
upper-open power endpoints, primality, and target-prime exclusions. -/
def primeBox (m N : ℕ) (j : BoxIndex m) : Finset (Fin 8 → ℕ) :=
  actualPrimeBoxTuples N (logPrimeMeshLo 0 (19 / 96) m j)
    (logPrimeMeshHi 0 (19 / 96) m j)

theorem primeBox_log {m N : ℕ} (hN : 1 < N) (j : BoxIndex m)
    (p : Fin 8 → ℕ) (hp : p ∈ primeBox m N j) :
    actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j := by
  exact ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2

/-- Coincident coordinate mesh walls have one owner; arithmetic tuples
cannot be double-counted in two labels, even at a shared power endpoint. -/
theorem primeBox_unique {m N : ℕ} (hN : 1 < N) (j k : BoxIndex m)
    (p : Fin 8 → ℕ) (hj : p ∈ primeBox m N j) (hk : p ∈ primeBox m N k) : j = k := by
  exact logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96)
    (primeBox_log hN j p hj) (primeBox_log hN k p hk)

/-- The first coordinate of the actual reversed history has the same
mesh label as its actual rank-one ancestor. -/
theorem innerBox_firstStop (e : ℚ) (m N : ℕ) (j : BoxIndex m)
    (pre : List ℕ) (hlen : pre.length = 8) (hj : j ∈ innerBoxes e m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 8 pre ∈
      logPrimeMeshCell 0 (19 / 96) m j) :
    HistoricalThirdCoarse.firstStop (e : ℝ) m (N : ℝ) (rosserAncestor 1 pre) := by
  have hx := mem_logPrimeMeshCell.mp ht (0 : Fin 8)
  have hid := primeHistoryLogCoordinates_ancestor (N : ℝ) hlen
    (by decide : 1 ≤ 8) (0 : Fin 1)
  have hstop := ((mem_innerBoxes e m j).mp hj).1
  have hstopR : logPrimeMeshHi 0 (19 / 96) m j 0 ≤
      VariableEnvelope.extendedFirstStop - 4 * (e : ℝ) := by
    rw [← qHi_cast]
    dsimp [VariableEnvelope.extendedFirstStop]
    exact_mod_cast hstop
  refine ⟨j 0, ?_, ?_, ?_⟩
  · simpa only [hid, logPrimeMeshLo] using hx.1
  · simpa only [hid, logPrimeMeshHi] using hx.2
  · simpa only [logPrimeMeshHi] using hstopR

/-- The actual retained rank-eight frontier is restricted by membership
in actual prime boxes. Its incoming sign, mass and remaining prime carrier
are not recreated or discarded. -/
def selectedFrontier (e : ℚ) (m N cap : ℕ) (w z : ℝ)
    (parent : Bool → List ℕ → Bool) : List (FirstExitDepthState ℕ) :=
  (firstExitDepthFrontier 8 parent (fun p => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N cap w z)).filter fun s => decide
      (∃ j ∈ innerBoxes e m,
        primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m N j)

theorem selectedFrontier_actual_source (e : ℚ) (m N cap : ℕ) (hN : 1 < N)
    (w z : ℝ) (parent : Bool → List ℕ → Bool) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selectedFrontier e m N cap w z parent) :
    s.selectedPrefix.length = 8 ∧
      parent s.positive s.selectedPrefix = true ∧
      literalRows (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) ∧
      HistoricalThirdCoarse.firstStop (e : ℝ) m (N : ℝ)
        (rosserAncestor 1 s.selectedPrefix) := by
  have hmem : s ∈ firstExitDepthFrontier 8 parent
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) ∧
      ∃ j ∈ innerBoxes e m,
        primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m N j := by
    simpa only [selectedFrontier, List.mem_filter, decide_eq_true_eq] using hs
  obtain ⟨hfront, j, hj, hp⟩ := hmem
  have hlen := firstExitDepthFrontier_selected_length 8 parent
    (fun p => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap w z)
    true 1 (by simp) s hfront
  have ht : primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix ∈
      logPrimeMeshCell 0 (19 / 96) m j := primeBox_log hN j _ hp
  exact ⟨hlen, mem_firstExitDepthFrontier_root_admitted 8 (by decide) parent
    (fun p => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap w z) s hfront,
    innerBox_literalRows e m j hj _ ht,
    innerBox_firstStop e m N j s.selectedPrefix hlen hj ht⟩

/-- The finite geometric decision used by the local cell0 action. -/
def boxOwns (e : ℚ) (m : ℕ) (t : Fin 8 → ℝ) : Prop :=
  ∃ j ∈ innerBoxes e m, t ∈ logPrimeMeshCell 0 (19 / 96) m j

def affineWall (t : Fin 8 → ℝ) : Prop :=
  ∃ k : Fin 96, evalRow (sourceRow k).2 t = 0

/-- Every exact affine equality wall is on the inherit side of this
action. This also handles prime tuples lying exactly on such walls. -/
theorem affineWall_not_boxOwns (e : ℚ) (m : ℕ) (t : Fin 8 → ℝ)
    (hwall : affineWall t) : ¬ boxOwns e m t := by
  obtain ⟨k, hk⟩ := hwall
  rintro ⟨j, hj, ht⟩
  have hs := innerBox_literalRows e m j hj t ht k
  rw [hk] at hs
  exact (lt_irrefl 0) hs

private def rowEndpoint (k : Fin 96) (m : ℕ) (j : BoxIndex m) : Fin 8 → ℝ :=
  fun i => if 0 ≤ (sourceRow k).2 i.succ then
    logPrimeMeshLo 0 (19 / 96) m j i else logPrimeMeshHi 0 (19 / 96) m j i

private theorem rowLower_tendsto (k : Fin 96) (j : ∀ m, BoxIndex m)
    (t : Fin 8 → ℝ)
    (ht : ∀ m, t ∈ logPrimeMeshCell 0 (19 / 96) m (j m)) :
    Tendsto (fun m => (rowLowerQ m (j m) k : ℝ)) atTop
      (𝓝 (evalRow (sourceRow k).2 t)) := by
  have hend : Tendsto (fun m => rowEndpoint k m (j m)) atTop (𝓝 t) := by
    apply tendsto_pi_nhds.mpr
    intro i
    by_cases hc : 0 ≤ (sourceRow k).2 i.succ
    · simpa [rowEndpoint, hc] using tendsto_logPrimeMeshLo_apply 0 (19 / 96) j ht i
    · simpa [rowEndpoint, hc] using tendsto_logPrimeMeshHi_apply 0 (19 / 96) j ht i
  have hcont : Continuous (evalRow (sourceRow k).2) := by
    unfold evalRow P4AOriginalSeed7Unequal15Literal.evalAffine
    fun_prop
  have hev := hcont.continuousAt.tendsto.comp hend
  simpa only [rowLowerQ_cast, evalRow,
    P4AOriginalSeed7Unequal15Literal.evalAffine, rowEndpoint] using hev

/-- The literal largest<25/128 row leaves a fixed firstStop margin.
With this explicit small-e bound the first-stop endpoint test is not an
additional geometric assumption on the original open source cell. -/
theorem literalRows_stop_margin (e : ℚ) (he : e ≤ 1 / 1536)
    (t : Fin 8 → ℝ) (ht : literalRows t) :
    t 0 < 19 / 96 - 4 * (e : ℝ) := by
  have hc := literalRows_cellGuard t ht
  have heR : (e : ℝ) ≤ 1 / 1536 := by exact_mod_cast he
  have hl := hc.largest
  dsimp [VariableEnvelope.mu] at hl
  linarith

/-- For any point of the original open source cell, a single sufficiently
fine mesh passes all 96 tests and the genuine first-label stop together.
The mesh is selected before any N is introduced. No claim about the mass
of omitted boxes or the full upper reserve is made here. -/
theorem literalRows_eventual_innerBox (e : ℚ) (he : e ≤ 1 / 1536)
    (t : Fin 8 → ℝ) (ht : literalRows t) :
    ∃ j : ∀ m, BoxIndex m,
      (∀ m, t ∈ logPrimeMeshCell 0 (19 / 96) m (j m)) ∧
        ∀ᶠ m in atTop, j m ∈ innerBoxes e m := by
  have hc := literalRows_cellGuard t ht
  have hcube : t ∈ logPrimeBox (fun _ => (0 : ℝ)) (fun _ => 19 / 96) := by
    apply mem_logPrimeBox.mpr
    intro i
    have hlo : t 7 ≤ t i := hc.order.antitone (Fin.le_last i)
    have hhi : t i ≤ t 0 := hc.order.antitone (Fin.zero_le i)
    have hl := hc.largest
    dsimp [VariableEnvelope.mu] at hl
    exact ⟨(hc.last_pos.trans_le hlo).le, by linarith⟩
  choose j hj using fun m => exists_logPrimeMeshCell 0 (19 / 96) m hcube
  have hrows : ∀ᶠ m in atTop, ∀ k : Fin 96, 0 < (rowLowerQ m (j m) k : ℝ) := by
    apply eventually_all.mpr
    intro k
    exact (rowLower_tendsto k j t hj).eventually (lt_mem_nhds (ht k))
  have hstop : ∀ᶠ m in atTop,
      logPrimeMeshHi 0 (19 / 96) m (j m) 0 < 19 / 96 - 4 * (e : ℝ) :=
    (tendsto_logPrimeMeshHi_apply 0 (19 / 96) j hj (0 : Fin 8)).eventually
      (gt_mem_nhds (literalRows_stop_margin e he t ht))
  refine ⟨j, hj, ?_⟩
  filter_upwards [hrows, hstop] with m hm hs
  apply (mem_innerBoxes e m (j m)).mpr
  constructor
  · have hs' : (qHi m (j m) 0 : ℝ) ≤ 19 / 96 - 4 * (e : ℝ) := by
      rw [qHi_cast]
      exact hs.le
    exact_mod_cast hs'
  · intro k
    exact_mod_cast hm k

open P4AOriginalActualSeed7Slot15
open P4AOriginalAscendingCell0AfterSeed7
open P1OriginalVariableFifthContinuation P1OriginalVariableFourthContinuation
open ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
  (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- The finite box decision is tested on the original retained tree,
and then attached to the actual slot16 constructor. The real sixth
ancestor guard remains the exact unresolved parent supplier. -/
theorem selected_actual_slot16 (hN : 1 < N) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selectedFrontier e m N cap w z
      (actual58Candidate e chi m omega (N : ℝ) rows4 licensed4 J5 rows5))
    (hparent : CurrentParentGuard
      (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix)
      (sixth e chi m omega (N : ℝ) rows4 licensed4 J5 rows5
        (rosserAncestor 6 s.selectedPrefix))) :
    P4AOriginalPrior58Chronology.slot16 (N : ℝ)
      (sixth e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) s.selectedPrefix =
        M (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) := by
  obtain ⟨hlen, _hadmit, hrows, hstop⟩ := selectedFrontier_actual_source e m N cap hN w z
    (actual58Candidate e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) s hs
  exact retainedLiteralCell0_slot16 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5
    s.selectedPrefix ⟨hlen, hstop, hrows, hparent⟩

/-- This local cell0 action has an explicit inherit branch on every
unselected box and every affine equality wall. It is not identified with
the whole14/58/87 action. -/
def localCell0Cap (pre : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
  if pre.length = 8 ∧ boxOwns e m t ∧ CurrentParentGuard t
      (sixth e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 (rosserAncestor 6 pre)) then
    M t
  else P4AOriginalPrior58Chronology.slot15 (N : ℝ)
    (sixth e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) pre


/-- The compiler is a true raise relative to slot15 on its explicitly
licensed domain, and exact inheritance elsewhere. -/
theorem slot15_le_localCell0Cap (pre : List ℕ) :
    P4AOriginalPrior58Chronology.slot15 (N : ℝ)
      (sixth e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) pre ≤
        localCell0Cap e chi m omega N rows4 licensed4 J5 rows5 pre := by
  let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
  by_cases h : pre.length = 8 ∧ boxOwns e m t ∧ CurrentParentGuard t
      (sixth e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 (rosserAncestor 6 pre))
  · have hcopy := h
    obtain ⟨hlen, ⟨j, hj, ht⟩, hp⟩ := hcopy
    have hr := innerBox_literalRows e m j hj t ht
    have hsel : cell0Selected e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 pre :=
      ⟨hlen, literalRows_cellGuard t hr, hp,
        P4AOriginalAscendingCell0Literal96.sourceRows_core t hr⟩
    have heq := chronological_slot16_cell0 e chi m omega (N : ℝ)
      rows4 licensed4 J5 rows5 pre hsel
    have hle := P4AOriginalPrior58Chronology.slot15_le_slot16 (N : ℝ)
      (sixth e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) pre
    rw [heq] at hle
    simpa [localCell0Cap, t, h] using hle
  · simp [localCell0Cap, t, h]

theorem localCell0Cap_on_wall (pre : List ℕ)
    (hwall : affineWall (primeHistoryLogCoordinates (N : ℝ) 8 pre)) :
    localCell0Cap e chi m omega N rows4 licensed4 J5 rows5 pre =
      P4AOriginalPrior58Chronology.slot15 (N : ℝ)
        (sixth e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) pre := by
  have hn := affineWall_not_boxOwns e m _ hwall
  simp [localCell0Cap, hn]

end
end ImbalancedChen.P4AOriginalCell0HalfOpenPrimeCarrier
