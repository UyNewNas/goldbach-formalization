import ImbalancedChen.Part5OriginalH430IntegerItineraries
import ImbalancedChen.Part5OriginalH430FrozenRootRefinement
import ImbalancedChen.P2OriginalPositiveSameQMassLift

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original U3/U4 frozen root, evaluated on an actual root prime, is
realized along integer prime coordinates. Its same-Q residual dictionary,
parentWindow, positive residual floor and genuine alpha are DERIVED.
The Member hypothesis is retained literally; this does not prove that the
selected count interpreter enumerates exactly these histories.
-/
namespace ImbalancedChen.Part5OriginalH430FrozenIntegerSupport

noncomputable section
open Set
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430IntegerItineraries
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement

/-- Lowering the root total preserves the actual alpha inequality.
The enhanced/classical split and the max-two query are not changed. -/
theorem frozenRoot_alpha {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (ht : t ∈ rootBand k)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    2 ≤ alpha (frozenRoot n k tau t).physical := by
  have hs := sourceResidual_bounds htau htauhi ht
  have hs0 : 0 < sourceResidual k tau t := (by norm_num : (0:ℝ) < 11/192).trans_le hs.1
  have hsrc : 2 ≤ (1-t)/sourceResidual k tau t := by
    simpa [alpha, sourceRoot, residual, word] using sourceRoot_alpha htau htauhi ht
  have hnum := (le_div_iff₀ hs0).mp hsrc
  have hf := frozenRoot_residual_bounds htau htauhi ht hn
  have hf0 : 0 < residual (frozenRoot n k tau t).physical :=
    (by norm_num : (0:ℝ) < 11/384).trans_le hf.1
  have hl := (frozenLevel_bounds (root_total_bounds htau htauhi ht) n).1
  have hr : residual (frozenRoot n k tau t).physical ≤ sourceResidual k tau t := by
    rw [frozenRoot_residual]
    change frozenLevel n (t+sourceResidual k tau t) ≤ t+sourceResidual k tau t at hl
    linarith
  have hw : (word (frozenRoot n k tau t).physical).sum = t := by
    simp [word, frozenRoot, sourceRoot]
  rw [alpha, hw]
  apply (le_div_iff₀ hf0).mpr
  linarith

theorem frozenResidualFloor_pos : 0 < frozenResidualFloor := by
  unfold frozenResidualFloor
  positivity

/-- Export the residual-floor deduction already used inside the old
leaf-cutoff proof, so arithmetic row consumers can use the residual itself. -/
theorem frozen_history_residual_floor {n : ℕ} {k : Root} {tau t lo hi : ℝ}
    {mesh depth : ℕ} (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (ht : t ∈ rootBand k) (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (hd : depth ≤ 440) {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    frozenResidualFloor ≤ residual (realize depth (frozenRoot n k tau t) code z).physical := by
  have hr := (frozenRoot_residual_bounds htau htauhi ht hn).1
  have hp : (101:ℝ)^depth ≤ (101:ℝ)^440 := pow_le_pow_right₀ (by norm_num) hd
  have hd0 : 0 < (101:ℝ)^depth := pow_pos (by norm_num) _
  calc
    frozenResidualFloor ≤ (11/384:ℝ)/(101:ℝ)^depth :=
      div_le_div_of_nonneg_left (by norm_num) hd0 hp
    _ ≤ residual (frozenRoot n k tau t).physical/(101:ℝ)^depth :=
      div_le_div_of_nonneg_right hr hd0.le
    _ ≤ _ := realize_residual_bound hz

/-- The exact level frozen from the original physical root, NOT a new
level inferred from the last child or optimized after the history. -/
def rootLevel (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) : ℝ :=
  frozenLevel n (sourceRoot k tau (physicalPrime N p)).physical.total

def rootQ (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) : ℝ :=
  (N:ℝ)^(rootLevel N n k tau p)

def historyNode (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ)
    {mesh depth : ℕ} (code : Program mesh depth) (q : IntegerCoordinates depth) : TypedNode :=
  realize depth (frozenRoot n k tau (physicalPrime N p)) code (physicalCoordinates N q)

def historyWord (p : ℕ) {mesh depth : ℕ} (code : Program mesh depth)
    (q : IntegerCoordinates depth) : List ℕ := integerWord depth [p] code q

theorem history_word_dictionary (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ)
    {mesh depth : ℕ} (code : Program mesh depth) (q : IntegerCoordinates depth) :
    word (historyNode N n k tau p code q).physical =
      (historyWord p code q).map (physicalPrime N) := by
  apply realize_word
  simp [word, frozenRoot, sourceRoot]

theorem history_total (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ)
    {mesh depth : ℕ} (code : Program mesh depth) (q : IntegerCoordinates depth) :
    (historyNode N n k tau p code q).physical.total = rootLevel N n k tau p :=
  realize_total _ _ _

theorem history_selected (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ)
    {mesh depth : ℕ} (code : Program mesh depth) (q : IntegerCoordinates depth) :
    selectedWord (historyNode N n k tau p code q).physical.slots = [physicalPrime N p] := by
  rw [historyNode, realize_selected]
  simp [frozenRoot, sourceRoot, selectedWord]

/-- Concrete roots and actual integer coordinates supply all geometric
inputs of the local row theorem except the NEXT action's admission test.
No count licence, limit, coefficient error, or final h34 premise occurs. -/
theorem history_support {N n mesh depth : ℕ} {k : Root} {tau lo hi : ℝ}
    {p : ℕ} {code : Program mesh depth} {q : IntegerCoordinates depth}
    (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hd : depth ≤ 440)
    (hp : p.Prime ∧ p.Coprime N) (ht : physicalPrime N p ∈ rootBand k)
    (hq : PrimeLetters N code q)
    (hz : Member lo hi depth (frozenRoot n k tau (physicalPrime N p))
      code (physicalCoordinates N q)) :
    let v := (historyNode N n k tau p code q).physical
    let old := historyWord p code q
    let Q := rootQ N n k tau p
    parentWindow N Q old v.ceiling ∧
    residual v = physicalLevel N Q old ∧
    frozenResidualFloor ≤ physicalLevel N Q old ∧
    v.argument ∈ Icc (1:ℝ) 6 ∧
    2 ≤ P2OriginalChildPhysicalNormalization.alpha
      (Real.log (parentProduct old:ℝ)/Real.log (N:ℝ)) (physicalLevel N Q old) ∧
    Q = (parentProduct old:ℝ)*(N:ℝ)^(physicalLevel N Q old) := by
  dsimp only
  let v := (historyNode N n k tau p code q).physical
  let old := historyWord p code q
  let Q := rootQ N n k tau p
  have hold : ∀ r ∈ old, r.Prime ∧ r.Coprime N := by
    apply integerWord_letters [p] code q
    · intro r hr
      have he : r = p := List.mem_singleton.mp hr
      subst r
      exact hp
    · exact hq
  have holdpos : ∀ r ∈ old, 0 < r := fun r hr => (hold r hr).1.pos
  have hw : word v = old.map (physicalPrime N) := history_word_dictionary N n k tau p code q
  have htotal : v.total = rootLevel N n k tau p := history_total N n k tau p code q
  have hlevel : rootLevel N n k tau p ≤ 1 :=
    (frozenLevel_bounds (root_total_bounds htau htauhi ht) n).1.trans
      (root_total_bounds htau htauhi ht).2
  have hfloor : frozenResidualFloor ≤ residual v :=
    frozen_history_residual_floor htau htauhi ht hn hd hz
  have hpos := frozenResidualFloor_pos.trans_le hfloor
  have hc : 0 < v.ceiling := by
    apply realize_ceiling_pos (n := frozenRoot n k tau (physicalPrime N p)) _ hz
    change 0 < physicalPrime N p
    exact div_pos (Real.log_pos (by exact_mod_cast hp.1.one_lt))
      (Real.log_pos (by exact_mod_cast hN))
  have hwindow : parentWindow N Q old v.ceiling :=
    parentWindow_of_realization hN htotal hlevel hw holdpos hpos hc
  have hres : residual v = physicalLevel N Q old :=
    residual_eq_physicalLevel hN htotal hw holdpos
  have harg : v.argument ∈ Icc (1:ℝ) 6 :=
    realize_argument_bounds (frozenRoot_argument_bounds htau htauhi ht hn) hz
  have hrootA := frozenRoot_alpha htau htauhi ht hn
  have hA : 2 ≤ alpha v := hrootA.trans (realize_alpha_mono hrootA hz)
  have hAeq : alpha v = P2OriginalChildPhysicalNormalization.alpha
      (Real.log (parentProduct old:ℝ)/Real.log (N:ℝ)) (physicalLevel N Q old) := by
    rw [alpha, hw, sum_physicalPrime N holdpos, hres]
    rfl
  have hQ : Q = (parentProduct old:ℝ)*(N:ℝ)^(physicalLevel N Q old) := by
    simpa only [P2OriginalPositiveSameQMassLift.residualExponent,
      physicalLevel, residualLevel] using
      P2OriginalPositiveSameQMassLift.sameQ_eq_residualExponent hN hwindow.2.1
        (zero_lt_one.trans (parentWindow_logs hwindow).2.1)
  exact ⟨hwindow, hres, hres ▸ hfloor, harg, hAeq ▸ hA, hQ⟩

end
end ImbalancedChen.Part5OriginalH430FrozenIntegerSupport
