import ImbalancedChen.HistoricalUnorderedThirdGeometry
import ImbalancedChen.BufferedFirstCubeGeometry
import ImbalancedChen.SelectedPrefixRationalMesh

/-!
# The finite third coarse rule and its literal rough activation

This is a finite, explicitly generated subpolicy of the frozen manuscript's
coarse construction (upper-finite-compact-margin-audit-20261010, lines 62--130).
The adopted cells here are closed, wholly ordered rectangles, owned half-open
on the existing mesh. Cells meeting an ordering wall without being wholly
ordered keep the inherited policy. Coverage and the density cost of those
omitted cells are NOT asserted by this file.

Gamma is the maximum of the actual branch lower endpoints, with the two
nonleading pairs admitted only by their whole-rectangle gate gaps. The W
entry is the rescue max(A,W), not an ungated W action. The transition strip
uses v alone. No numerical integral-certificate endpoint is used as Gamma.

The parameters are introduced in the order e, chi, finite mesh, omega, N.
The table is determined before omega and N. Initial nu, actual lambda and
later ancestor-frozen levels are distinct. No initial <= third comparison
is assumed. Full approximation, auxiliary distribution licensing, fourth/
fifth updates, and the complete manuscript strategy remain separate work.
In particular (C3) and (C5), including the uniform error 4e+6chi, and a
proper-parent/fifth-frontier dictionary for this first-stop policy are NOT
claimed here.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open VariableEnvelope

namespace HistoricalThirdCoarse

/-- Exact whole-rectangle infimum of the complete xz selected-gate gap. -/
def xzGap (b : RationalBox) : ℝ :=
  v ((b.ux : ℝ) + b.uz) - ((b.ux : ℝ) + 2 * b.uy + b.uz)

/-- Exact whole-rectangle infimum of the complete yz selected-gate gap. -/
def yzGap (b : RationalBox) : ℝ :=
  v ((b.uy : ℝ) + b.uz) - (2 * (b.ux : ℝ) + b.uy + b.uz)

theorem xzGap_le {b : RationalBox} {x y z : ℝ} (h : b.InBox x y z) :
    xzGap b ≤ v (x + z) - (x + 2 * y + z) := by
  have ha := min_le_left (A ((b.ux : ℝ) + b.uz)) (C ((b.ux : ℝ) + b.uz))
  have hc := min_le_right (A ((b.ux : ℝ) + b.uz)) (C ((b.ux : ℝ) + b.uz))
  rw [← v_eq_min] at ha hc
  rw [le_sub_iff_add_le, v_eq_min]
  apply le_min <;> dsimp [xzGap, A, C] at * <;>
    linarith [h.2.1, h.2.2.2.1, h.2.2.2.2.2]

theorem yzGap_le {b : RationalBox} {x y z : ℝ} (h : b.InBox x y z) :
    yzGap b ≤ v (y + z) - (2 * x + y + z) := by
  have ha := min_le_left (A ((b.uy : ℝ) + b.uz)) (C ((b.uy : ℝ) + b.uz))
  have hc := min_le_right (A ((b.uy : ℝ) + b.uz)) (C ((b.uy : ℝ) + b.uz))
  rw [← v_eq_min] at ha hc
  rw [le_sub_iff_add_le, v_eq_min]
  apply le_min <;> dsimp [yzGap, A, C] at * <;>
    linarith [h.2.1, h.2.2.2.1, h.2.2.2.2.2]

private theorem upperCorner_mem (b : RationalBox) (hw : b.WellFormed) :
    b.InBox b.ux b.uy b.uz := by
  exact ⟨by exact_mod_cast hw.1, le_rfl, by exact_mod_cast hw.2.1,
    le_rfl, by exact_mod_cast hw.2.2, le_rfl⟩

/-- This is equivalent to testing the entire rectangle, not merely v at a corner. -/
theorem xzGate_iff (e : ℝ) (b : RationalBox) (hw : b.WellFormed) :
    e ≤ xzGap b ↔ ∀ x y z, b.InBox x y z →
      e ≤ v (x + z) - (x + 2 * y + z) := by
  constructor
  · intro he x y z h
    exact he.trans (xzGap_le h)
  · intro h
    exact h b.ux b.uy b.uz (upperCorner_mem b hw)

theorem yzGate_iff (e : ℝ) (b : RationalBox) (hw : b.WellFormed) :
    e ≤ yzGap b ↔ ∀ x y z, b.InBox x y z →
      e ≤ v (y + z) - (2 * x + y + z) := by
  constructor
  · intro he x y z h
    exact he.trans (yzGap_le h)
  · intro h
    exact h b.ux b.uy b.uz (upperCorner_mem b hw)

/-- The rescue lower endpoint is attained at the mixed corner (lx,ly,uz).
It is not permission to apply W without its original gate. -/
def rescue (b : RationalBox) : ℚ := max (qA b.lx) (qB b.uz)

theorem rescue_le {b : RationalBox} {x y z : ℝ} (h : b.InBox x y z) :
    (rescue b : ℝ) ≤ max (A x) (B z) := by
  simp only [rescue, Rat.cast_max, cast_qA, cast_qB]
  apply max_le_max <;> dsimp [A, B] <;> linarith [h.1, h.2.2.2.2.2]

theorem rescue_attained (b : RationalBox) (hw : b.WellFormed) :
    b.InBox b.lx b.ly b.uz ∧
      max (A b.lx) (B b.uz) = (rescue b : ℝ) := by
  refine ⟨⟨le_rfl, by exact_mod_cast hw.1, le_rfl,
    by exact_mod_cast hw.2.1, by exact_mod_cast hw.2.2, le_rfl⟩, ?_⟩
  simp only [rescue, Rat.cast_max, cast_qA, cast_qB]

/-- The interval formula is the infimum, including intervals crossing mu.
This identity also identifies which of the two endpoints attains it. -/
theorem interval_lower_endpoints (l u : ℚ) (h : l ≤ u) :
    qVLo l u = min (qV l) (qV u) := by
  have ha : qA l ≤ qA u := by dsimp [qA]; linarith
  have hc : qC u ≤ qC l := by dsimp [qC]; linarith
  unfold qVLo qV
  apply le_antisymm
  · exact le_min
      (le_min (min_le_left _ _) ((min_le_right _ _).trans hc))
      (le_min ((min_le_left _ _).trans ha) (min_le_right _ _))
  · exact le_min ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _))

theorem interval_lower_iff (c : ℝ) (l u : ℚ) (h : l ≤ u) :
    (∀ t : ℝ, (l : ℝ) ≤ t → t ≤ (u : ℝ) → c ≤ v t) ↔
      c ≤ (qVLo l u : ℝ) := by
  constructor
  · intro ht
    rw [interval_lower_endpoints l u h, Rat.cast_min, cast_qV, cast_qV]
    exact le_min (ht l le_rfl (by exact_mod_cast h))
      (ht u (by exact_mod_cast h) le_rfl)
  · intro hc t hl hu
    exact hc.trans (qVLo_le_v hl hu)

/-- A failed pair contributes only the already present baseline. -/
def fullGamma (e : ℝ) (b : RationalBox) : ℚ :=
  let g0 := qVLo b.lx b.ux
  max g0 (max (qVLo (b.lx + b.ly) (b.ux + b.uy))
    (max (qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz))
      (max (rescue b)
        (max (if e ≤ xzGap b then qVLo (b.lx + b.lz) (b.ux + b.uz) else g0)
          (if e ≤ yzGap b then qVLo (b.ly + b.lz) (b.uy + b.uz) else g0)))))

/-- The full rule is used only wholly below mu-4e; every other box uses v. -/
def gamma (e : ℝ) (b : RationalBox) : ℚ :=
  if (b.ux : ℝ) ≤ mu - 4 * e then fullGamma e b else qVLo b.lx b.ux

def initial (e : ℝ) : ℝ := extendedDistributionCap - 2 * e

def levelExponent (e : ℝ) (b : RationalBox) : ℝ := (gamma e b : ℝ) - 2 * e

theorem baseline_le_fullGamma (e : ℝ) (b : RationalBox) :
    qVLo b.lx b.ux ≤ fullGamma e b := le_max_left _ _

theorem baseline_le_gamma (e : ℝ) (b : RationalBox) :
    qVLo b.lx b.ux ≤ gamma e b := by
  unfold gamma
  split_ifs
  · exact baseline_le_fullGamma e b
  · exact le_rfl

private theorem interval_le_cap {l u : ℚ} (h : l ≤ u) :
    (qVLo l u : ℝ) ≤ cap :=
  (qVLo_le_v (le_refl (l : ℝ)) (by exact_mod_cast h)).trans (v_le_cap _)

/-- Every admitted entry has the manuscript upper ceiling. -/
theorem fullGamma_le_cap (e : ℝ) (b : RationalBox)
    (hw : b.WellFormed) (hz : 0 ≤ b.lz) (hx : (b.lx : ℝ) ≤ mu) :
    (fullGamma e b : ℝ) ≤ cap := by
  have h0 := interval_le_cap hw.1
  have hxy := interval_le_cap (add_le_add hw.1 hw.2.1)
  have hxyz := interval_le_cap (add_le_add (add_le_add hw.1 hw.2.1) hw.2.2)
  have hxz := interval_le_cap (add_le_add hw.1 hw.2.2)
  have hyz := interval_le_cap (add_le_add hw.2.1 hw.2.2)
  have huz : (0 : ℝ) ≤ b.uz := by exact_mod_cast hz.trans hw.2.2
  have hr : (rescue b : ℝ) ≤ cap := by
    simp only [rescue, Rat.cast_max, cast_qA, cast_qB]
    apply max_le <;> dsimp [A, B, mu, cap] at * <;> linarith
  unfold fullGamma
  simp only [Rat.cast_max, apply_ite, max_le_iff]
  refine ⟨h0, hxy, hxyz, hr, ?_, ?_⟩
  · split_ifs <;> assumption
  · split_ifs <;> assumption

theorem gamma_le_cap (e : ℝ) (b : RationalBox) (he : 0 ≤ e)
    (hw : b.WellFormed) (hz : 0 ≤ b.lz) : (gamma e b : ℝ) ≤ cap := by
  unfold gamma
  split_ifs with hx
  · apply fullGamma_le_cap e b hw hz
    have hl : (b.lx : ℝ) ≤ b.ux := by exact_mod_cast hw.1
    linarith
  · exact interval_le_cap hw.1

theorem fullGamma_le_original (e : ℝ) (b : RationalBox) {x y z : ℝ}
    (ht : b.InBox x y z) (ho : Ordered x y z) :
    (fullGamma e b : ℝ) ≤ original x y z := by
  have h0 := qVLo_le_v ht.1 ht.2.1
  have hxy : (qVLo (b.lx + b.ly) (b.ux + b.uy) : ℝ) ≤ v (x + y) := by
    apply qVLo_le_v <;> push_cast <;> linarith [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1]
  have hxyz : (qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz) : ℝ) ≤
      v (x + y + z) := by
    apply qVLo_le_v <;> push_cast <;>
      linarith [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2]
  have hxz : (qVLo (b.lx + b.lz) (b.ux + b.uz) : ℝ) ≤ v (x + z) := by
    apply qVLo_le_v <;> push_cast <;> linarith [ht.1, ht.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2]
  have hyz : (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) ≤ v (y + z) := by
    apply qVLo_le_v <;> push_cast <;>
      linarith [ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2]
  have hs0 := v_le_six x y z
  have hsxy : v (x + y) ≤ six x y z := by simp [six]
  have hsxyz : v (x + y + z) ≤ six x y z := by simp [six]
  have hsxz : v (x + z) ≤ six x y z := by simp [six]
  have hsyz : v (y + z) ≤ six x y z := by simp [six]
  have hr : (rescue b : ℝ) ≤ six x y z := by
    apply (rescue_le ht).trans
    rw [← v_eq_A ho.2.2.2]
    exact max_le hs0 (B_le_six x y z)
  rw [original_eq_six ho]
  unfold fullGamma
  simp only [Rat.cast_max, apply_ite, max_le_iff]
  refine ⟨h0.trans hs0, hxy.trans hsxy, hxyz.trans hsxyz, hr, ?_, ?_⟩
  · split_ifs
    · exact hxz.trans hsxz
    · exact h0.trans hs0
  · split_ifs
    · exact hyz.trans hsyz
    · exact h0.trans hs0

/-- Actual extended endpoint, before the finite mesh approximation loss. -/
def endpoint (x y z : ℝ) : ℝ := if x ≤ mu then original x y z else v x

theorem gamma_le_endpoint (e : ℝ) (b : RationalBox) (he : 0 ≤ e)
    {x y z : ℝ} (ht : b.InBox x y z)
    (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    (gamma e b : ℝ) ≤ endpoint x y z := by
  unfold gamma
  split_ifs with hfull
  · have hx : x ≤ mu := by linarith [ht.2.1]
    rw [endpoint, if_pos hx]
    exact fullGamma_le_original e b ht ⟨hz, hzy, hyx, hx⟩
  · have hb := qVLo_le_v ht.1 ht.2.1
    unfold endpoint
    split_ifs with hx
    · exact hb.trans (v_le_original ⟨hz, hzy, hyx, hx⟩)
    · exact hb

/-- In particular the initial level is strictly above this third cap.
This does not assert any comparison between later selected caps. -/
theorem levelExponent_lt_initial (e : ℝ) (b : RationalBox) (he : 0 ≤ e)
    (hw : b.WellFormed) (hz : 0 ≤ b.lz) : levelExponent e b < initial e := by
  have hg := gamma_le_cap e b he hw hz
  dsimp [levelExponent, initial, extendedDistributionCap, cap] at *
  linarith

/-- The baseline alone pays the strict first cube, for this actual Gamma.
No global Gamma approximation estimate is assumed. -/
theorem first_cube_margin (e chi : ℝ) (b : RationalBox)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100)
    (hchi : chi < e / 10) (hwidth : (b.width : ℝ) ≤ chi)
    {x y z : ℝ} (ht : b.InBox x y z)
    (hstop : (b.ux : ℝ) ≤ extendedFirstStop - 4 * e) :
    3 * x < levelExponent e b := by
  have hside : (b.ux : ℝ) - b.lx ≤ b.width := by
    exact_mod_cast b.coordinate_widths_le.1
  have hb := rationalInterval_buffered_first_cube he (by linarith) ht.1 ht.2.1
    hstop (by linarith : (3 / 2 : ℝ) * ((b.ux : ℝ) - b.lx) ≤ e)
  have hbase : (qVLo b.lx b.ux : ℝ) ≤ gamma e b := by
    exact_mod_cast baseline_le_gamma e b
  have hm : 3 * x < (qVLo b.lx b.ux : ℝ) - 2 * e :=
    hb.trans_le (min_le_right _ _)
  dsimp [levelExponent]
  linarith

theorem first_prime_cube (e chi : ℝ) (b : RationalBox)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100)
    (hchi : chi < e / 10) (hwidth : (b.width : ℝ) ≤ chi)
    {x y z N : ℝ} (ht : b.InBox x y z)
    (hstop : (b.ux : ℝ) ≤ extendedFirstStop - 4 * e)
    (p : ℕ) (hN : 1 < N) (hp : (p : ℝ) ≤ N ^ x) :
    (p : ℝ) ^ 3 < N ^ levelExponent e b :=
  first_cube_lt_level_of_exponent p hN hp
    (first_cube_margin e chi b he hesmall hchi hwidth ht hstop)

/-- This finite label set and every stored Gamma are fixed before omega and N. -/
abbrev Cell (m : ℕ) := Fin 3 → Fin (m + 1)

def box (m : ℕ) (j : Cell m) : RationalBox where
  lx := qLogPrimeMeshLo 0 (19 / 96) m j 0
  ux := qLogPrimeMeshHi 0 (19 / 96) m j 0
  ly := qLogPrimeMeshLo 0 (19 / 96) m j 1
  uy := qLogPrimeMeshHi 0 (19 / 96) m j 1
  lz := qLogPrimeMeshLo 0 (19 / 96) m j 2
  uz := qLogPrimeMeshHi 0 (19 / 96) m j 2

/-- Only wholly ordered closed rectangles are adopted in this increment.
In particular this does not claim coverage of cells crossing an order wall. -/
def cells (e chi : ℝ) (m : ℕ) : Finset (Cell m) :=
  Finset.univ.filter fun j =>
    let b := box m j
    b.WellFormed ∧ 0 ≤ b.lz ∧ b.uz ≤ b.ly ∧ b.uy ≤ b.lx ∧
      (b.ux : ℝ) ≤ extendedFirstStop - 4 * e ∧ (b.width : ℝ) ≤ chi

theorem mem_cells (e chi : ℝ) (m : ℕ) (j : Cell m) :
    j ∈ cells e chi m ↔
      (box m j).WellFormed ∧ 0 ≤ (box m j).lz ∧
        (box m j).uz ≤ (box m j).ly ∧ (box m j).uy ≤ (box m j).lx ∧
        ((box m j).ux : ℝ) ≤ extendedFirstStop - 4 * e ∧
        ((box m j).width : ℝ) ≤ chi := by
  simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and]

theorem inBox_of_cell {m : ℕ} {j : Cell m} {t : Fin 3 → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    (box m j).InBox (t 0) (t 1) (t 2) := by
  have hl (i : Fin 3) : (qLogPrimeMeshLo 0 (19 / 96) m j i : ℝ) ≤ t i := by
    rw [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).1
  have hu (i : Fin 3) : t i ≤ (qLogPrimeMeshHi 0 (19 / 96) m j i : ℝ) := by
    rw [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).2.le
  exact ⟨hl 0, hu 0, hl 1, hu 1, hl 2, hu 2⟩

/-- The finite lookup stores Gamma; the common 2e loss is subtracted once.
This permits real e without pretending the buffered cap itself is rational. -/
def exponent (e chi : ℝ) (m : ℕ) (t : Fin 3 → ℝ) : ℝ :=
  (historicalPrefixLookup 0 (19 / 96) m (cells e chi m)
    (fun j => gamma e (box m j)) (299 / 500) t : ℝ) - 2 * e

theorem exponent_on_cell (e chi : ℝ) (m : ℕ) (t : Fin 3 → ℝ)
    (j : Cell m) (hj : j ∈ cells e chi m)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    exponent e chi m t = levelExponent e (box m j) := by
  unfold exponent levelExponent
  rw [historicalPrefixLookup_on_cell 0 (19 / 96) (by norm_num) m
    (cells e chi m) _ (299 / 500) t j hj ht]

theorem exponent_outside (e chi : ℝ) (m : ℕ) (t : Fin 3 → ℝ)
    (ht : ∀ j ∈ cells e chi m, t ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    exponent e chi m t = initial e := by
  unfold exponent
  rw [historicalPrefixLookup_outside 0 (19 / 96) m (cells e chi m) _ _ t ht]
  norm_num [initial, extendedDistributionCap]

/-- Literal natural-prime rough test at rank three, with equality active. -/
def active (omega N : ℝ) (history : List ℕ) : Prop :=
  history.length = 3 ∧ N ^ omega ≤ (primeHistoryTuple 3 history 2 : ℝ)

def rawLevel (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) : ℝ :=
  if active omega N history then
    N ^ exponent e chi m (primeHistoryLogCoordinates N 3 history)
  else N ^ initial e

def frozenLevel (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) : ℝ :=
  rawLevel e chi m omega N (rosserAncestor 3 history)

theorem active_triple (omega N : ℝ) (p1 p2 p3 : ℕ) :
    active omega N [p3, p2, p1] ↔ N ^ omega ≤ (p3 : ℝ) := by
  simp [active, primeHistoryTuple]

theorem rawLevel_on_cell (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) (ha : active omega N history) (j : Cell m)
    (hj : j ∈ cells e chi m)
    (ht : primeHistoryLogCoordinates N 3 history ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    rawLevel e chi m omega N history = N ^ levelExponent e (box m j) := by
  rw [rawLevel, if_pos ha, exponent_on_cell e chi m _ j hj ht]

theorem rawLevel_triple_on_cell (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p1 p2 p3 : ℕ) (hrough : N ^ omega ≤ (p3 : ℝ)) (j : Cell m)
    (hj : j ∈ cells e chi m)
    (ht : primeHistoryLogCoordinates N 3 [p3, p2, p1] ∈
      logPrimeMeshCell 0 (19 / 96) m j) :
    rawLevel e chi m omega N [p3, p2, p1] = N ^ levelExponent e (box m j) :=
  rawLevel_on_cell e chi m omega N _
    ((active_triple omega N p1 p2 p3).mpr hrough) j hj ht

theorem rawLevel_inactive (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) (ha : ¬active omega N history) :
    rawLevel e chi m omega N history = N ^ initial e := if_neg ha

theorem rawLevel_small_third (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p1 p2 p3 : ℕ) (hp : (p3 : ℝ) < N ^ omega) :
    rawLevel e chi m omega N [p3, p2, p1] = N ^ initial e := by
  apply rawLevel_inactive
  rw [active_triple]
  exact not_le.mpr hp

theorem rawLevel_outside (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ)
    (ht : ∀ j ∈ cells e chi m, primeHistoryLogCoordinates N 3 history ∉
      logPrimeMeshCell 0 (19 / 96) m j) :
    rawLevel e chi m omega N history = N ^ initial e := by
  unfold rawLevel
  split_ifs
  · rw [exponent_outside e chi m _ ht]
  · rfl

/-- A local drop calculation avoids importing the older broad analytic carrier. -/
private theorem ancestor_append (later history : List ℕ) (hlen : 3 ≤ history.length) :
    rosserAncestor 3 (later ++ history) = rosserAncestor 3 history := by
  induction later with
  | nil => rfl
  | cons q later ih =>
      have hi : (q :: (later ++ history)).length - 3 =
          (later ++ history).length - 3 + 1 := by
        simp only [List.length_cons, List.length_append]
        omega
      have ha : rosserAncestor 3 (q :: (later ++ history)) =
          rosserAncestor 3 (later ++ history) := by
        unfold rosserAncestor
        rw [hi, List.drop_succ_cons]
      simpa only [List.cons_append, ha] using ih

theorem frozenLevel_append (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (later history : List ℕ) (hlen : 3 ≤ history.length) :
    frozenLevel e chi m omega N (later ++ history) =
      frozenLevel e chi m omega N history := by
  unfold frozenLevel
  rw [ancestor_append later history hlen]

theorem frozenActive_append (omega N : ℝ) (later history : List ℕ)
    (hlen : 3 ≤ history.length) :
    active omega N (rosserAncestor 3 (later ++ history)) ↔
      active omega N (rosserAncestor 3 history) := by
  rw [ancestor_append later history hlen]

/-- The first coarse-label upper endpoint, not just the prime itself, is stopped. -/
def firstStop (e : ℝ) (m : ℕ) (N : ℝ) (history : List ℕ) : Prop :=
  ∃ i : Fin (m + 1),
    logPrimeMeshPoint 0 (19 / 96) m i.val ≤ primeHistoryLogCoordinates N 1 history 0 ∧
    primeHistoryLogCoordinates N 1 history 0 < logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ∧
    logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤ extendedFirstStop - 4 * e

/-- A selected third cell identifies the already retained first coarse label.
The half-open ownership and the closed upper-endpoint stop are both retained. -/
theorem firstStop_of_triple_cell (e chi : ℝ) (m : ℕ) (N : ℝ)
    (p1 p2 p3 : ℕ) (j : Cell m) (hj : j ∈ cells e chi m)
    (ht : primeHistoryLogCoordinates N 3 [p3, p2, p1] ∈
      logPrimeMeshCell 0 (19 / 96) m j) :
    firstStop e m N [p1] := by
  have h0 := mem_logPrimeMeshCell.mp ht (0 : Fin 3)
  have hc : primeHistoryLogCoordinates N 1 [p1] 0 =
      primeHistoryLogCoordinates N 3 [p3, p2, p1] 0 := by
    simp [primeHistoryLogCoordinates, primeHistoryTuple]
  have hs := ((mem_cells e chi m j).mp hj).2.2.2.2.1
  refine ⟨j 0, ?_, ?_, ?_⟩
  · simpa only [hc, logPrimeMeshLo] using h0.1
  · simpa only [hc, logPrimeMeshHi] using h0.2
  · simpa [box, qLogPrimeMeshHi] using hs

/-- Selected-cell geometry supplies the strict first cube at the actual
rough-activated level, rather than assuming it as a cap-table field. -/
theorem rawLevel_first_cube_on_cell (e chi : ℝ)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100) (hchi : chi < e / 10)
    (m : ℕ) (omega N : ℝ) (hN : 1 < N)
    (p1 p2 p3 : ℕ) (hp1 : 0 < p1) (hrough : N ^ omega ≤ (p3 : ℝ))
    (j : Cell m) (hj : j ∈ cells e chi m)
    (ht : primeHistoryLogCoordinates N 3 [p3, p2, p1] ∈
      logPrimeMeshCell 0 (19 / 96) m j) :
    (p1 : ℝ) ^ 3 < rawLevel e chi m omega N [p3, p2, p1] := by
  rw [rawLevel_triple_on_cell e chi m omega N p1 p2 p3 hrough j hj ht]
  have hs := (mem_cells e chi m j).mp hj
  have hp : N ^ primeHistoryLogCoordinates N 3 [p3, p2, p1] 0 = (p1 : ℝ) := by
    apply (Real.mul_log_eq_log_iff (zero_lt_one.trans hN) (by exact_mod_cast hp1)).mp
    simpa [primeHistoryLogCoordinates, primeHistoryTuple] using
      (div_mul_cancel₀ (Real.log (p1 : ℝ)) (Real.log_pos hN).ne')
  exact first_prime_cube e chi (box m j) he hesmall hchi hs.2.2.2.2.2
    (inBox_of_cell ht) hs.2.2.2.2.1 p1 hN hp.ge

/-- The original initial policy includes the first-label stop. -/
def initialPolicy (e : ℝ) (m : ℕ) (N : ℝ) : Bool → List ℕ → Bool :=
  oddFirstExitPolicy fun history => decide
    (ordinaryRosserPrefixAdmissible false (N ^ initial e) history ∧
      (history.length = 1 → firstStop e m N history))

def policy (e chi : ℝ) (m : ℕ) (omega N : ℝ) : Bool → List ℕ → Bool :=
  thirdCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N)

theorem policy_through_two (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ) (hlen : history.length ≤ 2) :
    policy e chi m omega N positive history = initialPolicy e m N positive history := by
  simp only [policy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy, if_pos hlen]

theorem policy_even (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) :
    policy e chi m omega N true history = true := by
  simp [policy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy, initialPolicy,
    frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
    oddFirstExitPolicy]

/-- Above rank two, an inactive ancestor restores the original initial policy. -/
theorem policy_inactive (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ)
    (ha : ¬active omega N (rosserAncestor 3 history)) :
    policy e chi m omega N positive history = initialPolicy e m N positive history := by
  by_cases hlen : history.length ≤ 2
  · exact policy_through_two e chi m omega N positive history hlen
  · have hne : history.length ≠ 1 := by omega
    simp [policy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy, hlen,
      frozenParityRosserPolicy, ancestorFrozenPolicy, rawLevel_inactive e chi m omega N _ ha,
      ordinaryParityRosserPolicy, initialPolicy, oddFirstExitPolicy, hne]

/-- The actual third test keeps its own first cube and third cube strictly.
The initial first-cube test was already paid at rank one, at its distinct level. -/
theorem policy_third_iff (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p1 p2 p3 : ℕ) (h3 : 0 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
    policy e chi m omega N false [p3, p2, p1] = true ↔
      (p1 : ℝ) ^ 3 < rawLevel e chi m omega N [p3, p2, p1] ∧
      (p1 : ℝ) * p2 * p3 ^ 3 < rawLevel e chi m omega N [p3, p2, p1] := by
  have htest : policy e chi m omega N false [p3, p2, p1] = true ↔
      ordinaryRosserPrefixAdmissible false
        (rawLevel e chi m omega N [p3, p2, p1]) [p3, p2, p1] := by
    simp [policy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
      frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
      oddFirstExitPolicy, rosserAncestor]
  exact htest.trans (historicalUnorderedThird_admissible_iff _ p1 p2 p3 h3 h32 h21)

end HistoricalThirdCoarse

end

end ImbalancedChen
