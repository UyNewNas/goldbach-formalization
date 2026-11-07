import ImbalancedChen.P5OriginalFeedbackTableKernels

/-!
Literal W1/W2 child profiles on the original positive feedback domains.
SOURCE ONLY. Domain definitions and positive mass estimates are reused
from P5OriginalActionMassBound. Parent alpha is transported, never reset.
-/

namespace ImbalancedChen.P5OriginalFeedbackDomains

noncomputable section

open Set MeasureTheory
open P5OriginalActionMassBound

def singletonProfile (s0 u : ℝ) : ℝ := s0 * (1 - u)
def fixedPairProfile (p : W2Parameters) (x : Point) : ℝ := p.s0 * (1 - x 0 - x 1)
def movingPairProfile (x : Point) : ℝ := (1 - x 0 - x 1) / x 0
def pairProfile (p : W2Parameters) (j : Fin 4) (x : Point) : ℝ :=
  if j.val < 2 then fixedPairProfile p x else movingPairProfile x

theorem measurable_singletonProfile (s0 : ℝ) : Measurable (singletonProfile s0) := by
  exact measurable_const.mul (measurable_const.sub measurable_id)

theorem measurable_pairProfile (p : W2Parameters) (j : Fin 4) : Measurable (pairProfile p j) := by
  unfold pairProfile
  split_ifs
  · exact measurable_const.mul ((measurable_const.sub (measurable_pi_apply 0)).sub
      (measurable_pi_apply 1))
  · exact (((measurable_const.sub (measurable_pi_apply 0)).sub
      (measurable_pi_apply 1)).div (measurable_pi_apply 0))

theorem measurableSet_W2SingletonDomain (p : W2Parameters) (j : Fin 3) :
    MeasurableSet (W2SingletonDomain p j) := by
  fin_cases j <;> exact measurableSet_Ioo

theorem measurableSet_W2PairDomain (p : W2Parameters) (j : Fin 4) :
    MeasurableSet (W2PairDomain p j) := by
  fin_cases j
  · exact W2Pair5_measurable p
  · exact W2Pair6_measurable p
  · exact W2Pair7_measurable p
  · exact W2Pair8_measurable p

theorem W2PairDomain_geometry {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4)
    {x : Point} (hx : x ∈ W2PairDomain p j) :
    x ∈ pairAmbient ∧ (1 / 5 : ℝ) ≤ 1 - x 0 - x 1 := by
  fin_cases j
  · exact W2Pair5_geometry hp hx
  · exact W2Pair6_geometry hp hx
  · exact W2Pair7_geometry hp hx
  · exact W2Pair8_geometry hp hx

/-- All actual full/selected square gates; the bad part of D5 is excluded. -/
theorem W2PairDomain_gates {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4)
    {x : Point} (hx : x ∈ W2PairDomain p j) :
    a0 p < x 0 ∧ x 0 < x 1 ∧ 2 * x 1 < 1 ∧ x 1 + 2 * x 0 < 1 := by
  rcases hp with ⟨h0, h01, h12, h23, h3, hb, hg6, hg7, hg8⟩
  fin_cases j
  · rcases hx with ⟨hu, huv, hv, hgate⟩
    exact ⟨hu, huv, by linarith, hgate⟩
  · rcases hx with ⟨hu, hu', hv, hv'⟩
    exact ⟨hu, by linarith, by linarith, by linarith⟩
  · rcases hx with ⟨hu, huv, hv⟩
    exact ⟨hu, huv, by linarith, by linarith⟩
  · rcases hx with ⟨hu, hu', hv, hv'⟩
    exact ⟨hu, by linarith, by linarith, by linarith⟩

theorem W2_anchor_positive {p : W2Parameters} (hp : W2Geometry p) : 0 < p.s0 := by
  have ha : 0 < 1 / p.s0 := lt_of_lt_of_le (by norm_num) hp.1
  exact one_div_pos.mp ha

theorem W2_anchor_le_five {p : W2Parameters} (hp : W2Geometry p) : p.s0 ≤ 5 := by
  have hs := W2_anchor_positive hp
  have heq : p.s0 * a0 p = 1 := by
    unfold a0
    field_simp [hs.ne']
  have hmul := mul_le_mul_of_nonneg_left hp.1 hs.le
  nlinarith

/-- The exact original pair arguments are in (1,s0-2), without a max-two reset. -/
theorem W2PairDomain_profile_bounds {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4)
    {x : Point} (hx : x ∈ W2PairDomain p j) :
    1 < pairProfile p j x ∧ pairProfile p j x < p.s0 - 2 ∧ p.s0 - 2 ≤ 3 := by
  obtain ⟨hu, huv, _, hgate⟩ := W2PairDomain_gates hp j hx
  have hs := W2_anchor_positive hp
  have ha : 0 < a0 p := lt_of_lt_of_le (by norm_num) hp.1
  have hu0 : 0 < x 0 := ha.trans hu
  have hsa : p.s0 * a0 p = 1 := by unfold a0; field_simp [hs.ne']
  have hsu : 1 < p.s0 * x 0 := by
    have hm := mul_lt_mul_of_pos_left hu hs
    linarith
  have hsv : p.s0 * x 0 < p.s0 * x 1 := mul_lt_mul_of_pos_left huv hs
  have hsr : p.s0 * x 0 < p.s0 * (1 - x 0 - x 1) :=
    mul_lt_mul_of_pos_left (by linarith : x 0 < 1 - x 0 - x 1) hs
  have hlast : p.s0 - 2 ≤ 3 := by linarith [W2_anchor_le_five hp]
  unfold pairProfile
  split_ifs
  · dsimp [fixedPairProfile]
    refine ⟨?_, ?_, hlast⟩
    · nlinarith
    · nlinarith
  · dsimp [movingPairProfile]
    refine ⟨(lt_div_iff₀ hu0).mpr ?_, (div_lt_iff₀ hu0).mpr ?_, hlast⟩ <;> nlinarith

def singletonChildAlpha (alpha u : ℝ) : ℝ := 1 + (alpha - 1) / (1 - u)
def pairChildAlpha (alpha : ℝ) (x : Point) : ℝ :=
  1 + (alpha - 1) / (1 - x 0 - x 1)

/-- The scalar table is evaluated on the first coordinate only; this pair
records the actual marked child supplied to any future count license. -/
def markedSingletonChild (s0 alpha u : ℝ) : ℝ × ℝ :=
  (singletonProfile s0 u, singletonChildAlpha alpha u)

def markedPairChild (p : W2Parameters) (j : Fin 4) (alpha : ℝ) (x : Point) : ℝ × ℝ :=
  (pairProfile p j x, pairChildAlpha alpha x)

theorem singletonChildAlpha_eq_ratio (alpha : ℝ) {u : ℝ} (hu : u ∈ singletonAmbient) :
    singletonChildAlpha alpha u = (alpha - u) / (1 - u) := by
  have hr : 1 - u ≠ 0 := by linarith [hu.2]
  dsimp [singletonChildAlpha]
  field_simp [hr] <;> ring

theorem pairChildAlpha_eq_ratio {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4)
    (alpha : ℝ) {x : Point} (hx : x ∈ W2PairDomain p j) :
    pairChildAlpha alpha x = (alpha - x 0 - x 1) / (1 - x 0 - x 1) := by
  have hg := W2PairDomain_geometry hp j hx
  have hr : 1 - x 0 - x 1 ≠ 0 := by linarith [hg.2]
  dsimp [pairChildAlpha]
  field_simp [hr] <;> ring

theorem alpha_transport_mono {alpha r : ℝ} (ha : 1 ≤ alpha) (hr : 0 < r) (hr1 : r ≤ 1) :
    alpha ≤ 1 + (alpha - 1) / r := by
  have hm := mul_le_mul_of_nonneg_left hr1 (sub_nonneg.mpr ha)
  have hd : alpha - 1 ≤ (alpha - 1) / r :=
    (le_div_iff₀ hr).mpr (by simpa only [mul_one] using hm)
  linarith

/-- The marked singleton child retains its real transported alpha. -/
theorem singletonChildAlpha_ge_parent {alpha u : ℝ} (ha : 2 ≤ alpha)
    (hu : u ∈ singletonAmbient) : alpha ≤ singletonChildAlpha alpha u := by
  apply alpha_transport_mono (by linarith) (by linarith [hu.2])
  linarith [hu.1]

/-- Every original legal pair keeps alpha_child >= alpha >= 2. -/
theorem pairChildAlpha_ge_parent {p : W2Parameters} (hp : W2Geometry p) (j : Fin 4)
    {alpha : ℝ} (ha : 2 ≤ alpha) {x : Point} (hx : x ∈ W2PairDomain p j) :
    alpha ≤ pairChildAlpha alpha x := by
  have hg := W2PairDomain_geometry hp j hx
  have hu : (1 / 5 : ℝ) ≤ x 0 := hg.1.1 0
  have hv : (1 / 5 : ℝ) ≤ x 1 := hg.1.1 1
  apply alpha_transport_mono (by linarith) (lt_of_lt_of_le (by norm_num) hg.2)
  linarith

end
end ImbalancedChen.P5OriginalFeedbackDomains
