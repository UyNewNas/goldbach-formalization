import ImbalancedChen.P2EnhancedLowerFinitePhysicalGraph
import ImbalancedChen.Part5OriginalU34PhysicalCutoffSource
import ImbalancedChen.Part5OriginalU34ClampIntegral
import ImbalancedChen.RenewalFiniteErrorPropagationP5

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original U3/U4 roots of the seed-only430 graph.  The root total level
varies with its physical prime coordinate.  Descendants retain that exact
total; neither a constant root level nor a residual-floor hypothesis is
an input.  The original 70+36 action geometries supply every step bound.
No seed estimate, signed AP estimate, table entry or count licence is proved
or postulated here.  The source graph is not an installed dependency.
-/

namespace ImbalancedChen.Part5OriginalH430PhysicalRoots

noncomputable section
open Set
open scoped BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P5OriginalActionMassBound
open P5OriginalFeedbackDomains
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a floorValue)

inductive Root where
  | U3 | U4
  deriving DecidableEq, Fintype

def rootBand : Root → Set ℝ
  | .U3 => Icc a (1 / 3)
  | .U4 => Icc a (59 / 250)

def sourceResidual : Root → ℝ → ℝ → ℝ
  | .U3, tau, t => U3Residual tau t
  | .U4, _, t => mainResidual t

def sourceRoot (k : Root) (tau t : ℝ) : TypedNode :=
  ⟨true, ⟨(if k = .U3 then 2 else 3), t + sourceResidual k tau t,
    [⟨t, true⟩], t, rootArgument (sourceResidual k tau) t⟩⟩

@[simp] theorem sourceRoot_residual (k : Root) (tau t : ℝ) :
    residual (sourceRoot k tau t).physical = sourceResidual k tau t := by
  simp [sourceRoot, residual, word]

theorem rootBand_subset (k : Root) : rootBand k ⊆ coordinateInterval := by
  cases k with
  | U3 => exact Subset.rfl
  | U4 => intro t ht; exact ⟨ht.1, ht.2.trans (by norm_num)⟩

theorem sourceResidual_bounds {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k) :
    (11 / 192 : ℝ) ≤ sourceResidual k tau t ∧ sourceResidual k tau t ≤ 1 / 2 := by
  have hc := rootBand_subset k ht
  cases k with
  | U3 =>
      have hr := U3Residual_bounds htau htauhi hc
      exact ⟨(by norm_num : (11 / 192 : ℝ) ≤ 1 / 12).trans hr.1, hr.2⟩
  | U4 => exact mainResidual_bounds hc

theorem sourceRoot_argument {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k) :
    (sourceRoot k tau t).physical.argument ∈ Icc (1 : ℝ) 6 := by
  have hc := rootBand_subset k ht
  have harg : rootArgument (sourceResidual k tau) t ∈ Icc (2 : ℝ) 6 := by
    cases k with
    | U3 => exact U3_rootArgument_mem htau htauhi hc
    | U4 => exact rootArgument_mem (fun _ hx => mainResidual_bounds hx) hc
  exact ⟨(by norm_num : (1 : ℝ) ≤ 2).trans harg.1, harg.2⟩

theorem sourceRoot_alpha {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k) :
    2 ≤ alpha (sourceRoot k tau t).physical := by
  have hc := rootBand_subset k ht
  cases k with
  | U3 =>
      simpa [alpha, sourceRoot, word, residual] using U3_alpha_ge_two htau htauhi hc
  | U4 =>
      have hr : 0 < mainResidual t :=
        lt_of_lt_of_le (by norm_num) (mainResidual_bounds hc).1
      have hv : VariableEnvelope.v t ≤ (1 + t) / 2 := by
        rw [VariableEnvelope.v_eq_min]; exact min_le_left _ _
      simp only [alpha, sourceRoot, sourceResidual, word, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, residual]
      apply (le_div_iff₀ (by simpa using hr)).mpr
      dsimp [mainResidual] at *
      linarith

private theorem reciprocal_parameter_bounds {v : ℝ}
    (h : (1 / 5 : ℝ) ≤ 1 / v ∧ 1 / v ≤ 1 / 2) : 2 ≤ v ∧ v ≤ 5 := by
  have hv : 0 < v := one_div_pos.mp (lt_of_lt_of_le (by norm_num) h.1)
  have he : v * (1 / v) = 1 := by field_simp [hv.ne']
  have hlo := mul_le_mul_of_nonneg_left h.1 hv.le
  have hhi := mul_le_mul_of_nonneg_left h.2 hv.le
  constructor <;> nlinarith only [he, hlo, hhi]

private theorem W2_parameters_bounds (j : Fin 36) :
    2 ≤ (originalW2At j).s0 ∧ (originalW2At j).s0 ≤ 5 ∧
    2 ≤ (originalW2At j).phi1 ∧ (originalW2At j).phi1 ≤ 5 := by
  obtain ⟨h0,h01,h12,h23,h3,_⟩ :=
    originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have hs := reciprocal_parameter_bounds ⟨h0, h01.trans (h12.trans (h23.trans h3))⟩
  have hp := reciprocal_parameter_bounds ⟨h0.trans h01, h12.trans (h23.trans h3)⟩
  exact ⟨hs.1, hs.2, hp.1, hp.2⟩

private theorem W1_anchor_bounds (j : Fin 10) : 2 ≤ W1Anchor j ∧ W1Anchor j ≤ 5 := by
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hj9 : (j.val : ℝ) ≤ 9 := by exact_mod_cast (show j.val ≤ 9 by omega)
  dsimp [W1Anchor]
  constructor <;> linarith

/-- Every actual child query, including unclamped H pair queries, remains
in [1,6].  This is distinct from clamping the U3/U4 ROOT at two. -/
theorem perform_argument_bounds {n : PhysicalNode} {s : StepShape} {z : Point}
    (hn : n.argument ∈ Icc (1 : ℝ) 6) (hz : LocalDomain n s z) :
    (perform n s z).argument ∈ Icc (1 : ℝ) 6 := by
  cases s with
  | retain => exact hn
  | transport cell =>
      have h0 : (0 : ℝ) ≤ cell.val := Nat.cast_nonneg _
      have h199 : (cell.val : ℝ) ≤ 199 := by exact_mod_cast (show cell.val ≤ 199 by omega)
      dsimp [perform, compareAt, gridArgument]
      constructor <;> linarith
  | buchstabUpper =>
      have hw := buchstabUpperDomain_subset n.argument hz.2.2
      exact ⟨hw.1, hw.2.trans (by norm_num)⟩
  | buchstabLower =>
      have hw := buchstabLowerDomain_subset hz.2.1 hz.2.2.2
      exact ⟨hw.1, hw.2.trans (by norm_num)⟩
  | w1Fixed i j =>
      have h := W1_anchor_bounds j
      exact ⟨(by norm_num : (1 : ℝ) ≤ 2).trans h.1, h.2.trans (by norm_num)⟩
  | w1Singleton i j =>
      have hu := W1Domain_subset i j hz.2.2.1
      have ha := W1_anchor_bounds j
      change 1 ≤ W1Anchor j * (1 - normalized n z 0) ∧
        W1Anchor j * (1 - normalized n z 0) ≤ 6
      constructor <;> nlinarith [hu.1, hu.2, ha.1, ha.2]
  | w2Fixed j anchor =>
      have h := W2_parameters_bounds j
      cases anchor <;> simp only [perform, compareAt, Bool.false_eq_true, if_false, if_true]
      · exact ⟨(by norm_num : (1 : ℝ) ≤ 2).trans h.2.2.1, h.2.2.2.trans (by norm_num)⟩
      · exact ⟨(by norm_num : (1 : ℝ) ≤ 2).trans h.1, h.2.1.trans (by norm_num)⟩
  | w2Singleton j piece =>
      have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
      have hu := W2SingletonDomain_subset hg piece hz.2.2.1
      have ha := W2_parameters_bounds j
      change 1 ≤ (originalW2At j).s0 * (1 - normalized n z 0) ∧
        (originalW2At j).s0 * (1 - normalized n z 0) ≤ 6
      constructor <;> nlinarith [hu.1, hu.2, ha.1, ha.2.1]
  | w2Pair j piece =>
      have hp := W2PairDomain_profile_bounds
        (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) piece hz.2.2.1
      exact ⟨hp.1.le, (hp.2.1.le.trans hp.2.2).trans (by norm_num)⟩

theorem realize_argument_bounds {lo hi : ℝ} {mesh depth : ℕ} {n : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (hn : n.physical.argument ∈ Icc (1 : ℝ) 6)
    (hz : Member lo hi depth n code z) :
    (realize depth n code z).physical.argument ∈ Icc (1 : ℝ) 6 := by
  induction depth generalizing n with
  | zero => exact hn
  | succ d ih => exact ih (perform_argument_bounds hn hz.2.2.1) hz.2.2.2

def residualFloor : ℝ := (11 / 192) / (101 : ℝ)^440
def leafCutoffFloor : ℝ := residualFloor / 6

theorem residualFloor_pos : 0 < residualFloor := by unfold residualFloor; positivity
theorem leafCutoffFloor_pos : 0 < leafCutoffFloor := by
  exact div_pos residualFloor_pos (by norm_num)

/-- Actual original source floor.  There is no assumed source-floor field. -/
theorem actual430_residual_floor {k : Root} {tau t lo hi : ℝ} {mesh depth : ℕ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k)
    (hd : depth ≤ 440) {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k tau t) code z) :
    residualFloor ≤ residual (realize depth (sourceRoot k tau t) code z).physical := by
  have hp : (101 : ℝ)^depth ≤ (101 : ℝ)^440 :=
    pow_le_pow_right₀ (by norm_num) hd
  have hpow : 0 < (101 : ℝ)^depth := pow_pos (by norm_num) _
  have hr := (sourceResidual_bounds htau htauhi ht).1
  calc
    residualFloor ≤ (11 / 192 : ℝ) / (101 : ℝ)^depth :=
      div_le_div_of_nonneg_left (by norm_num) hpow hp
    _ ≤ residual (sourceRoot k tau t).physical / (101 : ℝ)^depth := by
      rw [sourceRoot_residual]
      exact div_le_div_of_nonneg_right hr hpow.le
    _ ≤ _ := realize_residual_bound hz

/-- A positive fixed physical sieve exponent for every leaf of every
430-round root itinerary, allowing ten extra comparison/leaf levels. -/
theorem actual430_leaf_cutoff_floor {k : Root} {tau t lo hi : ℝ} {mesh depth : ℕ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k)
    (hd : depth ≤ 440) {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k tau t) code z) :
    leafCutoffFloor ≤
      residual (realize depth (sourceRoot k tau t) code z).physical /
        (realize depth (sourceRoot k tau t) code z).physical.argument := by
  have hr := actual430_residual_floor htau htauhi ht hd hz
  have hs := realize_argument_bounds (sourceRoot_argument htau htauhi ht) hz
  have hs0 : 0 < (realize depth (sourceRoot k tau t) code z).physical.argument :=
    zero_lt_one.trans_le hs.1
  calc
    leafCutoffFloor ≤
        residual (realize depth (sourceRoot k tau t) code z).physical / 6 :=
      div_le_div_of_nonneg_right hr (by norm_num)
    _ ≤ _ := div_le_div_of_nonneg_left (residualFloor_pos.le.trans hr) hs0 hs.2

/-- Varying root Q and constant descendant Q are the same stored object. -/
theorem actual430_same_total (k : Root) (tau t : ℝ) {mesh depth : ℕ}
    (code : Program mesh depth) (z : Coordinates depth) :
    (realize depth (sourceRoot k tau t) code z).physical.total =
      t + sourceResidual k tau t := realize_total _ _ _

theorem actual430_same_Q (N : ℕ) (k : Root) (tau t : ℝ) {mesh depth : ℕ}
    (code : Program mesh depth) (z : Coordinates depth) :
    (N : ℝ)^((realize depth (sourceRoot k tau t) code z).physical.total) =
      (N : ℝ)^(t + sourceResidual k tau t) := by rw [actual430_same_total]

theorem U3_root_Q_is_original (N p : ℕ) (tau : ℝ) :
    (N : ℝ)^((sourceRoot .U3 tau (primeCoordinate N p)).physical.total) =
      rowTotalLevel N p (U3Residual tau) := rfl

theorem U4_root_Q_is_original (N p : ℕ) (tau : ℝ) :
    (N : ℝ)^((sourceRoot .U4 tau (primeCoordinate N p)).physical.total) =
      rowTotalLevel N p mainResidual := rfl

/-- The equality stratum is retained, with the exact two adjacent cells. -/
theorem actual_U3_clamp {t : ℝ} (ht : clampStart ≤ t) :
    (sourceRoot .U3 0 t).physical.argument = 2 ∧
    H430 ((sourceRoot .U3 0 t).physical.argument) =
      min (floorValue H430Numerators 49) (floorValue H430Numerators 50) := by
  have h := U3_rootArgument_eq_two_iff.mpr ht
  exact ⟨h, by rw [h]; exact H430_two_eq_adjacent_min⟩

/-- All106, both Buchstab directions and retention have the stated norm.
These are actual integral masses, not a row-norm assumption. -/
theorem actual_transition_norms (a : Original106Action) {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ original106Mass a ∧ original106Mass a ≤ 12 ∧
    buchstabMass (buchstabUpperDomain s) ≤ 12 ∧
    buchstabMass (buchstabLowerDomain s) ≤ 12 ∧ (1 : ℝ) ≤ 12 :=
  ⟨original106Mass_nonneg a, original106Mass_le_twelve a,
    (originalBuchstab_upper_mass_lt_twelve s).le,
    (originalBuchstab_lower_mass_lt_twelve hs).le, by norm_num⟩

theorem actual_root_coefficient_norm :
    (∑ i : Fin 11, |P5RenewalFiniteError.rootCoefficient i|) = (7 / 2 : ℝ) :=
  P5RenewalFiniteError.rootCoefficient_norm

end
end ImbalancedChen.Part5OriginalH430PhysicalRoots
