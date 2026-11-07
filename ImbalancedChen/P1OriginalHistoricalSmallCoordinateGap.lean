import ImbalancedChen.P1OriginalCoarseFourthJointGeometry
import ImbalancedChen.ActualPrimeBoxOwnCubeResidual

/-!
# P1: original active-third gaps when the fourth/fifth coordinate is small

The original selected third cube and inclusive t2>=omega give a positive
numerator gap.  The fourth gap is in fact greater than omega throughout
its parent region.  The fifth gap is greater than omega-t4, without
requiring t3 to be small.  Only the terminal coordinate is truncated.
This is finite geometry, not a large-s kernel or an actual tail estimate.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open Set

namespace HistoricalThirdCoarse.P1OriginalSmallCoordinate

/-- The original active third cube leaves more than twice the rough
exponent after dividing by the complete three-prime prefix. -/
theorem third_numerator_gap (omega gamma : ℝ) (t : Fin 3 → ℝ)
    (hactive : omega ≤ t 2) (hcube : t 0 + t 1 + 3 * t 2 < gamma) :
    2 * omega < gamma - ∑ i, t i := by
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hsum]
  linarith

/-- The actual fourth ordering yields the stronger omega gap, alongside
the direct 2*omega-t3 inequality. -/
theorem fourth_numerator_gap (omega gamma lambda : ℝ) (t : Fin 4 → ℝ)
    (hactive : omega ≤ t 2) (hcube : t 0 + t 1 + 3 * t 2 < gamma)
    (horder : t 3 < t 2) (hlevel : gamma ≤ lambda) :
    2 * omega - t 3 < lambda - ∑ i, t i ∧ omega < lambda - ∑ i, t i := by
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hsum]
  constructor <;> linarith

/-- At fifth rank the fourth coordinate may stay large.  Its strict order
under the active third coordinate still leaves omega-t4 at both later levels. -/
theorem fifth_numerator_gap (omega gamma lambda : ℝ) (t : Fin 5 → ℝ)
    (hactive : omega ≤ t 2) (hcube : t 0 + t 1 + 3 * t 2 < gamma)
    (horder : t 3 < t 2) (hlevel : gamma ≤ lambda) :
    2 * omega - t 3 - t 4 < lambda - ∑ i, t i ∧
      omega - t 4 < lambda - ∑ i, t i := by
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 + t 4 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hsum]
  constructor <;> linarith

/-- Uniform reciprocal-coordinate lower bound with only the last coordinate
small.  This is also the form needed for canonical large-s kernel bounds. -/
theorem ratio_gt_of_small_denominator (c a numerator last : ℝ)
    (hc : 0 < c) (ha : 0 < a) (hlast : 0 < last) (hsmall : last ≤ a)
    (hnum : c < numerator) : c / a < numerator / last := by
  have hmul : (c / a) * last ≤ c := by
    have h := mul_le_mul_of_nonneg_left hsmall (div_nonneg hc.le ha.le)
    simpa only [div_mul_cancel₀ _ ha.ne'] using h
  apply (lt_div_iff₀ hlast).mpr
  linarith

/-- Both original fourth PLUS legs have s>omega/a at a small terminal
coordinate; raising the level only improves this true numerator gap. -/
theorem fourth_small_last_ratios (omega gamma lambda4 a : ℝ) (t : Fin 4 → ℝ)
    (homega : 0 < omega) (ha : 0 < a) (hlast : 0 < t 3) (hsmall : t 3 ≤ a)
    (hactive : omega ≤ t 2) (hcube : t 0 + t 1 + 3 * t 2 < gamma)
    (horder : t 3 < t 2) (h34 : gamma ≤ lambda4) :
    omega < gamma - ∑ i, t i ∧ omega < lambda4 - ∑ i, t i ∧
      omega / a < (gamma - ∑ i, t i) / t 3 ∧
      omega / a < (lambda4 - ∑ i, t i) / t 3 := by
  have hold := fourth_numerator_gap omega gamma gamma t hactive hcube horder le_rfl
  have hnew := fourth_numerator_gap omega gamma lambda4 t hactive hcube horder h34
  exact ⟨hold.2, hnew.2,
    ratio_gt_of_small_denominator omega a _ _ homega ha hlast hsmall hold.2,
    ratio_gt_of_small_denominator omega a _ _ homega ha hlast hsmall hnew.2⟩

/-- This additional geometric fourth own-cube fact uses a<=omega/2.
It is not inserted as a filter on the actual fourth PLUS source. -/
theorem fourth_small_last_ownCube (omega gamma lambda4 a : ℝ) (t : Fin 4 → ℝ)
    (haomega : a ≤ omega / 2) (hsmall : t 3 ≤ a)
    (hactive : omega ≤ t 2) (hcube : t 0 + t 1 + 3 * t 2 < gamma)
    (horder : t 3 < t 2) (h34 : gamma ≤ lambda4) :
    primeTupleOwnCubeForm t < gamma ∧ primeTupleOwnCubeForm t < lambda4 := by
  have hold := (fourth_numerator_gap omega gamma gamma t hactive hcube horder le_rfl).2
  have hnew := (fourth_numerator_gap omega gamma lambda4 t hactive hcube horder h34).2
  constructor
  · unfold primeTupleOwnCubeForm
    change (∑ i, t i) + 2 * t 3 < gamma
    linarith
  · unfold primeTupleOwnCubeForm
    change (∑ i, t i) + 2 * t 3 < lambda4
    linarith
/-- A small fifth coordinate leaves a uniform omega/2 numerator and forces
both strict own-cube indicators on, at old4 and new5 respectively. -/
theorem fifth_small_last_gates (omega gamma lambda4 lambda5 a : ℝ) (t : Fin 5 → ℝ)
    (homega : 0 < omega) (ha : 0 < a) (haomega : a ≤ omega / 3)
    (hlast : 0 < t 4) (hsmall : t 4 ≤ a)
    (hactive : omega ≤ t 2) (hcube : t 0 + t 1 + 3 * t 2 < gamma)
    (horder : t 3 < t 2) (h34 : gamma ≤ lambda4) (h45 : lambda4 ≤ lambda5) :
    omega - t 4 < lambda4 - ∑ i, t i ∧
      omega - t 4 < lambda5 - ∑ i, t i ∧
      omega / 2 < lambda4 - ∑ i, t i ∧ omega / 2 < lambda5 - ∑ i, t i ∧
      omega / (2 * a) < (lambda4 - ∑ i, t i) / t 4 ∧
      omega / (2 * a) < (lambda5 - ∑ i, t i) / t 4 ∧
      primeTupleOwnCubeForm t < lambda4 ∧ primeTupleOwnCubeForm t < lambda5 := by
  have hold := (fifth_numerator_gap omega gamma lambda4 t hactive hcube horder h34).2
  have hnew := (fifth_numerator_gap omega gamma lambda5 t hactive hcube horder (h34.trans h45)).2
  have holdhalf : omega / 2 < lambda4 - ∑ i, t i := by linarith
  have hnewhalf : omega / 2 < lambda5 - ∑ i, t i := by linarith
  have hratioOld := ratio_gt_of_small_denominator (omega / 2) a _ _
    (by positivity) ha hlast hsmall holdhalf
  have hratioNew := ratio_gt_of_small_denominator (omega / 2) a _ _
    (by positivity) ha hlast hsmall hnewhalf
  have hratioeq : (omega / 2) / a = omega / (2 * a) := by
    field_simp [ha.ne'] <;> ring
  rw [hratioeq] at hratioOld hratioNew
  refine ⟨hold, hnew, holdhalf, hnewhalf, hratioOld, hratioNew, ?_, ?_⟩
  · unfold primeTupleOwnCubeForm
    change (∑ i, t i) + 2 * t 4 < lambda4
    linarith
  · unfold primeTupleOwnCubeForm
    change (∑ i, t i) + 2 * t 4 < lambda5
    linarith

/-- Original first-stop, three cube tests and rough activation remain in
the region hypothesis; the following conclusion uses their actual Gamma. -/
theorem fourth_original_region_gaps (e omega : ℝ) (m : ℕ) (j3 : Cell m)
    (t : Fin 4 → ℝ) (ht : t ∈ P1OriginalFourth.jointRegion e omega m j3)
    (lambda : ℝ) (hlevel : levelExponent e (box m j3) ≤ lambda) :
    2 * omega - t 3 < lambda - ∑ i, t i ∧ omega < lambda - ∑ i, t i := by
  have hg := (P1OriginalFourth.mem_gateRegion _ _ _).mp ht.1.1
  exact fourth_numerator_gap omega (levelExponent e (box m j3)) lambda t
    ht.2 hg.2.2.2 (hg.1 (by decide : (2 : Fin 4) < 3)) hlevel

/-- Oldest four processing coordinates of a real fifth candidate. -/
def prefix4 {α : Type*} (p : Fin 5 → α) : Fin 4 → α :=
  historicalPrefixProject (by omega : 4 ≤ 5) p

theorem prefix4_log (N : ℕ) (p : Fin 5 → ℕ) :
    prefix4 (actualPrimeTupleLog N p) = actualPrimeTupleLog N (prefix4 p) := by rfl

/-- Every real fifth candidate comes from a fully admitted fourth parent;
no old/new fifth own-cube gate is assumed here. -/
theorem fifth_candidate_prefix_admitted (P : Bool → List ℕ → Bool) (carrier : List ℕ)
    (p : Fin 5 → ℕ) (hp : p ∈ firstExitFrontierTuples 4 P carrier) :
    prefix4 p ∈ firstExitAdmittedTuples 4 P carrier := by
  have hparent := (mem_firstExitFrontierTuples_iff 4 P carrier p).mp hp
  have hdrop : List.ofFn (prefix4 p) = (List.ofFn p).dropLast := by
    simp [prefix4, historicalPrefixProject, List.ofFn_succ]
  apply (mem_firstExitAdmittedTuples_iff 4 P carrier (prefix4 p)).mpr
  rw [hdrop]
  exact ⟨(List.dropLast_sublist _).trans hparent.1, hparent.2⟩

/-- Exact integer/logarithmic version of a small terminal prime cutoff. -/
theorem last_log_le_iff_prime_le_rpow {k N : ℕ} (hN : 1 < N)
    (p : Fin (k + 1) → ℕ) (hpos : ∀ i, 0 < p i) (a : ℝ) :
    actualPrimeTupleLog N p (Fin.last k) ≤ a ↔
      (p (Fin.last k) : ℝ) ≤ (N : ℝ) ^ a := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  rw [← actualPrimeTupleLog_rpow hN p hpos (Fin.last k), Real.rpow_le_rpow_left_iff hn]

/-- Inclusive original rough activation is exactly the original natural
prime cutoff, at the same target N. -/
theorem active_third_log_iff_prime_cutoff {N : ℕ} (hN : 1 < N)
    (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i) (omega : ℝ) :
    omega ≤ actualPrimeTupleLog N p 2 ↔ (N : ℝ) ^ omega ≤ (p 2 : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  rw [← actualPrimeTupleLog_rpow hN p hpos 2, Real.rpow_le_rpow_left_iff hn]
/-- Literal original-policy fourth tuples have a uniform old/new positive
gap even if only their terminal coordinate tends to zero. -/
theorem actual_fourth_small_last
    (e chi : ℝ) (m n : ℕ) (omega : ℝ) (homega : 0 < omega)
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) (j3 : Cell m) (hj3 : j3 ∈ cells e chi m)
    (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (ht : actualPrimeTupleLog N p ∈ P1OriginalFourth.jointCell m n j3 j4)
    (hp : p ∈ firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))))
    (a lambda4 : ℝ) (ha : 0 < a) (hsmall : actualPrimeTupleLog N p 3 ≤ a)
    (h34 : levelExponent e (box m j3) ≤ lambda4) :
    omega < levelExponent e (box m j3) - ∑ i, actualPrimeTupleLog N p i ∧
      omega < lambda4 - ∑ i, actualPrimeTupleLog N p i ∧
      omega / a < (levelExponent e (box m j3) - ∑ i, actualPrimeTupleLog N p i) /
        actualPrimeTupleLog N p 3 ∧
      omega / a < (lambda4 - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p 3 := by
  have hd := (P1OriginalFourth.mem_admitted_iff_log_on_selected_jointCell
    e chi m n omega N cap hN hcap p j3 hj3 j4 hwhole ht).mp hp
  have hg := (P1OriginalFourth.mem_gateRegion _ _ _).mp hd.2.1.1
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hp3 : (1 : ℝ) < p 3 := by exact_mod_cast (hd.1 3).1.one_lt
  have ht3 : 0 < actualPrimeTupleLog N p 3 := div_pos (Real.log_pos hp3) (Real.log_pos hn)
  exact fourth_small_last_ratios omega (levelExponent e (box m j3)) lambda4 a
    (actualPrimeTupleLog N p) homega ha ht3 hsmall hd.2.2 hg.2.2.2
    (hg.1 (by decide : (2 : Fin 4) < 3)) h34

/-- Real fifth candidates inherit the original active Gamma gap.  For
terminal log at most a<=omega/3 both actual old/new own-cube tests pass.
The fourth coordinate is not required to be small. -/
theorem actual_fifth_small_last
    (e chi : ℝ) (m n : ℕ) (omega : ℝ) (homega : 0 < omega)
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) (j3 : Cell m) (hj3 : j3 ∈ cells e chi m)
    (j4 : Fin 4 → Fin (n + 1))
    (hwhole : omega ≤ logPrimeMeshLo 0 (19 / 96) m j3 2)
    (ht : actualPrimeTupleLog N (prefix4 p) ∈ P1OriginalFourth.jointCell m n j3 j4)
    (hp : p ∈ firstExitFrontierTuples 4 (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))))
    (a lambda4 lambda5 : ℝ) (ha : 0 < a) (haomega : a ≤ omega / 3)
    (hsmall : actualPrimeTupleLog N p 4 ≤ a)
    (h34 : levelExponent e (box m j3) ≤ lambda4) (h45 : lambda4 ≤ lambda5) :
    omega / 2 < lambda4 - ∑ i, actualPrimeTupleLog N p i ∧
      omega / 2 < lambda5 - ∑ i, actualPrimeTupleLog N p i ∧
      omega / (2 * a) < (lambda4 - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p 4 ∧
      omega / (2 * a) < (lambda5 - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p 4 ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ lambda4 ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ lambda5 := by
  have hparent := fifth_candidate_prefix_admitted _ _ p hp
  have hd := (P1OriginalFourth.mem_admitted_iff_log_on_selected_jointCell
    e chi m n omega N cap hN hcap (prefix4 p) j3 hj3 j4 hwhole ht).mp hparent
  have hg := (P1OriginalFourth.mem_gateRegion _ _ _).mp hd.2.1.1
  have hfront := (mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 4
    (policy e chi m omega (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) hcap p).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hfront.2.1 i).1.pos
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hp4 : (1 : ℝ) < p 4 := by exact_mod_cast (hfront.2.1 4).1.one_lt
  have ht4 : 0 < actualPrimeTupleLog N p 4 := div_pos (Real.log_pos hp4) (Real.log_pos hn)
  have hactive : omega ≤ actualPrimeTupleLog N p 2 := hd.2.2
  have hcube : actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
      3 * actualPrimeTupleLog N p 2 < levelExponent e (box m j3) := hg.2.2.2
  have horder : actualPrimeTupleLog N p 3 < actualPrimeTupleLog N p 2 :=
    hg.1 (by decide : (2 : Fin 4) < 3)
  have h := fifth_small_last_gates omega (levelExponent e (box m j3)) lambda4 lambda5 a
    (actualPrimeTupleLog N p) homega ha haomega ht4 hsmall hactive hcube horder h34 h45
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    (actualPrimeTupleOwnCube_iff hN p hpos lambda4).mpr h.2.2.2.2.2.2.1,
    (actualPrimeTupleOwnCube_iff hN p hpos lambda5).mpr h.2.2.2.2.2.2.2⟩

/-- The proved numerator gaps give real physical quotient lower bounds at
that same target and complete prefix product, with no rounded level. -/
theorem actual_quotient_gt_rpow_of_gap {d N : ℕ} (hN : 1 < N)
    (p : Fin d → ℕ) (hpos : ∀ i, 0 < p i) (lambda c : ℝ)
    (hgap : c < lambda - ∑ i, actualPrimeTupleLog N p i) :
    (N : ℝ) ^ c < (N : ℝ) ^ lambda / (∏ i, p i : ℕ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hquot : (N : ℝ) ^ lambda / (∏ i, p i : ℕ) =
      (N : ℝ) ^ (lambda - ∑ i, actualPrimeTupleLog N p i) := by
    rw [actualPrimeTupleLog_sum_prod p hpos]
    exact (residual_rpow_level_div _ _ _ hn hP).symm
  rw [hquot, Real.rpow_lt_rpow_left_iff hn]
  exact hgap

/-- Actual physical quotient levels preserve the stated old/new exponent
ordering, including all prefix primes in both denominators. -/
theorem actual_quotient_mono_level {d N : ℕ} (hN : 1 < N)
    (p : Fin d → ℕ) (hpos : ∀ i, 0 < p i) (old new : ℝ) (hlevel : old ≤ new) :
    (N : ℝ) ^ old / (∏ i, p i : ℕ) ≤ (N : ℝ) ^ new / (∏ i, p i : ℕ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  exact (div_le_div_iff_of_pos_right hP).mpr
    (Real.rpow_le_rpow_of_exponent_le hn.le hlevel)

end HistoricalThirdCoarse.P1OriginalSmallCoordinate
end
end ImbalancedChen
