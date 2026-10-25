import ImbalancedChen.Part3Gamma0QuotientCellPushforward
import ImbalancedChen.Part3Gamma0FiniteCarrierExactMeasure
import ImbalancedChen.Part3Gamma0ActualCusps

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The natural map from the ACTUAL Gamma0(N) orbit quotient to the full
modular orbit quotient pushes the canonical carrier measure to the
actual subgroup index times the canonical modular measure. Level one
is proved to be the full integral modular group. Each actual coset cell
is transported separately; the previously proved null-overlap theorem
then gives exact finite additivity. No cover-measure, covolume, index
multiplier, measure-preserving map, or quotient-FD premise is supplied.
-/

namespace ImbalancedChen.Part3.Gamma0ModularFiniteCoverMeasure20261025a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open Gamma0QuotientCellPushforward20261025a
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0FiniteCarrierExactMeasure20261024zz
open ModularFundamentalFiniteMeasure20261024z
open Gamma0ActualCuspsSourceOnly

theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = (⊤ : Subgroup SL(2, ℤ)) := by
  ext g
  simp [gamma0_mem_iff_level_dvd_c]

theorem gamma0_one_index : (CongruenceSubgroup.Gamma0 1).index = 1 := by
  rw [gamma0_one_eq_top, Subgroup.index_top]

/-- An actual integral matrix, considered as an actual level-one matrix. -/
def levelOneMatrix (g : SL(2, ℤ)) : CongruenceSubgroup.Gamma0 1 :=
  ⟨g, by rw [gamma0_mem_iff_level_dvd_c]; simp⟩

/-- Forget the level without changing the upper-half-plane point. The
codomain is precisely the full integral modular orbit quotient. -/
def forgetLevel (N : ℕ) : Gamma0OrbitSpace N → Gamma0OrbitSpace 1 :=
  Quotient.lift (orbitProjection 1) (by
    intro z w hzw
    apply Quotient.sound
    obtain ⟨g, hg⟩ := (MulAction.orbitRel_apply).mp hzw
    exact (MulAction.orbitRel_apply).mpr ⟨levelOneMatrix (g : SL(2, ℤ)), hg⟩)

@[simp] theorem forgetLevel_projection (N : ℕ) (z : UpperHalfPlane) :
    forgetLevel N (orbitProjection N z) = orbitProjection 1 z := rfl

theorem forgetLevel_measurable (N : ℕ) : Measurable (forgetLevel N) := by
  apply measurable_from_quotient.mpr
  exact orbitProjection_measurable 1

@[simp] theorem orbitProjection_one_smul (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    orbitProjection 1 (g • z) = orbitProjection 1 z :=
  orbitProjection_smul 1 (levelOneMatrix g) z

@[simp] theorem forgetLevel_one : forgetLevel 1 = id := by
  funext q
  refine Quotient.inductionOn q (fun z => ?_)
  rfl

theorem forgetLevel_map_cell (N : ℕ) (s : Set UpperHalfPlane) :
    (cellPushforward N s).map (forgetLevel N) = cellPushforward 1 s := by
  unfold cellPushforward
  rw [Measure.map_map (forgetLevel_measurable N) (orbitProjection_measurable N)]
  rfl

/-- Every genuine integral translate of the modular cell projects to
the SAME base quotient measure. This uses actual spatial invariance. -/
theorem modular_cell_translate_pushforward (g : SL(2, ℤ)) :
    cellPushforward 1 (g • modularFD) = cellPushforward 1 modularFD :=
  cellPushforward_gamma0_translate 1 (levelOneMatrix g) modularFD

/-- Exact finite-cover measure theorem, initially with its literal
modular-cell base measure. Neither degree nor measure transport is input. -/
theorem forgetLevel_map_carrier_eq_index_cell (N : ℕ) [NeZero N] :
    (carrierPushforward N).map (forgetLevel N) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) • cellPushforward 1 modularFD := by
  letI : Fintype (gamma0Classes N) :=
    (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex
  ext A hA
  rw [Measure.map_apply (forgetLevel_measurable N) hA]
  rw [carrierPushforward, cellPushforward_apply N _ ((forgetLevel_measurable N) hA)]
  have hpre : orbitProjection N ⁻¹' (forgetLevel N ⁻¹' A) = orbitProjection 1 ⁻¹' A := rfl
  rw [hpre]
  calc
    (volume : Measure UpperHalfPlane) (orbitProjection 1 ⁻¹' A ∩ gamma0Carrier N) =
        ∑' q : gamma0Classes N,
          (volume : Measure UpperHalfPlane)
            (orbitProjection 1 ⁻¹' A ∩ (inverseClassRep N q • modularFD)) := by
      unfold gamma0Carrier
      rw [inter_iUnion]
      exact measure_iUnion₀
        ((distinct_coset_cells_aeDisjoint N).mono fun i j hij =>
          hij.mono inter_subset_right inter_subset_right)
        (fun q => (((orbitProjection_measurable 1) hA).inter
          (modularFD_measurable.const_smul _)).nullMeasurableSet)
    _ = ∑' q : gamma0Classes N,
        cellPushforward 1 (inverseClassRep N q • modularFD) A := by
      apply tsum_congr
      intro q
      exact (cellPushforward_apply 1 _ hA).symm
    _ = ∑ q : gamma0Classes N, cellPushforward 1 modularFD A := by
      rw [tsum_fintype]
      simp only [modular_cell_translate_pushforward]
    _ = (((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) •
        cellPushforward 1 modularFD) A := by
      rw [← gamma0Classes_card_eq_index N]
      simp [Finset.sum_const, nsmul_eq_mul, Measure.smul_apply, smul_eq_mul]

/-- At level one the actual canonical carrier measure IS the modular-cell
measure; no choice-of-section or normalized-covolume premise is needed. -/
theorem carrierPushforward_one_eq_modular_cell :
    carrierPushforward 1 = cellPushforward 1 modularFD := by
  have h := forgetLevel_map_carrier_eq_index_cell 1
  simpa only [forgetLevel_one, Measure.map_id, gamma0_one_index,
    Nat.cast_one, one_smul] using h

/-- Natural actual finite-cover pushforward with the SAME canonical
quotient measures already used for the actual quotient L2 spaces. -/
theorem forgetLevel_map_carrier (N : ℕ) [NeZero N] :
    (carrierPushforward N).map (forgetLevel N) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) • carrierPushforward 1 := by
  rw [forgetLevel_map_carrier_eq_index_cell, carrierPushforward_one_eq_modular_cell]

theorem carrier_preimage_modular_set (N : ℕ) [NeZero N]
    {A : Set (Gamma0OrbitSpace 1)} (hA : MeasurableSet A) :
    carrierPushforward N (forgetLevel N ⁻¹' A) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * carrierPushforward 1 A := by
  rw [← Measure.map_apply (forgetLevel_measurable N) hA,
    forgetLevel_map_carrier, Measure.smul_apply, smul_eq_mul]

/-- The lifted full-modular observable is invariant under EVERY integral
matrix, not merely under Gamma0(N). -/
theorem modular_observable_lift_invariant (N : ℕ) {α : Type*}
    (F : Gamma0OrbitSpace 1 → α) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    F (forgetLevel N (orbitProjection N (g • z))) =
      F (forgetLevel N (orbitProjection N z)) := by
  simp only [forgetLevel_projection, orbitProjection_one_smul]

/-- The quotient whose acting group is literally SL(2,Z), without a
Gamma0 subtype in its definition. -/
abbrev ModularOrbitSpace := Quotient (MulAction.orbitRel SL(2, ℤ) UpperHalfPlane)

def modularProjection : UpperHalfPlane → ModularOrbitSpace := Quotient.mk''

theorem modularProjection_measurable : Measurable modularProjection :=
  measurable_quotient_mk''

def levelOneToModular : Gamma0OrbitSpace 1 → ModularOrbitSpace :=
  Quotient.lift modularProjection (by
    intro z w hzw
    apply Quotient.sound
    obtain ⟨g, hg⟩ := (MulAction.orbitRel_apply).mp hzw
    exact (MulAction.orbitRel_apply).mpr ⟨(g : SL(2, ℤ)), hg⟩)

def modularToLevelOne : ModularOrbitSpace → Gamma0OrbitSpace 1 :=
  Quotient.lift (orbitProjection 1) (by
    intro z w hzw
    apply Quotient.sound
    obtain ⟨g, hg⟩ := (MulAction.orbitRel_apply).mp hzw
    exact (MulAction.orbitRel_apply).mpr ⟨levelOneMatrix g, hg⟩)

theorem levelOneToModular_measurable : Measurable levelOneToModular :=
  measurable_from_quotient.mpr modularProjection_measurable

theorem modularToLevelOne_measurable : Measurable modularToLevelOne :=
  measurable_from_quotient.mpr (orbitProjection_measurable 1)

/-- An actual measurable equivalence, with both inverse identities proved
on original orbit representatives. -/
def levelOneModularEquiv : Gamma0OrbitSpace 1 ≃ᵐ ModularOrbitSpace where
  toFun := levelOneToModular
  invFun := modularToLevelOne
  left_inv q := Quotient.inductionOn q (fun _ => rfl)
  right_inv q := Quotient.inductionOn q (fun _ => rfl)
  measurable_toFun := levelOneToModular_measurable
  measurable_invFun := modularToLevelOne_measurable

/-- Canonical full-modular spatial measure from Mathlib's actual cell. -/
def modularMeasure : Measure ModularOrbitSpace :=
  ((volume : Measure UpperHalfPlane).restrict modularFD).map modularProjection

theorem levelOneToModular_map_carrier :
    (carrierPushforward 1).map levelOneToModular = modularMeasure := by
  rw [carrierPushforward_one_eq_modular_cell]
  unfold cellPushforward modularMeasure
  rw [Measure.map_map levelOneToModular_measurable (orbitProjection_measurable 1)]
  rfl

/-- The literal finite-cover quotient map to SL(2,Z)\H. -/
def modularForget (N : ℕ) : Gamma0OrbitSpace N → ModularOrbitSpace :=
  levelOneToModular ∘ forgetLevel N

theorem modularForget_measurable (N : ℕ) : Measurable (modularForget N) :=
  levelOneToModular_measurable.comp (forgetLevel_measurable N)

@[simp] theorem modularForget_projection (N : ℕ) (z : UpperHalfPlane) :
    modularForget N (orbitProjection N z) = modularProjection z := rfl

/-- Exact finite-cover pushforward to the LITERAL SL(2,Z) quotient and its
canonical modular measure, with the actual Gamma0 index as degree. -/
theorem modularForget_map_carrier (N : ℕ) [NeZero N] :
    (carrierPushforward N).map (modularForget N) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) • modularMeasure := by
  change (carrierPushforward N).map (levelOneToModular ∘ forgetLevel N) = _
  rw [← Measure.map_map levelOneToModular_measurable (forgetLevel_measurable N),
    forgetLevel_map_carrier, Measure.map_smul, levelOneToModular_map_carrier]

end
end ImbalancedChen.Part3.Gamma0ModularFiniteCoverMeasure20261025a
