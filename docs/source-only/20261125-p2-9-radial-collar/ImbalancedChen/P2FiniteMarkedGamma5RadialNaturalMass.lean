import ImbalancedChen.P2FiniteMarkedGamma5RadialProfileCollar

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The complete natural-prime outer support of one existing Gamma5 ambient
profile. The finite carrier is the coordinatewise natural-value image of
the proved bounded enumerator. Its membership theorem identifies it with
all prime natural tuples on the original nonzero outer support.

The value map is injective, so the original profile sum is unchanged.
Every coordinate, its order and repeated value are retained. This is a
single-ambient sum dictionary and payment, not an identification with all
old history marks or the manuscript's J.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5RadialNaturalMass
noncomputable section
open Filter Finset Real
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor)
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2FiniteMarkedGamma5EulerWordBudget (finPhysicalProfile)
open P2FiniteMarkedGamma5RadialProfileCollar
open scoped Classical Topology BigOperators

def tupleValues {N d : ℕ} (t : Fin d → Fin (2 * N + 1)) : Fin d → ℕ :=
  fun i => (t i).val

/-- Taking natural values forgets no bounded-tuple coordinate. -/
theorem tupleValues_injective (N d : ℕ) :
    Function.Injective (tupleValues (N := N) (d := d)) := by
  intro t s hts
  funext i
  apply Fin.ext
  exact congrFun hts i

def naturalOuterTuples (N k r : ℕ) (logQ h : ℝ) :
    Finset (Fin (k + (2 + r)) → ℕ) :=
  (profileOuterTuples N k r logQ h).image
    (tupleValues (N := N) (d := k + (2 + r)))

/-- This finite carrier is exactly the full natural-prime outer support
under the admitted positive width. The reverse implication uses the
existing integer enumeration, not a new support or payment premise. -/
theorem mem_naturalOuterTuples {N k r : ℕ} {logQ h : ℝ}
    {u : Fin (k + (2 + r)) → ℕ} (hN : 0 < N)
    (hp : 0 < h) (h8 : h ≤ 1 / 8) :
    u ∈ naturalOuterTuples N k r logQ h ↔
      (∀ i, (u i).Prime) ∧
        finPhysicalProfile logQ (N : ℝ) (radialWidth h)
          ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ)) ≠ 0 ∧
        (N : ℝ) < ((∏ i, u i : ℕ) : ℝ) := by
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
    obtain ⟨hprime, hne, houter⟩ := mem_filter.mp ht
    exact ⟨(mem_filter.mp hprime).2, hne, houter⟩
  · rintro ⟨hprime, hne, houter⟩
    obtain ⟨t, ht, hvalues⟩ :=
      profile_outer_integer_enumeration hN hp h8 hprime hne houter
    refine mem_image.mpr ⟨t, ht, ?_⟩
    funext i
    exact hvalues i

def naturalOuterMass (N k r : ℕ) (logQ h : ℝ) : ℝ :=
  ∑ u ∈ naturalOuterTuples N k r logQ h,
    finPhysicalProfile logQ (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ))

/-- The injective value map preserves the exact original weight and the
whole finite sum. No product-image collapse or multiplicity factor is
introduced. This equality itself needs no scale or width assumption. -/
theorem naturalOuterMass_eq_profileOuterMass (N k r : ℕ) (logQ h : ℝ) :
    naturalOuterMass N k r logQ h = profileOuterMass N k r logQ h := by
  unfold naturalOuterMass naturalOuterTuples
  rw [Finset.sum_image
    (fun _ _ _ _ hts => tupleValues_injective N (k + (2 + r)) hts)] <;> rfl

/-- The same fixed h pays the full natural-prime outer support of each
one-ambient profile. The order of h, N, k, r and logQ is unchanged. -/
theorem absolute_natural_outer_payment {ε : ℝ} (he : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧
      0 < radialWidth h ∧ radialWidth h ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (k r : ℕ) (logQ : ℝ),
        k + 2 + r ≤ frozenSourceRankBound →
        P2FiniteMarkedGamma5RadialRoughMass.norm N *
          naturalOuterMass N k r logQ h ≤ ε := by
  obtain ⟨h, hp, h8, hw, hw1, H⟩ := absolute_profile_outer_payment he
  refine ⟨h, hp, h8, hw, hw1, ?_⟩
  filter_upwards [H] with N hpaid
  intro k r logQ hkr
  rw [naturalOuterMass_eq_profileOuterMass]
  exact hpaid k r logQ hkr

end
end ImbalancedChen.P2FiniteMarkedGamma5RadialNaturalMass
