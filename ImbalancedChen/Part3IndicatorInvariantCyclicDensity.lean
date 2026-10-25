import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

An actual L² closed subspace containing all measurable-set truncations of
one vector which is nonzero almost everywhere is the whole L² space.
Consequently a closed subspace stable under all measurable indicator
multipliers and containing such a vector is the whole space.

The proof uses the genuine integrability of the pointwise inner product
of two L² vectors, uniqueness from all set integrals, and Hilbert-space
orthogonal complements. It needs neither a finite nor a sigma-finite
measure. No spectral decomposition or density hypothesis is assumed.
Application to a raw Kontorovich--Lebedev range still requires its actual
indicator invariance and an actual almost-everywhere nonzero range vector.
-/

namespace ImbalancedChen.Part3.IndicatorInvariantCyclicDensity20261025a

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

abbrev ScalarL2 := Lp ℂ 2 μ

/-- Measurable-set multiplication on the genuine L² quotient. -/
def indicatorL2 (B : Set X) (hB : MeasurableSet B) (u : ScalarL2 μ) : ScalarL2 μ :=
  ((Lp.memLp u).indicator hB).toLp (B.indicator u)

theorem indicatorL2_coe_ae (B : Set X) (hB : MeasurableSet B) (u : ScalarL2 μ) :
    indicatorL2 μ B hB u =ᵐ[μ] B.indicator u :=
  ((Lp.memLp u).indicator hB).coeFn_toLp

def indicatorLinear (B : Set X) (hB : MeasurableSet B) : ScalarL2 μ →ₗ[ℂ] ScalarL2 μ where
  toFun := indicatorL2 μ B hB
  map_add' u v := by
    apply Lp.ext
    filter_upwards [indicatorL2_coe_ae μ B hB (u + v), Lp.coeFn_add u v,
      Lp.coeFn_add (indicatorL2 μ B hB u) (indicatorL2 μ B hB v),
      indicatorL2_coe_ae μ B hB u, indicatorL2_coe_ae μ B hB v]
        with x hleft hin hright hu hv
    rw [hleft, hright, hu, hv]
    by_cases hx : x ∈ B
    · simpa only [Set.indicator_of_mem hx] using hin
    · simp only [Set.indicator_of_notMem hx, zero_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [indicatorL2_coe_ae μ B hB (c • u), Lp.coeFn_smul c u,
      Lp.coeFn_smul c (indicatorL2 μ B hB u), indicatorL2_coe_ae μ B hB u]
        with x hleft hin hright hu
    rw [hleft, hright, hu]
    by_cases hx : x ∈ B
    · simpa only [Set.indicator_of_mem hx] using hin
    · simp only [Set.indicator_of_notMem hx, smul_zero]

theorem indicatorL2_norm_le (B : Set X) (hB : MeasurableSet B) (u : ScalarL2 μ) :
    ‖indicatorL2 μ B hB u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [indicatorL2_coe_ae μ B hB u] with x hx
  rw [hx]
  by_cases hmem : x ∈ B
  · simp only [Set.indicator_of_mem hmem, le_refl]
  · simpa only [Set.indicator_of_notMem hmem, norm_zero] using norm_nonneg (u x)

def indicatorMultiplier (B : Set X) (hB : MeasurableSet B) :
    ScalarL2 μ →L[ℂ] ScalarL2 μ :=
  (indicatorLinear μ B hB).mkContinuous 1 (by
    intro u
    simpa only [one_mul] using indicatorL2_norm_le μ B hB u)

theorem indicatorMultiplier_coe_ae (B : Set X) (hB : MeasurableSet B) (u : ScalarL2 μ) :
    indicatorMultiplier μ B hB u =ᵐ[μ] B.indicator u :=
  indicatorL2_coe_ae μ B hB u

theorem indicatorMultiplier_norm_le (B : Set X) (hB : MeasurableSet B) (u : ScalarL2 μ) :
    ‖indicatorMultiplier μ B hB u‖ ≤ ‖u‖ :=
  indicatorL2_norm_le μ B hB u

/-- The Hilbert pairing with a truncation is literally a set integral of
the pointwise scalar product. Both sides use the actual L² representatives. -/
theorem indicatorMultiplier_inner (B : Set X) (hB : MeasurableSet B) (u v : ScalarL2 μ) :
    inner ℂ (indicatorMultiplier μ B hB u) v =
      ∫ x in B, inner ℂ (u x) (v x) ∂μ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, B.indicator (fun t => inner ℂ (u t) (v t)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorMultiplier_coe_ae μ B hB u] with x hx
      rw [hx]
      by_cases hmem : x ∈ B
      · simp only [Set.indicator_of_mem hmem]
      · simp only [Set.indicator_of_notMem hmem, inner_zero_left]
    _ = _ := integral_indicator hB

/-- Genuine local annihilation lemma: no density premise occurs.
The product is integrable by the L² inner-product theorem. Its every
measurable-set integral vanishes, so the product vanishes almost everywhere;
the almost-everywhere nonvanishing of `h` then forces `g = 0` in L². -/
theorem eq_zero_of_all_indicator_pairings (h g : ScalarL2 μ)
    (hnonzero : ∀ᵐ x ∂μ, h x ≠ 0)
    (hpair : ∀ B : Set X, ∀ hB : MeasurableSet B,
      inner ℂ (indicatorMultiplier μ B hB h) g = 0) : g = 0 := by
  have hprod : Integrable (fun x => inner ℂ (h x) (g x)) μ :=
    L2.integrable_inner h g
  have hprod_zero : (fun x => inner ℂ (h x) (g x)) =ᵐ[μ] 0 :=
    hprod.ae_eq_zero_of_forall_setIntegral_eq_zero (by
      intro B hB _
      rw [← indicatorMultiplier_inner μ B hB h g]
      exact hpair B hB)
  apply Lp.ext
  filter_upwards [hprod_zero, hnonzero, Lp.coeFn_zero ℂ (2 : ℝ≥0∞) μ]
    with x hpx hnx hzx
  rw [hzx]
  change g x * star (h x) = 0 at hpx
  have hsx : star (h x) ≠ 0 := by simpa only [ne_eq, star_eq_zero] using hnx
  exact (mul_eq_zero.mp hpx).resolve_right hsx

/-- A closed subspace containing every measurable truncation of an
almost-everywhere nonzero vector is the full actual L² space. -/
theorem closed_eq_top_of_indicator_parts (S : Submodule ℂ (ScalarL2 μ))
    (hclosed : IsClosed (S : Set (ScalarL2 μ))) (h : ScalarL2 μ)
    (hnonzero : ∀ᵐ x ∂μ, h x ≠ 0)
    (hparts : ∀ B : Set X, ∀ hB : MeasurableSet B,
      indicatorMultiplier μ B hB h ∈ S) : S = ⊤ := by
  have horth : Sᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro g hg
    apply eq_zero_of_all_indicator_pairings μ h g hnonzero
    intro B hB
    exact (S.mem_orthogonal g).mp hg _ (hparts B hB)
  calc
    S = S.topologicalClosure := hclosed.submodule_topologicalClosure_eq.symm
    _ = Sᗮᗮ := S.orthogonal_orthogonal_eq_closure.symm
    _ = ⊤ := by rw [horth, Submodule.bot_orthogonal_eq_top]

/-- Closed indicator-invariant subspaces with an almost-everywhere
nonvanishing vector are the whole L² space. The stability assumption is
literal membership under the constructed measurable indicator CLMs. -/
theorem closed_indicator_invariant_eq_top (S : Submodule ℂ (ScalarL2 μ))
    (hclosed : IsClosed (S : Set (ScalarL2 μ)))
    (hstable : ∀ B : Set X, ∀ hB : MeasurableSet B, ∀ u : ScalarL2 μ,
      u ∈ S → indicatorMultiplier μ B hB u ∈ S)
    (h : ScalarL2 μ) (hmem : h ∈ S) (hnonzero : ∀ᵐ x ∂μ, h x ≠ 0) : S = ⊤ :=
  closed_eq_top_of_indicator_parts μ S hclosed h hnonzero
    (fun B hB => hstable B hB h hmem)

end

end ImbalancedChen.Part3.IndicatorInvariantCyclicDensity20261025a
