import ImbalancedChen.Part3GenericCyclicBorelProjection
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Finite disjoint indicator sums and genuine countable strong additivity
for the constructed generic scalar/cyclic Borel projections. The countable
proof is dominated convergence of squared actual indicator tails along
the finite-subsets filter, so it proves unconditional `HasSum`, not merely
convergence in one chosen enumeration. No PVM/countable-additivity premise.
-/

namespace ImbalancedChen.Part3.GenericCyclicBorelCountableAdditivity20261025a

noncomputable section

open MeasureTheory Filter
open scoped Topology
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericCyclicBorelProjection20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (f : H)

def finiteUnion {ι : Type*} (B : ι → Set (ResolventSpectrum R)) (s : Finset ι) :
    Set (ResolventSpectrum R) := ⋃ i ∈ s, B i

theorem measurableSet_finiteUnion {ι : Type*} (B : ι → Set (ResolventSpectrum R))
    (hB : ∀ i, MeasurableSet (B i)) (s : Finset ι) : MeasurableSet (finiteUnion R B s) :=
  Finset.measurableSet_biUnion s (fun i _ => hB i)

private theorem indicator_finset_sum {ι : Type*} (B : ι → Set (ResolventSpectrum R))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (s : Finset ι) (ξ : ResolventSpectrum R → ℂ) :
    (∑ i ∈ s, (B i).indicator ξ) = (finiteUnion R B s).indicator ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteUnion]
  | @insert i s hi ih =>
      have hd : Disjoint (B i) (finiteUnion R B s) := by
        apply Set.disjoint_left.mpr
        intro t hti htU
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp htU
        obtain ⟨hjs, htj⟩ := Set.mem_iUnion.mp hj
        have hij : i ≠ j := by
          intro heq
          subst j
          exact hi hjs
        exact Set.disjoint_left.mp (hdisj hij) hti htj
      have hU : finiteUnion R B (insert i s) = B i ∪ finiteUnion R B s := by
        ext t
        simp [finiteUnion]
      rw [Finset.sum_insert hi, ih, hU, Set.indicator_union_of_disjoint hd]

theorem borelMultiplier_finset_sum {ι : Type*} (B : ι → Set (ResolventSpectrum R))
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (s : Finset ι) (ξ : ScalarL2 R hSA f) :
    (∑ i ∈ s, borelMultiplier R hSA f (B i) (hB i) ξ) =
      borelMultiplier R hSA f (finiteUnion R B s) (measurableSet_finiteUnion R B hB s) ξ := by
  classical
  apply Lp.ext
  have hall : ∀ᵐ t ∂scalarMeasure R hSA f, ∀ i ∈ s,
      (borelMultiplier R hSA f (B i) (hB i) ξ) t = (B i).indicator ξ t :=
    (Filter.eventually_all_finset s).mpr (fun i _ => borelMultiplier_coe_ae R hSA f (B i) (hB i) ξ)
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun i => borelMultiplier R hSA f (B i) (hB i) ξ),
    hall, borelMultiplier_coe_ae R hSA f (finiteUnion R B s)
      (measurableSet_finiteUnion R B hB s) ξ] with t hsum ht hright
  rw [hsum, hright]
  calc
    _ = ∑ i ∈ s, (B i).indicator ξ t := Finset.sum_congr rfl (fun i hi => ht i hi)
    _ = _ := congrFun (indicator_finset_sum R B hdisj s ξ) t

theorem borelMultiplier_finset_sum_norm_le {ι : Type*} (B : ι → Set (ResolventSpectrum R))
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (s : Finset ι) (ξ : ScalarL2 R hSA f) :
    ‖∑ i ∈ s, borelMultiplier R hSA f (B i) (hB i) ξ‖ ≤ ‖ξ‖ := by
  rw [borelMultiplier_finset_sum R hSA f B hB hdisj s ξ]
  exact borelMultiplier_norm_le R hSA f _ _ ξ

private theorem scalarL2_norm_square (ξ : ScalarL2 R hSA f) :
    ‖ξ‖ ^ 2 = ∫ t : ResolventSpectrum R, ‖ξ t‖ ^ 2 ∂scalarMeasure R hSA f := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  simpa only [integral_complex_ofReal, Complex.ofReal_re]

/-- Unconditional strong additivity for every countable disjoint family. -/
theorem borelMultiplier_hasSum {ι : Type*} [Countable ι]
    (B : ι → Set (ResolventSpectrum R)) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) (ξ : ScalarL2 R hSA f) :
    HasSum (fun i => borelMultiplier R hSA f (B i) (hB i) ξ)
      (borelMultiplier R hSA f (⋃ i, B i) (MeasurableSet.iUnion hB) ξ) := by
  classical
  let U : Set (ResolventSpectrum R) := ⋃ i, B i
  have hU : MeasurableSet U := MeasurableSet.iUnion hB
  have hsub (s : Finset ι) : finiteUnion R B s ⊆ U := by
    intro t ht
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
    obtain ⟨_, hti⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨i, hti⟩
  let F : Finset ι → ResolventSpectrum R → ℝ := fun s t =>
    ‖(finiteUnion R B s).indicator ξ t - U.indicator ξ t‖ ^ 2
  have hFmeas (s : Finset ι) : AEStronglyMeasurable (F s) (scalarMeasure R hSA f) := by
    have hd := ((Lp.aestronglyMeasurable ξ).indicator (measurableSet_finiteUnion R B hB s)).sub
      ((Lp.aestronglyMeasurable ξ).indicator hU)
    simpa only [F, pow_two] using hd.norm.mul hd.norm
  have hboundInt : Integrable (fun t : ResolventSpectrum R => ‖ξ t‖ ^ 2)
      (scalarMeasure R hSA f) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ξ)).mp (Lp.memLp ξ)
  have hbound (s : Finset ι) (t : ResolventSpectrum R) : ‖F s t‖ ≤ ‖ξ t‖ ^ 2 := by
    by_cases htE : t ∈ finiteUnion R B s
    · have htU := hsub s htE
      simp [F, htE, htU, sq_nonneg]
    · by_cases htU : t ∈ U <;> simp [F, htE, htU, sq_nonneg]
  have hpoint (t : ResolventSpectrum R) :
      Tendsto (fun s : Finset ι => F s t) atTop (𝓝 0) := by
    by_cases htU : t ∈ U
    · obtain ⟨i, hti⟩ := Set.mem_iUnion.mp htU
      have hev : (fun s : Finset ι => F s t) =ᶠ[atTop] (fun _ => 0) := by
        refine Filter.eventually_atTop.mpr ⟨{i}, ?_⟩
        intro s hs
        have his : i ∈ s := hs (Finset.mem_singleton_self i)
        have htE : t ∈ finiteUnion R B s :=
          Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨his, hti⟩⟩
        simp [F, htE, htU]
      exact (Filter.tendsto_congr' hev).mpr tendsto_const_nhds
    · have hev : (fun s : Finset ι => F s t) =ᶠ[atTop] (fun _ => 0) :=
        Filter.Eventually.of_forall fun s => by
          have htE : t ∉ finiteUnion R B s := fun he => htU (hsub s he)
          simp [F, htE, htU]
      exact (Filter.tendsto_congr' hev).mpr tendsto_const_nhds
  have hIntegral : Tendsto (fun s : Finset ι => ∫ t, F s t ∂scalarMeasure R hSA f)
      atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence
        (fun t : ResolventSpectrum R => ‖ξ t‖ ^ 2)
        (Filter.Eventually.of_forall hFmeas)
        (Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall (hbound s))
        hboundInt (Filter.Eventually.of_forall hpoint))
  let V : Finset ι → ScalarL2 R hSA f := fun s =>
    borelMultiplier R hSA f (finiteUnion R B s) (measurableSet_finiteUnion R B hB s) ξ
  let W : ScalarL2 R hSA f := borelMultiplier R hSA f U hU ξ
  have hsquare (s : Finset ι) : ‖V s - W‖ ^ 2 = ∫ t, F s t ∂scalarMeasure R hSA f := by
    rw [scalarL2_norm_square R hSA f]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (V s) W,
      borelMultiplier_coe_ae R hSA f (finiteUnion R B s) (measurableSet_finiteUnion R B hB s) ξ,
      borelMultiplier_coe_ae R hSA f U hU ξ] with t hδ hV hW
    simpa only [hδ, hV, hW, F]
  have hnormSq : Tendsto (fun s : Finset ι => ‖V s - W‖ ^ 2) atTop (𝓝 0) := by
    have heq := funext hsquare
    rwa [← heq] at hIntegral
  have hnorm : Tendsto (fun s : Finset ι => ‖V s - W‖) atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hnormSq
    simpa only [Function.comp_apply, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  have hV : Tendsto V atTop (𝓝 W) := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  change Tendsto (fun s : Finset ι => ∑ i ∈ s, borelMultiplier R hSA f (B i) (hB i) ξ)
    atTop (𝓝 W)
  have heq : (fun s : Finset ι => ∑ i ∈ s, borelMultiplier R hSA f (B i) (hB i) ξ) = V :=
    funext (fun s => borelMultiplier_finset_sum R hSA f B hB hdisj s ξ)
  rwa [heq]

theorem borelMultiplier_hasSum_univ {ι : Type*} [Countable ι]
    (B : ι → Set (ResolventSpectrum R)) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcover : (⋃ i, B i) = Set.univ) (ξ : ScalarL2 R hSA f) :
    HasSum (fun i => borelMultiplier R hSA f (B i) (hB i) ξ) ξ := by
  simpa only [hcover, borelMultiplier_univ, ContinuousLinearMap.id_apply] using
    borelMultiplier_hasSum R hSA f B hB hdisj ξ

theorem cyclicBorelProjection_finset_sum {ι : Type*} (B : ι → Set (ResolventSpectrum R))
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (s : Finset ι) (u : cyclicSubspace R hSA f) :
    (∑ i ∈ s, cyclicBorelProjection R hSA f (B i) (hB i) u) =
      cyclicBorelProjection R hSA f (finiteUnion R B s) (measurableSet_finiteUnion R B hB s) u := by
  let U := cyclicRepresentation R hSA f
  simpa only [map_sum, cyclicBorelProjection_apply] using
    congrArg U (borelMultiplier_finset_sum R hSA f B hB hdisj s (U.symm u))

theorem cyclicBorelProjection_finset_sum_norm_le {ι : Type*} (B : ι → Set (ResolventSpectrum R))
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (s : Finset ι) (u : cyclicSubspace R hSA f) :
    ‖∑ i ∈ s, cyclicBorelProjection R hSA f (B i) (hB i) u‖ ≤ ‖u‖ := by
  rw [cyclicBorelProjection_finset_sum R hSA f B hB hdisj s u]
  exact cyclicBorelProjection_norm_le R hSA f _ _ u

theorem cyclicBorelProjection_hasSum {ι : Type*} [Countable ι]
    (B : ι → Set (ResolventSpectrum R)) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) (u : cyclicSubspace R hSA f) :
    HasSum (fun i => cyclicBorelProjection R hSA f (B i) (hB i) u)
      (cyclicBorelProjection R hSA f (⋃ i, B i) (MeasurableSet.iUnion hB) u) := by
  let U := cyclicRepresentation R hSA f
  simpa only [cyclicBorelProjection_apply] using
    U.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
      (borelMultiplier_hasSum R hSA f B hB hdisj (U.symm u))

theorem cyclicBorelProjection_hasSum_univ {ι : Type*} [Countable ι]
    (B : ι → Set (ResolventSpectrum R)) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcover : (⋃ i, B i) = Set.univ) (u : cyclicSubspace R hSA f) :
    HasSum (fun i => cyclicBorelProjection R hSA f (B i) (hB i) u) u := by
  simpa only [hcover, cyclicBorelProjection_univ, ContinuousLinearMap.id_apply] using
    cyclicBorelProjection_hasSum R hSA f B hB hdisj u

end

end ImbalancedChen.Part3.GenericCyclicBorelCountableAdditivity20261025a
