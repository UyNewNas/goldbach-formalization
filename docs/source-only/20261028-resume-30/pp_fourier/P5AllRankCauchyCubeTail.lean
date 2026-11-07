import ImbalancedChen.P5AllRankCauchyKernelIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Source-only continuation of the original PP proof, section 4, equation (F).
The finite-coordinate union bound and product Fubini argument below are
proved, rather than supplied as a cube-tail premise. Rank zero is included.
The coordinate variable in this file is the manuscript's physical frequency
xi; conversion xi = 2*pi*nu from Mathlib's Fourier transform is separate.
No Lean invocation or numerical evaluation has been performed.
-/
namespace ImbalancedChen.P5Z.AllRankCauchyCubeTail
noncomputable section

open MeasureTheory Set
open scoped BigOperators
open AllRankCauchyKernelIntegral

/-- The omitted part of one coordinate, with the boundary retained. -/
def tail1 (k : ℝ → ℝ) (H : ℝ) (x : ℝ) : ℝ :=
  if H < |x| then k x else 0

def outsideCube (m : ℕ) (H : ℝ) : Set (Fin m → ℝ) :=
  {ξ | ∃ i, H < |ξ i|}

def cubeTail (m : ℕ) (k : ℝ → ℝ) (H : ℝ) (ξ : Fin m → ℝ) : ℝ :=
  if ξ ∈ outsideCube m H then ∏ i, k (ξ i) else 0

/-- A single-coordinate slab is a product of one-dimensional functions. -/
def slabFactor {m : ℕ} (k : ℝ → ℝ) (H : ℝ) (j i : Fin m) (x : ℝ) : ℝ :=
  if i = j then tail1 k H x else k x

def slab {m : ℕ} (k : ℝ → ℝ) (H : ℝ) (j : Fin m) (ξ : Fin m → ℝ) : ℝ :=
  ∏ i, slabFactor k H j i (ξ i)

theorem measurableSet_tail1 (H : ℝ) : MeasurableSet {x : ℝ | H < |x|} :=
  measurableSet_lt measurable_const measurable_id.abs

theorem measurableSet_outsideCube (m : ℕ) (H : ℝ) :
    MeasurableSet (outsideCube m H) := by
  have heq : outsideCube m H = ⋃ i : Fin m, {ξ : Fin m → ℝ | H < |ξ i|} := by
    ext ξ
    simp [outsideCube]
  rw [heq]
  exact MeasurableSet.iUnion (fun i =>
    measurableSet_lt measurable_const (measurable_pi_apply i).abs)

theorem tail1_integrable {k : ℝ → ℝ} (hk : Integrable k) (H : ℝ) :
    Integrable (tail1 k H) := by
  simpa only [tail1, Set.indicator, Set.mem_setOf_eq] using
    hk.indicator (measurableSet_tail1 H)

theorem slab_integrable {m : ℕ} {k : ℝ → ℝ} (hk : Integrable k)
    (H : ℝ) (j : Fin m) : Integrable (slab k H j) := by
  have hi (i : Fin m) : Integrable (slabFactor k H j i) := by
    by_cases hij : i = j
    · simpa only [slabFactor, hij, if_true] using tail1_integrable hk H
    · simpa only [slabFactor, hij, if_false] using hk
  simpa only [slab] using
    (Integrable.fintype_prod (μ := fun _ : Fin m => volume) hi)

theorem cubeTail_integrable {m : ℕ} {k : ℝ → ℝ} (hk : Integrable k) (H : ℝ) :
    Integrable (cubeTail m k H) := by
  have hp : Integrable (fun ξ : Fin m → ℝ => ∏ i, k (ξ i)) := by
    simpa using (Integrable.fintype_prod (μ := fun _ : Fin m => volume)
      (fun _ => hk))
  simpa only [cubeTail, Set.indicator] using
    hp.indicator (measurableSet_outsideCube m H)

/-- Literal finite union majorant. There is no disjointness assumption:
points in several omitted slabs may be counted several times. -/
theorem cubeTail_le_sum_slab (m : ℕ) (k : ℝ → ℝ)
    (hk : ∀ x, 0 ≤ k x) (H : ℝ) (ξ : Fin m → ℝ) :
    cubeTail m k H ξ ≤ ∑ j : Fin m, slab k H j ξ := by
  classical
  have hslab (j : Fin m) : 0 ≤ slab k H j ξ := by
    apply Finset.prod_nonneg
    intro i hi
    unfold slabFactor tail1
    split_ifs <;> positivity
  by_cases hξ : ξ ∈ outsideCube m H
  · obtain ⟨j, hj⟩ := hξ
    have heq : slab k H j ξ = ∏ i, k (ξ i) := by
      unfold slab
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hij : i = j
      · subst i
        simp [slabFactor, tail1, hj]
      · simp [slabFactor, hij]
    rw [cubeTail, if_pos hξ, ← heq]
    exact Finset.single_le_sum (fun i hi => hslab i) (Finset.mem_univ j)
  · rw [cubeTail, if_neg hξ]
    exact Finset.sum_nonneg (fun j hj => hslab j)

/-- Product Fubini: for a unit-mass one-dimensional kernel, a coordinate
slab has exactly the one-dimensional omitted mass, in every finite rank. -/
theorem integral_slab {m : ℕ} (k : ℝ → ℝ) (H : ℝ) (j : Fin m)
    (hunit : (∫ x : ℝ, k x) = 1) :
    (∫ ξ : Fin m → ℝ, slab k H j ξ) = ∫ x : ℝ, tail1 k H x := by
  classical
  rw [slab, integral_fintype_prod_volume_eq_prod]
  have hi (i : Fin m) :
      (∫ x : ℝ, slabFactor k H j i x) =
        if i = j then (∫ x : ℝ, tail1 k H x) else 1 := by
    by_cases hij : i = j
    · simp only [slabFactor, hij, if_true]
    · simp only [slabFactor, hij, if_false, hunit]
  simp_rw [hi]
  have hprod := Finset.prod_eq_single (s := (Finset.univ : Finset (Fin m)))
    (f := fun i => if i = j then (∫ x : ℝ, tail1 k H x) else 1) j
    (fun i hi hij => by simp [hij]) (by simp)
  simpa using hprod

/-- The all-rank cube-tail Fubini inequality. It is valid for m=0, where
both sides vanish, and needs no lower bound such as m≥4. -/
theorem integral_cubeTail_le (m : ℕ) (k : ℝ → ℝ)
    (hk : Integrable k) (hnonneg : ∀ x, 0 ≤ k x)
    (hunit : (∫ x : ℝ, k x) = 1) (H : ℝ) :
    (∫ ξ : Fin m → ℝ, cubeTail m k H ξ) ≤
      (m : ℝ) * (∫ x : ℝ, tail1 k H x) := by
  classical
  calc
    (∫ ξ : Fin m → ℝ, cubeTail m k H ξ) ≤
        ∫ ξ : Fin m → ℝ, ∑ j : Fin m, slab k H j ξ := by
      apply integral_mono (cubeTail_integrable hk H)
        (integrable_finset_sum _ (fun j hj => slab_integrable hk H j))
      exact cubeTail_le_sum_slab m k hnonneg H
    _ = ∑ j : Fin m, ∫ ξ : Fin m → ℝ, slab k H j ξ :=
      integral_finset_sum _ (fun j hj => slab_integrable hk H j)
    _ = (m : ℝ) * (∫ x : ℝ, tail1 k H x) := by
      simp_rw [integral_slab k H _ hunit]
      simp

/-- The elementary positive Cauchy tail is compared with x^(-2), and the
latter integral is evaluated by the pinned improper-integral theorem. -/
theorem cauchy_positive_tail_le {H : ℝ} (hH : 0 < H) :
    (∫ x : ℝ in Ioi H, cauchy x) ≤ H⁻¹ := by
  have hr : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi H) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hH
  have heval : (∫ x : ℝ in Ioi H, x ^ (-2 : ℝ)) = H⁻¹ := by
    convert (integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hH) using 1 <;>
      norm_num [Real.rpow_neg_one]
  rw [← heval]
  apply setIntegral_mono_on cauchy_integrable.integrableOn hr measurableSet_Ioi
  intro x hx
  have hxpos : 0 < x := hH.trans hx
  have hxpow : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg hxpos.le, Real.rpow_two]
  rw [hxpow]
  simpa only [cauchy, one_div] using
    (one_div_le_one_div_of_le (sq_pos_of_pos hxpos)
      (show x ^ 2 ≤ 1 + x ^ 2 by linarith))

/-- Both signs are included. The cutoff boundary has zero contribution
because the omitted set is strict, exactly as in the physical cube. -/
theorem cauchy_absolute_tail_le {H : ℝ} (hH : 0 < H) :
    (∫ x : ℝ, tail1 cauchy H x) ≤ 2 / H := by
  let p : ℝ → ℝ := (Ioi H).indicator cauchy
  let n : ℝ → ℝ := (Iio (-H)).indicator cauchy
  have hp : Integrable p := cauchy_integrable.indicator measurableSet_Ioi
  have hn : Integrable n := cauchy_integrable.indicator measurableSet_Iio
  have hsplit : tail1 cauchy H = fun x => p x + n x := by
    funext x
    by_cases hx : 0 ≤ x
    · have hn' : ¬ x < -H := by linarith
      simp [tail1, p, n, Set.indicator, abs_of_nonneg hx, hn']
    · have hx' : x ≤ 0 := le_of_not_ge hx
      have hp' : ¬ H < x := by linarith
      have hiff : H < -x ↔ x < -H := by constructor <;> intro h <;> linarith
      simp [tail1, p, n, Set.indicator, abs_of_nonpos hx', hp', hiff]
  have hneg : (∫ x : ℝ, n x) = ∫ x : ℝ, p x := by
    have hncomp : n = fun x : ℝ => p (-x) := by
      funext x
      have hiff : H < -x ↔ x < -H := by constructor <;> intro h <;> linarith
      simp [p, n, Set.indicator, hiff, cauchy]
    rw [hncomp]
    exact integral_comp_neg p
  have hpos : (∫ x : ℝ, p x) ≤ H⁻¹ := by
    rw [show p = (Ioi H).indicator cauchy from rfl,
      integral_indicator measurableSet_Ioi]
    exact cauchy_positive_tail_le hH
  rw [hsplit, integral_add hp hn, hneg]
  calc
    (∫ x : ℝ, p x) + (∫ x : ℝ, p x) ≤ H⁻¹ + H⁻¹ := add_le_add hpos hpos
    _ = 2 / H := by ring

/-- Normalize the one-dimensional kernel before product Fubini. This
makes every unexceptional coordinate integrate to one. -/
def normalizedCauchy (x : ℝ) : ℝ := cauchy x / Real.pi

theorem normalizedCauchy_integrable : Integrable normalizedCauchy :=
  cauchy_integrable.div_const Real.pi

theorem normalizedCauchy_nonneg (x : ℝ) : 0 ≤ normalizedCauchy x := by
  unfold normalizedCauchy cauchy
  positivity

theorem normalizedCauchy_integral : (∫ x : ℝ, normalizedCauchy x) = 1 := by
  rw [normalizedCauchy, integral_div, cauchy_integral]
  exact div_self Real.pi_ne_zero

theorem normalizedCauchy_tail_le {H : ℝ} (hH : 0 < H) :
    (∫ x : ℝ, tail1 normalizedCauchy H x) ≤ (2 / H) / Real.pi := by
  have heq : tail1 normalizedCauchy H = fun x => tail1 cauchy H x / Real.pi := by
    funext x
    unfold tail1 normalizedCauchy
    split_ifs <;> simp
  rw [heq, integral_div]
  exact div_le_div_of_nonneg_right (cauchy_absolute_tail_le hH) Real.pi_pos.le

theorem normalized_cube_tail_le (m : ℕ) {H : ℝ} (hH : 0 < H) :
    (∫ ξ : Fin m → ℝ, cubeTail m normalizedCauchy H ξ) ≤
      (m : ℝ) * ((2 / H) / Real.pi) :=
  (integral_cubeTail_le m normalizedCauchy normalizedCauchy_integrable
    normalizedCauchy_nonneg normalizedCauchy_integral H).trans
      (mul_le_mul_of_nonneg_left (normalizedCauchy_tail_le hH) (Nat.cast_nonneg m))

theorem physical_cubeTail_eq (m : ℕ) (H : ℝ) (ξ : Fin m → ℝ) :
    cubeTail m cauchy H ξ = Real.pi ^ m * cubeTail m normalizedCauchy H ξ := by
  classical
  unfold cubeTail
  split_ifs
  · simp only [normalizedCauchy, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    field_simp [Real.pi_ne_zero] <;> ring
  · simp

/-- The product kernel, with precisely the manuscript's (2*pi)^(-m)
normalization, has omitted mass at most m/H. No cube volume is charged. -/
theorem normalized_physical_cube_tail_le (m : ℕ) {H : ℝ} (hH : 0 < H) :
    (∫ ξ : Fin m → ℝ, cubeTail m cauchy H ξ) / (2 * Real.pi) ^ m ≤
      (m : ℝ) / H := by
  have hpow : (1 : ℝ) ≤ 2 ^ m := by
    induction m with
    | zero => norm_num
    | succ m hm => rw [pow_succ]; nlinarith
  have hpowpos : (0 : ℝ) < 2 ^ m := lt_of_lt_of_le zero_lt_one hpow
  have hpi2 : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hscalar : ((2 / H) / Real.pi) / 2 ^ m ≤ 1 / H := by
    apply (div_le_iff₀ hpowpos).2
    apply (div_le_iff₀ Real.pi_pos).2
    apply (div_le_iff₀ hH).2
    have hbase : (2 : ℝ) ≤ 2 ^ m * Real.pi := by nlinarith [Real.pi_pos]
    convert hbase using 1 <;> field_simp <;> ring
  have hmass := normalized_cube_tail_le m hH
  have hidentity :
      (∫ ξ : Fin m → ℝ, cubeTail m cauchy H ξ) / (2 * Real.pi) ^ m =
        (∫ ξ : Fin m → ℝ, cubeTail m normalizedCauchy H ξ) / 2 ^ m := by
    simp_rw [physical_cubeTail_eq]
    rw [integral_const_mul, mul_pow]
    field_simp [pow_ne_zero m Real.pi_ne_zero] <;> ring
  rw [hidentity]
  calc
    (∫ ξ : Fin m → ℝ, cubeTail m normalizedCauchy H ξ) / 2 ^ m ≤
        ((m : ℝ) * ((2 / H) / Real.pi)) / 2 ^ m :=
      div_le_div_of_nonneg_right hmass hpowpos.le
    _ = (m : ℝ) * (((2 / H) / Real.pi) / 2 ^ m) := by ring
    _ ≤ (m : ℝ) * (1 / H) :=
      mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg m)
    _ = (m : ℝ) / H := by ring

/-- An arbitrary integrable physical-frequency coefficient inherits the
cube-tail estimate from mixed IBP. The pointwise input is the derivative
estimate, not the final arithmetic discrepancy or the desired tail bound. -/
theorem physical_frequency_tail_le (m : ℕ) (A : (Fin m → ℝ) → ℂ)
    (hA : Integrable A) (D H : ℝ) (hD : 0 ≤ D) (hH : 0 < H)
    (hPoint : ∀ ξ, ‖A ξ‖ ≤ D * productCauchy m ξ) :
    (∫ ξ in outsideCube m H, ‖A ξ‖) / (2 * Real.pi) ^ m ≤
      (m : ℝ) * D / H := by
  have hcomp :
      (∫ ξ in outsideCube m H, ‖A ξ‖) ≤
        D * (∫ ξ : Fin m → ℝ, cubeTail m cauchy H ξ) := by
    rw [← integral_indicator (measurableSet_outsideCube m H), ← integral_const_mul]
    apply integral_mono (hA.norm.indicator (measurableSet_outsideCube m H))
      ((cubeTail_integrable cauchy_integrable H).const_mul D)
    intro ξ
    by_cases hξ : ξ ∈ outsideCube m H
    · simpa [Set.indicator, cubeTail, hξ, productCauchy] using hPoint ξ
    · simp [Set.indicator, cubeTail, hξ]
  have hden : 0 < (2 * Real.pi) ^ m := pow_pos (by positivity) m
  calc
    (∫ ξ in outsideCube m H, ‖A ξ‖) / (2 * Real.pi) ^ m ≤
        D * (∫ ξ : Fin m → ℝ, cubeTail m cauchy H ξ) / (2 * Real.pi) ^ m :=
      div_le_div_of_nonneg_right hcomp hden.le
    _ = D * ((∫ ξ : Fin m → ℝ, cubeTail m cauchy H ξ) /
        (2 * Real.pi) ^ m) := by ring
    _ ≤ D * ((m : ℝ) / H) :=
      mul_le_mul_of_nonneg_left (normalized_physical_cube_tail_le m hH) hD
    _ = (m : ℝ) * D / H := by ring

/-- Actual retained-cube Fourier synthesis: bounded measurable phases do
not cost a frequency-cube volume. In particular unit complex exponential
phases preserve the same uniform error, independently of the evaluation
point and of the independent occurrence rank. -/
theorem normalized_synthesis_error_le (m : ℕ)
    (A : (Fin m → ℝ) → ℂ) (phase : (Fin m → ℝ) → ℂ)
    (hA : Integrable A) (hphase : AEStronglyMeasurable phase volume)
    (hphase_norm : ∀ ξ, ‖phase ξ‖ ≤ 1)
    (D H : ℝ) (hD : 0 ≤ D) (hH : 0 < H)
    (hPoint : ∀ ξ, ‖A ξ‖ ≤ D * productCauchy m ξ) :
    ‖(∫ ξ : Fin m → ℝ, A ξ * phase ξ) -
        (∫ ξ in (outsideCube m H)ᶜ, A ξ * phase ξ)‖ /
      (2 * Real.pi) ^ m ≤ (m : ℝ) * D / H := by
  have hAP : Integrable (fun ξ => A ξ * phase ξ) := by
    apply hA.norm.mono' (hA.aestronglyMeasurable.mul hphase)
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_left (hphase_norm ξ) (norm_nonneg (A ξ)))
  have hdecomp := integral_add_compl (measurableSet_outsideCube m H) hAP
  have heq :
      (∫ ξ : Fin m → ℝ, A ξ * phase ξ) -
        (∫ ξ in (outsideCube m H)ᶜ, A ξ * phase ξ) =
      ∫ ξ in outsideCube m H, A ξ * phase ξ :=
    (sub_eq_iff_eq_add).2 hdecomp.symm
  rw [heq]
  have hraw : ‖∫ ξ in outsideCube m H, A ξ * phase ξ‖ ≤
      ∫ ξ in outsideCube m H, ‖A ξ‖ := by
    calc
      ‖∫ ξ in outsideCube m H, A ξ * phase ξ‖ ≤
          ∫ ξ in outsideCube m H, ‖A ξ * phase ξ‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ξ in outsideCube m H, ‖A ξ‖ := by
        apply integral_mono hAP.norm.integrableOn hA.norm.integrableOn
        intro ξ
        rw [norm_mul]
        simpa using mul_le_mul_of_nonneg_left (hphase_norm ξ) (norm_nonneg (A ξ))
  exact (div_le_div_of_nonneg_right hraw
    (pow_pos (show 0 < 2 * Real.pi by positivity) m).le).trans
      (physical_frequency_tail_le m A hA D H hD hH hPoint)

end
end ImbalancedChen.P5Z.AllRankCauchyCubeTail
