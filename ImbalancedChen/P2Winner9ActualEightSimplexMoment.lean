import ImbalancedChen.P2Winner9SimplexCoordinateSlice
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This file supplies the missing measure step after the frozen Phase15
eightfold nested beta calculation. At each dimension it transports the
actual closed simplex set integral through Mathlib's volume-preserving
coordinate split, then applies product Fubini to its measurable indicator.
The first coordinate has the true interval [0,s], and the remaining
simplex has parameter s-t. Induction equates that actual set integral to
the previously proved nested beta integral. No final mixed identity (M),
physical affine change, witness row, or cap is asserted.

Both imported manuscript-specific sources are held source-only and have
not been compiled. No Lean, lake, checker, or numerical replay ran here.
-/

namespace ImbalancedChen.P2Winner9ActualEightSimplexMoment

noncomputable section

open Set MeasureTheory
open ImbalancedChen.P2Winner9SimplexCoordinateSlice
open ImbalancedChen.P2Winner9NestedEightSimplexMoment

def actualMomentN (n m0 : Nat) (ms : Fin n → Nat) (s : ℝ) : ℝ :=
  ∫ x in standardSimplex n s, monomial m0 ms s x

/-- The true set integral has one slanted Fubini slice. This is proved
for any continuous integrand, so no moment value is built into the
measure step. -/
theorem integral_simplex_succ (n : Nat) {s : ℝ} (hs : 0 ≤ s)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Continuous f) :
    (∫ x in standardSimplex (n + 1) s, f x) =
      ∫ t in Icc (0 : ℝ) s,
        ∫ y in standardSimplex n (s - t), f (Fin.cons t y) := by
  let e := splitEquiv n
  let S : Set (Fin (n + 1) → ℝ) := standardSimplex (n + 1) s
  let R : Set (ℝ × (Fin n → ℝ)) :=
    {p | p.1 ∈ Icc (0 : ℝ) s ∧ p.2 ∈ standardSimplex n (s - p.1)}
  have hS : MeasurableSet S := (isClosed_standardSimplex s).measurableSet
  have hR : MeasurableSet R := by
    have he : R = e ⁻¹' S := by
      simpa only [R, S, e] using (splitEquiv_preimage n s).symm
    rw [he]
    exact hS.preimage e.measurable
  have hpre : e ⁻¹' S = R := by
    simpa only [R, S, e] using splitEquiv_preimage n s
  have hInt : IntegrableOn f S :=
    hf.continuousOn.integrableOn_compact (isCompact_standardSimplex hs)
  have hIntR : IntegrableOn (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2)) R := by
    have h := ((splitEquiv_volume n).integrableOn_comp_preimage
      (splitEquiv n).measurableEmbedding (f := f) (s := S)).2 hInt
    simpa only [hpre, Function.comp_def, splitEquiv_apply] using h
  have hInd : Integrable (R.indicator
      (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))) :=
    hIntR.integrable_indicator hR
  calc
    (∫ x in standardSimplex (n + 1) s, f x) =
        ∫ p in R, f (Fin.cons p.1 p.2) := by
      have he := ((splitEquiv_volume n).setIntegral_preimage_emb
        (splitEquiv n).measurableEmbedding f S).symm
      simpa only [S, e, hpre, splitEquiv_apply] using he
    _ = ∫ p : ℝ × (Fin n → ℝ),
        R.indicator (fun p => f (Fin.cons p.1 p.2)) p :=
      (integral_indicator hR).symm
    _ = ∫ t : ℝ, ∫ y : Fin n → ℝ,
        R.indicator (fun p => f (Fin.cons p.1 p.2)) (t, y) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod _ (by simpa only [Measure.volume_eq_prod] using hInd)
    _ = ∫ t in Icc (0 : ℝ) s,
          ∫ y in standardSimplex n (s - t), f (Fin.cons t y) := by
      rw [← integral_indicator measurableSet_Icc]
      congr 1
      funext t
      by_cases ht : t ∈ Icc (0 : ℝ) s
      · have hslice : (fun y : Fin n → ℝ =>
            R.indicator (fun p => f (Fin.cons p.1 p.2)) (t, y)) =
            (standardSimplex n (s - t)).indicator
              (fun y => f (Fin.cons t y)) := by
          funext y
          by_cases hy : y ∈ standardSimplex n (s - t)
          · simp [R, ht, hy]
          · simp [R, ht, hy]
        simp only [Set.indicator_of_mem ht]
        rw [hslice, integral_indicator
          (isClosed_standardSimplex (s - t)).measurableSet]
      · have hzero : ∀ y : Fin n → ℝ, (t, y) ∉ R := by
          intro y hy
          exact ht hy.1
        simp only [Set.indicator_of_not_mem ht]
        have hz : (fun y : Fin n → ℝ =>
            R.indicator (fun p => f (Fin.cons p.1 p.2)) (t, y)) = 0 := by
          funext y
          exact Set.indicator_of_not_mem (hzero y) _
        simp [hz]

/-- Repeated Fubini identifies the actual n-dimensional integral with
the nested beta expression. The zero-dimensional volume is Mathlib's
empty product measure, a unit point mass. -/
theorem actualMomentN_eq_nested (n m0 : Nat) (ms : Fin n → Nat)
    {s : ℝ} (hs : 0 ≤ s) :
    actualMomentN n m0 ms s =
      nestedMoment m0 (List.ofFn ms) s := by
  induction n generalizing s ms with
  | zero =>
      have hset : standardSimplex 0 s = Set.univ := by
        ext x
        simp [standardSimplex, hs]
      simp [actualMomentN, hset, monomial, nestedMoment,
        Measure.volume_pi_eq_dirac]
  | succ n ih =>
      rw [actualMomentN, integral_simplex_succ n hs _
        (continuous_monomial m0 ms s)]
      have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) s) :
          (∫ y in standardSimplex n (s - t),
            monomial m0 ms s (Fin.cons t y)) =
            t^(ms 0) * nestedMoment m0
              (List.ofFn fun i : Fin n => ms i.succ) (s - t) := by
        simp_rw [monomial_cons]
        rw [integral_const_mul]
        change t^(ms 0) * actualMomentN n m0
          (fun i : Fin n => ms i.succ) (s - t) = _
        rw [ih _ (by linarith [ht.2])]
      calc
        (∫ t in Icc (0 : ℝ) s,
          ∫ y in standardSimplex n (s - t),
            monomial m0 ms s (Fin.cons t y)) =
          ∫ t in Icc (0 : ℝ) s,
            t^(ms 0) * nestedMoment m0
              (List.ofFn fun i : Fin n => ms i.succ) (s - t) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro t ht
          exact he t ht
        _ = nestedMoment m0 (List.ofFn ms) s := by
          have hlist : List.ofFn ms = ms 0 ::
              List.ofFn (fun i : Fin n => ms i.succ) := List.ofFn_succ
          rw [hlist]
          change (∫ t in Icc (0 : ℝ) s,
            t^(ms 0) * nestedMoment m0
              (List.ofFn fun i : Fin n => ms i.succ) (s - t)) =
            ∫ t in (0 : ℝ)..s,
              t^(ms 0) * nestedMoment m0
                (List.ofFn fun i : Fin n => ms i.succ) (s - t)
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hs]

/-- Genuine Lebesgue/Dirichlet monomial law on the canonical Δ8.
This combines the proved Fubini equality with the frozen nested beta
calculation; no dimension-eight moment law is a hypothesis. -/
theorem actual_eight_factorial (m0 : Nat) (ms : Fin 8 → Nat)
    {s : ℝ} (hs : 0 ≤ s) :
    ImbalancedChen.P2Winner9NestedEightSimplexMoment.actualMoment m0 ms s =
      (((m0.factorial * factorialProduct (List.ofFn ms) : Nat) : ℝ) /
        ((m0 + (List.ofFn ms).sum + 8).factorial : ℝ)) *
          s ^ (m0 + (List.ofFn ms).sum + 8) := by
  have hlen : (List.ofFn ms).length = 8 := List.length_ofFn
  calc
    _ = actualMomentN 8 m0 ms s := rfl
    _ = nestedMoment m0 (List.ofFn ms) s := actualMomentN_eq_nested 8 m0 ms hs
    _ = _ := nested_eight_factorial m0 (List.ofFn ms) hlen s

end

end ImbalancedChen.P2Winner9ActualEightSimplexMoment
