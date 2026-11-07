import ImbalancedChen.P5ActualIndependentUpperPairLogFields
import ImbalancedChen.P5OriginalPrimeAtlasReserveBranches

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The denominators in the EXISTING recursive all-group HB atlas are moved
into the existing smooth normalized pair profile.  The finite orders,
block banks, factor tuples, row order and original group products are
unchanged.  This is an equality on the actual arithmetic atlas, including
unit group products; it does not apply PP to the log-divided prime weight.
-/
namespace ImbalancedChen.P5ActualUpperPairHBLogTransport
noncomputable section
open Classical
open scoped BigOperators
open P5Z.LiteralHeathBrownOccurrenceWords P5Z.ActualRoughHeathBrownWords
open P5Z.HBRightClosedDyadicRoles P5Z.ActualHBDyadicOccurrenceFamily
open P5Z.SmoothChartHBDyadicPartition
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.PerGroupIntegerHBAtlasPushforward P5Z.LicensedOriginalIntegerProfile
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open Part3.OriginalProperPowerActualChart
open P5ActualIndependentUpperPairProfile

/-- Logs of ORIGINAL group products, never logs of individual HB factors. -/
def wordLog : List ℕ → ℝ
  | [] => 1
  | n :: ns => Real.log (n : ℝ) * wordLog ns

theorem wordLog_eq_map_prod (ns : List ℕ) :
    wordLog ns = (ns.map (fun n => Real.log (n : ℝ))).prod := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp only [wordLog, List.map_cons, List.prod_cons, ih]

theorem wordLog_ofFn {k : ℕ} (u : Fin k → ℕ) :
    wordLog (List.ofFn u) = ∏ i, Real.log (u i : ℝ) := by
  rw [wordLog_eq_map_prod]
  simp only [List.map_ofFn, List.prod_ofFn]

/-- The G smooth normalizer is exactly the denominator ALREADY present
in the arithmetic HB atlas.  This includes n=0,1 by totalized division. -/
theorem actual_listExtension_normalization (D : Parameters) (b : Band D)
    (N : ℕ) (ns : List ℕ) :
    listExtension (P5Z.ActualIndependentUpperPairLogFields.licence D b N) ns =
      listExtension (P5ActualIndependentUpperPairProfile.licence D b N) ns /
        wordLog ns := by
  by_cases hlen : ns.length = 2
  · have htest :
        listExtension (P5Z.ActualIndependentUpperPairLogFields.licence D b N)
            (List.ofFn (wordVector 2 ns)) =
          listExtension (P5ActualIndependentUpperPairProfile.licence D b N)
              (List.ofFn (wordVector 2 ns)) / wordLog (List.ofFn (wordVector 2 ns)) := by
      simp only [listExtension_ofFn, wordLog_ofFn, integerExtension]
      exact P5Z.ActualIndependentGroupLogNormalization.normalize_nat
        (P5ActualIndependentUpperPairProfile.profile D b N) (wordVector 2 ns)
    simpa only [ofFn_wordVector hlen] using htest
  · simp only [listExtension, dif_neg hlen, zero_div]

/-- Literal original atlas recursion with ONLY its per-group reciprocal
logs removed.  No new carrier or surjectivity premise is introduced. -/
def numeratorAtlas (chi : ℝ → ℝ) (z : ℝ) :
    List ℕ → List ℕ → (List Row → ℂ) → ℂ
  | [], [], F => F []
  | cj :: cjs, n :: ns, F =>
      psi chi ((n : ℝ) / R cj) *
        ∑ j ∈ Finset.range 3, scalar j *
          ∑ bs ∈ blockWords (hbCap cj) (2 * (j + 1)),
            ∑ fs ∈ factorTuples (2 * (j + 1)) n,
              assignedWeight z (hbCutoff cj) (roles j) bs fs *
                numeratorAtlas chi z cjs ns
                  (fun rows => F ({order := j, blocks := bs, factors := fs} :: rows))
  | _, _, _ => 0

/-- Denominators factor through EVERY genuine original group, before
any prime restriction, branch selection, mode expansion or q summation. -/
theorem actual_atlas_denominators (chi : ℝ → ℝ) (z : ℝ) :
    ∀ cjs ns : List ℕ, ∀ F : List Row → ℂ,
      atlasEval chi z cjs ns F = numeratorAtlas chi z cjs ns F / (wordLog ns : ℂ) := by
  intro cjs
  induction cjs with
  | nil =>
    intro ns F
    cases ns <;> simp [atlasEval, numeratorAtlas, wordLog]
  | cons cj cjs ih =>
    intro ns F
    cases ns with
    | nil => simp [atlasEval, numeratorAtlas, wordLog]
    | cons n ns =>
      simp only [atlasEval, numeratorAtlas, wordLog, Complex.ofReal_mul]
      simp_rw [ih, ← mul_div_assoc, ← Finset.sum_div]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem numeratorAtlas_div_const (chi : ℝ → ℝ) (z : ℝ) :
    ∀ cjs ns : List ℕ, ∀ (F : List Row → ℂ) (c : ℂ),
      numeratorAtlas chi z cjs ns (fun rows => F rows / c) =
        numeratorAtlas chi z cjs ns F / c := by
  intro cjs
  induction cjs with
  | nil => intro ns F c; cases ns <;> simp [numeratorAtlas]
  | cons cj cjs ih =>
    intro ns F c
    cases ns with
    | nil => simp [numeratorAtlas]
    | cons n ns =>
      simp only [numeratorAtlas]
      simp_rw [ih, ← mul_div_assoc, ← Finset.sum_div]

/-- Actual factorTuples certify the ORIGINAL ordered group products.
F and G may depend on the full HB rows, not merely the complete product. -/
theorem numeratorAtlas_congr_on_originalProducts (chi : ℝ → ℝ) (z : ℝ) :
    ∀ cjs ns : List ℕ, ∀ F G : List Row → ℂ,
      (∀ rows, originalProducts rows = ns → F rows = G rows) →
      numeratorAtlas chi z cjs ns F = numeratorAtlas chi z cjs ns G := by
  intro cjs
  induction cjs with
  | nil =>
    intro ns F G hFG
    cases ns with
    | nil => exact hFG [] rfl
    | cons n ns => rfl
  | cons cj cjs ih =>
    intro ns F G hFG
    cases ns with
    | nil => rfl
    | cons n ns =>
      simp only [numeratorAtlas]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      apply Finset.sum_congr rfl
      intro bs hbs
      apply Finset.sum_congr rfl
      intro fs hfs
      congr 1
      apply ih ns
      intro rows hrows
      apply hFG
      change fs.prod :: originalProducts rows = n :: ns
      rw [(factorTuples_spec (2 * (j + 1)) n fs hfs).2.1, hrows]

/-- Genuine arithmetic normalization on the SAME all-group atlas.
The arbitrary test F retains medium/no-medium decisions, all dyadic
labels, complete-product eta, Fourier factors and the SAME signed q kernel.
No nonzero-log premise is required and no normalization reserve is added. -/
theorem actual_all_group_normalization (D : Parameters) (b : Band D) (N : ℕ)
    (chi : ℝ → ℝ) (z : ℝ) (cjs ns : List ℕ) (F : List Row → ℂ) :
    atlasEval chi z cjs ns (fun rows =>
      (listExtension (P5ActualIndependentUpperPairProfile.licence D b N)
        (originalProducts rows) : ℂ) * F rows) =
      numeratorAtlas chi z cjs ns (fun rows =>
        (listExtension (P5Z.ActualIndependentUpperPairLogFields.licence D b N)
          (originalProducts rows) : ℂ) * F rows) := by
  rw [actual_atlas_denominators]
  symm
  calc
    _ = numeratorAtlas chi z cjs ns (fun rows =>
        ((listExtension (P5ActualIndependentUpperPairProfile.licence D b N)
          (originalProducts rows) : ℂ) * F rows) / (wordLog ns : ℂ)) := by
      apply numeratorAtlas_congr_on_originalProducts
      intro rows hrows
      simp only [actual_listExtension_normalization, Complex.ofReal_div, hrows]
      ring
    _ = _ := numeratorAtlas_div_const chi z cjs ns _ _

end
end ImbalancedChen.P5ActualUpperPairHBLogTransport
