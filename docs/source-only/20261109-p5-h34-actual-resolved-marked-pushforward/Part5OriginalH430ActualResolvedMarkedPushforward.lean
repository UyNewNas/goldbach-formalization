import ImbalancedChen.Part5OriginalH430AllActionOccurrenceSource
import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted

/-!
P5.6 / h34: push the ACTUAL resolved request-level LIST POSITIONS into
the GENUINE positive finite marked-product Phi/Theta normalization.

The support consists of parent integer products of resolved requests at
one actual generation. Multiplicities are NOT discarded: distinct Fin
positions with the same product contribute separate positive path marks
to the same sigma(d). This is a legitimate finite marked family attached
to the generated request history, NOT a proof that it equals the
original U3/U4 arithmetic selected-count family. In particular q != d
is never assumed or asserted. Its primitive level gates must still be
verified before applying analytic estimates.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualResolvedMarkedPushforward

noncomputable section
open scoped Classical BigOperators
open Finset Wu2008DoubleSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430AllActionOccurrenceSource
open P2EnhancedTwentyOneSameQWeighted

/-- One actual level-list position has one original integer parent product. -/
private abbrev productAt {N n : ℕ} {root : Root} {tau : ℝ}
    {p : ℕ} {g : Fin 430}
    (l : Index N n root tau p g) : ℕ :=
  parentProduct (levelOccurrence l).current.old

/-- The original resolver, not an arbitrary action picker, removes only
unresolved positions. Scalar and specified-cell reads remain distinct. -/
def activePositions (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l =>
    ∃ i : Fin 200,
      resolve (g.val+1) (levelOccurrence l).current = some i)

/-- Physical product support; multiple positions MAY have this product. -/
def activeProductSupport (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : Finset ℕ :=
  (activePositions N n root tau p g).image (fun l => productAt l)

/-- The original positive path marks, aggregated rather than quotienting
away collisions among distinct original Fin positions. -/
def activeProductSigma (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (d : ℕ) : ℝ :=
  ∑ l ∈ activePositions N n root tau p g,
    if productAt l = d then levelMark l else 0

/-- All literal request-path marks are positive, so this genuine sigma
is nonnegative even when the resolved level is empty. -/
theorem activeProductSigma_nonneg (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (d : ℕ) :
    0 ≤ activeProductSigma N n root tau p g d := by
  unfold activeProductSigma
  apply Finset.sum_nonneg
  intro l hl
  by_cases h : productAt l = d
  · simpa [h] using (mark_pos (levelOccurrence l)).le
  · simp [h]

/-- Any actual resolved occurrence contributes strictly positive weight
at its product, including when another occurrence shares the product. -/
theorem activeProductSigma_pos_of_member (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n root tau p g)
    (hl : l ∈ activePositions N n root tau p g) :
    0 < activeProductSigma N n root tau p g (productAt l) := by
  unfold activeProductSigma
  apply Finset.sum_pos'
  · intro j hj
    by_cases h : productAt j = productAt l
    · simpa [h] using (mark_pos (levelOccurrence j)).le
    · simp [h]
  · exact ⟨l, hl, by simpa using (mark_pos (levelOccurrence l))⟩

/-- Exact occurrence-preserving pushforward for EVERY signed test F.
The product map need not be injective; all list positions are summed
BEFORE multiplying by an arbitrary product-dependent real test. -/
theorem activeProduct_signed_pushforward (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℕ → ℝ) :
    (∑ d ∈ activeProductSupport N n root tau p g,
      activeProductSigma N n root tau p g d * F d) =
    ∑ l ∈ activePositions N n root tau p g,
      levelMark l * F (productAt l) := by
  classical
  unfold activeProductSupport activeProductSigma
  calc
    (∑ d ∈ (activePositions N n root tau p g).image (fun l => productAt l),
        (∑ l ∈ activePositions N n root tau p g,
          if productAt l = d then levelMark l else 0) * F d) =
      ∑ d ∈ (activePositions N n root tau p g).image (fun l => productAt l),
        ∑ l ∈ activePositions N n root tau p g,
          if productAt l = d then levelMark l * F d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l hl
        by_cases h : productAt l = d <;> simp [h]
    _ = ∑ l ∈ activePositions N n root tau p g,
          ∑ d ∈ (activePositions N n root tau p g).image (fun j => productAt j),
            if productAt l = d then levelMark l * F d else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ l ∈ activePositions N n root tau p g,
          levelMark l * F (productAt l) := by
        apply Finset.sum_congr rfl
        intro l hl
        have hmem : productAt l ∈
            (activePositions N n root tau p g).image (fun j => productAt j) :=
          Finset.mem_image.mpr ⟨l, hl, rfl⟩
        simp [hmem]

/-- The installed TRUE positive Phi source, at this root's actual Q,
is exactly the signed-multiplicity-preserving generated source. The
identity does not convert original arithmetic q-count into Phi. -/
theorem activeProduct_Phi_exact (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    Phi N (rootQ N n root tau p)
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) (11/5) =
    ∑ l ∈ activePositions N n root tau p g,
      levelMark l *
        (sourceSieveCount N (productAt l) ((productAt l) * N)
          (cutoff (rootQ N n root tau p) (productAt l) (11/5)) : ℝ) := by
  simpa only [Phi] using
    activeProduct_signed_pushforward N n root tau p g
      (fun d => (sourceSieveCount N d (d*N)
        (cutoff (rootQ N n root tau p) d (11/5)) : ℝ))

/-- Its TRUE same-Q Theta has exactly the original per-occurrence mark
and arithmetic kernel. Neither a q-tag owner nor Theta-count conversion
is postulated. -/
theorem activeProduct_Theta_exact (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    Theta N (rootQ N n root tau p)
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) =
    4 * logarithmicIntegral N *
      ∑ l ∈ activePositions N n root tau p g,
        levelMark l * (wuSingularSeries ((productAt l) * N) /
          ((Nat.totient (productAt l) : ℝ) *
            Real.log (rootQ N n root tau p / (productAt l : ℝ)))) := by
  have hsum :=
    activeProduct_signed_pushforward N n root tau p g
      (fun d => wuSingularSeries (d*N) /
        ((Nat.totient d : ℝ) *
          Real.log (rootQ N n root tau p / (d : ℝ))))
  simpa only [Theta, mul_div_assoc] using
    congrArg (fun x : ℝ => 4 * logarithmicIntegral N * x) hsum

/-- Nonempty genuine resolved level plus checked primitive marked gates
gives a positive SAME-Q normalizer, with no fabricated count estimate. -/
theorem activeProduct_Theta_pos (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N)
    (hnonempty : (activePositions N n root tau p g).Nonempty)
    (hdpos : ∀ l ∈ activePositions N n root tau p g, 0 < productAt l)
    (hlevel : ∀ l ∈ activePositions N n root tau p g,
      1 < rootQ N n root tau p / (productAt l : ℝ)) :
    0 < Theta N (rootQ N n root tau p)
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) := by
  have hd : ∀ d ∈ activeProductSupport N n root tau p g, 0 < d := by
    intro d hmem
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hmem
    exact hdpos l hl
  have hr : ∀ d ∈ activeProductSupport N n root tau p g,
      1 < rootQ N n root tau p / (d : ℝ) := by
    intro d hmem
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hmem
    exact hlevel l hl
  obtain ⟨l, hl⟩ := hnonempty
  have hmem : productAt l ∈ activeProductSupport N n root tau p g :=
    Finset.mem_image.mpr ⟨l, hl, rfl⟩
  exact Theta_pos hN (rootQ N n root tau p)
    (activeProductSupport N n root tau p g)
    (activeProductSigma N n root tau p g)
    hd (fun d _ => activeProductSigma_nonneg N n root tau p g d)
    hr ⟨productAt l, hmem,
      activeProductSigma_pos_of_member N n root tau p g l hl⟩

end
end ImbalancedChen.Part5OriginalH430ActualResolvedMarkedPushforward
