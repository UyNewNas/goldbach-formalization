import ImbalancedChen.Part3OriginalGevreyTwoBoxSeed

/-!
Source only; uncompiled; zero formal credit. The import is a guarded frozen
source dependency, not an installed module.

This leaf identifies the previously bounded signed seed as the actual
iterated derivative of a finite convolution of the first `j+3` uniform
boxes, in an explicit order. The order depends on `j`; compatibility with
one canonical finite-convolution sequence and passage to its infinite
limit remain separate obligations.
-/

open MeasureTheory
open ImbalancedChen.Part3.OriginalGevreyBoxAverageFTC20261028
open ImbalancedChen.Part3.OriginalGevreyBoxDifference20261028
open ImbalancedChen.Part3.OriginalGevreyDerivativeTailCauchy20261028
open ImbalancedChen.Part3.OriginalGevreyTwoBoxSeed20261028

namespace ImbalancedChen.Part3.OriginalGevreyFiniteDerivativeSeed20261028

/-- The signed endpoint operator supplied by the one-box FTC lemma. -/
def endpointDiff (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  a⁻¹ * (f (x + a / 2) - f (x - a / 2))

theorem continuous_boxAverage (a : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) : Continuous (boxAverage a f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasDerivAt_boxAverage a f hf x).continuousAt

theorem continuous_endpointDiff (a : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) : Continuous (endpointDiff a f) := by
  have hp : Continuous (fun x : ℝ => f (x + a / 2)) :=
    hf.comp (continuous_id.add continuous_const)
  have hm : Continuous (fun x : ℝ => f (x - a / 2)) :=
    hf.comp (continuous_id.sub continuous_const)
  exact (hp.sub hm).const_mul a⁻¹

theorem hasDerivAt_endpointDiff (a : ℝ) (f g : ℝ → ℝ)
    (hfg : ∀ x, HasDerivAt f (g x) x) (x : ℝ) :
    HasDerivAt (endpointDiff a f) (endpointDiff a g x) x := by
  have hp : HasDerivAt (fun y => f (y + a / 2))
      (g (x + a / 2)) x :=
    (hfg (x + a / 2)).comp_add_const x (a / 2)
  have hm : HasDerivAt (fun y => f (y - a / 2))
      (g (x - a / 2)) x :=
    (hfg (x - a / 2)).comp_sub_const x (a / 2)
  simpa only [endpointDiff] using (hp.sub hm).const_mul a⁻¹

/-- Every layer is the real integral convolution with one normalized box.
For a fixed `n`, row `k` is its proposed `k`-th derivative. -/
noncomputable def frontTower (a : ℕ → ℝ) (base : ℝ → ℝ) :
    ℕ → ℕ → ℝ → ℝ
  | 0, _ => base
  | n + 1, 0 => boxAverage (a n) (frontTower a base n 0)
  | n + 1, k + 1 => endpointDiff (a n) (frontTower a base n k)

theorem frontTower_continuous (a : ℕ → ℝ) (base : ℝ → ℝ)
    (hbase : Continuous base) :
    ∀ n k, k ≤ n → Continuous (frontTower a base n k) := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simpa [frontTower] using hbase
  | succ n ih =>
      intro k hk
      cases k with
      | zero =>
          exact continuous_boxAverage (a n) _ (ih 0 (Nat.zero_le n))
      | succ k =>
          exact continuous_endpointDiff (a n) _
            (ih k (Nat.le_of_succ_le_succ hk))

theorem frontTower_hasDerivAt (a : ℕ → ℝ) (base : ℝ → ℝ)
    (hbase : Continuous base) :
    ∀ n k, k < n → ∀ x,
      HasDerivAt (frontTower a base n k)
        (frontTower a base n (k + 1) x) x := by
  intro n
  induction n with
  | zero =>
      intro k hk
      exact (Nat.not_lt_zero k hk).elim
  | succ n ih =>
      intro k hk x
      cases k with
      | zero =>
          have hc := frontTower_continuous a base hbase n 0
            (Nat.zero_le n)
          have h := hasDerivAt_boxAverage (a n)
            (frontTower a base n 0) hc x
          simpa only [frontTower, endpointDiff, div_eq_mul_inv,
            mul_comm] using h
      | succ k =>
          have hk' : k < n := Nat.lt_of_succ_lt_succ hk
          have h := hasDerivAt_endpointDiff (a n)
            (frontTower a base n k) (frontTower a base n (k + 1))
            (ih k hk') x
          simpa only [frontTower] using h

/-- The tower really is the tower of iterated derivatives, rather than
merely a family of continuous signed differences. -/
theorem frontTower_iteratedDeriv (a : ℕ → ℝ) (base : ℝ → ℝ)
    (hbase : Continuous base) (n j : ℕ) (hj : j ≤ n) :
    iteratedDeriv j (frontTower a base n 0) =
      frontTower a base n j := by
  revert hj
  induction j with
  | zero =>
      intro _
      simp only [iteratedDeriv_zero]
  | succ j ih =>
      intro hj
      have hj' : j ≤ n := Nat.le_of_lt (Nat.lt_of_succ_le hj)
      have hlt : j < n := Nat.lt_of_succ_le hj
      rw [iteratedDeriv_succ, ih hj']
      funext x
      exact (frontTower_hasDerivAt a base hbase n j hlt x).deriv

/-- The paper width turns the endpoint operator into precisely the
signed difference used in the preceding factorial bound. -/
theorem boxDifference_succ_eq_endpointDiff (f : ℝ → ℝ) (j : ℕ) :
    boxDifference f (j + 1) =
      endpointDiff (paperWidth j) (boxDifference f j) := by
  funext x
  let q : ℝ := ((j + 1 : ℕ) : ℝ)
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hw : paperWidth j / 2 = 1 / (8 * q ^ 2) := by
    dsimp [paperWidth, q]
    field_simp [hq] <;> ring
  have hi : (paperWidth j)⁻¹ = 4 * q ^ 2 := by
    dsimp [paperWidth, q]
    field_simp [hq] <;> ring
  change (4 * q ^ 2) *
      (boxDifference f j (x + 1 / (8 * q ^ 2)) -
       boxDifference f j (x - 1 / (8 * q ^ 2))) =
    (paperWidth j)⁻¹ *
      (boxDifference f j (x + paperWidth j / 2) -
       boxDifference f j (x - paperWidth j / 2))
  rw [hw, hi]

theorem frontTower_diagonal (f : ℝ → ℝ) (j : ℕ) :
    frontTower paperWidth f j j = boxDifference f j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [boxDifference_succ_eq_endpointDiff]
      simp only [frontTower]
      rw [ih]

/-- Translation commutes with a box average at the level of exact
integrands; no differentiability assumption is involved. -/
theorem boxAverage_translate (b u : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    boxAverage b (fun z => f (z + u)) x = boxAverage b f (x + u) := by
  have hintegrand :
      (fun t : ℝ => f ((x - t) + u)) =
      (fun t : ℝ => f ((x + u) - t)) := by
    funext t
    congr 1
    ring
  unfold boxAverage
  rw [hintegrand]

/-- The signed endpoint difference can be moved inside a box integral.
This is the commutation needed to expose the first `j` signed factors. -/
theorem endpointDiff_boxAverage_commute (a b : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    endpointDiff a (boxAverage b f) =
      boxAverage b (endpointDiff a f) := by
  funext x
  have hp : Continuous (fun t : ℝ => f ((x + a / 2) - t)) :=
    hf.comp (continuous_const.sub continuous_id)
  have hm : Continuous (fun t : ℝ => f ((x - a / 2) - t)) :=
    hf.comp (continuous_const.sub continuous_id)
  have hpI := hp.intervalIntegrable (-b / 2) (b / 2)
  have hmI := hm.intervalIntegrable (-b / 2) (b / 2)
  have hlinear :
      (∫ t in (-b / 2)..(b / 2),
          a⁻¹ * (f ((x + a / 2) - t) - f ((x - a / 2) - t))) =
      a⁻¹ * ((∫ t in (-b / 2)..(b / 2), f ((x + a / 2) - t)) -
        (∫ t in (-b / 2)..(b / 2), f ((x - a / 2) - t))) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hpI hmI]
  calc
    endpointDiff a (boxAverage b f) x =
        a⁻¹ * (b⁻¹ *
          (∫ t in (-b / 2)..(b / 2), f ((x + a / 2) - t)) -
          b⁻¹ *
          (∫ t in (-b / 2)..(b / 2), f ((x - a / 2) - t))) := rfl
    _ = b⁻¹ *
        (∫ t in (-b / 2)..(b / 2),
          a⁻¹ * (f ((x + a / 2) - t) - f ((x - a / 2) - t))) := by
      rw [hlinear]
      ring
    _ = boxAverage b (endpointDiff a f) x := by
      have hintegrand :
          (fun t : ℝ => a⁻¹ *
            (f ((x + a / 2) - t) - f ((x - a / 2) - t))) =
          (fun t : ℝ => a⁻¹ *
            (f ((x - t) + a / 2) - f ((x - t) - a / 2))) := by
        funext t
        congr 1 <;> ring
      unfold boxAverage endpointDiff
      rw [hintegrand]

theorem boxDifference_boxAverage_commute (b : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (j : ℕ) :
    boxDifference (boxAverage b f) j =
      boxAverage b (boxDifference f j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [boxDifference_succ_eq_endpointDiff,
        boxDifference_succ_eq_endpointDiff, ih]
      exact endpointDiff_boxAverage_commute (paperWidth j) b
        (boxDifference f j) (boxDifference_continuous f hf j)

/-- A literal finite integral convolution using each of the first `j+3`
boxes once, ordered to expose the first `j` endpoint differences. -/
noncomputable def finiteBoxForOrder (j : ℕ) : ℝ → ℝ :=
  frontTower paperWidth
    (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) j 0

/-- The previously bounded signed three-box seed is exactly the `j`-th
derivative of that finite box convolution. -/
theorem finiteBoxForOrder_iteratedDeriv (j : ℕ) :
    iteratedDeriv j (finiteBoxForOrder j) =
      threeBoxSignedSeed j := by
  have hbase : Continuous
      (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) :=
    continuous_boxAverage _ _ (twoBoxAtOrder_continuous j)
  calc
    iteratedDeriv j (finiteBoxForOrder j) =
        frontTower paperWidth
          (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) j j :=
      frontTower_iteratedDeriv paperWidth _ hbase j j le_rfl
    _ = boxDifference
          (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) j :=
      frontTower_diagonal _ j
    _ = boxAverage (paperWidth (j + 2)) (signedSeed j) := by
      rw [boxDifference_boxAverage_commute _ _
        (twoBoxAtOrder_continuous j) j]
      rfl
    _ = threeBoxSignedSeed j := rfl

theorem finiteBoxForOrder_derivative_sup (j : ℕ) (x : ℝ) :
    |iteratedDeriv j (finiteBoxForOrder j) x| ≤
      derivativeSupBound j := by
  rw [finiteBoxForOrder_iteratedDeriv]
  exact threeBoxSignedSeed_sup j x

theorem finiteBoxForOrder_derivative_lip (j : ℕ) (x y : ℝ) :
    |iteratedDeriv j (finiteBoxForOrder j) x -
      iteratedDeriv j (finiteBoxForOrder j) y| ≤
      derivativeLipReserve j * |x - y| := by
  rw [finiteBoxForOrder_iteratedDeriv]
  exact threeBoxSignedSeed_lip j x y

theorem continuous_tailAverage (a : ℕ → ℝ) (shift : ℕ)
    (base : ℝ → ℝ) (hbase : Continuous base) (n : ℕ) :
    Continuous (tailAverage a shift base n) := by
  induction n with
  | zero => simpa only [tailAverage] using hbase
  | succ n ih =>
      exact continuous_boxAverage (a (shift + n)) _ ih

/-- Moving every one of the first `j` signed factors through any finite
tail is a finite induction, so the bound is for genuine finite derivatives. -/
theorem boxDifference_tailAverage_commute (a : ℕ → ℝ) (shift : ℕ)
    (base : ℝ → ℝ) (hbase : Continuous base) (j n : ℕ) :
    boxDifference (tailAverage a shift base n) j =
      tailAverage a shift (boxDifference base j) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [tailAverage, boxDifference_boxAverage_commute
        (a (shift + n)) (tailAverage a shift base n)
        (continuous_tailAverage a shift base hbase n) j, ih]
      rfl

/-- The finite tail adds boxes `j+3,...,j+2+n` to the first `j+3`
ones. Every factor occurs exactly once as a normalized real integral. -/
noncomputable def finiteBoxForOrderTail (j n : ℕ) : ℝ → ℝ :=
  frontTower paperWidth
    (tailAverage paperWidth (j + 3)
      (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) n) j 0

theorem finiteBoxForOrderTail_iteratedDeriv (j n : ℕ) :
    iteratedDeriv j (finiteBoxForOrderTail j n) =
      tailAverage paperWidth (j + 3) (threeBoxSignedSeed j) n := by
  have hbase : Continuous
      (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) :=
    continuous_boxAverage _ _ (twoBoxAtOrder_continuous j)
  have htail : Continuous
      (tailAverage paperWidth (j + 3)
        (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) n) :=
    continuous_tailAverage paperWidth (j + 3) _ hbase n
  calc
    iteratedDeriv j (finiteBoxForOrderTail j n) =
        frontTower paperWidth
          (tailAverage paperWidth (j + 3)
            (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) n)
          j j :=
      frontTower_iteratedDeriv paperWidth _ htail j j le_rfl
    _ = boxDifference
          (tailAverage paperWidth (j + 3)
            (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) n) j :=
      frontTower_diagonal _ j
    _ = tailAverage paperWidth (j + 3)
          (boxDifference
            (boxAverage (paperWidth (j + 2)) (twoBoxAtOrder j)) j) n :=
      boxDifference_tailAverage_commute paperWidth (j + 3) _ hbase j n
    _ = tailAverage paperWidth (j + 3) (threeBoxSignedSeed j) n := by
      rw [boxDifference_boxAverage_commute _ _
        (twoBoxAtOrder_continuous j) j]
      rfl

/-- For each fixed derivative order, the actual finite derivative values
are uniformly Cauchy over the whole real line. This still does not assert
that the finite functions for different `j` are the same canonical sequence. -/
theorem finiteBoxForOrderTail_derivative_uniformCauchy (j : ℕ) :
    UniformCauchySeqOn
      (fun n x => iteratedDeriv j (finiteBoxForOrderTail j n) x)
      Filter.atTop Set.univ := by
  simpa only [finiteBoxForOrderTail_iteratedDeriv] using
    signedSeed_tail_uniformCauchy j

end ImbalancedChen.Part3.OriginalGevreyFiniteDerivativeSeed20261028
