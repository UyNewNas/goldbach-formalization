import ImbalancedChen.P5ZU11ActualH248Ordinary
import ImbalancedChen.ActualPrimeIcoCellTestFunctions

/-!
One fixed four-prime box and one open H248 cell. The scalar floor query is
pulled back to affine inequalities `grid_i*w < L < grid_(i+1)*w` and
`2*w < L`. On this piece the actual ordinary H248 expression is a continuous
rational function. The existing affine sandwich prime test theorem then
transfers the genuine minimum against the canonical switched kernel to its
harmonic four-dimensional integral.

This is a local test-function primitive. It asserts no Rosser or signed AP
estimate, and does not identify the arithmetic source with this test sum.
SOURCE-WRITTEN, UNCOMPILED.
-/

namespace ImbalancedChen.P5Z.U1011FixedH248

open Set MeasureTheory Filter Topology
open Classical
open U11Integral U11Canonical U11H248
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators

noncomputable section

private theorem H248_eq_value_of_open_atom (i : Fin 200) {s : ℝ}
    (hs : s ∈ upperAtomSet (.inl i)) :
    H248 s = floorValue H248Numerators i := by
  unfold H248 upperFloor
  calc
    _ = (upperAtomSet (.inl i)).indicator
        (fun _ => floorAtomValue H248Numerators (.inl i)) s := by
      apply Finset.sum_eq_single (.inl i)
      · intro b _ hb
        exact indicator_of_notMem
          (fun h => hb (upperAtom_unique h hs)) _
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = floorValue H248Numerators i := by
      rw [indicator_of_mem hs]
      rfl

/-- The fixed open grid cell is an affine pullback when the smallest
logarithmic coordinate `w` is positive. The clamp is inactive here. -/
theorem H248_affine_open_cell (i : Fin 200) (L w : ℝ)
    (hw : 0 < w) (h2 : 2 * w < L)
    (hlo : floorGrid i.val * w < L)
    (hhi : L < floorGrid (i.val + 1) * w)
    (hgrid : floorGrid (i.val + 1) ≤ 5) :
    H248 (max 2 (L / w)) = floorValue H248Numerators i := by
  have h2q : 2 < L / w := (lt_div_iff₀ hw).2 h2
  have hlq : floorGrid i.val < L / w := (lt_div_iff₀ hw).2 hlo
  have huq : L / w < floorGrid (i.val + 1) := (div_lt_iff₀ hw).2 hhi
  have hquery : max 2 (L / w) = L / w := max_eq_right h2q.le
  have hmem : max 2 (L / w) ∈ upperAtomSet (.inl i) := by
    rw [hquery]
    change L / w ∈ Icc (1 : ℝ) 5 ∩ Ioo (floorGrid i.val) (floorGrid (i.val + 1))
    exact ⟨⟨by linarith, huq.le.trans hgrid⟩, ⟨hlq, huq⟩⟩
  exact H248_eq_value_of_open_atom i hmem

/-- The three strict floor gates as genuine continuous linear forms.
Writing an affine residual as `A v + beta`, their bounds are respectively
`2*w < L`, `grid_i*w < L`, and `L < grid_(i+1)*w`. -/
def affineCellForms (i : Fin 200) (A : LogFour →L[ℝ] ℝ) :
    Fin 3 → LogFour →L[ℝ] ℝ :=
  ![(2 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3 - A,
    floorGrid i.val • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3 - A,
    A - floorGrid (i.val + 1) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3]

def affineCellBounds (beta : ℝ) : Fin 3 → ℝ := ![beta, beta, -beta]

theorem mem_affineCellRegion_iff (i : Fin 200) (A : LogFour →L[ℝ] ℝ)
    (beta : ℝ) (v : LogFour) :
    v ∈ primeAffineGateRegion (affineCellForms i A) (affineCellBounds beta) ↔
      2 * v 3 < A v + beta ∧
      floorGrid i.val * v 3 < A v + beta ∧
      A v + beta < floorGrid (i.val + 1) * v 3 := by
  change (∀ j, affineCellForms i A j v < affineCellBounds beta j) ↔ _
  constructor
  · intro h
    have h0 : 2 * v 3 - A v < beta := by
      simpa [affineCellForms, affineCellBounds] using h 0
    have h1 : floorGrid i.val * v 3 - A v < beta := by
      simpa [affineCellForms, affineCellBounds] using h 1
    have h2 : A v - floorGrid (i.val + 1) * v 3 < -beta := by
      simpa [affineCellForms, affineCellBounds] using h 2
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2⟩ j
    fin_cases j
    · simpa [affineCellForms, affineCellBounds] using
        (show 2 * v 3 - A v < beta by linarith)
    · simpa [affineCellForms, affineCellBounds] using
        (show floorGrid i.val * v 3 - A v < beta by linarith)
    · simpa [affineCellForms, affineCellBounds] using
        (show A v - floorGrid (i.val + 1) * v 3 < -beta by linarith)

def ordinaryCell (i : Fin 200) (L : LogFour → ℝ) (v : LogFour) : ℝ :=
  4 * (1 - floorValue H248Numerators i) / L v

def fixedMinimum (i : Fin 200) (L : LogFour → ℝ) (v : LogFour) : ℝ :=
  min (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
    (ordinaryCell i L v)

/-- The exact H248 ordinary candidate equals its smooth cell formula;
this equality includes the original `max 2` query. -/
theorem ordinary_eq_cell (i : Fin 200) (L : LogFour → ℝ) (v : LogFour)
    (hw : 0 < v 3) (h2 : 2 * v 3 < L v)
    (hlo : floorGrid i.val * v 3 < L v)
    (hhi : L v < floorGrid (i.val + 1) * v 3)
    (hgrid : floorGrid (i.val + 1) ≤ 5) :
    ordinaryKernel H248 (fun _ => L) 0 v = ordinaryCell i L v := by
  unfold ordinaryKernel ordinaryCell
  rw [H248_affine_open_cell i (L v) (v 3) hw h2 hlo hhi hgrid]

private theorem cube_subset_compactBox :
    Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ)) ⊆
      compactBox := by
  intro v hv
  constructor
  · intro j
    exact (hv j (Set.mem_univ _)).1
  · intro j
    exact (hv j (Set.mem_univ _)).2

/-- The selected ordinary expression is continuous on the fixed positive
box, and so is its minimum with the actual canonical switched kernel. -/
theorem continuousOn_fixedMinimum (i : Fin 200) (L : LogFour → ℝ)
    (hL : ContinuousOn L
      (Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))))
    (hpos : ∀ v ∈ Set.univ.pi
      (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ)), 0 < L v) :
    ContinuousOn (fixedMinimum i L)
      (Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))) := by
  have hs := (continuousOn_canonical_switched_compactBox currentK).mono
    cube_subset_compactBox
  have ho : ContinuousOn (ordinaryCell i L)
      (Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))) := by
    exact continuousOn_const.div hL (fun v hv => (hpos v hv).ne')
  exact hs.min ho

/-- A single fixed four-dimensional affine-sandwich region on which the
H248 query lies in one open grid cell has the actual prime harmonic limit
for the minimum. All affine gate and floor-cell conditions are geometric,
and no target prime-sum convergence is assumed. -/
theorem tendsto_actualPrimeBox_fixed_H248_minimum {r : ℕ}
    (i : Fin 200) (L : LogFour → ℝ)
    (hL : ContinuousOn L
      (Set.univ.pi (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))))
    (hpos : ∀ v ∈ Set.univ.pi
      (fun _ : Fin 4 => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ)), 0 < L v)
    (G : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hG : ∀ j, G j ≠ 0) (R : Set LogFour) (hR : MeasurableSet R)
    (hstrict : primeAffineGateRegion G c ⊆ R)
    (hweak : ∀ v ∈ R, ∀ j, G j v ≤ c j)
    (hcell : ∀ v ∈ R, 0 < v 3 ∧ 2 * v 3 < L v ∧
      floorGrid i.val * v 3 < L v ∧
      L v < floorGrid (i.val + 1) * v 3)
    (hgrid : floorGrid (i.val + 1) ≤ 5) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ))
      (fun _ : Fin 4 => (59 / 250 : ℝ))
      (R.indicator (fun v => min
        (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
        (ordinaryKernel H248 (fun _ => L) 0 v)))) atTop
      (𝓝 (∫ v in logPrimeBox
          (fun _ : Fin 4 => (417 / 5000 : ℝ))
          (fun _ : Fin 4 => (59 / 250 : ℝ)) ∩ R,
        min (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
          (ordinaryKernel H248 (fun _ => L) 0 v) * ∏ j, 1 / v j)) := by
  have heq (v : LogFour) (hv : v ∈ R) :
      min (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
        (ordinaryKernel H248 (fun _ => L) 0 v) = fixedMinimum i L v := by
    rw [fixedMinimum, ordinary_eq_cell i L v
      (hcell v hv).1 (hcell v hv).2.1 (hcell v hv).2.2.1
      (hcell v hv).2.2.2 hgrid]
  have hf : R.indicator (fun v => min
        (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
        (ordinaryKernel H248 (fun _ => L) 0 v)) =
      R.indicator (fixedMinimum i L) := by
    funext v
    by_cases hv : v ∈ R
    · simp only [indicator_of_mem hv, heq v hv]
    · simp only [indicator_of_notMem hv]
  have hlim := tendsto_actualPrimeBoxTestSum_cube_affineSandwich
    (by norm_num : (0 : ℝ) < 417 / 5000)
    (by norm_num : (417 / 5000 : ℝ) < 59 / 250)
    G c hG R hR hstrict hweak (fixedMinimum i L)
    (continuousOn_fixedMinimum i L hL hpos)
  have hint : (∫ v in logPrimeBox
      (fun _ : Fin 4 => (417 / 5000 : ℝ))
      (fun _ : Fin 4 => (59 / 250 : ℝ)) ∩ R,
        fixedMinimum i L v * ∏ j, 1 / v j) =
      ∫ v in logPrimeBox
        (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ : Fin 4 => (59 / 250 : ℝ)) ∩ R,
          min (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)
            (ordinaryKernel H248 (fun _ => L) 0 v) * ∏ j, 1 / v j := by
    apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter hR)
    intro v hv
    rw [heq v hv.2]
  rw [hf, ← hint]
  exact hlim

end

end ImbalancedChen.P5Z.U1011FixedH248
