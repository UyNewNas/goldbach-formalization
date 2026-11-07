import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapModulusConvolution

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal physical coefficient splits into finitely many selected-cell
convolutions with its own frozen native residual coefficient. The rough
factor is the pushforward of the ORIGINAL selected tuples, with their
actual multiplicities. In particular, E is still evaluated at the actual
last pair, and exact grid walls keep their unique arithmetic owner.

This establishes a two-block convolution. It deliberately makes no
separation claim for the four prime slots: their order and the same E
still occur in selectedCellTuples. Strong PP remains OPEN.
-/

namespace ImbalancedChen.P5Z.U1011NativeSelectedCellConvolution

noncomputable section
open Classical
open scoped BigOperators
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy)
open U1011OriginalSixteenJointNearCapCompiler
open U1011OriginalSixteenJointNearCapModulusConvolution
open U1011OriginalSixteenJointNativeCompiler (selectedCellTuples)

/-- The entire true native residual row is frozen by the geometric cell. -/
def residualContribution (n N : ℕ) (eta : ℚ) (j : Grid n) (b q : ℕ) : ℝ :=
  ∑ d ∈ rowSupport (boxPolicy (gridBox n j)) (gridBox n j) eta N,
    if b * d = q then rowCoefficient (boxPolicy (gridBox n j)) (gridBox n j) eta N d else 0

def cellConvolution (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop)
    (j : Grid n) (q : ℕ) : ℝ :=
  ∑ t ∈ selectedCellTuples n N E j, residualContribution n N eta j (fullPrefix t) q

def prefixSupport (n N : ℕ) (E : ℕ × ℕ → Prop) (j : Grid n) : Finset ℕ :=
  (selectedCellTuples n N E j).image fullPrefix

def prefixFibre (n N : ℕ) (E : ℕ × ℕ → Prop) (j : Grid n) (b : ℕ) : Finset Four :=
  (selectedCellTuples n N E j).filter (fun t => fullPrefix t = b)

/-- A prefix coefficient counts actual tuples. It is not silently replaced
by an indicator, nor divided by an unspecified permutation factorial. -/
def prefixMultiplicity (n N : ℕ) (E : ℕ × ℕ → Prop) (j : Grid n) (b : ℕ) : ℕ :=
  (prefixFibre n N E j b).card

/-- Expand the exact native physical fibre, including zero residual rows. -/
theorem sigma_eq_native_tuple_sum (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) :
    sigma n N eta E q =
      ∑ t ∈ ordinaryTuples n N E, ∑ d ∈ support n N eta t,
        if fullPrefix t * d = q then coefficient n N eta t d else 0 := by
  unfold sigma fibre
  rw [Finset.sum_filter]
  rw [marks, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro t ht
  rw [activeRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hz : coefficient n N eta t d = 0 <;> simp [weight, modulus, hz]

/-- Exact finite cell splitting of the actual same-rho coefficient.
There is no geometric approximation and no boundary deletion. -/
theorem sigma_eq_sum_cellConvolution {n N : ℕ} (hN : 1 < N)
    (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) :
    sigma n N eta E q = ∑ j : Grid n, cellConvolution n N eta E j q := by
  rw [sigma_eq_native_tuple_sum]
  rw [U1011OriginalSixteenJointNativeCompiler.exact_cell_reindex]
  apply Finset.sum_congr rfl
  intro j hj
  unfold cellConvolution
  apply Finset.sum_congr rfl
  intro t ht
  have hg := U1011OriginalSixteenJointNativeCompiler.selectedCellTuples_geometry hN ht
  obtain ⟨hs, hc⟩ := compiled_static_on_cell n N eta hg
  unfold residualContribution
  rw [hs]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hc d]

/-- The rough block is the literal prefix pushforward. This formula
retains tuple multiplicity even before invoking any uniqueness theorem. -/
theorem cellConvolution_eq_prefix_convolution (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (j : Grid n) (q : ℕ) :
    cellConvolution n N eta E j q =
      ∑ b ∈ prefixSupport n N E j,
        (prefixMultiplicity n N E j b : ℝ) * residualContribution n N eta j b q := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := selectedCellTuples n N E j) (t := prefixSupport n N E j)
    (g := fullPrefix) (fun t ht => Finset.mem_image_of_mem fullPrefix ht)
    (fun t => residualContribution n N eta j (fullPrefix t) q)
  unfold cellConvolution
  rw [← hf]
  apply Finset.sum_congr rfl
  intro b hb
  have hconst :
      (∑ t ∈ (selectedCellTuples n N E j).filter (fun t => fullPrefix t = b),
        residualContribution n N eta j (fullPrefix t) q) =
      ∑ _t ∈ prefixFibre n N E j b, residualContribution n N eta j b q := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [(Finset.mem_filter.mp ht).2]
  rw [hconst]
  simp [prefixMultiplicity, nsmul_eq_mul]

/-- Literal moduli and multiplicities, with the original E untouched. -/
theorem sigma_eq_cell_prefix_residual_convolution {n N : ℕ} (hN : 1 < N)
    (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) :
    sigma n N eta E q =
      ∑ j : Grid n, ∑ b ∈ prefixSupport n N E j,
        (prefixMultiplicity n N E j b : ℝ) *
          ∑ d ∈ rowSupport (boxPolicy (gridBox n j)) (gridBox n j) eta N,
            if b * d = q then
              rowCoefficient (boxPolicy (gridBox n j)) (gridBox n j) eta N d else 0 := by
  rw [sigma_eq_sum_cellConvolution hN]
  apply Finset.sum_congr rfl
  intro j hj
  exact cellConvolution_eq_prefix_convolution n N eta E j q

end
end ImbalancedChen.P5Z.U1011NativeSelectedCellConvolution
