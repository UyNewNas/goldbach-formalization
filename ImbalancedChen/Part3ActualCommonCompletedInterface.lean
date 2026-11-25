import ImbalancedChen.Part3ActualLiteralPacketIntegral
import ImbalancedChen.Part3CommonCompletedInterface

/-!
# The common completion consumer for the actual separated packet

The frozen `PacketData` is the one used by the already proved native Fourier
reconstruction. Its original interval, physical phase `k 1 / (64 * P.V)`,
packet, signed cusp coefficient and n-carrier are retained below.

The finite spectral index is a dependent pair of an original row and a height
label. Only the Fourier coefficients and exceptional exponent can depend on
the height. In particular no new packet or m interval is chosen at a height.

The analytic premise is a full-block bound for the pure m-side coefficient
array, uniform in its one additive phase. The finite Cauchy consumer derives
the bilinear packet bound from that premise and the actual n-side norm. It
does not assume a full-block bound for the product of the two sides, prove
Theorem J, or instantiate automorphic Fourier coefficients.
-/

namespace ImbalancedChen.Part3.ActualCommonCompletedInterface

noncomputable section

open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open CommonIntervalFourier ExceptionalWeightExtension
open ActualIntervalGeometricSumSourceOnly

variable {κ : Type*}

/-- A spectral height belongs to one of the original finite packet rows.
The packet and its carrier will be read only through the first projection. -/
abbrev SpectralIndex (P : PacketData κ) (Height : κ → Type*) :=
  Σ row : P.rows, Height row.1

/-- The original common m-functional of one separated Fourier mode. -/
def mSide (P : PacketData κ) (k : D4 → ℤ) (Rinf : ℕ → ℂ) : ℂ :=
  ∑ m ∈ P.mCarrier, (P.completed k).weight m * Rinf m

/-- The original signed, modulated coprime packet on one fixed row. -/
def nSide (P : PacketData κ) (k : D4 → ℤ) (row : κ) (Rone : ℕ → ℂ) : ℂ :=
  ∑ n ∈ P.nCarrier row,
    signedCoefficient P.negativeCusp (modePacket (P.packet row) k P.U P.Z) n * Rone n

/-- The literal m/n row with a product Fourier kernel. Both cusp signs stay
in `signedCoefficient`; equality of the two signed complex rows is not used. -/
def rowPair (P : PacketData κ) (k : D4 → ℤ) (row : κ)
    (Rone Rinf : ℕ → ℂ) : ℂ :=
  ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier row,
    (P.completed k).weight m *
      signedCoefficient P.negativeCusp (modePacket (P.packet row) k P.U P.Z) n *
        (Rone n * Rinf m)

/-- The dyadic support gate removes the full-block extension exactly. The
same statement also covers an empty or reversed original interval. -/
theorem fullBlock_weight_sum_eq_mCarrier
    (P : PacketData κ) (k : D4 → ℤ) (j : ℕ)
    (hI : P.mCarrier ⊆ fullBlock j) (b : ℕ → ℂ) :
    (∑ m ∈ fullBlock j, (P.completed k).weight m * b m) =
      ∑ m ∈ P.mCarrier, (P.completed k).weight m * b m := by
  classical
  rw [CommonCompletedInterface.sum_weight_mul_eq_sum_inter,
    CommonCompletedInterface.sum_weight_mul_eq_sum_inter]
  change
    (∑ m ∈ fullBlock j ∩ P.mCarrier, phaseAt (P.completed k).additivePhase m * b m) =
      ∑ m ∈ P.mCarrier ∩ P.mCarrier, phaseAt (P.completed k).additivePhase m * b m
  rw [Finset.inter_eq_right.mpr hI, Finset.inter_self]

/-- The actual reconstructed mode, with its original kernel unchanged,
is exactly its common-weight full-block expansion. -/
theorem modeCore_eq_fullBlock
    (P : PacketData κ) (k : D4 → ℤ) (j : ℕ) (q : ℝ)
    (hI : P.mCarrier ⊆ fullBlock j) :
    P.modeCore k q =
      ∑ row ∈ P.rows, ∑ m ∈ fullBlock j, (P.completed k).weight m *
        (∑ n ∈ P.nCarrier row,
          signedCoefficient P.negativeCusp (modePacket (P.packet row) k P.U P.Z) n *
            P.kernel row m n q) := by
  classical
  unfold PacketData.modeCore
  apply Finset.sum_congr rfl
  intro row _hrow
  rw [fullBlock_weight_sum_eq_mCarrier P k j hI]
  simp only [Finset.mul_sum, mul_assoc]

/-- The common-interval estimate is consumed by the pure m-side on the
finite row/height family. The same `Rinf` occurs at every phase in the premise. -/
theorem spectral_mSide_weightedEnergy_le
    (P : PacketData κ) (Height : κ → Type*) [∀ row, Fintype (Height row)]
    (k : D4 → ℤ) (j : ℕ) (hI : P.mCarrier ⊆ fullBlock j)
    (bound : ℝ) {W T cap : ℝ} (hW : 0 < W) (hT : 0 < T)
    (exponent : SpectralIndex P Height → ℝ)
    (hexponent : ∀ i, 0 ≤ exponent i) (hcap : ∀ i, exponent i ≤ cap)
    (Rinf : SpectralIndex P Height → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ,
      weightedEnergy (fullBlock j) ρ T exponent Rinf ≤ bound) :
    (∑ i : SpectralIndex P Height,
      W ^ exponent i * ‖mSide P k (Rinf i)‖ ^ 2) ≤
      4 * ((2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound) := by
  classical
  unfold mSide
  have h := CommonCompletedInterface.weight_weightedEnergy_le
    (P.completed k) j bound hW hT exponent hexponent hcap Rinf full_uniform
  simpa only [fullBlock_weight_sum_eq_mCarrier P k j hI] using h

/-- Exact finite factorization of the original product-kernel row. -/
theorem rowPair_eq_nSide_mul_mSide
    (P : PacketData κ) (k : D4 → ℤ) (row : κ) (Rone Rinf : ℕ → ℂ) :
    rowPair P k row Rone Rinf = nSide P k row Rone * mSide P k Rinf := by
  classical
  unfold rowPair nSide mSide
  calc
    _ = ∑ m ∈ P.mCarrier,
        (∑ n ∈ P.nCarrier row,
          signedCoefficient P.negativeCusp (modePacket (P.packet row) k P.U P.Z) n *
            Rone n) * ((P.completed k).weight m * Rinf m) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- When the existing kernel is identified pointwise as its two Fourier
factors, the original `modeCore` becomes the sum of the same n- and m-sides.
The premise is the local kernel identity, not an estimate for that sum. -/
theorem modeCore_eq_sum_nSide_mul_mSide
    (P : PacketData κ) (k : D4 → ℤ) (q : ℝ)
    (Rone Rinf : κ → ℕ → ℂ)
    (hkernel : ∀ row ∈ P.rows, ∀ m ∈ P.mCarrier, ∀ n ∈ P.nCarrier row,
      P.kernel row m n q = Rone row n * Rinf row m) :
    P.modeCore k q = ∑ row ∈ P.rows, nSide P k row (Rone row) * mSide P k (Rinf row) := by
  classical
  calc
    P.modeCore k q = ∑ row ∈ P.rows, rowPair P k row (Rone row) (Rinf row) := by
      unfold PacketData.modeCore
      apply Finset.sum_congr rfl
      intro row hrow
      unfold rowPair
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [hkernel row hrow m hm n hn]
    _ = _ := by simp_rw [rowPair_eq_nSide_mul_mSide]

/-- Finite spectral Cauchy for the actual signed packet rows. The square
root puts precisely `W ^ exponent i` on the pure m-side energy. The n-side
norm is retained explicitly, so no product-energy bound is an input. -/
theorem spectral_pair_norm_sq_le
    (P : PacketData κ) (Height : κ → Type*) [∀ row, Fintype (Height row)]
    (k : D4 → ℤ) (j : ℕ) (hI : P.mCarrier ⊆ fullBlock j)
    (bound : ℝ) {W T cap : ℝ} (hW : 0 < W) (hT : 0 < T)
    (exponent : SpectralIndex P Height → ℝ)
    (hexponent : ∀ i, 0 ≤ exponent i) (hcap : ∀ i, exponent i ≤ cap)
    (Rone Rinf : SpectralIndex P Height → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ,
      weightedEnergy (fullBlock j) ρ T exponent Rinf ≤ bound) :
    ‖∑ i : SpectralIndex P Height, (Real.sqrt (W ^ exponent i) : ℂ) *
      rowPair P k i.1.1 (Rone i) (Rinf i)‖ ^ 2 ≤
      (∑ i : SpectralIndex P Height, ‖nSide P k i.1.1 (Rone i)‖ ^ 2) *
        (4 * ((2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound)) := by
  classical
  have hsum :
      (∑ i : SpectralIndex P Height, (Real.sqrt (W ^ exponent i) : ℂ) *
        rowPair P k i.1.1 (Rone i) (Rinf i)) =
      ∑ i : SpectralIndex P Height, nSide P k i.1.1 (Rone i) *
        ((Real.sqrt (W ^ exponent i) : ℂ) * mSide P k (Rinf i)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [rowPair_eq_nSide_mul_mSide]
    ring
  have hweight (i : SpectralIndex P Height) :
      ‖(Real.sqrt (W ^ exponent i) : ℂ) * mSide P k (Rinf i)‖ ^ 2 =
        W ^ exponent i * ‖mSide P k (Rinf i)‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Real.rpow_nonneg hW.le _)]
  have hm :
      (∑ i : SpectralIndex P Height,
        ‖(Real.sqrt (W ^ exponent i) : ℂ) * mSide P k (Rinf i)‖ ^ 2) ≤
        4 * ((2 + Real.log (period j)) ^ 2 * max 1 ((W / T) ^ cap) * bound) := by
    simp_rw [hweight]
    exact spectral_mSide_weightedEnergy_le P Height k j hI bound hW hT
      exponent hexponent hcap Rinf full_uniform
  have hc := complex_finset_cauchy_norm_sq
    (Finset.univ : Finset (SpectralIndex P Height))
    (fun i => nSide P k i.1.1 (Rone i))
    (fun i => (Real.sqrt (W ^ exponent i) : ℂ) * mSide P k (Rinf i))
  rw [hsum]
  exact hc.trans (mul_le_mul_of_nonneg_left hm
    (Finset.sum_nonneg (fun _i _hi => sq_nonneg _)))

end

end ImbalancedChen.Part3.ActualCommonCompletedInterface
