import ImbalancedChen.Part3PrintedHolomorphicRegularNorm
import ImbalancedChen.Part3OriginalExceptionalPostRemovalPair

/-! The two holomorphic rows in the regular spectral Cauchy estimate.
The m interval and additive phase are common to all levels. The n row
uses the original modulated beta after the coprime packet operation. -/

noncomputable section
namespace ImbalancedChen.Part3.OriginalPrintedHolomorphicFourierPair20261123

open Finset
open scoped BigOperators MatrixGroups ComplexConjugate InnerProductSpace
open scoped OriginalHolomorphicPeterssonSpace20261112
open PrintedHolomorphicRegularNorm20261123 (Atom atomHeight printedCoeff measuredRow finite_cumulative)
open OriginalRegularHolomorphicCumulative20261113 (WeightBasis)
open OriginalRegularPacketTest20261113 (Dyadic energy)
open RegularCumulativeShellPayment20261102 (heightCut regularBase regular_R1_finite)
open OriginalExceptionalPostRemovalPair20261113 (rowLength rowMass)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds commonMBlock_classical_support)
open OriginalCommonPoissonLanes20261102 (commonMBlock commonPoissonCompleted commonPoissonCompleted_weight)
open OriginalContinuousClassRemoval20261110 (M reduced markedRow)
open OriginalPrincipalTraceRow20261102r (principalTraceSign)
open ActualPrincipalCuspOneRemoval20261102r (sourceCuspPhase sourceCuspPhase_norm)
open OriginalTwoZFourierAssembly20261102 (modulatedBeta norm_modulatedBeta)
open OriginalSignedTraceInput20261102 (traceNegative)
open OriginalCompletedReciprocalSource20261102 (OriginalData)
open OriginalSimultaneousPrefixCompletion20261102 (prefixPeriod)
open OriginalPrimaryPacketRows20261102 (BlockKey levelCarrier levelCarrier_has_n nCarrier
  nCarrier_positive_coprime nCarrier_dyadic)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale)
open P3NativePeriod64SamplingSourceOnly (D4)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

/-- The conjugation inside M restores the original Fourier weight when
the common row is conjugated in the bilinear expression. -/
def commonRow (q : ℕ+) (J j : ℕ) (ell : D4 → ℤ)
    (bases : ∀ v, WeightBasis q.val v) (p : Atom q.val) : ℂ :=
  M J j ell (fun m => printedCoeff q.val p.1 false (bases p.1 p.2) m.toNat)

/-- On the same-sign branch the integer passed by reduced is the
positive original n at cusp one. -/
def reducedRow (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (q : ℕ+) (hq : q.val ∈ levelCarrier D k) (upper negativeM : Bool) (ell : D4 → ℤ)
    (bases : ∀ v, WeightBasis q.val v) (p : Atom q.val) : ℂ :=
  reduced D r k ⟨q.val,hq⟩ upper negativeM ell
    (fun n => printedCoeff q.val p.1 true (bases p.1 p.2) n.toNat)

private theorem occupied_support (D : OriginalData) (k : BlockKey)
    (q : ℕ+) (hq : q.val ∈ levelCarrier D k) :
    1/2 ≤ rowLength k ∧ Dyadic (rowLength k) (nCarrier D k q.val) := by
  obtain ⟨n₀, hn₀⟩ := levelCarrier_has_n D k hq
  have h₀ := nCarrier_positive_coprime D k q.val hn₀
  have hν : 0 < (k.1 : ℝ) := by exact_mod_cast h₀.1
  have hband : Dyadic (rowLength k) (nCarrier D k q.val) := by
    intro n hn
    obtain ⟨lo,hi⟩ := nCarrier_dyadic D k q.val hn
    rw [Nat.cast_mul] at lo hi
    constructor
    · exact (div_lt_iff₀ hν).mpr (by simpa only [mul_comm (k.1 : ℝ) (n : ℝ)] using lo)
    · change (n : ℝ) ≤ 2*(dyadicScale k.2.1/(k.1 : ℝ))
      rw [← mul_div_assoc]
      exact (le_div_iff₀ hν).mpr (by simpa only [mul_comm (k.1 : ℝ) (n : ℝ)] using hi)
  have hn₁ : (1 : ℝ) ≤ n₀ := by exact_mod_cast Nat.succ_le_of_lt h₀.2.1
  exact ⟨by linarith only [hn₁, (hband n₀ hn₀).2], hband⟩

/-- Analytic appendix, regular summation on a single original level and
Fourier mode. Both cumulative hypotheses of regular_R1_finite are
supplied by the printed Petersson norm. The scalar Bessel test retains
its two pointwise bounds. -/
theorem original_fourier_pair (ε : ℝ) (hε : 0 < ε) :
    ∃ Dε : ℝ, 0 < Dε ∧ ∀ (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (q : ℕ+) (hq : q.val ∈ levelCarrier D k) (upper negativeM : Bool)
    (J j : ℕ) (ell : D4 → ℤ), traceNegative D k negativeM = false →
    ∀ (bases : ∀ v, WeightBasis q.val v) (F : Finset (Atom q.val))
      (H : Atom q.val → ℂ) {C Y : ℝ}, 0 ≤ C → 0 < Y →
      (∀ p ∈ heightCut F (atomHeight q.val) (regularBase Y),
        ‖H p‖ ≤ C*(1+|Real.log Y|)/(1+Y)) →
      (∀ p ∈ F, regularBase Y ≤ |atomHeight q.val p| →
        ‖H p‖ ≤ C*(1/(|atomHeight q.val p|^2*Real.sqrt |atomHeight q.val p|) +
          Y/|atomHeight q.val p|^3)) →
      ∀ d : ℕ,
        ‖∑ p ∈ heightCut F (atomHeight q.val) ((4 : ℝ)^d*regularBase Y),
          ((1/(2*Real.pi) : ℝ) : ℂ) *
            (H p * reducedRow D r k q hq upper negativeM ell bases p *
              conj (commonRow q J j ell bases p))‖ ≤
          516*C*(1+|Real.log Y|)/(1+Y) *
            Real.sqrt (((1+Y^2+(rowLength k)^(1+ε)/(q.val : ℝ)) *
                        (Dε * rowMass D r k q)) *
              ((1+Y^2+(classicalMScale j)^(1+ε)/(q.val : ℝ)) *
                        (Dε * ((commonMBlock J j).card : ℝ)))) := by
  obtain ⟨Dε, hDε, bound⟩ := finite_cumulative ε hε
  refine ⟨Dε, hDε, ?_⟩
  intro D r k q hq upper negativeM J j ell hsign bases F H C Y hC hY hlow hdecay d
  classical
  let μ : ℝ := 1/(2*Real.pi)
  let w : ℂ := Real.sqrt μ
  let A := reducedRow D r k q hq upper negativeM ell bases
  let B := commonRow q J j ell bases
  let weightedN := fun p => w * A p
  let weightedM := fun p => w * B p
  let wM := fun m : ℕ => star ((commonPoissonCompleted J j (ell 1)).weight m)
  let wN := fun n : ℕ => modulatedBeta D r k upper ell q.val n * sourceCuspPhase q.val (-(n : ℤ))
  have hs : principalTraceSign D k negativeM = 1 := by simp [principalTraceSign, hsign]
  have mRow : weightedM =
      measuredRow q.val false (commonMBlock J j) wM bases := by
    funext p
    simp only [weightedM, w, μ, B, commonRow, M, markedRow, measuredRow, wM, Int.toNat_natCast]
  have nRow : weightedN =
      measuredRow q.val true (nCarrier D k q.val) wN bases := by
    funext p
    simp only [weightedN, w, μ, A, reducedRow, reduced, markedRow, measuredRow, wN, hs,
      one_mul, Int.toNat_natCast]
  have mMass : energy (commonMBlock J j) wM = ((commonMBlock J j).card : ℝ) := by
    calc
      _ = ∑ _m ∈ commonMBlock J j, (1 : ℝ) := by
        apply sum_congr rfl
        intro m hm
        change ‖star ((commonPoissonCompleted J j (ell 1)).weight m)‖^2 = 1
        rw [norm_star, commonPoissonCompleted_weight J j (ell 1) m hm, Complex.norm_exp]
        simp [Complex.mul_re, Complex.mul_im]
      _ = _ := by simp
  have nMass : energy (nCarrier D k q.val) wN = rowMass D r k q := by
    simp only [energy, wN, norm_mul, sourceCuspPhase_norm, mul_one, norm_modulatedBeta, rowMass]
  obtain ⟨hL, nBand⟩ := occupied_support D k q hq
  have hP := (classicalMScale_bounds j).1
  have mBand : Dyadic (classicalMScale j) (commonMBlock J j) :=
    fun m hm => commonMBlock_classical_support J j hm
  have nCost := mul_nonneg hDε.le
    (show 0 ≤ rowMass D r k q from sum_nonneg (fun _ _ => sq_nonneg _))
  have mCost := mul_nonneg hDε.le (Nat.cast_nonneg (α := ℝ) (commonMBlock J j).card)
  have u0 : 0 ≤ (rowLength k)^(1+ε)/(q.val : ℝ) :=
    div_nonneg (Real.rpow_nonneg (by linarith only [hL]) _) (Nat.cast_nonneg _)
  have v0 : 0 ≤ (classicalMScale j)^(1+ε)/(q.val : ℝ) :=
    div_nonneg (Real.rpow_nonneg (by linarith only [hP]) _) (Nat.cast_nonneg _)
  have hw : w^2 = (μ : ℂ) := by
    change (Real.sqrt μ : ℂ)^2 = (μ : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt (show 0 ≤ μ by dsimp [μ]; positivity)]
  have hwc : conj w = w := Complex.conj_ofReal _
  calc
    _ = ‖∑ p ∈ heightCut F (atomHeight q.val) ((4 : ℝ)^d*regularBase Y),
          H p * weightedN p * conj (weightedM p)‖ := by
      apply congrArg norm
      apply sum_congr rfl
      intro p _
      change (μ : ℂ)*(H p*A p*conj (B p)) = H p*(w*A p)*conj (w*B p)
      rw [map_mul, hwc, ← hw]
      ring
    _ ≤ _ := regular_R1_finite F (atomHeight q.val) H weightedN weightedM
      hC hY u0 v0 nCost mCost (by
        intro T hT
        rw [nRow]
        simpa only [nMass] using bound q.val true hT hL (nCarrier D k q.val) wN nBand bases F)
      (by
        intro T hT
        rw [mRow]
        simpa only [mMass] using bound q.val false hT hP (commonMBlock J j) wM mBand bases F)
      hlow hdecay d

end ImbalancedChen.Part3.OriginalPrintedHolomorphicFourierPair20261123
end
