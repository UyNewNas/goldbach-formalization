import ImbalancedChen.Part3OriginalAdditionalSpectralCosts
import ImbalancedChen.Part3OriginalTwoZSourceAssembly
import ImbalancedChen.Part3ZRegularSpectralPolynomial

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Connect the existing ordinary and exceptional (24)-to-(25) scalar
comparisons to an occupied original row, a fixed physical Z chart, and
the one global cutoff shared by the six physical smooth scale pairs.
No spectral quadratic-form estimate or gap is asserted here.
-/

noncomputable section
namespace ImbalancedChen.Part3.OriginalSixScaleReturnAdapter20261119
open Finset
open scoped BigOperators Classical
open OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102
open OriginalTwoZSourceAssembly20261102
open OriginalAdditionalSpectralCosts20261102
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZRegularSpectralPolynomial (regular_return_le_rpow_cutoff)
open ImbalancedChen.P3ZExceptionalSpectralPolynomial (exceptionalReturn exceptionalPolynomial)

/-- A single cutoff threshold works for every original occupied row and
every one of the six physical scale pairs. Both returned scalar terms pay
the same explicit squared cutoff factor. No spectral estimate is assumed. -/
theorem original_six_scale_returns {η : ℝ} (hη : 0 < η) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ (D : OriginalData) (x : ℝ), X ≤ x →
    ∀ (j : ℕ) (k : BlockKey) (upper : Bool) (z : Row D k)
      (hz : z.val ∈ chartLevels D k upper) (n : ℕ) (hn : n ∈ nCarrier D k z.val)
      (M N : ℝ),
      D.block.atom.residue ≠ 0 → 0 < M → 0 < N → M ≤ 2*D.bScale → D.cScale ≤ N →
      (commonMBlock (globalCutoff D x (η/2)) j).Nonempty →
    let A : ℝ := D.block.atom.residue.natAbs
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let U := dyadicScale k.2.1
    let L := U/(k.1 : ℝ)
    let Z := fixedZ D upper
    (M/N)^2 * (V*N^4*Z/(A*V*U+N^2*Z)) *
        (L+Z+A*V*U/N^2) * (V+Z+A*V*U/N^2) ≤
      x^(2*η)*(N*(L+Z)*(N+M*Z)+A*U*Z) ∧
    exceptionalReturn A U N M V Z ((7:ℝ)/32) ≤
      x^(2*η)*exceptionalPolynomial U N M Z ((7:ℝ)/32) := by
  obtain ⟨X, hX1, hX⟩ := exists_globalCutoff_six_rho_threshold hη
  refine ⟨X, hX1, ?_⟩
  intro D x hx j k upper z hz n hn M N ha hM hN hMbound hNbound hne
  dsimp only
  let A : ℝ := D.block.atom.residue.natAbs
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let U := dyadicScale k.2.1
  let L := U/(k.1 : ℝ)
  let Z := fixedZ D upper
  have hx1 : 1 ≤ x := hX1.trans hx
  have hA : 0 < A := by
    dsimp only [A]
    exact_mod_cast Int.natAbs_pos.mpr ha
  have hV : 0 < V := by dsimp [V]; positivity
  have hU : 0 < U := dyadicScale_pos _
  have hZ : 0 < Z := fixedZ_pos D upper
  have hν : 0 < (k.1 : ℝ) := by
    exact_mod_cast (nCarrier_positive_coprime D k z.val hn).1
  have hL : 0 ≤ L := (div_pos hU hν).le
  have hρ : V*M/N ≤ x^η := hX D x hx j M N hM hN hMbound hNbound hne
  have hcut : V ≤ x^η*N/M := by
    apply (le_div_iff₀ hM).mpr
    exact (div_le_iff₀ hN).mp hρ
  constructor
  · exact regular_return_le_rpow_cutoff hA hU hN hM hL hV hZ hx1 hη.le hcut
  · exact exceptional_return_le_rpow_cutoff (theta := (7:ℝ)/32) hA hU hN hM hV hZ
      (by norm_num) (by norm_num) hx1 hη.le hcut

end ImbalancedChen.Part3.OriginalSixScaleReturnAdapter20261119
end
