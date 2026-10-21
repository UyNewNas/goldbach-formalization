import ImbalancedChen.Part3PairedAlphaDeletion
import ImbalancedChen.Part3SharedFirstFactorDispersion
import ImbalancedChen.Part3SmoothCoprimeError
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual cleaned common-p row has one uniformly short progression

The row is the literal cleaned/transposed beta carrier with the signed
target-divisor deletion and the original product congruence. Its modulus
is an arbitrary integer factor from the primitive first-factor carrier.
No primality of p or admissibility of the transposed atom is assumed.

Nonzero common smoothing supplies the real endpoints V/2 <= m <= 3V,
including positivity even though its finite carrier contains zero. An
occupied row supplies coprimality, and the original Q1 geometry supplies
the uniform 3U/Q1 cardinal bound for the later common-p row Cauchy step.
No divisor-fiber sum, shifted moment or analytic estimate is proved here.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Set

def MediumAtom.cleanedCommonPProgression (d : MediumAtom) (p m : ℕ) : Finset ℕ :=
  d.cleanedAlphaAtom.transposedAtom.betaCarrier.filter
    (fun n => ¬(n : ℤ) ∣ d.residue ∧
      Int.ModEq p ((m : ℤ) * n) d.residue)

namespace CommonPFiniteReduction

private theorem q1_lt_U
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma) :
    d.Q1 < d.U := by
  have hU0 : 0 ≤ d.U := zero_le_one.trans hd.1
  have hx : 1 ≤ d.scale := by
    change 1 ≤ d.U * d.V
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 zero_le_one hU0
  have hpow : d.scale ^ (-sigma) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hsigma.le)
  have hgeom : d.Q1 < d.U * d.scale ^ (-sigma) :=
    hd.2.2.2.2.2.2.2.2.1
  exact hgeom.trans_le (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hU0)

end CommonPFiniteReduction

/-- The occupied original cleaned row retains its signed residue and
deletion gate. A nonzero common smooth weight gives its true physical
endpoints; the original primitive factor and full admissibility give
the coprimality and 3U/Q1 count, without a restriction on kappa. -/
theorem MediumAtom.cleaned_commonP_progression_geometry
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma)
    (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) (m : ℕ)
    (hpsi : d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m ≠ 0)
    (hrow : (d.cleanedCommonPProgression p m).Nonempty) :
    d.V / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ 3 * d.V ∧ 0 < m ∧
      m.Coprime p ∧
        ((d.cleanedCommonPProgression p m).card : ℝ) ≤ 3 * d.U / d.Q1 := by
  have hU0 : 0 ≤ d.U := zero_le_one.trans hd.1
  have hVpos : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQpos : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hweight : CommonSmoothCutoff.scaledDyadicCutoff d.V (m : ℝ) ≠ 0 := by
    simpa only [MediumAtom.commonSmoothWeight, MediumAtom.transposedAtom,
      MediumAtom.cleanedAlphaAtom] using hpsi
  have hmSupport : (m : ℝ) ∈
      tsupport (CommonSmoothCutoff.scaledDyadicCutoff d.V) :=
    subset_closure hweight
  have hmBounds := CommonSmoothCutoff.scaledDyadicCutoff_tsupport_subset hVpos hmSupport
  have hmpos : 0 < m := by
    have hmReal : (0 : ℝ) < m := (half_pos hVpos).trans_le hmBounds.1
    exact_mod_cast hmReal
  have hpCarrier : p ∈ factorCarrier d.Q1 := (Finset.mem_filter.mp hp).1
  have hpLower : d.Q1 ≤ (p : ℝ) :=
    (Nat.le_ceil d.Q1).trans (by
      exact_mod_cast (Finset.mem_Icc.mp hpCarrier).1)
  have hppos : 0 < p := by
    exact_mod_cast hQpos.trans_le hpLower
  have ha : Int.gcd d.residue p = 1 := by
    simpa only [Int.gcd, Int.natAbs_natCast] using (Finset.mem_filter.mp hp).2.symm
  obtain ⟨n0, hn0⟩ := hrow
  have hmod : Int.ModEq p ((m : ℤ) * n0) d.residue :=
    (Finset.mem_filter.mp hn0).2.2
  have hunit : m.Coprime p :=
    (CommonSmoothCutoff.coprime_of_product_congruent ha hmod).1
  have hsub : d.cleanedCommonPProgression p m ⊆
      d.cleanedAlphaAtom.transposedAtom.betaCarrier.filter
        (fun n : ℕ => Int.ModEq p ((n : ℤ) * m) d.residue) := by
    intro n hn
    obtain ⟨hnCarrier, _hdelete, hnmod⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnCarrier, by simpa only [mul_comm] using hnmod⟩
  have hprogression :
      ((d.cleanedAlphaAtom.transposedAtom.betaCarrier.filter
        (fun n : ℕ => Int.ModEq p ((n : ℤ) * m) d.residue)).card : ℝ) ≤
          2 * d.U / (p : ℝ) + 1 := by
    exact PairedAlphaDeletion.betaCarrier_progression_card_le
      (d := d.cleanedAlphaAtom.transposedAtom)
      (show 1 ≤ d.cleanedAlphaAtom.transposedAtom.V from hd.1) hppos hunit
  have hQU : d.Q1 < d.U := CommonPFiniteReduction.q1_lt_U hd hsigma
  have hone : (1 : ℝ) ≤ d.U / d.Q1 := by
    apply (le_div_iff₀ hQpos).mpr
    simpa only [one_mul] using hQU.le
  have hdiv : 2 * d.U / (p : ℝ) ≤ 2 * d.U / d.Q1 :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hU0) hQpos hpLower
  refine ⟨hmBounds.1, hmBounds.2, hmpos, hunit, ?_⟩
  calc
    _ ≤ ((d.cleanedAlphaAtom.transposedAtom.betaCarrier.filter
        (fun n : ℕ => Int.ModEq p ((n : ℤ) * m) d.residue)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ 2 * d.U / (p : ℝ) + 1 := hprogression
    _ ≤ 2 * d.U / d.Q1 + 1 := add_le_add hdiv le_rfl
    _ ≤ 2 * d.U / d.Q1 + d.U / d.Q1 := add_le_add_left hone _
    _ = 3 * d.U / d.Q1 := by ring

end

end ImbalancedChen.Part3
