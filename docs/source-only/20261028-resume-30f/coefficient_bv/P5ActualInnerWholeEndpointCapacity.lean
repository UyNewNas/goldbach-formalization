import ImbalancedChen.P5All16InnerCartesianDictionary
import ImbalancedChen.P5OriginalOrdinaryWholeAtomMonomials

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Concrete ORIGINAL fine-cell endpoint port to the existing ordinary15
whole-atom numerical action. All rough endpoint cubes and order are
derived from innerCells itself with the actual rank/mesh width payment.
No Dwell/factorization/capacity target is an input.

This action includes the original four marked slots. It is NOT silently
identified with the signed-owner's residual-only computedGroups action.
The common coloured-prefix alphabet/source identity is still necessary
to pass these numerical bounds to that same normalized tensor. W, small
beta endpoint consumption and the original group SW supplier are not
claimed by this ordinary15 prime-endpoint theorem.
-/

namespace ImbalancedChen.P5Z.ActualInnerWholeEndpointCapacity
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles
open PresievedRoughSlotAffineGates PresievedRoughGateMeshReserve
open SelectedRealEndpointSupport SelectedRealWholeAtomGroups
open OriginalNearCapRealEndpointGeometry OriginalOrdinaryWholeAtomMonomials

def roughWidth (r m : ℕ) : ℝ := (r + 3 : ℝ) * logPrimeMeshStep 0 1 m

/-- The same ACTUAL inner cell gives nonnegative antitone rough upper
endpoints. Its positive mesh padding pays every original upper cube. -/
theorem actual_inner_endpoint_inputs {r m : ℕ} (ell : ℝ)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 ell m) :
    (∀ i, 0 ≤ logPrimeMeshHi 0 1 m j i) ∧
      Antitone (logPrimeMeshHi 0 1 m j) ∧
      (∀ i : Fin r, Even i.val →
        cube (logPrimeMeshHi 0 1 m j) i < ell + roughWidth r m) := by
  have hab : (0 : ℝ) < 1 := by norm_num
  have hstep : 0 < logPrimeMeshStep 0 1 m := logPrimeMeshStep_pos hab m
  have hlo : logPrimeMeshLo 0 1 m j ∈ cell 0 1 m j := by
    apply mem_logPrimeMeshCell.mpr
    intro i
    exact ⟨le_rfl, (logPrimeMeshLoHi_bounds hab m j i).2.1⟩
  obtain ⟨hregion, hanti⟩ := (roughRegion_dictionary ell _).mp ((Finset.mem_filter.mp hj).2 _ hlo)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (logPrimeMeshLoHi_bounds hab m j i).1.trans
      (logPrimeMeshLoHi_bounds hab m j i).2.1.le
  · intro i k hik
    rw [logPrimeMeshHi_eq_lo_add_step, logPrimeMeshHi_eq_lo_add_step]
    exact add_le_add_right (hanti.antitone hik) _
  · intro i hi
    have hcount : ((Finset.univ.filter (fun k : Fin r => k.val < i.val)).card : ℝ) ≤ r := by
      have hn : (Finset.univ.filter (fun k : Fin r => k.val < i.val)).card ≤ r := by
        simpa only [Fintype.card_fin] using
          Finset.card_le_univ (Finset.univ.filter (fun k : Fin r => k.val < i.val))
      exact_mod_cast hn
    have hshift : cube (logPrimeMeshHi 0 1 m j) i =
        cube (logPrimeMeshLo 0 1 m j) i +
          (((Finset.univ.filter (fun k : Fin r => k.val < i.val)).card : ℝ) + 3) *
            logPrimeMeshStep 0 1 m := by
      unfold cube prefix
      simp_rw [logPrimeMeshHi_eq_lo_add_step]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hshift]
    have hcube := hregion.2 i hi
    have hpad := mul_le_mul_of_nonneg_right (add_le_add_right hcount 3) hstep.le
    dsimp only [roughWidth]
    linarith

/-- Original ordinary15 eligible near-cap certificate + SAME actual
inner mesh box -> actual computed REAL whole-atom endpoint monomials,
in both capacity and full-vector repair branches. The original native
run exponent is nu-2delta; no desired monomial is assumed. -/
theorem actual_inner_ordinary_endpoint_monomials {r N m : ℕ} (hN : 1 < N)
    (p : Policy) (hp : p.val < 15) (B : Box) (eta : ℚ)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta) (u : LogFour)
    (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding p B eta)
    {j : Grid r m} (hj : j ∈ innerCells r 0 1 (physicalResidual p B eta : ℝ) m)
    (hwidth : roughWidth r m ≤ (delta p B eta : ℝ))
    {kappa A : ℝ} (hk0 : 0 < kappa) (hk : kappa ≤ (delta p B eta : ℝ) / 64)
    (hAlower : (N : ℝ) ^ kappa ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 - kappa / 2)) :
    let v := logPrimeMeshHi 0 1 m j
    let level := (nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)
    let abc := endpointFactors N p u v level A
    abc.1 ≤ A ∧
      A ^ 2 * abc.2.1 * abc.2.2 ^ 2 ≤ (N : ℝ) ^ (1 - 3 * kappa / 2) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - 3 * kappa / 2) ∧
      (A * abc.2.2 / abc.2.1) ^ (7 / 16 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - kappa) := by
  obtain ⟨hv0, hvanti, hcubes⟩ := actual_inner_endpoint_inputs (physicalResidual p B eta : ℝ) hj
  exact actual_ordinary_whole_atom_monomials hN p hp B eta hv hw hc heta u hlo hhi
    (logPrimeMeshHi 0 1 m j) hv0 hvanti hwidth hcubes hk0 hk hAlower hAupper

end
end ImbalancedChen.P5Z.ActualInnerWholeEndpointCapacity
