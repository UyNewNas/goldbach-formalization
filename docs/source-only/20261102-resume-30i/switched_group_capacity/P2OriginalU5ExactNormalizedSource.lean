import ImbalancedChen.P2OriginalU5WholeGroupCapacity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact original ALL-Gamma source and its normalized consumer. The unit
quotient contributes to the unsifted J and is separated by an equality,
never deleted. H's paid comparison is normalized by its SAME Theta_Q.
No finite bound or limit for J, Buchstab cost, K, PP or final switched
cost is a premise. Those analytic obligations remain OPEN.
-/
namespace ImbalancedChen.P2OriginalU5ExactNormalizedSource
noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open P2OriginalU5SmallPartnerRootPayment P2OriginalU5WholeGroupCapacity
open P5OriginalU5CausalFinite (pairSupport originalResidual)
open P2TwentyOneUnsiftedArithmeticSource (product)
open P2TwentyOneAllWordTailDecomposition (goodSwitchedPrimeMass)
open P2ActualSameQTwentyOnePositiveSourceBinding (actualGoodMass)
open P2EnhancedTwentyOneSameQWeighted (Theta)

/-- Independent unsifted arithmetic test, retaining the mother LIST's
22 occurrences and each original quotient label. -/
def sourceTest (N : ℕ) (t : ℕ × ℕ) (F : ℕ → ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map fun cs =>
      ∑ x ∈ rootLabels N t cs,F (product (t.1*t.2) x)).sum).sum

def unitTest (N : ℕ) (t : ℕ × ℕ) (F : ℕ → ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map fun cs =>
      ∑ x ∈ (rootLabels N t cs).filter (fun x => x.2=1),F (product (t.1*t.2) x)).sum).sum

def nonunitTest (N : ℕ) (t : ℕ × ℕ) (F : ℕ → ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map fun cs =>
      ∑ x ∈ (rootLabels N t cs).filter (fun x => x.2≠1),F (product (t.1*t.2) x)).sum).sum

/-- Valid for signed tests too. No source equality or cost bound is an input. -/
theorem sourceTest_unit_nonunit (N : ℕ) (t : ℕ × ℕ) (F : ℕ → ℝ) :
    sourceTest N t F=unitTest N t F+nonunitTest N t F := by
  have hsplit (cs : List ℕ) :
      (∑ x ∈ rootLabels N t cs,F (product (t.1*t.2) x))=
        (∑ x ∈ (rootLabels N t cs).filter (fun x => x.2=1),F (product (t.1*t.2) x))+
        (∑ x ∈ (rootLabels N t cs).filter (fun x => x.2≠1),F (product (t.1*t.2) x)) :=
    (Finset.sum_filter_add_sum_filter_not _ (fun x => x.2=1) _).symm
  unfold sourceTest unitTest nonunitTest
  simp_rw [hsplit]
  simp only [List.sum_map_add]

/-- The actual finite unsifted J quantity. Its eventual finite bound
must still be proved; this definition is not an assumed limiting cost. -/
def sourceJ (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  Real.log N/(N : ℝ)*sourceTest N t (fun _ => 1)

theorem sourceJ_unit_nonunit (N : ℕ) (t : ℕ × ℕ) :
    sourceJ N t=Real.log N/(N : ℝ)*unitTest N t (fun _ => 1)+
      Real.log N/(N : ℝ)*nonunitTest N t (fun _ => 1) := by
  rw [sourceJ,sourceTest_unit_nonunit,mul_add]

def primeIndicator (N m : ℕ) : ℝ := if m<N ∧ (N-m).Prime then 1 else 0

/-- H's actual marked good mass is exactly this independently defined
source tested for additive primality. ANY real old scalar is preserved;
nonnegativity is required only when an upper inequality is taken. -/
theorem actualGoodMass_eq_sourceTest (N : ℕ) (t : ℕ × ℕ) (s : ℝ) :
    actualGoodMass N (rootQ N t) {t.1*t.2} (fun _ => s) (smallCap N)=
      s*sourceTest N t (primeIndicator N) := by
  simp only [actualGoodMass,Finset.sum_singleton,goodSwitchedPrimeMass,
    p5z_labelledPrimeMass,sourceTest,rootLabels,primeIndicator]

/-- Literal same-Q Theta at the genuine root, in physical residual
coordinates. The old signed scalar occurs once and is not renormalized. -/
theorem root_Theta_exact {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (s : ℝ) :
    Theta N (rootQ N t) {t.1*t.2} (fun _ => s)=
      4*logarithmicIntegral N*s*wuSingularSeries ((t.1*t.2)*N)/
        ((Nat.totient (t.1*t.2) : ℝ)*originalResidual N t*Real.log N) := by
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  simp only [Theta,Finset.sum_singleton]
  rw [root_residual_identity (by omega) ht,Real.log_rpow hNpos]
  ring

/-- This is the actual normalized cost consumer left by H. Its right
side contains the true source prime test, not a supplied switched bound.
Evaluating sourceJ and applying the SAME licensed upper rho remain internal. -/
theorem original_U5_normalized_paid_source {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ t ∈ pairSupport N,∀ s : ℝ,0<s →
      P2EnhancedTwentyOneChildCorrection.switchedCount N (rootQ N t)
        {t.1*t.2} (fun _ => s)/Theta N (rootQ N t) {t.1*t.2} (fun _ => s)≤
      s*sourceTest N t (primeIndicator N)/
        Theta N (rootQ N t) {t.1*t.2} (fun _ => s)+epsilon := by
  obtain ⟨T,hT,hpaid⟩ := original_U5_switched_good_source_paid hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT he t ht s hs
  have hN4 := hT.trans hNT
  have htheta : 0<Theta N (rootQ N t) {t.1*t.2} (fun _ => s) := by
    apply P2EnhancedTwentyOneSameQWeighted.Theta_pos hN4
    · intro d hd
      rw [Finset.mem_singleton.mp hd]
      exact pair_product_pos ht
    · intro d hd
      exact hs.le
    · intro d hd
      rw [Finset.mem_singleton.mp hd]
      exact root_residual_gt_one (by omega) ht
    · exact ⟨t.1*t.2,Finset.mem_singleton_self _,hs⟩
  have h := div_le_div_of_nonneg_right (hpaid N hNT he t ht s hs.le) htheta.le
  rw [actualGoodMass_eq_sourceTest,add_div,mul_div_cancel_right₀ _ htheta.ne'] at h
  exact h

/-- Zero marked mass is retained explicitly; no positive-mass theorem
is used to discard it or to divide a vanishing normalization. -/
theorem zero_marked_source (N : ℕ) (t : ℕ × ℕ) :
    actualGoodMass N (rootQ N t) {t.1*t.2} (fun _ => 0) (smallCap N)=0 ∧
      Theta N (rootQ N t) {t.1*t.2} (fun _ => 0)=0 ∧
      P2EnhancedTwentyOneChildCorrection.switchedCount N (rootQ N t)
        {t.1*t.2} (fun _ => 0)=0 := by
  simp [actualGoodMass,Theta,P2EnhancedTwentyOneChildCorrection.switchedCount]

end
end ImbalancedChen.P2OriginalU5ExactNormalizedSource
