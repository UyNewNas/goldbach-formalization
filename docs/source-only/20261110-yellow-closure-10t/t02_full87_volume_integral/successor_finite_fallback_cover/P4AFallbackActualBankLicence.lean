import ImbalancedChen.P4AFallbackOmittedRegions

/-! SOURCE_ONLY / UNCOMPILED.
Concrete downstream interface: the shared finite Bank contains only
actual original second/third masks on whole CLOSED physical boxes.
The common finite family is selected after the original trims and before
all history/rough cutoffs and the target. Unresolved owners inherit.
No gain, compiler, prime asymptotic or transport field is an input.
-/
namespace ImbalancedChen.P4AFallbackActualBankLicence
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AFallbackCanonicalBanks P4AFallbackOriginalCompactTrims
open P4AFallbackUniformMargins P4AFallbackJointFiniteCover P4AFallbackOmittedRegions
open P4AOriginalFiniteFallbackBank (read read_some_iff)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

theorem second_closed_original_licence (m : ℕ) (j : Label 2 m) (c : ℚ)
    (hc : (bank m).second j=some c) (t : Point 2) (ht : t∈closedBox m j) :
    SecondRegion (t 0) (t 1) ∧ 3*t 0<v (t 0) ∧
      v (t 0)<(c : ℝ) ∧ (c : ℝ)<299/500 ∧ (1/2 : ℝ)<c ∧
      (∀ i,prefixSquareExpr t i<c) ∧
      (∀ i∉secondMask,selectedSquareExpr secondMask t i<c) ∧
      (c : ℝ)<v (t 1) := by
  obtain ⟨hg,rfl⟩ := (second_some_iff m j c).mp hc
  exact good2_sound m j hg t ht

theorem third_closed_original_licence (m : ℕ) (j : Label 3 m) (c : ℚ)
    (hc : (bank m).third j=some c) (t : Point 3) (ht : t∈closedBox m j) :
    ThirdRegion (t 0) (t 1) (t 2) ∧ 3*t 0<v (t 0) ∧
      t 0+t 1+3*t 2<v (t 0) ∧
      v (t 0)<(c : ℝ) ∧ (c : ℝ)<299/500 ∧ (1/2 : ℝ)<c ∧
      (∀ i,prefixSquareExpr t i<c) ∧
      (∀ i∉thirdMask,selectedSquareExpr thirdMask t i<c) ∧
      (c : ℝ)<v (t 1+t 2) := by
  obtain ⟨hg,rfl⟩ := (third_some_iff m j c).mp hc
  exact good3_sound m j hg t ht

theorem second_read_region (m : ℕ) (t : Point 2) (c : ℚ)
    (hc : read m (bank m).second t=some c) : SecondRegion (t 0) (t 1) := by
  obtain ⟨j,ht,hj⟩ := read_some_iff.mp hc
  exact (second_closed_original_licence m j c hj t (meshCell_subset_closedBox m j ht)).1

theorem third_read_region (m : ℕ) (t : Point 3) (c : ℚ)
    (hc : read m (bank m).third t=some c) : ThirdRegion (t 0) (t 1) (t 2) := by
  obtain ⟨j,ht,hj⟩ := read_some_iff.mp hc
  exact (third_closed_original_licence m j c hj t (meshCell_subset_closedBox m j ht)).1

/-- The real rank-two branch is disjoint from the rank-three branch;
the third splice therefore retains the original second decision. -/
theorem reads_mutually_exclusive (m : ℕ) (t : Point 3) (c2 c3 : ℚ)
    (h2 : read m (bank m).second ![t 0,t 1]=some c2)
    (h3 : read m (bank m).third t=some c3) : False := by
  have hsecond := second_read_region m ![t 0,t 1] c2 h2
  apply above_mu_regions_disjoint (by simpa using hsecond) (third_read_region m t c3 h3)

/-- Every accepted third row is enabled by every subsequently chosen
physical rough cutoff below the ORIGINAL 5/96 threshold. -/
theorem third_read_above_rough (m : ℕ) (t : Point 3) (omega : ℝ)
    (q : ℚ) (hc : read m (bank m).third t=some q) (homega : omega<5/96) :
    ∀ i : Fin 3,omega<t i := by
  have hg := third_read_region m t q hc
  obtain ⟨hx,_,hz,hzy,_,_,_,_,hcut,_⟩ := hg
  dsimp only [mu] at hx
  intro i
  fin_cases i <;> linarith

/-- The original trims are chosen first. Thereafter one common finite
bank (or any finer member of this canonical sequence) has exact original
owners, arbitrary endpoint accuracy, a positive uniform gate margin,
and arbitrarily small omitted ACTUAL third physical kernel.
-/
theorem exists_common_original_bank (delta : ℝ) (hd : 0<delta)
    (eta epsilon : ℝ) (heta : 0<eta) (heps : 0<epsilon) (mMin : ℕ) :
    ∃ r m0 : ℕ,mMin≤m0 ∧ ∀ m : ℕ,m0≤m →
      (∀ t∈secondCore delta,∃! j : Label 2 m,
        t∈logPrimeMeshCell 0 (19/96) m j ∧ (bank m).second j=some (level2 m j)) ∧
      (∀ t∈thirdCore r,∃! j : Label 3 m,
        t∈logPrimeMeshCell 0 (19/96) m j ∧ (bank m).third j=some (level3 m j)) ∧
      (∀ j : Label 2 m,∀ t∈closedBox m j,
        0<v (t 1)-(level2 m j : ℝ) ∧ v (t 1)-(level2 m j : ℝ)<eta) ∧
      (∀ j : Label 3 m,∀ t∈closedBox m j,
        0<v (t 1+t 2)-(level3 m j : ℝ) ∧ v (t 1+t 2)-(level3 m j : ℝ)<eta) ∧
      0<(uniformMargin m : ℝ) ∧ lostThird m<epsilon := by
  obtain ⟨r,mo,hmo,hO⟩ := exists_arbitrarily_small_third_omission epsilon heps mMin
  obtain ⟨m0,hm0,hM⟩ := exists_joint_original_cover delta hd r eta heta mo
  refine ⟨r,m0,hmo.trans hm0,?_⟩
  intro m hm
  have H := hM m hm
  exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2,hO m (hm0.trans hm)⟩

end
end ImbalancedChen.P4AFallbackActualBankLicence
