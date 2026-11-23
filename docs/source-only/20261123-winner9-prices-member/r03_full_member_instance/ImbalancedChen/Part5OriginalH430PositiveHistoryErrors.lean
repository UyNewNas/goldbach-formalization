import ImbalancedChen.Part5OriginalH430EnhancedPositivePrices
import ImbalancedChen.Part5OriginalH430RootTentOwnTheta
import ImbalancedChen.Part5OriginalH430ReselectedReceivers

/-! Relative errors on a genuinely positive specified root family. The
reader and altered bare membership are tested on their actual chronological
occurrences and unrestricted additive-prime submasks. -/
namespace ImbalancedChen.Part5OriginalH430PositiveHistoryErrors
noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430RequestedHistory Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads Part5OriginalH430NativeQueryPaths
open Part5OriginalH430FixedProgramL1 Part5OriginalH430FullPrimeTheta
open Part5OriginalH430AllReceiverPrimePassage Part5OriginalH430ChangedPrefixDescendants
open Part5OriginalH430WholeMemberScreen Part5OriginalH430ReselectedReceivers
open Part5OriginalH430RootTentScreen Part5OriginalH430EnhancedPositivePrices
open P5OriginalU5FrozenSource (receiver)

/-- The denominator is the raw fixed/retained own-Theta sum on the
specified positive interval, with no division by multiplicities. All
three integer numerators are evaluated at the same parameters. -/
theorem actual_positive_relative_errors (mesh : ℕ) {b c eps : ℝ}
    (hb : 1/5≤b) (hbc : b<c) (hc : c≤59/250) (he : 0<eps) :
    ∃ T : ℕ, ∀ n≥T, ∃ N₀ : ℕ, ∀ N≥N₀, Even N →
      ∀ (v : Programs mesh) (u : SplitPrograms mesh) (k : Root) (m G : ℕ) (mode)
        (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      let P := ∑ p∈Part5OriginalH430RootIntervalTheta.primeBand N b c,
        inheritedAtom N n m k (Part5OriginalH430FrozenRootMass.finiteTau n) p
      0<P ∧
      readerLoss N n m G k v.2 (order v.2) mode E f +
        descendants N n m k u.2.2 (chronologicalOrder u.2.2)
          (fun p => actualPrimeTupleLog N p∈bareScreen k (prefixCode u.2.2) (order (prefixCode u.2.2)) n) E f 0 +
        descendants N n m k v.2 (rootFirst v.2)
          (fun p : Fin 1→ℕ => collar n (collarIndex n) (actualPrimeTupleLog N p 0)) E f 0
        < eps*P := by
  obtain ⟨hP,lim⟩ := positive_interval hb hbc hc
  let I := priceLimit b c
  let share := eps*I/6
  have hshare : 0<share := div_pos (mul_pos he hP) (by norm_num)
  obtain ⟨T0,H0⟩ := lim (I/2) (half_pos hP)
  obtain ⟨T1,H1⟩ := reselected_actual_receivers mesh hshare
  obtain ⟨T2,H2⟩ := all_bare_changed_prefix_descendants mesh hshare
  obtain ⟨T3,H3⟩ := all_root_tent_descendants mesh hshare
  refine ⟨max (max T0 T1) (max T2 T3),fun n hn=>?_⟩
  obtain ⟨n0,h0⟩ := H0 n (by omega)
  obtain ⟨n1,h1⟩ := H1 n (by omega)
  obtain ⟨n2,h2⟩ := H2 n (by omega)
  obtain ⟨n3,h3⟩ := H3 n (by omega)
  refine ⟨max (max n0 n1) (max n2 n3),fun N hN hEven v u k m G mode E f hE hf=>?_⟩
  dsimp only
  obtain ⟨hclose,hraw,_⟩ := h0 N (by omega) m k _ (Part5OriginalH430FrozenRootMass.finiteTau_pos n).le
    (Part5OriginalH430FrozenRootMass.finiteTau_le n)
  have hlow := (abs_lt.mp hclose).1
  have hhalf : I/2 < ∑ p∈Part5OriginalH430RootIntervalTheta.primeBand N b c,
      inheritedAtom N n m k (Part5OriginalH430FrozenRootMass.finiteTau n) p := by
    dsimp [I] at *
    linarith only [hlow,hraw]
  refine ⟨(half_pos hP).trans hhalf,?_⟩
  apply lt_trans _ (mul_lt_mul_of_pos_left hhalf he)
  have hreader := h1 N (by omega) hEven v k m G mode E f hE hf
  have hbare := h2 N (by omega) hEven u k m E f hE hf
  have hroot := h3 N (by omega) hEven v k m E f hE hf
  dsimp only [share] at hreader hbare hroot
  linarith only [hreader,hbare,hroot]

end
end ImbalancedChen.Part5OriginalH430PositiveHistoryErrors
