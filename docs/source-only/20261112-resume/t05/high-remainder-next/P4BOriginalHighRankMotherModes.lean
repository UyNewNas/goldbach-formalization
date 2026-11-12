import ImbalancedChen.P4BOriginalAllRankClassicalRange
import ImbalancedChen.P4BUpperPairOrderedRowModes

/-! The full original chart sum on the remaining physical modulus set, with the
actual two mother coordinates and the unchanged signed coefficient in every mode. -/
namespace ImbalancedChen.P4BOriginalHighRankMotherModes
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalAllRankClassicalRange (wholeHigh)
open P4BOriginalTwoAtlasSmallPayment (atlasPair)
open P4BOriginalFiniteSmoothCount (coefficient Q)
open P4BOriginalFiniteSignedTrim (trimmedWeight pairLicence)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOuterRampRoughness (baseline)
open P4BArbitraryWidthUpperPairProfile (eventually_full_support_inside_original_cap profile)
open P4BArbitraryWidthUpperPairHBNormalization (rawAtlas_eq_normalized)
open P4BUpperPairOrderedRowModes (normalizedAtlas_pair_eq_rowBank rowBank_eq_modeBank modeBank)
open P5Z.OriginalPrimeAtlasReserveBranches (allGroup_actual_branch_split originalMediumLow originalMediumHigh)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank words_spec)
open Part3 (primeProductSignedError)

def modes (b kap s : ℝ) (N K : ℕ) (kap0 : ℝ) (S : Finset ℕ) (c : ℕ → ℝ) :=
  ∑ js∈chartBank N 2,modeBank b kap s N K (js.getD 0 0) (js.getD 1 0) kap0 S (fun q => (c q:ℂ))

/-- Equality on each original label. Both original group logs, the smooth trim,
all integer HB blocks, their signs and the complete inverse Fourier integrals are
those of the original modeBank. This works for the actual rectangular coefficient. -/
theorem chart_eq_modes {b kap s : ℝ} (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N K : ℕ) (kap0 zeta : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) (js : List ℕ)
    (hjs : js∈chartBank N 2)
    (hcap : ∀ p : Fin 2→ℝ,profile b kap s N p≠0 → ∀ i,p i<(N:ℝ)) :
    let L := pairLicence hb hs hg N
    let r := fun q => (c q:ℂ)
    P5Z.OriginalPrimeAtlasReserveBranches.mediumAtlas L K N N kap0
        (originalMediumLow zeta js) (originalMediumHigh zeta js) S r js+
      P5Z.OriginalPrimeAtlasReserveBranches.noMediumAtlas L K N N kap0
        (originalMediumLow zeta js) (originalMediumHigh zeta js) S r js=
      modeBank b kap s N K (js.getD 0 0) (js.getD 1 0) kap0 S r := by
  have H : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  have hshape : js=[js.getD 0 0,js.getD 1 0] := by
    have hlen := (words_spec _ _ _ hjs).1
    cases js with
    | nil => simp at hlen
    | cons j rest =>
      cases rest with
      | nil => simp at hlen
      | cons l tail =>
        have he : tail=[] := List.length_eq_zero.mp (by simpa using hlen)
        subst tail
        rfl
  dsimp only
  rw [←allGroup_actual_branch_split]
  rw [rawAtlas_eq_normalized hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs H]
  conv_lhs => rw [hshape]
  rw [normalizedAtlas_pair_eq_rowBank hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs H
    N K _ _ hcap, rowBank_eq_modeBank hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs H]

theorem eventually_atlas_eq_modes {b kap : ℝ} (hb : 0<b) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96),
      ∀ (K : ℕ) (kap0 zeta : ℝ) (S : Finset ℕ) (c : ℕ→ℝ),
        atlasPair hb hs hg K N kap0 zeta S c=modes b kap s N K kap0 S c := by
  have hc := eventually_full_support_inside_original_cap (kappa:=kap) hb
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
  filter_upwards [hc] with N hN
  intro s hs hg K kap0 zeta S c
  exact Finset.sum_congr rfl (fun js hjs => chart_eq_modes hb hs hg N K kap0 zeta S c js hjs
    (hN s hs (by simpa only [one_mul] using hg)))

/-- Only the actual full integral on the original whole high-rank subset remains
in this reduction; there is no height filter on the three convolution factors. -/
theorem eventually_wholeHigh_modes_remainder (K : ℕ) (hK : 2≤K) {b kap : ℝ} (hb : 0<b)
    (hk : 0<kap) (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96),
      ∀ (kap0 : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      ell<1/1000 →
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖(primeProductSignedError 2 N N (Q omega N) c (trimmedWeight b kap s kap0 N):ℂ)-
        modes b kap s N K kap0 (wholeHigh m r n e q a omega k N ell) c‖≤
        delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  filter_upwards [P4BOriginalAllRankClassicalRange.eventually_height_and_wholeHigh K hK hb hk A delta hd,
    eventually_atlas_eq_modes (kap:=kap) hb] with N H M
  intro s hs hg kap0 m r n e q a omega k ell hell
  dsimp only
  intro hrange
  have hw := (H s hs hg kap0 0 m r n e q a omega k ell hell hrange).2.1
  rw [M s hs hg K kap0 0] at hw
  exact hw

end
end ImbalancedChen.P4BOriginalHighRankMotherModes
