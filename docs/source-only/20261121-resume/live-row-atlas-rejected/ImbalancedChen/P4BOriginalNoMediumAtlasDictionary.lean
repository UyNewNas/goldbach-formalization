import ImbalancedChen.P4BOriginalNoMediumAtlasNormalization

/-! SOURCE ONLY / UNCOMPILED. The original rank-two noMediumAtlas is
identified on its own with the paid bank. No conclusion is extracted
from a bound on mediumAtlas+noMediumAtlas. Every original chart, HB scalar,
ordered Row, before-HB cutoff, group log and arithmetic kernel is retained. -/
namespace ImbalancedChen.P4BOriginalNoMediumAtlasDictionary
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalNoMediumAtlasNormalization
open P4BOriginalTwoLongMotherBank (originalBank)
open P4BOriginalTwoLongRetainedRows (originalBranchRow)
open P4BOriginalTwoLongSourceRow (originalBranchRow_eq_typeI)
open P4BOriginalUpperFourierTailPaid (groupEval)
open P4BUpperPairOrderedRowModes (upperTest)
open P4BUpperPairOrderedRowGeometry (rowRoles)
open P5Z.AllGroupOrderedRectangleReindex (fullEval)
open P5Z.OrderedFactorTupleRectangleReindex (blockVector ofFn_blockVector)
open P5Z.ActualHBDyadicOccurrenceFamily (blockWords_spec)
open P5Z.PerGroupIntegerHBAtlasPushforward (typeIValue hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (R chartBank words_spec beforeHBCutoff)
open P5Z.ActualHBMediumBranchPartition (originalLower originalUpper)
open P5Z.OriginalPrimeAtlasReserveBranches (noMediumAtlas originalMediumLow originalMediumHigh)
open P4BOriginalFiniteSignedTrim (pairLicence)
open P4BArbitraryWidthUpperPairProfile (profile eventually_full_support_inside_original_cap)
open P4BOuterRampRoughness (baseline)

theorem fullEval_typeI_pair_eq_bankMother (zeta : ℝ) {b kap s : ℝ}
    (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N K cj ck : ℕ) (kap0 : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) :
    fullEval P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K [cj,ck]) [cj,ck]
      (typeIValue (originalLower (R cj*R ck) zeta) (originalUpper (R cj*R ck) zeta)
        (upperTest hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
          hs (by simpa only [one_mul] using hg) N kap0 S (fun d => (c d:ℂ))))=
      groupEval cj (fun j bs => groupEval ck (fun l cs =>
        originalBranchRow (u:=2*(j+1)) (v:=2*(l+1)) zeta b kap s N kap0 cj ck
          (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
          (beforeHBCutoff K [cj,ck])
          (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
          (Fin.append (rowRoles j) (rowRoles l)) S c)) := by
  simp only [fullEval,groupEval]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Finset.sum_congr rfl
  intro bs hbs
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cs hcs
  have hbslen := (blockWords_spec _ _ _ hbs).1
  have hcslen := (blockWords_spec _ _ _ hcs).1
  rw [originalBranchRow_eq_typeI zeta hb hs hg N kap0 cj ck j l
    (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs)
    (beforeHBCutoff K [cj,ck]) S c]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [ofFn_blockVector hbslen,ofFn_blockVector hcslen]
  ring

theorem noMediumAtlas_pair_eq_bankMother (zeta : ℝ) {b kap s : ℝ}
    (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N K cj ck : ℕ) (kap0 : ℝ) (S : Finset ℕ) (c : ℕ→ℝ)
    (hcap : ∀ p : Fin 2→ℝ,profile b kap s N p≠0 → ∀ i,p i<(N:ℝ)) :
    noMediumAtlas (pairLicence hb hs hg N) K N N kap0
      (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck]) S (fun d => (c d:ℂ)) [cj,ck]=
      groupEval cj (fun j bs => groupEval ck (fun l cs =>
        originalBranchRow (u:=2*(j+1)) (v:=2*(l+1)) zeta b kap s N kap0 cj ck
          (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
          (beforeHBCutoff K [cj,ck])
          (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
          (Fin.append (rowRoles j) (rowRoles l)) S c)) := by
  have hlo : originalMediumLow zeta [cj,ck]=originalLower (R cj*R ck) zeta := by
    simp [originalMediumLow,P5Z.ExactOriginalSmoothDyadicPartition.scales,originalLower]
  have hhi : originalMediumHigh zeta [cj,ck]=originalUpper (R cj*R ck) zeta := by
    simp [originalMediumHigh,P5Z.ExactOriginalSmoothDyadicPartition.scales,originalUpper]
  rw [noMediumAtlas_eq_fullEval hb hs hg N K kap0 _ _ S (fun d => (c d:ℂ)) [cj,ck]
    (by simp) hcap,hlo,hhi]
  exact fullEval_typeI_pair_eq_bankMother zeta hb hs hg N K cj ck kap0 S c

/-- This is literally the original rank-two no-medium atlas sum, before
any bound. The licence is raw; original group-log transport is proved above. -/
def noMediumTotal {b kap s : ℝ} (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N K : ℕ) (kap0 zeta : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) : ℂ :=
  ∑ js∈chartBank N 2,noMediumAtlas (pairLicence hb hs hg N) K N N kap0
    (originalMediumLow zeta js) (originalMediumHigh zeta js) S (fun d => (c d:ℂ)) js

theorem noMediumTotal_eq_originalBank {b kap s : ℝ}
    (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N K : ℕ) (kap0 zeta : ℝ) (S : Finset ℕ) (c : ℕ→ℝ)
    (hcap : ∀ p : Fin 2→ℝ,profile b kap s N p≠0 → ∀ i,p i<(N:ℝ)) :
    noMediumTotal hb hs hg N K kap0 zeta S c=originalBank zeta b kap s N K kap0 S c := by
  unfold noMediumTotal originalBank
  apply Finset.sum_congr rfl
  intro js hjs
  have hlen := (words_spec _ _ _ hjs).1
  obtain ⟨cj,ck,rfl⟩ : ∃ cj ck,js=[cj,ck] := by
    cases js with
    | nil => simp at hlen
    | cons cj rest =>
        cases rest with
        | nil => simp at hlen
        | cons ck tail =>
            have he : tail=[] := List.length_eq_zero.mp (by simpa using hlen)
            subst tail
            exact ⟨cj,ck,rfl⟩
  simpa using noMediumAtlas_pair_eq_bankMother zeta hb hs hg N K cj ck kap0 S c hcap

/-- The actual smooth support supplies the temporary cap uniformly for
all legal widths. The public identity has no CapSupported/source-price premise. -/
theorem eventually_noMediumTotal_eq_originalBank {b kap : ℝ} (hb : 0<b) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96),
      ∀ (K : ℕ) (kap0 zeta : ℝ) (S : Finset ℕ) (c : ℕ→ℝ),
      noMediumTotal hb hs hg N K kap0 zeta S c=originalBank zeta b kap s N K kap0 S c := by
  have hc := eventually_full_support_inside_original_cap (kappa:=kap) hb
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
  filter_upwards [hc] with N hN
  intro s hs hg K kap0 zeta S c
  exact noMediumTotal_eq_originalBank hb hs hg N K kap0 zeta S c
    (hN s hs (by simpa only [one_mul] using hg))

end
end ImbalancedChen.P4BOriginalNoMediumAtlasDictionary
