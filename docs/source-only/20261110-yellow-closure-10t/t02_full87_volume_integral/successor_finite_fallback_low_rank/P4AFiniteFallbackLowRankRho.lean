import ImbalancedChen.P4AFiniteFallbackLowRankBoxes

/-! SOURCE_ONLY / UNCOMPILED.
The low-rank part of the SAME finite-fallback rho. ALL/ANY is kept on
its complete divisor universe; a retained raw modulus is not substituted.
The actual sign-sensitive beta gives the strict small-factor bound.
-/
namespace ImbalancedChen.P4AFiniteFallbackLowRankRho
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler (universe coefficient)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AFallbackCanonicalBanks (bank)
open P4AFiniteFallbackLowRankBoxes (short_product_le)

abbrev retain (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :=
  F (bank m) (P4AOriginalFull87HistoryCore.width r) n (P4AOriginalNewFifthUnion.data e q a) omega N

abbrev actualRho (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (tau ell : ℝ) :=
  P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau ((N : ℝ)^ell)

/-- The unique small/rough decomposition has rough rank 0, 1 or 2.
Universal wording avoids an arbitrary choice of factorization. The
original rho and its original support remain unchanged in the sum. -/
def activeLow (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (tau ell : ℝ) : Finset ℕ :=
  (P4AUpperTaggedBetaAttachment.support N N ((N : ℝ)^omega) (cutoff N)).filter (fun Q =>
    actualRho m r n e q a omega N tau ell Q≠0 ∧
      ∀ b∈actualSmallRosserSupport N N ((N : ℝ)^omega),
      ∀ d∈universe N N ((N : ℝ)^omega) (cutoff N),b*d=Q → d.primeFactorsList.length≤2)

/-- Exactness of the low-rank class follows from the ORIGINAL unique
small/rough factorization; the universal test does not discard a genuine
rank-zero/one/two contribution of this rho. -/
theorem mem_activeLow_of_decomposition (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau ell : ℝ) {Q b d : ℕ}
    (hne : actualRho m r n e q a omega N tau ell Q≠0)
    (hb : b∈actualSmallRosserSupport N N ((N : ℝ)^omega))
    (hd : d∈universe N N ((N : ℝ)^omega) (cutoff N))
    (hprod : b*d=Q) (hrank : d.primeFactorsList.length≤2) :
    Q∈activeLow m r n e q a omega N tau ell := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
    ⟨(b,d),Finset.mem_product.mpr ⟨hb,hd⟩,hprod⟩,hne,?_⟩
  intro b' hb' d' hd' hprod'
  have he := P4AUpperTaggedBetaAttachment.product_unique N N ((N : ℝ)^omega) (cutoff N)
    hb hd hb' hd' (hprod.trans hprod'.symm)
  rw [←he.2]
  exact hrank

theorem actual_decomposition (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau ell : ℝ) {Q : ℕ} (hQ : Q∈activeLow m r n e q a omega N tau ell) :
    ∃ b d : ℕ,b∈actualSmallRosserSupport N N ((N : ℝ)^omega) ∧
      d∈universe N N ((N : ℝ)^omega) (cutoff N) ∧ b*d=Q ∧
      (b : ℝ)<(N : ℝ)^ell ∧ d.primeFactorsList.length≤2 ∧
      coefficient (retain m r n e q a omega N) (fun _ => []) N N ((N : ℝ)^omega) (cutoff N) tau d≠0 := by
  obtain ⟨hsupport,hne,hlow⟩ := Finset.mem_filter.mp hQ
  obtain ⟨⟨b,d⟩,hbd,hprod⟩ := Finset.mem_image.mp hsupport
  obtain ⟨hb,hd⟩ := Finset.mem_product.mp hbd
  have H := P4AUpperTaggedBetaAttachment.rho_at_product (retain m r n e q a omega N)
    (fun _ => []) N N ((N : ℝ)^omega) (cutoff N) tau ((N : ℝ)^ell) hb hd
  have hp : coefficient (retain m r n e q a omega N) (fun _ => []) N N ((N : ℝ)^omega) (cutoff N) tau d*
      (if 0≤coefficient (retain m r n e q a omega N) (fun _ => []) N N ((N : ℝ)^omega) (cutoff N) tau d
      then actualSmallRosserPlus N N ((N : ℝ)^omega) ((N : ℝ)^ell) b
      else actualSmallRosserMinus N N ((N : ℝ)^omega) ((N : ℝ)^ell) b)≠0 := by
    rw [←H,hprod]
    exact hne
  obtain ⟨hc,hbeta⟩ := mul_ne_zero_iff.mp hp
  have hbL : (b : ℝ)<(N : ℝ)^ell := by
    split_ifs at hbeta
    · exact (actualSmallRosserPlus_active hbeta).2.1
    · exact (actualSmallRosserMinus_active hbeta).2.1
  exact ⟨b,d,hb,hd,hprod,hbL,hlow b hb d hd hprod,hc⟩

theorem universe_short_bound (N : ℕ) (hN : 1≤N) (omega : ℝ) {d : ℕ}
    (hd : d∈universe N N ((N : ℝ)^omega) (cutoff N)) (hrank : d.primeFactorsList.length≤2) :
    (d : ℝ)≤(N : ℝ)^(19/48 : ℝ) := by
  obtain ⟨hsub,hprod⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe
    N N ((N : ℝ)^omega) (cutoff N) hd
  have H := short_product_le hN d.primeFactorsList.reverse (by simpa using hrank)
    (fun p hp => (mem_roughPrimeUniverse.mp (hsub.subset hp)).2.2.2.2.le)
  simpa only [hprod] using H

/-- Uniform over every actual history parameter, either beta sign and
ALL/ANY cell. No fine-width loss is needed: the actual slots are cropped
at the original upper rough endpoint, even in the last label bin. -/
theorem activeLow_power (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (hN : 1<N) (tau ell : ℝ) (hell : ell<1/1000)
    {Q : ℕ} (hQ : Q∈activeLow m r n e q a omega N tau ell) :
    (Q : ℝ)<(N : ℝ)^(2/5 : ℝ) := by
  obtain ⟨b,d,hb,hd,hprod,hbL,hrank,_⟩ := actual_decomposition m r n e q a omega N tau ell hQ
  have hdB := universe_short_bound N (by omega : 1≤N) omega hd hrank
  have hn : (1 : ℝ)<N := by exact_mod_cast hN
  calc
    (Q : ℝ) = (b : ℝ)*(d : ℝ) := by rw [←hprod,Nat.cast_mul]
    _ ≤ (N : ℝ)^ell*(N : ℝ)^(19/48 : ℝ) :=
      mul_le_mul hbL.le hdB (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = (N : ℝ)^(ell+19/48) := (Real.rpow_add (zero_lt_one.trans hn) _ _).symm
    _ < _ := (Real.rpow_lt_rpow_left_iff hn).mpr (by linarith)

theorem activeLow_squarefree (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau ell : ℝ) {Q : ℕ} (hQ : Q∈activeLow m r n e q a omega N tau ell) :
    Squarefree Q := P4AUpperTaggedBetaAttachment.support_squarefree N N _ _ (Finset.mem_filter.mp hQ).1

theorem activeLow_target_coprime (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau ell : ℝ) {Q : ℕ} (hQ : Q∈activeLow m r n e q a omega N tau ell) :
    Nat.Coprime N Q := (P4AUpperTaggedBetaAttachment.support_coprime_target N N _ _
      (Finset.mem_filter.mp hQ).1).symm

theorem actualRho_abs_le_one (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau ell : ℝ) (Q : ℕ) : |actualRho m r n e q a omega N tau ell Q|≤1 :=
  P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ N N _ _ tau _ Q

end
end ImbalancedChen.P4AFiniteFallbackLowRankRho
