import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional

/- Independent consumer-side literal specification. No mathematical premise. -/
open Filter Finset
open scoped Classical BigOperators

namespace IndependentBV

def primeCount (x q a : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p ≡ a [MOD q])).card

noncomputable def li (x : ℝ) : ℝ :=
  2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t

noncomputable def residueMax (x q : ℕ) : ℝ :=
  let S := (Finset.range q).filter (fun a => Nat.Coprime a q)
  if h : S.Nonempty then
    (S.image (fun a => |(primeCount x q a : ℝ) - li x / Nat.totient q|)).max'
      (Finset.image_nonempty.mpr h)
  else 0

noncomputable def prefixMax (N q : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image (fun y => residueMax y q)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

noncomputable def cutoff (N : ℕ) (B : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B)

theorem standard_bv :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
        ∀ᶠ N : ℕ in atTop, 2 ≤ N →
          ∑ q ∈ Finset.Icc 1 (cutoff N B), prefixMax N q ≤
            C * (N : ℝ) / Real.log N ^ A := by
  simpa only [MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov,
    cutoff, prefixMax, residueMax, primeCount, li,
    MathlibNt.SieveTheory.LiuWeight.panModulusCutoff,
    MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError,
    MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPMaxError,
    MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError,
    MathlibNt.SieveTheory.BombieriVinogradov.primesInAP,
    MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral,
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral,
    AnalyticNumberTheory.Sieve.unitResidues] using
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov

end IndependentBV

set_option pp.all true in
#check @IndependentBV.standard_bv
#print axioms AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
#print axioms IndependentBV.standard_bv
