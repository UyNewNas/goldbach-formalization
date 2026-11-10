import ImbalancedChen.Part3FiniteLambdaOverLogDictionary
import ImbalancedChen.P5LicensedOriginalIntegerProfile
import ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / ready=false.
-- The held imports are source-review candidates, not installed actual APIs.
-- This is occurrencewise finite algebra on the original ordered integer words.

namespace ImbalancedChen.Part3.AllKLambdaChartCorrection

noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open ImbalancedChen.P5Z.LicensedOriginalIntegerProfile
open ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward
open ImbalancedChen.Part3
open ImbalancedChen.Part3.FiniteLambdaOverLogDictionary
open ImbalancedChen.Part3.OriginalProperPowerActualChart

def lambdaWord : List ℕ → ℂ
  | [] => 1
  | n :: ns => (lambdaOverLog n : ℂ) * lambdaWord ns

def roughWord (z : ℝ) : List ℕ → ℂ
  | [] => 1
  | n :: ns => roughOneSlot z n * roughWord z ns

theorem singleSource_lambda (chi : ℝ → ℝ) (z : ℝ)
    (cj n : ℕ) (hn : 1 ≤ n) :
    singleSource chi z cj n =
      (lambdaOverLog n : ℂ) * roughOneSlot z n * psi chi ((n : ℝ)/R cj) := by
  by_cases h1 : n = 1
  · subst n
    simp [singleSource, lambdaOverLog,
      ArithmeticFunction.vonMangoldt_apply_one]
  · have hnot : ¬n ≤ 1 := by omega
    simp only [singleSource, lambdaOverLog, if_neg hnot,
      Complex.ofReal_div]
    ring

theorem sourceTuple_lambda_factor (chi : ℝ → ℝ) (z : ℝ) :
    ∀ cjs ns : List ℕ, (∀ n ∈ ns, 1 ≤ n) →
      sourceTuple chi z cjs ns =
        lambdaWord ns * roughWord z ns * tupleProfile chi cjs ns := by
  intro cjs
  induction cjs with
  | nil =>
    intro ns hpos
    cases ns <;> simp [sourceTuple, lambdaWord, roughWord, tupleProfile]
  | cons cj cjs ih =>
    intro ns hpos
    cases ns with
    | nil => simp [sourceTuple, lambdaWord, roughWord, tupleProfile]
    | cons n ns =>
      have hn : 1 ≤ n := hpos n (by simp)
      have htail : ∀ m ∈ ns, 1 ≤ m := by
        intro m hm
        exact hpos m (by simp [hm])
      simp only [sourceTuple, lambdaWord, roughWord, tupleProfile]
      rw [singleSource_lambda chi z cj n hn, ih ns htail]
      ring

def primeOnly (ps : List ℕ) : Prop := ∀ n ∈ ps, n.Prime

-- A supported coordinate is either a prime or a composite prime power.
-- Thus the exceptional carrier has at least one *occurrence* of a proper
-- prime power. Equal numerical values in distinct positions remain distinct.
def supportedWord (ps : List ℕ) : Prop :=
  ∀ n ∈ ps, n.Prime ∨ (IsPrimePow n ∧ ¬n.Prime)

def properChartWords (cap k : ℕ) : Finset (List ℕ) :=
  (integerWords cap k).filter (fun ps => supportedWord ps ∧ ¬primeOnly ps)

theorem lambdaWord_of_primes {ps : List ℕ} (hp : primeOnly ps) :
    lambdaWord ps = 1 := by
  induction ps with
  | nil => rfl
  | cons n ns ih =>
    have hn : n.Prime := hp n (by simp)
    have htail : primeOnly ns := by
      intro m hm
      exact hp m (by simp [hm])
    simp [lambdaWord, lambdaOverLog_prime hn, ih htail]

theorem lambdaWord_zero_of_off_power {ps : List ℕ}
    (h : ∃ n ∈ ps, ¬n.Prime ∧ ¬IsPrimePow n) :
    lambdaWord ps = 0 := by
  induction ps with
  | nil =>
    obtain ⟨n, hn, _⟩ := h
    simp at hn
  | cons n ns ih =>
    obtain ⟨m, hm, hnp, hpow⟩ := h
    rcases List.mem_cons.mp hm with rfl | htail
    · simp [lambdaWord, lambdaOverLog_off_prime_powers hpow]
    · simp [lambdaWord, ih ⟨m, htail, hnp, hpow⟩]

theorem lambdaWord_zero_of_unsupported {ps : List ℕ}
    (h : ¬supportedWord ps) : lambdaWord ps = 0 := by
  have hoff : ∃ n ∈ ps, ¬n.Prime ∧ ¬IsPrimePow n := by
    unfold supportedWord at h
    push_neg at h
    obtain ⟨n, hn, hbad⟩ := h
    refine ⟨n, hn, ?_, ?_⟩
    · exact fun hp => hbad (Or.inl hp)
    · exact fun hpp => hbad (Or.inr ⟨hpp, fun hp => hbad (Or.inl hp)⟩)
  exact lambdaWord_zero_of_off_power hoff

theorem primeTuples_eq_integer_filter (cap k : ℕ) :
    primeTuples cap k = (integerWords cap k).filter primeOnly := by
  ext ps
  constructor
  · intro hp
    obtain ⟨hlen, hprime⟩ := primeTuples_spec cap k hp
    apply Finset.mem_filter.mpr
    constructor
    · apply words_mem (Finset.Icc 1 cap) k ps hlen
      intro p hmem
      exact Finset.mem_Icc.mpr ⟨(hprime p hmem).2.1, (hprime p hmem).2.2⟩
    · exact fun p hmem => (hprime p hmem).1
  · intro hp
    obtain ⟨hword, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlen, hmem⟩ := words_spec (Finset.Icc 1 cap) k ps hword
    apply primeTuples_mem cap k ps hlen
    intro p hp
    exact ⟨hprime p hp, (Finset.mem_Icc.mp (hmem p hp)).2⟩

theorem properChartWords_spec {cap k : ℕ} {ps : List ℕ}
    (hps : ps ∈ properChartWords cap k) :
    ps ∈ integerWords cap k ∧
      (∃ bad : Fin k, ∃ p e : ℕ,
        p.Prime ∧ 2 ≤ e ∧ ps.getD bad.val 0 = p ^ e ∧
          lambdaOverLog (ps.getD bad.val 0) = 1 / (e : ℝ)) := by
  obtain ⟨hword, hsupp, hnot⟩ := Finset.mem_filter.mp hps
  obtain ⟨hlen, _⟩ := words_spec (Finset.Icc 1 cap) k ps hword
  have hbad : ∃ n ∈ ps, ¬n.Prime := by
    unfold primeOnly at hnot
    push_neg at hnot
    exact hnot
  obtain ⟨n, hn, hnp⟩ := hbad
  have hpow : IsPrimePow n := by
    rcases hsupp n hn with hp | hp
    · exact False.elim (hnp hp)
    · exact hp.1
  obtain ⟨p,e,hp,he,hnpe,hcoeff⟩ :=
    proper_term_has_prime_exponent ⟨hpow,hnp⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hn
  have hik : i < k := by simpa [hlen] using hi
  refine ⟨hword, ⟨i, hik⟩, p, e, hp, he, ?_, ?_⟩
  · simpa [List.getD_eq_getElem _ _ hi, hget] using hnpe
  · simpa [List.getD_eq_getElem _ _ hi, hget] using hcoeff

theorem active_proper_chart_in_bad_words
    {cap k : ℕ} (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (T kappa0 : ℝ) (js : List ℕ) {ps : List ℕ}
    (hps : ps ∈ properChartWords cap k)
    (hactive : chartTerm chi eta W T kappa0 js ps ≠ 0) :
    ∃ bad : Fin k,
      ps ∈ badChartWords chi eta W T kappa0 cap k js bad := by
  obtain ⟨hword, bad, p, e, hp, he, hpower, _⟩ :=
    properChartWords_spec hps
  refine ⟨bad, Finset.mem_filter.mpr ?_⟩
  exact ⟨hword, hactive, ⟨p,e,hp,he,hpower⟩⟩

-- The test K may depend on the complete ordered word and on any fixed
-- independent-u label. No physical mark t or signed residue rho is inserted.
theorem all_k_lambda_chart_split (cap k : ℕ)
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ) (T kappa0 : ℝ)
    (js u : List ℕ) (K : List ℕ → List ℕ → ℂ) :
    (∑ ps ∈ integerWords cap k,
      lambdaWord ps * chartTerm chi eta W T kappa0 js ps * K u ps) =
      (∑ ps ∈ primeTuples cap k,
        chartTerm chi eta W T kappa0 js ps * K u ps) +
      (∑ ps ∈ properChartWords cap k,
        lambdaWord ps * chartTerm chi eta W T kappa0 js ps * K u ps) := by
  rw [primeTuples_eq_integer_filter]
  unfold properChartWords
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ps hps
  by_cases hp : primeOnly ps
  · simp [hp, lambdaWord_of_primes hp]
  · by_cases hs : supportedWord ps
    · simp [hp, hs]
    · simp [hp, hs, lambdaWord_zero_of_unsupported hs]

-- Phase8's ambient licence gives the SAME integer W for all replacement
-- words. Its agreement-on-primes identifies the prime summand with the
-- original Wprime; it does not manufacture a licence for native W_N.
theorem licensed_all_k_lambda_chart_split {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (cap : ℕ) (chi eta : ℝ → ℝ) (T kappa0 : ℝ)
    (js u : List ℕ) (K : List ℕ → List ℕ → ℂ) :
    (∑ ps ∈ integerWords cap k,
      lambdaWord ps *
        chartTerm chi eta (fun v => (listExtension L v : ℂ)) T kappa0 js ps *
          K u ps) =
      (∑ ps ∈ primeTuples cap k,
        chartTerm chi eta (fun v => (listExtension L v : ℂ)) T kappa0 js ps *
          K u ps) +
      (∑ ps ∈ properChartWords cap k,
        lambdaWord ps *
          chartTerm chi eta (fun v => (listExtension L v : ℂ)) T kappa0 js ps *
            K u ps) :=
  all_k_lambda_chart_split cap k chi eta
    (fun v => (listExtension L v : ℂ)) T kappa0 js u K

theorem licensed_prime_word_agreement {k cap : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    {ps : List ℕ} (hps : ps ∈ primeTuples cap k) :
    listExtension L ps = Wprime (wordVector k ps) := by
  obtain ⟨hlen, hprime⟩ := primeTuples_spec cap k hps
  have hp : ∀ i : Fin k, (wordVector k ps i).Prime := by
    intro i
    have hi : i.val < ps.length := by simpa [hlen] using i.isLt
    rw [wordVector, List.getD_eq_getElem _ _ hi]
    exact (hprime ps[i.val] (List.getElem_mem hi)).1
  calc
    listExtension L ps = listExtension L (List.ofFn (wordVector k ps)) := by
      rw [ofFn_wordVector hlen]
    _ = integerExtension L (wordVector k ps) := listExtension_ofFn L _
    _ = Wprime (wordVector k ps) := integerExtension_eq_on_primes L _ hp

-- Summing the Phase8 pushforward over the complete ordered integer bank
-- now yields the actual all-k finite chart identity. The rough factors
-- remain visible on BOTH prime and proper-power sides. Removing them on
-- primes requires the separate z<p support hypothesis at each coordinate.
theorem licensed_atlas_all_k_prime_plus_proper {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (cap : ℕ) (chi eta : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    {z : ℝ} (hz : 0 ≤ z) (T kappa0 : ℝ)
    (js u : List ℕ) (K : List ℕ → List ℕ → ℂ) :
    (∑ ps ∈ integerWords cap k,
      atlasEval chi z js ps (fun rows =>
        (listExtension L (originalProducts rows) : ℂ) *
          (eta (((originalProducts rows).prod : ℝ)/T^(1-kappa0)) : ℂ) *
            K u (originalProducts rows))) =
      (∑ ps ∈ primeTuples cap k,
        chartTerm chi eta (fun v => (listExtension L v : ℂ))
          T kappa0 js ps * (roughWord z ps * K u ps)) +
      (∑ ps ∈ properChartWords cap k,
        lambdaWord ps *
          chartTerm chi eta (fun v => (listExtension L v : ℂ))
            T kappa0 js ps * (roughWord z ps * K u ps)) := by
  let W : List ℕ → ℂ := fun v => (listExtension L v : ℂ)
  let G : List ℕ → List ℕ → ℂ := fun u' ps => roughWord z ps * K u' ps
  calc
    _ = ∑ ps ∈ integerWords cap k,
          lambdaWord ps * chartTerm chi eta W T kappa0 js ps * G u ps := by
        apply Finset.sum_congr rfl
        intro ps hps
        obtain ⟨_, hmem⟩ := words_spec (Finset.Icc 1 cap) k ps hps
        have hpositive : ∀ n ∈ ps, 1 ≤ n := by
          intro n hn
          exact (Finset.mem_Icc.mp (hmem n hn)).1
        rw [licensed_profile_atlas_identity L chi eta hone hzero hz
          T kappa0 js ps (K u)]
        rw [sourceTuple_lambda_factor chi z js ps hpositive]
        dsimp [W, G, chartTerm, trimmedWeight]
        ring
    _ = _ := by
      simpa only [W, G] using
        (all_k_lambda_chart_split cap k chi eta W T kappa0 js u G)

end
end ImbalancedChen.Part3.AllKLambdaChartCorrection
