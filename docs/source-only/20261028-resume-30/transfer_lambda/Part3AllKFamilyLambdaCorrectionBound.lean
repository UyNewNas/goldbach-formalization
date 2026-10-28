import ImbalancedChen.Part3AllKLambdaChartCorrection
import ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily

/-!
Source-only continuation. No compilation or formal credit is asserted.
The integer-bank licence below is DERIVED from the previously defined
all-rank geometric Family. In particular its zeroth mixed-Euler estimate,
not an assumed PP estimate, supplies a single amplitude for all ranks.
The signed test kernel remains independent of the original prime word.
-/
namespace ImbalancedChen.Part3.AllKFamilyLambdaCorrectionBound

noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open ImbalancedChen.P5Z.LicensedOriginalIntegerProfile
open ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
open ImbalancedChen.Part3.FiniteLambdaOverLogDictionary
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open ImbalancedChen.Part3.OriginalProperPowerChartCount
open ImbalancedChen.Part3.AllKLambdaChartCorrection

def bankWeight {kStar : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (ps : List ℕ) : ℂ :=
  (listExtension (licence A T k) ps : ℂ)

theorem bankWeight_eq_ambient {kStar : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) {ps : List ℕ} (hlen : ps.length = k.val) :
    bankWeight A T k ps =
      (A.ambient T k (fun i => (wordVector k.val ps i : ℝ)) : ℂ) := by
  change (listExtension (licence A T k) ps : ℂ) = _
  conv_lhs => rw [← ofFn_wordVector hlen]
  rw [listExtension_ofFn]
  rfl

-- These are full INTEGER-bank bounds. They do not quantify only over
-- primeTuples, so they remain valid after a prime-power replacement.
theorem bankWeight_support {kStar : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) {ps : List ℕ} (hlen : ps.length = k.val)
    (hW : bankWeight A T k ps ≠ 0) :
    (∀ n ∈ ps, A.lower * (T : ℝ) ^ A.aStar ≤ (n : ℝ)) ∧
      (ps.prod : ℝ) ≤ A.upper * (T : ℝ) := by
  have hamb : A.ambient T k (fun i => (wordVector k.val ps i : ℝ)) ≠ 0 := by
    intro h
    apply hW
    rw [bankWeight_eq_ambient A T k hlen, h]
    rfl
  have hs := A.support T k (fun i => (wordVector k.val ps i : ℝ)) hamb
  constructor
  · intro n hn
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hn
    have hik : i < k.val := by omega
    have hh := hs.1 (⟨i, hik⟩ : Fin k.val)
    simpa only [wordVector, List.getD_eq_getElem _ _ hi, hget] using hh
  · simpa only [← List.prod_ofFn, ofFn_wordVector hlen, Nat.cast_prod] using hs.2

theorem all_rank_bank_amplitude {kStar : ℕ} (A : Family kStar) :
    ∃ C B : ℕ, 0 < C ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (ps : List ℕ),
        ps.length = k.val →
        ‖bankWeight A T k ps‖ ≤
          (C : ℝ) * (Real.log ((T : ℝ) + 2)) ^ B := by
  obtain ⟨C, B, hC, hbound⟩ := A.mixedEuler 0
  refine ⟨C, B, hC, ?_⟩
  intro T k ps hlen
  rw [bankWeight_eq_ambient A T k hlen, Complex.norm_real]
  simpa only [Real.norm_eq_abs, eulerWord, List.foldr_nil] using
    hbound T k [] (fun i => (wordVector k.val ps i : ℝ)) (by simp)

theorem lambdaOverLog_norm_le_one (n : ℕ) :
    ‖(lambdaOverLog n : ℂ)‖ ≤ 1 := by
  by_cases hp : n.Prime
  · simp [lambdaOverLog_prime hp]
  · by_cases hpow : IsPrimePow n
    · obtain ⟨p, e, hp', he, hn, hcoeff⟩ :=
        proper_term_has_prime_exponent ⟨hpow, hp⟩
      rw [hcoeff, Complex.norm_real, Real.norm_eq_abs]
      have he' : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast (show 1 ≤ e by omega)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (e : ℝ))]
      exact (div_le_iff₀ (by linarith : (0 : ℝ) < e)).mpr (by simpa using he')
    · simp [lambdaOverLog_off_prime_powers hpow]

theorem lambdaWord_norm_le_one (ps : List ℕ) : ‖lambdaWord ps‖ ≤ 1 := by
  induction ps with
  | nil => simp [lambdaWord]
  | cons n ns ih =>
    rw [lambdaWord, norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (lambdaOverLog_norm_le_one n) ih
        (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _

theorem roughWord_norm_le_one (z : ℝ) (ps : List ℕ) :
    ‖roughWord z ps‖ ≤ 1 := by
  induction ps with
  | nil => simp [roughWord]
  | cons n ns ih =>
    rw [roughWord, norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (roughOneSlot_norm_le z n) ih
        (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _

theorem psi_norm_le_one (chi : ℝ → ℝ)
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1) (t : ℝ) :
    ‖psi chi t‖ ≤ 1 := by
  rw [psi, Complex.norm_real, Real.norm_eq_abs]
  unfold bump
  exact abs_le.mpr ⟨by linarith [(hchi t).1, (hchi (2*t)).2],
    by linarith [(hchi t).2, (hchi (2*t)).1]⟩

theorem tupleProfile_norm_le_one (chi : ℝ → ℝ)
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1) :
    ∀ js ps : List ℕ, ‖tupleProfile chi js ps‖ ≤ 1 := by
  intro js
  induction js with
  | nil => intro ps; cases ps <;> simp [tupleProfile]
  | cons j js ih =>
    intro ps
    cases ps with
    | nil => simp [tupleProfile]
    | cons p ps =>
      rw [tupleProfile, norm_mul]
      calc
        _ ≤ 1 * 1 := mul_le_mul (psi_norm_le_one chi hchi _) (ih ps)
          (norm_nonneg _) (by norm_num)
        _ = 1 := one_mul _

theorem bank_chart_amplitude {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar + 1)) (chi eta : ℝ → ℝ)
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1)
    (heta : ∀ t, |eta t| ≤ 1) (M : ℝ) (hM : 0 ≤ M)
    (hamp : ∀ ps, ps.length = k.val → ‖bankWeight A T k ps‖ ≤ M)
    (kappa0 : ℝ) (js ps : List ℕ) (hlen : ps.length = k.val) :
    ‖chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps‖ ≤ M := by
  have he : ‖(eta ((ps.prod : ℝ)/(T : ℝ)^(1-kappa0)) : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using heta _
  unfold chartTerm trimmedWeight
  rw [norm_mul, norm_mul]
  calc
    _ ≤ 1 * (1 * M) :=
      mul_le_mul (tupleProfile_norm_le_one chi hchi js ps)
        (mul_le_mul he (hamp ps hlen) (norm_nonneg _) (by norm_num))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = M := by ring

-- A finite covering lemma, including an empty rank and words with several
-- bad occurrences. Repeated bad occurrences are only overcounted, never
-- identified or divided by a permutation multiplicity.
theorem covered_nonnegative_sum_le {α ι : Type*} [DecidableEq α]
    [DecidableEq ι] (S : Finset α) (I : Finset ι) (B : ι → Finset α)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hcover : ∀ a ∈ S, f a ≠ 0 → ∃ i ∈ I, a ∈ B i) :
    (∑ a ∈ S, f a) ≤ ∑ i ∈ I, ∑ a ∈ B i, f a := by
  calc
    _ ≤ ∑ a ∈ S, ∑ i ∈ I, if a ∈ B i then f a else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hz : f a = 0
      · simp [hz]
      · obtain ⟨i, hi, hBi⟩ := hcover a ha hz
        calc
          f a = (if a ∈ B i then f a else 0) := by simp [hBi]
          _ ≤ ∑ j ∈ I, if a ∈ B j then f a else 0 :=
            Finset.single_le_sum (fun j hj => by split_ifs <;> simp [hf]) hi
    _ = ∑ i ∈ I, ∑ a ∈ S, if a ∈ B i then f a else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun a ha => (Finset.mem_filter.mp ha).2) (fun a ha _ => hf a)

theorem all_k_proper_correction_absolute_boxes
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (hone : ∀ t, t ≤ 1 → chi t = 1)
    (hzero : ∀ t, 2 ≤ t → chi t = 0)
    (cap k : ℕ) (T kappa0 : ℝ) {js : List ℕ}
    (hjs : js ∈ chartBank cap k) (K : ℕ → ℂ) :
    ‖∑ ps ∈ properChartWords cap k,
      lambdaWord ps * chartTerm chi eta W T kappa0 js ps * K ps.prod‖ ≤
      ∑ bad : Fin k, ∑ v ∈ oneBadSlotBox (chartUpper k js) bad,
        ‖chartTerm chi eta W T kappa0 js (List.ofFn v) * K (List.ofFn v).prod‖ := by
  let f : List ℕ → ℝ := fun ps =>
    ‖chartTerm chi eta W T kappa0 js ps * K ps.prod‖
  calc
    _ ≤ ∑ ps ∈ properChartWords cap k,
        ‖lambdaWord ps * chartTerm chi eta W T kappa0 js ps * K ps.prod‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ps ∈ properChartWords cap k, f ps := by
      apply Finset.sum_le_sum
      intro ps hps
      rw [mul_assoc, norm_mul]
      exact (mul_le_mul_of_nonneg_right (lambdaWord_norm_le_one ps)
        (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ ∑ bad : Fin k,
        ∑ ps ∈ badChartWords chi eta W T kappa0 cap k js bad, f ps := by
      apply covered_nonnegative_sum_le _ Finset.univ _ f (fun _ => norm_nonneg _)
      intro ps hps hf
      have hactive : chartTerm chi eta W T kappa0 js ps ≠ 0 := by
        intro hz
        apply hf
        simp [f, hz]
      obtain ⟨bad, hbad⟩ := active_proper_chart_in_bad_words
        chi eta W T kappa0 js hps hactive
      exact ⟨bad, Finset.mem_univ _, hbad⟩
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro bad hbad
      exact signed_kernel_bad_chart_absolute_box chi eta W K hone hzero
        cap k T kappa0 bad hjs

-- Every occurrence rank is allowed. This theorem now pays the complete
-- all-k correction by the ORIGINAL dyadic proper-power boxes, using the
-- derived full-integer-bank amplitude. No extra support/amplitude field
-- is postulated on an opaque extension licence.
theorem family_all_k_correction_cardinal_bound {kStar : ℕ}
    (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (chi eta : ℝ → ℝ)
    (hone : ∀ t, t ≤ 1 → chi t = 1)
    (hzero : ∀ t, 2 ≤ t → chi t = 0)
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1)
    (heta : ∀ t, |eta t| ≤ 1)
    (cap : ℕ) (kappa0 : ℝ) {js : List ℕ}
    (hjs : js ∈ chartBank cap k.val)
    (K : ℕ → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hamp : ∀ ps, ps.length = k.val → ‖bankWeight A T k ps‖ ≤ M)
    (hK : ∀ n, ‖K n‖ ≤ H) :
    ‖∑ ps ∈ properChartWords cap k.val,
      lambdaWord ps *
        chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps *
          K ps.prod‖ ≤
      ∑ bad : Fin k.val, (M * H) *
        (∏ i : Fin k.val,
          if i = bad then
            ((Nat.sqrt (chartUpper k.val js i) + 1) *
              (Nat.log2 (chartUpper k.val js i) + 1) : ℕ)
          else chartUpper k.val js i + 1) := by
  apply (all_k_proper_correction_absolute_boxes chi eta (bankWeight A T k)
    hone hzero cap k.val (T : ℝ) kappa0 hjs K).trans
  apply Finset.sum_le_sum
  intro bad hbad
  apply oneBadSlotBox_absolute_mass (chartUpper k.val js) bad
    (fun i => by unfold chartUpper; positivity)
    (fun v => chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js
      (List.ofFn v) * K (List.ofFn v).prod)
    (M * H) (mul_nonneg hM hH)
  intro v hv
  rw [norm_mul]
  exact mul_le_mul
    (bank_chart_amplitude A T k chi eta hchi heta M hM hamp kappa0 js
      (List.ofFn v) (by simp))
    (hK _) (norm_nonneg _) hM

-- Crucially C and B are chosen before T, the original rank k, any
-- dyadic bank, and any test kernel. This is the all-rank order needed
-- by the original PP application, rather than finitely many fixed labels.
theorem family_uniform_all_k_correction {kStar : ℕ} (A : Family kStar) :
    ∃ C B : ℕ, 0 < C ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (chi eta : ℝ → ℝ),
        (∀ t, t ≤ 1 → chi t = 1) →
        (∀ t, 2 ≤ t → chi t = 0) →
        (∀ t, 0 ≤ chi t ∧ chi t ≤ 1) →
        (∀ t, |eta t| ≤ 1) →
        ∀ (cap : ℕ) (kappa0 : ℝ) (js : List ℕ),
          js ∈ chartBank cap k.val →
          ∀ (K : ℕ → ℂ) (H : ℝ), 0 ≤ H → (∀ n, ‖K n‖ ≤ H) →
          ‖∑ ps ∈ properChartWords cap k.val,
            lambdaWord ps *
              chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps *
                K ps.prod‖ ≤
            ∑ bad : Fin k.val,
              (((C : ℝ) * (Real.log ((T : ℝ) + 2))^B) * H) *
                (∏ i : Fin k.val,
                  if i = bad then
                    ((Nat.sqrt (chartUpper k.val js i) + 1) *
                      (Nat.log2 (chartUpper k.val js i) + 1) : ℕ)
                  else chartUpper k.val js i + 1) := by
  obtain ⟨C, B, hC, hamp⟩ := all_rank_bank_amplitude A
  refine ⟨C, B, hC, ?_⟩
  intro T k chi eta hone hzero hchi heta cap kappa0 js hjs K H hH hK
  have hlog : 0 ≤ Real.log ((T : ℝ) + 2) :=
    Real.log_nonneg (by positivity : (1 : ℝ) ≤ (T : ℝ) + 2)
  exact family_all_k_correction_cardinal_bound A T k chi eta hone hzero
    hchi heta cap kappa0 hjs K _ H (by positivity) hH (hamp T k) hK

-- The prime side really loses its rough projector on the active physical
-- support, instead of silently replacing a Lambda bulk by a prime sum.
theorem roughOneSlot_prime_of_lt {p : ℕ} (hp : p.Prime) {z : ℝ}
    (hz : z < (p : ℝ)) : roughOneSlot z p = 1 := by
  have hs : ∀ d : ℕ, d.Prime → d ∣ p → z < (d : ℝ) := by
    intro d hd hdp
    rcases (Nat.dvd_prime hp).mp hdp with h1 | heq
    · exact False.elim (hd.ne_one h1)
    · simpa only [heq] using hz
  simp [roughOneSlot, hs]

theorem roughWord_of_primes {z : ℝ} {ps : List ℕ}
    (hp : ∀ p ∈ ps, p.Prime ∧ z < (p : ℝ)) : roughWord z ps = 1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hhead := hp p (by simp)
    have htail : ∀ q ∈ ps, q.Prime ∧ z < (q : ℝ) := by
      intro q hq
      exact hp q (by simp [hq])
    simp only [roughWord, roughOneSlot_prime_of_lt hhead.1 hhead.2, ih htail, one_mul]

theorem bank_prime_chart_remove_rough {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar + 1)) (chi eta : ℝ → ℝ)
    (cap : ℕ) (kappa0 z : ℝ) (hz : z < A.lower * (T : ℝ)^A.aStar)
    (js : List ℕ) (K : List ℕ → ℂ) :
    (∑ ps ∈ primeTuples cap k.val,
      chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps *
        (roughWord z ps * K ps)) =
    ∑ ps ∈ primeTuples cap k.val,
      chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps * K ps := by
  apply Finset.sum_congr rfl
  intro ps hps
  by_cases hW : bankWeight A T k ps = 0
  · simp [chartTerm, trimmedWeight, hW]
  · obtain ⟨hlen, hprime⟩ := primeTuples_spec cap k.val hps
    have hs := (bankWeight_support A T k hlen hW).1
    have hr : roughWord z ps = 1 := roughWord_of_primes (by
      intro p hp
      exact ⟨(hprime p hp).1, lt_of_lt_of_le hz (hs p hp)⟩)
    rw [hr, one_mul]

theorem roughWord_eq_product {z : ℝ} (hz : 0 ≤ z) (ps : List ℕ) :
    roughWord z ps = roughOneSlot z ps.prod := by
  induction ps with
  | nil =>
    simp only [roughWord, List.prod_nil,
      ImbalancedChen.P5Z.ActualRoughHeathBrownWords.roughOne_one hz]
  | cons n ns ih =>
    rw [roughWord, List.prod_cons, ih,
      ImbalancedChen.P5Z.ActualRoughHeathBrownWords.roughOne_mul hz]

def familyAtlasSum {kStar : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (cap : ℕ) (chi eta : ℝ → ℝ)
    (z kappa0 : ℝ) (js : List ℕ) (K : ℕ → ℂ) : ℂ :=
  ∑ ps ∈ integerWords cap k.val,
    ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward.atlasEval chi z js ps
      (fun rows =>
        (listExtension (licence A T k)
          (ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward.originalProducts rows) : ℂ) *
        (eta (((ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward.originalProducts
          rows).prod : ℝ)/(T : ℝ)^(1-kappa0)) : ℂ) *
        K (ImbalancedChen.P5Z.PerGroupIntegerHBAtlasPushforward.originalProducts rows).prod)

def familyPrimeSum {kStar : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (cap : ℕ) (chi eta : ℝ → ℝ)
    (kappa0 : ℝ) (js : List ℕ) (K : ℕ → ℂ) : ℂ :=
  ∑ ps ∈ primeTuples cap k.val,
    chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps * K ps.prod

theorem family_atlas_sub_primes_exact {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar + 1)) (cap : ℕ) (chi eta : ℝ → ℝ)
    (hone : ∀ t, t ≤ 1 → chi t = 1)
    (hzero : ∀ t, 2 ≤ t → chi t = 0)
    (z kappa0 : ℝ) (hz : 0 ≤ z)
    (hfloor : z < A.lower * (T : ℝ)^A.aStar)
    (js : List ℕ) (K : ℕ → ℂ) :
    familyAtlasSum A T k cap chi eta z kappa0 js K -
      familyPrimeSum A T k cap chi eta kappa0 js K =
      ∑ ps ∈ properChartWords cap k.val,
        lambdaWord ps *
          chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps *
            (roughOneSlot z ps.prod * K ps.prod) := by
  have hsplit := licensed_atlas_all_k_prime_plus_proper (licence A T k)
    cap chi eta hone hzero hz (T : ℝ) kappa0 js [] (fun _ ps => K ps.prod)
  have hprime := bank_prime_chart_remove_rough A T k chi eta cap kappa0 z
    hfloor js (fun ps => K ps.prod)
  have hsplit' :
      familyAtlasSum A T k cap chi eta z kappa0 js K =
        familyPrimeSum A T k cap chi eta kappa0 js K +
          ∑ ps ∈ properChartWords cap k.val,
            lambdaWord ps *
              chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps *
                (roughOneSlot z ps.prod * K ps.prod) := by
    change familyAtlasSum A T k cap chi eta z kappa0 js K =
      (∑ ps ∈ primeTuples cap k.val,
        chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps * K ps.prod) + _
    rw [← hprime]
    simpa only [familyAtlasSum, bankWeight, roughWord_eq_product hz] using hsplit
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hsplit')

-- One kernel simultaneously covers a residue count, a coprime mean, their
-- signed difference, or a fixed finite signed modulus combination. Any
-- bound on that last combination is explicitly an additional obligation.
theorem family_atlas_to_primes_bound {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar + 1)) (cap : ℕ) (chi eta : ℝ → ℝ)
    (hone : ∀ t, t ≤ 1 → chi t = 1)
    (hzero : ∀ t, 2 ≤ t → chi t = 0)
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1)
    (heta : ∀ t, |eta t| ≤ 1)
    (z kappa0 : ℝ) (hz : 0 ≤ z)
    (hfloor : z < A.lower * (T : ℝ)^A.aStar)
    {js : List ℕ} (hjs : js ∈ chartBank cap k.val)
    (K : ℕ → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hamp : ∀ ps, ps.length = k.val → ‖bankWeight A T k ps‖ ≤ M)
    (hK : ∀ n, ‖K n‖ ≤ H) :
    ‖familyAtlasSum A T k cap chi eta z kappa0 js K -
      familyPrimeSum A T k cap chi eta kappa0 js K‖ ≤
      ∑ bad : Fin k.val, (M * H) *
        (∏ i : Fin k.val,
          if i = bad then
            ((Nat.sqrt (chartUpper k.val js i) + 1) *
              (Nat.log2 (chartUpper k.val js i) + 1) : ℕ)
          else chartUpper k.val js i + 1) := by
  rw [family_atlas_sub_primes_exact A T k cap chi eta hone hzero z kappa0 hz
    hfloor js K]
  apply family_all_k_correction_cardinal_bound A T k chi eta hone hzero hchi
    heta cap kappa0 hjs (fun n => roughOneSlot z n * K n) M H hM hH hamp
  intro n
  rw [norm_mul]
  exact (mul_le_mul (roughOneSlot_norm_le z n) (hK n)
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

end
end ImbalancedChen.Part3.AllKFamilyLambdaCorrectionBound
