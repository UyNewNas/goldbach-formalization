import ImbalancedChen.Part5OriginalH430TaggedSourceRejections

/-! P5.6 / h34: restore the original additive-prime label P behind
every true quotient receiver q=(N-P)/p in both tagged U3/U4 bands.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The quotient q is an integer, not in general prime.  No historical
full/selected/inherited owner or final count inequality is assumed. -/
namespace ImbalancedChen.Part5OriginalH430TaggedAdditivePrimeLabels
noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections

def additivePrimeLabel (N : ℕ) (z : TaggedReceiver) : ℕ :=
  N - arithmeticPrime z * arithmeticQuotientPrime z

def frozenPrimeCutoff (N n : ℕ) (tau : ℝ) (k : Root) (p : ℕ) : ℝ :=
  (rootQ N n k tau p / (p : ℝ)) ^
    (1 / (frozenRoot n k tau (physicalPrime N p)).physical.argument)

/-- The ORIGINAL prime P, not q, is the original additive receiver. -/
theorem raw_prime_fibre_iff (N p q : ℕ) :
    q ∈ chenQuotientPrimeSource N p ↔
      ∃ P ∈ chenAdditivePrimeCarrier N,
        p ∣ N - P ∧ (N - P) / p = q := by
  constructor
  · intro hq
    obtain ⟨P, hP, heq⟩ := Finset.mem_image.mp hq
    obtain ⟨hPc, hd⟩ := mem_chenQuotientPrimeCarrier.mp hP
    exact ⟨P, hPc, hd, heq⟩
  · rintro ⟨P, hPc, hd, heq⟩
    exact Finset.mem_image.mpr
      ⟨P, mem_chenQuotientPrimeCarrier.mpr ⟨hPc, hd⟩, heq⟩

/-- Strict original/frozen roughness gates share that SAME P. -/
theorem sifted_prime_fibre_iff (N p q : ℕ) (z : ℝ) :
    q ∈ chenSiftedQuotientPrimeSource N p z ↔
      ∃ P ∈ chenAdditivePrimeCarrier N,
        ChenQuotient p z (N - P) ∧ (N - P) / p = q := by
  constructor
  · intro hq
    change q ∈ (chenQuotientPrimeSource N p).filter (ChenPrimeRough z) at hq
    obtain ⟨hr, hrough⟩ := Finset.mem_filter.mp hq
    obtain ⟨P, hPc, hd, heq⟩ := (raw_prime_fibre_iff N p q).mp hr
    refine ⟨P, hPc, ?_, heq⟩
    exact ⟨hd, by simpa only [heq] using hrough⟩
  · rintro ⟨P, hPc, hquot, heq⟩
    obtain ⟨hd, hrough⟩ := hquot
    change q ∈ (chenQuotientPrimeSource N p).filter (ChenPrimeRough z)
    exact Finset.mem_filter.mpr
      ⟨(raw_prime_fibre_iff N p q).mpr ⟨P, hPc, hd, heq⟩,
       by simpa only [heq] using hrough⟩

theorem tagged_raw_quotient {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    arithmeticQuotientPrime z ∈ chenQuotientPrimeSource N (arithmeticPrime z) := by
  cases z with
  | inl x =>
      have hx : x ∈ rawPairs N .U3 := by simpa [rawTagged] using hz
      exact (Finset.mem_sigma.mp hx).2
  | inr x =>
      have hx : x ∈ rawPairs N .U4 := by simpa [rawTagged] using hz
      exact (Finset.mem_sigma.mp hx).2

/-- Actual prime P=N-p*q; equality uses exact divisibility. -/
theorem raw_prime_label_data {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    additivePrimeLabel N z ∈ chenAdditivePrimeCarrier N ∧
    (N - additivePrimeLabel N z) / arithmeticPrime z =
      arithmeticQuotientPrime z := by
  obtain ⟨P, hPc, hd, heq⟩ :=
    (raw_prime_fibre_iff N (arithmeticPrime z)
      (arithmeticQuotientPrime z)).mp (tagged_raw_quotient hz)
  have hPN : P < N := (mem_chenAdditivePrimeCarrier.mp hPc).1
  have hmul : arithmeticPrime z * arithmeticQuotientPrime z = N - P := by
    rw [← heq]
    exact Nat.mul_div_cancel' hd
  have hlabel : additivePrimeLabel N z = P := by
    unfold additivePrimeLabel
    rw [hmul]
    omega
  constructor
  · rwa [hlabel]
  · rwa [hlabel]

theorem raw_additive_label_prime {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) : (additivePrimeLabel N z).Prime :=
  (mem_chenAdditivePrimeCarrier.mp (raw_prime_label_data hz).1).2.1

/-- Tag, original selected p and actual additive prime P distinguish
all raw occurrences, including overlap between U3 and U4. -/
def taggedPrimeLabel (N : ℕ) (z : TaggedReceiver) : (Root × ℕ) × ℕ :=
  ((arithmeticBand z, arithmeticPrime z), additivePrimeLabel N z)

theorem tagged_prime_label_injective_on_raw (N : ℕ) :
    Set.InjOn (taggedPrimeLabel N) (rawTagged N : Set TaggedReceiver) := by
  intro x hx y hy heq
  have hk : arithmeticBand x = arithmeticBand y :=
    congrArg (fun t : (Root × ℕ) × ℕ => t.1.1) heq
  have hp : arithmeticPrime x = arithmeticPrime y :=
    congrArg (fun t : (Root × ℕ) × ℕ => t.1.2) heq
  have hP : additivePrimeLabel N x = additivePrimeLabel N y :=
    congrArg (fun t : (Root × ℕ) × ℕ => t.2) heq
  have hqx := (raw_prime_label_data hx).2
  have hqy := (raw_prime_label_data hy).2
  have hq : arithmeticQuotientPrime x = arithmeticQuotientPrime y := by
    calc
      arithmeticQuotientPrime x =
          (N - additivePrimeLabel N x) / arithmeticPrime x := hqx.symm
      _ = (N - additivePrimeLabel N y) / arithmeticPrime y := by rw [hP, hp]
      _ = arithmeticQuotientPrime y := hqy
  exact arithmetic_labels_injective (Prod.ext hk (Prod.ext hp hq))

/-- True original-prime-labelled U3/U4 receiver fibres. -/
def originalPrimePairs (N : ℕ) (k : Root) : Finset TaggedPair :=
  (originalBand N k).sigma (fun p =>
    (chenAdditivePrimeCarrier N).filter
      (fun P => ChenQuotient p ((N : ℝ)^a) (N - P)))

/-- Same additive-prime source, but actual frozen Q/max-two cutoff. -/
def frozenPrimePairs (N n : ℕ) (tau : ℝ) (k : Root) : Finset TaggedPair :=
  (originalBand N k).sigma (fun p =>
    (chenAdditivePrimeCarrier N).filter
      (fun P => ChenQuotient p (frozenPrimeCutoff N n tau k p) (N - P)))

theorem original_pairs_prime_card (N : ℕ) (k : Root) :
    (originalPairs N k).card = (originalPrimePairs N k).card := by
  rw [originalPairs, originalPrimePairs, Finset.card_sigma, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  exact chenSiftedQuotientPrimeSource_card N p ((N : ℝ)^a)

theorem frozen_pairs_prime_card (N n : ℕ) (tau : ℝ) (k : Root) :
    (frozenPairs N n tau k).card = (frozenPrimePairs N n tau k).card := by
  rw [frozenPairs, frozenPrimePairs, Finset.card_sigma, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  exact chenSiftedQuotientPrimeSource_card N p (frozenPrimeCutoff N n tau k p)

/-- Original U3+U4, preserving overlap, now on ACTUAL additive P labels.
No conversion to history marks or table weights. -/
theorem original_U34_eq_additive_prime_pairs (N : ℕ) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      ((originalPrimePairs N .U3).card : ℝ) +
      ((originalPrimePairs N .U4).card : ℝ) := by
  calc
    currentChenUpsilon3 N + currentChenUpsilon4 N =
        ((originalTagged N).card : ℝ) := original_U34_eq_tagged_card N
    _ = ((originalPairs N .U3).card : ℝ) +
        ((originalPairs N .U4).card : ℝ) := by
          simp [originalTagged, Finset.card_disjSum, Nat.cast_add]
    _ = _ := by
      rw [original_pairs_prime_card N .U3,
        original_pairs_prime_card N .U4]

/-- Newly accepted only because the frozen strict cutoff is smaller.
The original and frozen tests act on the SAME original prime P. -/
theorem frozen_only_pair_additive_iff (N n p q : ℕ) (tau : ℝ) (k : Root) :
    (⟨p,q⟩ : TaggedPair) ∈
        frozenPairs N n tau k \ originalPairs N k ↔
      p ∈ originalBand N k ∧
      ∃ P ∈ chenAdditivePrimeCarrier N,
        ChenQuotient p (frozenPrimeCutoff N n tau k p) (N - P) ∧
        ¬ ChenQuotient p ((N : ℝ)^a) (N - P) ∧
        (N - P) / p = q := by
  constructor
  · intro h
    obtain ⟨hf, hnot⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hp, hqf⟩ := Finset.mem_sigma.mp hf
    obtain ⟨P, hPc, hQf, heq⟩ :=
      (sifted_prime_fibre_iff N p q (frozenPrimeCutoff N n tau k p)).mp hqf
    refine ⟨hp, P, hPc, hQf, ?_, heq⟩
    intro hQo
    have hqo := (sifted_prime_fibre_iff N p q ((N : ℝ)^a)).mpr
      ⟨P, hPc, hQo, heq⟩
    exact hnot (Finset.mem_sigma.mpr ⟨hp, hqo⟩)
  · rintro ⟨hp, P, hPc, hQf, hno, heq⟩
    have hf := (sifted_prime_fibre_iff N p q
      (frozenPrimeCutoff N n tau k p)).mpr ⟨P, hPc, hQf, heq⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_sigma.mpr ⟨hp, hf⟩, ?_⟩
    intro ho
    have hqo := (Finset.mem_sigma.mp ho).2
    have hrough := (Finset.mem_filter.mp
      (show q ∈ (chenQuotientPrimeSource N p).filter
        (ChenPrimeRough ((N : ℝ)^a)) from hqo)).2
    apply hno
    exact ⟨hQf.1, by simpa only [heq] using hrough⟩

/-- The still-rejected lane is a genuine prime P whose quotient fails
the frozen roughness predicate, not another copy of frozenOnly. -/
theorem rejected_frozen_pair_additive_iff
    (N n p q : ℕ) (tau : ℝ) (k : Root) :
    (⟨p,q⟩ : TaggedPair) ∈ rawPairs N k \ frozenPairs N n tau k ↔
      p ∈ originalBand N k ∧
      ∃ P ∈ chenAdditivePrimeCarrier N,
        p ∣ N - P ∧
        ¬ ChenPrimeRough (frozenPrimeCutoff N n tau k p) ((N - P) / p) ∧
        (N - P) / p = q := by
  constructor
  · intro h
    obtain ⟨hr, hnot⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp hr
    obtain ⟨P, hPc, hd, heq⟩ := (raw_prime_fibre_iff N p q).mp hq
    refine ⟨hp, P, hPc, hd, ?_, heq⟩
    intro hrough
    have hf : q ∈ frozenReceiver N n tau k p := by
      change q ∈ (chenQuotientPrimeSource N p).filter
        (ChenPrimeRough (frozenPrimeCutoff N n tau k p))
      exact Finset.mem_filter.mpr
        ⟨hq, by simpa only [heq] using hrough⟩
    exact hnot (Finset.mem_sigma.mpr ⟨hp, hf⟩)
  · rintro ⟨hp, P, hPc, hd, hrough, heq⟩
    have hq := (raw_prime_fibre_iff N p q).mpr ⟨P, hPc, hd, heq⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_sigma.mpr ⟨hp, hq⟩, ?_⟩
    intro hf
    have hr := (Finset.mem_filter.mp
      (show q ∈ (chenQuotientPrimeSource N p).filter
        (ChenPrimeRough (frozenPrimeCutoff N n tau k p))
        from (Finset.mem_sigma.mp hf).2)).2
    exact hrough (by simpa only [heq] using hr)

end
end ImbalancedChen.Part5OriginalH430TaggedAdditivePrimeLabels
