import ImbalancedChen.P5OriginalPhysicalBufferedU6NativeMain
import ImbalancedChen.CurrentChenP5CausalPrimeCorrectionPayment
import ImbalancedChen.CurrentChenP5CausalRhoFactorization
import ImbalancedChen.SingletonPrimeProductTransportP5

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A common attachment and its summed full-policy reserve on the SAME actual
17572 crop. The source is the already defined strict physical interior;
its complementary arithmetic walls are dropped only from a positive count.
The entire even-exit raw density stays literal. It is NOT identified with
h248, the Runbo harmonic main, or the saved original L6 integer.
The signed primitive error is pushed to its actual full modulus coefficient
and identified with physical singleton PP, with both prime corrections kept.
-/
namespace ImbalancedChen.P5OriginalRetainedU6RawSourcePayment
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5SelectedMaskTransport
open P5Z.U1011OriginalPairedRowPrimeTests
open P5Z.U1011OriginalPairedFixedMaskHarmonic (outerUnion)
open P5U6OriginalPairedMaskNativeHarmonicSourceOnly
open P5OriginalPhysicalBufferedU6NativeMainSourceOnly

abbrev Policy := (ℕ × ℕ) → List ℕ → Bool
abbrev a : ℝ := 417 / 5000

def actualMask (N : ℕ) : ℕ × ℕ → Prop :=
  nativeMask (outerUnion (Finset.univ : Finset Row)) N

def source (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  strictSelector (Finset.univ : Finset Row) N eta

theorem actualMask_eq_original (N : ℕ) :
    actualMask N = Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ) := by
  funext p
  exact propext (by
    simp only [actualMask, P5Z.U1011OriginalPairedFixedMaskHarmonic.outerUnion_all,
      nativeMask_actual_adopted])

theorem source_subset_closed (N : ℕ) (eta : ℝ) :
    source N eta ⊆ currentChenUpsilon6RetainedSelector N (actualMask N) eta :=
  strictSelector_subset_closed _ N eta

theorem source_subset_sixth (N : ℕ) (eta : ℝ) : source N eta ⊆ sixthSupport N := by
  intro p hp
  have h := source_subset_closed N eta hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1

/-- Exact original complement, without changing its half-open row owners. -/
theorem source_not_deleted {N : ℕ} {eta : ℝ} {p : ℕ × ℕ}
    (hp : p ∈ source N eta) :
    ¬Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ) p := by
  have h := (Finset.mem_filter.mp (Finset.mem_filter.mp (source_subset_closed N eta hp)).1).2
  rw [← actualMask_eq_original N]
  exact h

/-- The independent original L6 root survives. In particular the first
max branch is used only below mu, and alpha is not reset to two. -/
theorem source_original_root {N : ℕ} (hN : (1 : ℝ) < N) {eta : ℝ}
    (heta : 0 ≤ eta) {p : ℕ × ℕ} (hp : p ∈ source N eta) :
    2 * a + eta < P5U6CausalLevelGeometry.residual
        (currentChenUpsilon6LogCoordinates N p) ∧
      2 ≤ P5U6CausalLevelGeometry.alpha (currentChenUpsilon6LogCoordinates N p) := by
  have hx := ((mem_currentChenUpsilon6RetainedSelector_log_iff hN _ eta p).1
    (source_subset_closed N eta hp)).2.2.2
  exact ⟨(P5U6CausalLevelGeometry.domain_bounds heta hx).1,
    P5U6CausalLevelGeometry.alpha_ge_two heta hx⟩

/-- Auxiliary small-factor allocation, independent of pair and root.
It changes neither the actual even-exit policy nor its frozen physical Q. -/
def smallCutoff (N : ℕ) (epsilon : ℝ) : ℝ := (N : ℝ) ^ (a * epsilon ^ 2)
def smallLevel (N : ℕ) (epsilon : ℝ) : ℝ := (N : ℝ) ^ (a * epsilon)

theorem attachment_gates {N : ℕ} (hN : (1 : ℝ) < N) {epsilon : ℝ}
    (heps : 0 < epsilon) (heps8 : epsilon < 1 / 8) :
    1 < smallLevel N epsilon ∧ smallCutoff N epsilon ≤ smallLevel N epsilon ∧
      smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N := by
  have hs : epsilon ^ 2 ≤ epsilon := by nlinarith
  have hs1 : epsilon ^ 2 ≤ 1 := by nlinarith
  refine ⟨Real.one_lt_rpow hN (mul_pos (by norm_num [a]) heps), ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hN.le
      (mul_le_mul_of_nonneg_left hs (by norm_num [a]))
  · apply Real.rpow_le_rpow_of_exponent_le hN.le
    change a * epsilon ^ 2 ≤ a
    nlinarith [show 0 < a by norm_num [a]]

/-- These are the actual beta-head and reserve gates required by I's W
receiver. They do not assert that every active atom has that W source. -/
theorem small_allocation {N : ℕ} (hN : (1 : ℝ) < N) {epsilon buffer : ℝ}
    (heps : 0 < epsilon) (heps8 : epsilon < 1 / 8) (halloc : a * epsilon ≤ buffer) :
    (smallCutoff N epsilon)^2 ≤ smallLevel N epsilon ∧
      smallLevel N epsilon ≤ (N : ℝ)^buffer := by
  constructor
  · unfold smallCutoff smallLevel
    rw [← Real.rpow_mul_natCast (zero_lt_one.trans hN).le]
    apply Real.rpow_le_rpow_of_exponent_le hN.le
    norm_num [a]
    nlinarith
  · exact Real.rpow_le_rpow_of_exponent_le hN.le halloc

def divisors (N : ℕ) (epsilon : ℝ) (policy : Policy) (p : ℕ × ℕ) : Finset ℕ :=
  actualLowerSmallRoughModuli (policy p) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N)
def rho (N : ℕ) (epsilon : ℝ) (policy : Policy) (p : ℕ × ℕ) : ℕ → ℝ :=
  actualLowerSmallRoughRho (policy p) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) (smallLevel N epsilon)
def rawDensity (N : ℕ) (policy : List ℕ → Bool) : ℝ :=
  reciprocalTotientDensity
    (fixedEvenRoughSupport policy N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      0 (P5CausalRhoQuotientBridge.cutoff N))
    (fixedEvenRoughCoefficient policy N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      0 (P5CausalRhoQuotientBridge.cutoff N))
def piMass (N : ℕ) : ℝ := ((chenPrimePrefix N).card : ℝ)
def primeScale (N : ℕ) : ℝ := piMass N * singularSeries N / Real.log (N : ℝ)
def pairMass (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ p ∈ source N eta, 1 / (Nat.totient (p.1 * p.2) : ℝ)
def rawMain (N : ℕ) (eta : ℝ) (policy : Policy) : ℝ :=
  ∑ p ∈ source N eta, piMass N / (Nat.totient (p.1 * p.2) : ℝ) * rawDensity N (policy p)
def physicalMain (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : ℝ :=
  ∑ p ∈ source N eta, piMass N / (Nat.totient (p.1 * p.2) : ℝ) *
    physicalDensitySum (divisors N epsilon policy p) (rho N epsilon policy p)
def projectionReserve (N : ℕ) (eta tolerance : ℝ) : ℝ :=
  ∑ p ∈ source N eta, piMass N / (Nat.totient (p.1 * p.2) : ℝ) *
    (tolerance * singularSeries N / Real.log (N : ℝ))

theorem projectionReserve_eq (N : ℕ) (eta tolerance : ℝ) :
    projectionReserve N eta tolerance = tolerance * pairMass N eta * primeScale N := by
  simp only [projectionReserve, pairMass, primeScale, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- A bound from the actual prime harmonic source, not pair cardinality.
One threshold precedes the buffer and every later policy. -/
theorem exists_uniform_pair_mass_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop, ∀ eta : ℝ, 0 ≤ eta → pairMass N eta ≤ B := by
  obtain ⟨M, hM, hm⟩ := currentChenUpsilon6Ordinary_reciprocalTotient_eventually_bounded 0
  refine ⟨M + 1, by linarith, ?_⟩
  filter_upwards [hm, eventually_ge_atTop (2 : ℕ)] with N hmass hN
  intro eta heta
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hs : source N eta ⊆ currentChenUpsilon6OrdinarySelector N 0 := by
    intro p hp
    have hc := source_subset_closed N eta hp
    have hi := (Finset.mem_filter.mp
      (show p ∈ (closedSelector (Finset.univ : Finset Row) N eta).filter (StrictInterior N eta) by
        rw [← strictSelector_eq_closed_filter]; exact hp)).2
    have hbase := source_subset_sixth N eta hp
    have hpow : (N : ℝ)^((833 / 2500 : ℝ)-eta) ≤ (N : ℝ)^((833 / 2500 : ℝ)-0) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    have hprod := hi.2.trans_le hpow
    apply Finset.mem_filter.mpr
    refine ⟨?_, hi.1, hprod⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hbase, by simp⟩, ?_⟩
    convert hprod.le using 1 <;> norm_num
  have hsub : pairMass N eta ≤ ∑ p ∈ currentChenUpsilon6OrdinarySelector N 0,
      1 / (Nat.totient (p.1 * p.2) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
  exact hsub.trans (hmass.trans (by linarith))

abbrev Mark := Σ _ : ℕ × ℕ, ℕ
def marks (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : Finset Mark :=
  (source N eta).sigma (divisors N epsilon policy)
def modulus (m : Mark) : ℕ := (m.1.1 * m.1.2) * m.2
def support (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : Finset ℕ :=
  (marks N eta epsilon policy).image modulus
def sigma (N : ℕ) (eta epsilon : ℝ) (policy : Policy) (q : ℕ) : ℝ :=
  ∑ m ∈ (marks N eta epsilon policy).filter (fun m => modulus m = q), rho N epsilon policy m.1 m.2

/-- All attached divisor primes are strictly below the ORIGINAL cutoff.
The cutoff equality belongs to the selected pair, never the divisor. -/
theorem divisors_strict_small {N : ℕ} {epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N)
    (p : ℕ × ℕ) {k : ℕ} (hk : k ∈ divisors N epsilon policy p) :
    SmallPrimeSupportedAt (P5CausalRhoQuotientBridge.cutoff N) k := by
  obtain ⟨⟨s,r⟩,hsr,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hs,hr⟩ := Finset.mem_product.mp hsr
  have hs0 := (actualSmallRosserSupport_squarefree N _ _ hs).ne_zero
  have hr0 := (fixedEvenRoughSupport_squarefree (policy p) N _ _ _ hr).ne_zero
  refine ⟨mul_ne_zero hs0 hr0,?_⟩
  intro l hl
  have hlp := (Nat.mem_primeFactors.mp hl).1
  rcases hlp.dvd_mul.mp (Nat.mem_primeFactors.mp hl).2.1 with hls | hlr
  · exact ((actualSmallRosserSupport_smallPrimeSupportedAt N _ _ hs).2 l
      (Nat.mem_primeFactors.mpr ⟨hlp,hls,hs0⟩)).trans_le hwz
  · exact mem_roughPrimeUniverse_upper
      (fixedEvenRoughSupport_primeFactors_mem (policy p) N _ _ _ hr
        (Nat.mem_primeFactors.mpr ⟨hlp,hlr,hr0⟩))

theorem source_multiplier_rough {N : ℕ} {eta : ℝ} {p : ℕ × ℕ}
    (hp : p ∈ source N eta) :
    RoughPrimeSupportedAt (P5CausalRhoQuotientBridge.cutoff N) (p.1*p.2) := by
  have hs := source_subset_sixth N eta hp
  have hd := chenY6PrimeSelector_sieve_data hs
  refine ⟨(Nat.zero_lt_one.trans hd.1).ne',?_⟩
  intro l hl
  exact P5CausalRhoQuotientBridge.row_multiplier_rough hs l
    (Nat.mem_primeFactors.mp hl).1 (Nat.mem_primeFactors.mp hl).2.1

/-- No multiplicity loss in the physical coefficient: rough/small
factorization recovers b, and the original ordered pair recovers p. -/
theorem modulus_injOn {N : ℕ} {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N) :
    Set.InjOn modulus (marks N eta epsilon policy : Set Mark) := by
  rintro ⟨p,k⟩ hpk ⟨q,l⟩ hql heq
  obtain ⟨hp,hk⟩ := Finset.mem_sigma.mp hpk
  obtain ⟨hq,hl⟩ := Finset.mem_sigma.mp hql
  have hf : (k,p.1*p.2) = (l,q.1*q.2) :=
    smallRough_factorization_unique
      (divisors_strict_small policy hwz p hk) (source_multiplier_rough hp)
      (divisors_strict_small policy hwz q hl) (source_multiplier_rough hq)
      (by simpa only [modulus,Nat.mul_comm] using heq)
  have hpq : p = q := chenY6PrimeSelector_multiplier_injOn N _ _ _
    (source_subset_sixth N eta hp) (source_subset_sixth N eta hq) (congrArg Prod.snd hf)
  have hkl : k = l := congrArg Prod.fst hf
  subst q
  subst l
  rfl

theorem sigma_at_mark {N : ℕ} {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N)
    {m : Mark} (hm : m ∈ marks N eta epsilon policy) :
    sigma N eta epsilon policy (modulus m) = rho N epsilon policy m.1 m.2 := by
  unfold sigma
  apply Finset.sum_eq_single m
  · intro n hn hne
    exact (hne (modulus_injOn policy hwz (Finset.mem_filter.mp hn).1 hm
      (Finset.mem_filter.mp hn).2)).elim
  · intro h
    exact (h (Finset.mem_filter.mpr ⟨hm,rfl⟩)).elim

/-- Actual scalar PP amplitude is derived, not assumed or multiplied by
the number of pair labels. This still supplies NO physical cap or PP saving. -/
theorem sigma_abs_le_one {N : ℕ} {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N) (q : ℕ) :
    |sigma N eta epsilon policy q| ≤ 1 := by
  by_cases hq : q ∈ support N eta epsilon policy
  · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hq
    rw [sigma_at_mark policy hwz hm]
    exact actualLowerSmallRoughRho_abs_le_one (policy m.1) N _ _ _ _ m.2
  · have hz : sigma N eta epsilon policy q = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      exact (hq (Finset.mem_image.mpr ⟨m,(Finset.mem_filter.mp hm).1,
        (Finset.mem_filter.mp hm).2⟩)).elim
    rw [hz]
    norm_num

theorem support_primitive_squarefree {N : ℕ} {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N)
    {q : ℕ} (hq : q ∈ support N eta epsilon policy) :
    0 < q ∧ Squarefree q ∧ Nat.Coprime q N := by
  obtain ⟨⟨p,k⟩,hpk,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hp,hk⟩ := Finset.mem_sigma.mp hpk
  have hs := source_subset_sixth N eta hp
  have hb := chenY6PrimeSelector_multiplier_squarefree hs
  have hd := actualLowerSmallRoughModuli_squarefree (policy p) N _ _ _ hk
  have hc := P5CausalRhoQuotientBridge.moduli_coprime_multiplier (policy p) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (p.1*p.2)
    (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) hwz
    (P5CausalRhoQuotientBridge.row_multiplier_rough hs) hk
  refine ⟨Nat.mul_pos (Nat.pos_of_ne_zero hb.ne_zero) (Nat.pos_of_ne_zero hd.ne_zero),
    (Nat.squarefree_mul hc).mpr ⟨hb,hd⟩,?_⟩
  exact Nat.coprime_mul_iff_left.mpr ⟨(chenY6PrimeSelector_sieve_data hs).2.1,
    actualLowerSmallRoughModuli_coprime_target (policy p) N _ _ _ hk⟩
/-- Actual physical moduli, with all coincident labels summed BEFORE PP. -/
theorem pushforward (N : ℕ) (eta epsilon : ℝ) (policy : Policy) (F : ℕ → ℝ) :
    (∑ p ∈ source N eta, ∑ k ∈ divisors N epsilon policy p,
      rho N epsilon policy p k * F ((p.1*p.2)*k)) =
      ∑ q ∈ support N eta epsilon policy, sigma N eta epsilon policy q * F q := by
  have hm : (∑ p ∈ source N eta, ∑ k ∈ divisors N epsilon policy p,
      rho N epsilon policy p k * F ((p.1*p.2)*k)) =
      ∑ m ∈ marks N eta epsilon policy, rho N epsilon policy m.1 m.2 * F (modulus m) := by
    rw [marks, Finset.sum_sigma]
    rfl
  rw [hm]
  have hf := Finset.sum_fiberwise_of_maps_to (s := marks N eta epsilon policy)
    (t := support N eta epsilon policy) (g := modulus)
    (fun m hm => Finset.mem_image_of_mem modulus hm)
    (fun m => rho N epsilon policy m.1 m.2 * F (modulus m))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro q _
  unfold sigma
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

def signedPP (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : ℝ :=
  Part3.primeProductSignedError 1 N N (support N eta epsilon policy)
    (sigma N eta epsilon policy) (P5S1SingletonPP.singletonWeight N (fun _ => 1))
def primeCorrections (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : ℝ :=
  (∑ q ∈ support N eta epsilon policy, sigma N eta epsilon policy q *
    (chenPrimeDivisorCount N q / (Nat.totient q : ℝ))) +
  ∑ q ∈ support N eta epsilon policy, sigma N eta epsilon policy q * chenCentrePrimeAPCount N N q

def estimator (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : ℝ :=
  ∑ p ∈ source N eta, P5CausalRhoQuotientBridge.rowEstimator N policy
    (fun _ => smallCutoff N epsilon) (fun _ => smallLevel N epsilon) p

/-- True-prime source, original total physical moduli, exact coprime
singleton mean, and both corrections. No PP estimate is an input. -/
theorem estimator_eq_same_rho_PP {N : ℕ} (hN : (1 : ℝ) < N)
    (eta : ℝ) {epsilon : ℝ} (heps : 0 < epsilon) (heps8 : epsilon < 1/8)
    (policy : Policy) :
    estimator N eta epsilon policy = physicalMain N eta epsilon policy +
      signedPP N eta epsilon policy - primeCorrections N eta epsilon policy := by
  have hg := attachment_gates hN heps heps8
  have hrow (p : ℕ × ℕ) (hp : p ∈ source N eta) :=
    P5CausalRhoQuotientBridge.rowEstimator_primitive_and_prime_corrections N policy
      (fun _ => smallCutoff N epsilon) (fun _ => smallLevel N epsilon) p
      (source_subset_sixth N eta hp) hg.2.2
  have heq := Finset.sum_congr rfl hrow
  change estimator N eta epsilon policy = _ at heq
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at heq
  change estimator N eta epsilon policy = physicalMain N eta epsilon policy +
    (∑ p ∈ source N eta, ∑ k ∈ divisors N epsilon policy p,
      rho N epsilon policy p k *
        finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N ((p.1*p.2)*k)) -
    (∑ p ∈ source N eta, ∑ k ∈ divisors N epsilon policy p,
      rho N epsilon policy p k *
        (chenPrimeDivisorCount N ((p.1*p.2)*k) / (Nat.totient ((p.1*p.2)*k) : ℝ))) -
    (∑ p ∈ source N eta, ∑ k ∈ divisors N epsilon policy p,
      rho N epsilon policy p k * chenCentrePrimeAPCount N N ((p.1*p.2)*k)) at heq
  rw [pushforward, pushforward, pushforward] at heq
  have hpp : signedPP N eta epsilon policy =
      ∑ q ∈ support N eta epsilon policy, sigma N eta epsilon policy q *
        finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q := by
    exact P5S1SingletonPP.primeProductSignedError_singleton_eq N N
      (support N eta epsilon policy) (sigma N eta epsilon policy) (fun _ => 1)
  rw [← hpp] at heq
  unfold primeCorrections
  linarith only [heq]

theorem estimator_le_actual {N : ℕ} (hN : (1 : ℝ) < N)
    (eta : ℝ) {epsilon : ℝ} (heps : 0 < epsilon) (heps8 : epsilon < 1/8)
    (policy : Policy) : estimator N eta epsilon policy ≤ currentChenUpsilon6 N (actualMask N) := by
  have hg := attachment_gates hN heps heps8
  have he : estimator N eta epsilon policy ≤ ∑ p ∈ source N eta, sixthWeight N p := by
    exact Finset.sum_le_sum (fun p _ =>
      P5CausalRhoQuotientBridge.rowEstimator_le_actual N policy
        (fun _ => smallCutoff N epsilon) (fun _ => smallLevel N epsilon) p hg)
  have hs : (∑ p ∈ source N eta, sixthWeight N p) ≤
      currentChenUpsilon6Retained N (actualMask N) eta :=
    Finset.sum_le_sum_of_subset_of_nonneg (source_subset_closed N eta)
      (fun _ _ _ => Nat.cast_nonneg _)
  exact he.trans (hs.trans (currentChenUpsilon6Retained_le N (actualMask N) eta))

/-- Missing aggregate source step: ONE epsilon and N0 precede eta and
ALL actual pair-dependent even-exit policies. Harmonic mass, not the
number of labelled pairs, pays the complete attachment reserve.
The remaining PP and prime corrections are the literal same-rho terms. -/
theorem exists_uniform_full_raw_count (delta epsilonMax : ℝ)
    (hdelta : 0 < delta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ eta : ℝ, 0 ≤ eta → ∀ policy : Policy,
          rawMain N eta policy - delta * primeScale N + signedPP N eta epsilon policy -
            primeCorrections N eta epsilon policy ≤ currentChenUpsilon6 N (actualMask N) := by
  obtain ⟨B,hB,hmass⟩ := exists_uniform_pair_mass_bound
  let tolerance := delta / B
  have htolerance : 0 < tolerance := div_pos hdelta hB
  obtain ⟨epsilon,heps,heps8,hepsMax,_hepsr,N1,hN1,hproj⟩ :=
    exists_actualLowerSmallRoughRho_density_ge_full_reserve a 1 tolerance epsilonMax
      (by norm_num [a]) (by norm_num) htolerance hepsilonMax
  obtain ⟨N2,hN2⟩ := eventually_atTop.mp hmass
  refine ⟨epsilon,heps,heps8,hepsMax,max N1 N2,hN1.trans (le_max_left _ _),?_⟩
  intro N hN hEven eta heta policy
  have hn1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hn2 : N2 ≤ N := (le_max_right _ _).trans hN
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 ≤ primeScale N :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (singularSeries_pos N).le) (Real.log_pos hn).le
  have hbound : projectionReserve N eta tolerance ≤ delta * primeScale N := by
    rw [projectionReserve_eq]
    have hm := mul_le_mul_of_nonneg_left (hN2 N hn2 eta heta) htolerance.le
    have heq : tolerance * B = delta := div_mul_cancel₀ _ hB.ne'
    rw [heq] at hm
    exact mul_le_mul_of_nonneg_right hm hscale
  have hmain : rawMain N eta policy - projectionReserve N eta tolerance ≤
      physicalMain N eta epsilon policy := by
    rw [rawMain,projectionReserve,← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hc : (N : ℝ)^(a*1) ≤ (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N) : ℝ) := by
      simpa only [mul_one] using (Nat.le_ceil (P5CausalRhoQuotientBridge.cutoff N))
    have h := hproj N hn1 hEven (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) hc (policy p)
    dsimp only at h
    simp only [mul_one] at h
    have hmul := mul_le_mul_of_nonneg_left h
      (div_nonneg (Nat.cast_nonneg (chenPrimePrefix N).card)
        (Nat.cast_nonneg (Nat.totient (p.1*p.2))))
    simpa only [rawDensity,physicalMain,divisors,rho,smallCutoff,smallLevel,piMass,mul_sub] using hmul
  have hfinite := estimator_le_actual hn eta heps heps8 policy
  rw [estimator_eq_same_rho_PP hn eta heps heps8 policy] at hfinite
  linarith only [hmain,hbound,hfinite]

/-- The remaining conversion to H_N is precisely the ordinary prime
prefix ratio. There is no hidden density or enhancement in this identity. -/
theorem primeScale_eq_ratio_mul_H {N : ℕ} (hN : (1 : ℝ) < N) :
    primeScale N = (piMass N * Real.log (N : ℝ) / (N : ℝ)) * singularNormalization N := by
  unfold primeScale singularNormalization
  field_simp [(zero_lt_one.trans hN).ne', (Real.log_pos hN).ne']
  <;> ring

/-- Exact saved-density restriction, not subtraction of a bound for a
removed true count. The original policy is identical on both sums. -/
theorem rawMain_eq_whole_sub_deleted (N : ℕ) (eta : ℝ) (policy : Policy) :
    rawMain N eta policy =
      (∑ p ∈ currentChenUpsilon6OrdinarySelector N eta,
        piMass N / (Nat.totient (p.1*p.2) : ℝ) * rawDensity N (policy p)) -
      ∑ p ∈ (currentChenUpsilon6OrdinarySelector N eta).filter (actualMask N),
        piMass N / (Nat.totient (p.1*p.2) : ℝ) * rawDensity N (policy p) := by
  have h := Finset.sum_filter_add_sum_filter_not
    (currentChenUpsilon6OrdinarySelector N eta) (actualMask N)
    (fun p => piMass N / (Nat.totient (p.1*p.2) : ℝ) * rawDensity N (policy p))
  change _ + rawMain N eta policy = _ at h
  linarith only [h]

end
end ImbalancedChen.P5OriginalRetainedU6RawSourcePayment