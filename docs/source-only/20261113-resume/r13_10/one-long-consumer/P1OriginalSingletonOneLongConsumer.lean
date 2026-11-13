import ImbalancedChen.P1OriginalSingletonOneLongGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.

Final consumer for the ACTUAL final-singleton one-long sub-sum, in the
physical and free whole-modulus channels. The finite E5 and its B1/B2,
primitive density and divisor-moment suppliers are reused. No bound on
E5, the profile error, total restoration or a uniform threshold is an
input. Medium, two-long, comparisonMiddle, savingMiddle and whole PP are
outside this theorem.
-/
namespace ImbalancedChen.P1OriginalSingletonOneLongConsumer
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open P4BOriginalCollisionWords (Params)
open P4AHeldTaggedCompilerSupport (J0)
open P4BOriginalCollisionTensor (products free)
open P1OriginalSingletonMiddleRank (live)
open P5Z.ActualRoughHeathBrownWords P5Z.HBRightClosedDyadicRoles
open P5Z.ActualHBDyadicProductWindow P5Z.ActualHBDyadicOccurrenceFamily
open P5Z.ActualHBMediumBranchPartition P5Z.OrderedFactorTupleRectangleReindex
open P5Z.ActualLowerNormalizedAtlasOccurrence P5Z.PerGroupIntegerHBAtlasPushforward
open P5Z.ExactOriginalSmoothDyadicPartition P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.IndependentPrimeSourceWordDictionary
open P1OriginalSingletonOneLongCoefficients P1OriginalSingletonOneLongRectangle
open P1OriginalSingletonOneLongFibres P1OriginalSingletonOneLongProfile
open P1OriginalSingletonOneLongFiniteE5 P1OriginalSingletonOneLongRestoration
open P1OriginalSingletonOneLongGeometry
open OriginalOneLongModulusMeans OriginalOneLongSupportAbsorption
open OriginalOneLongExplicitBrunRates OriginalOneLongMertensChartHarmonic

def sourceChannel (kap : ℝ) (N K : ℕ) (zeta : ℝ) (Q : Finset ℕ) (rho : ℕ→ℂ) : ℂ :=
  ∑ js∈chartBank (2*N) 1,
    oneLongAtlas (P5CanonicalTentNarrowSingletonTransfer.actualLicence kap 6 N)
      K (2*N) N kap (originalMediumLow zeta js) (originalMediumHigh zeta js) Q rho js

theorem sourceChannel_singletons (kap : ℝ) (hk : kap<1) (N K : ℕ) (zeta : ℝ)
    (Q : Finset ℕ) (rho : ℕ→ℂ) :
    sourceChannel kap N K zeta Q rho=
      ∑ cj∈Finset.range (cutoffIndex (2*N)+1),
        occurrenceChart kap 6 N cj K kap (originalMediumLow zeta [cj])
          (originalMediumHigh zeta [cj]) Q rho := by
  unfold sourceChannel chartBank
  rw [words_sum_cons]
  simp only [words,Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro cj hcj
  exact source_to_actual_rectangles kap hk 6 N cj K kap _ _ Q rho

theorem wordKernel_live (P : Params) (ps : List ℕ) :
    wordKernel (live P) (fun q=>(P.rho q : ℂ)) P.N ps=
      wordKernel P.S (fun q=>(P.rho q : ℂ)) P.N ps :=
  physical_read_live P (fun q=>PrimeProducts.MellinInsertion20261028.residueKernel q P.N ps.prod)

theorem physicalChannel_dictionary (P : Params) (kap : ℝ) (K : ℕ) (zeta : ℝ) :
    physicalChannel P kap K zeta=
      sourceChannel kap P.N K zeta (live P) (fun q=>(P.rho q : ℂ)) := by
  unfold physicalChannel sourceChannel oneLongAtlas oneLongValue sourceTest
  simp_rw [wordKernel_live]

theorem freeChannel_dictionary (P : Params) (kap : ℝ) (K : ℕ) (zeta : ℝ) :
    freeChannel P kap K zeta=
      sourceChannel kap P.N K zeta (products P) (fun q=>(free P q : ℂ)) := rfl

def graphHeight (N : ℕ) : ℝ := (Nat.log2 (8*N)+4 : ℕ)
def graphConstant : ℝ := 4+1/Real.log 2
def heightConstant : ℝ := 2+Real.log 16
def brunGapAccuracy (A : ℕ) : ℕ := A+100
def supportReserve : ℝ := 1/10

theorem small_zeta_margin {zeta : ℝ} (hzeta : 0<zeta) (hsmall : zeta≤1/20000) :
    15*zeta+599/1000+supportReserve<1 := by
  dsimp [supportReserve]
  nlinarith

theorem modulusCap_le_power (N : ℕ) :
    (modulusCap N : ℝ)≤(N : ℝ)^(599/1000 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem modulusCap_le_target (N : ℕ) (hN : 1≤N) : modulusCap N≤N := by
  have hh : (modulusCap N : ℝ)≤(N : ℝ) := by
    apply (modulusCap_le_power N).trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ)≤N by exact_mod_cast hN) (by norm_num : (599/1000 : ℝ)≤1)
  exact_mod_cast hh

theorem nat_log2_mono {m n : ℕ} (hn : n≠0) (h : m≤n) : Nat.log2 m≤Nat.log2 n := by
  by_cases hm : m=0
  · simp [hm]
  exact (Nat.le_log2 hn).mpr ((Nat.log2_self_le hm).trans h)

theorem graphHeight_nonneg (N : ℕ) : 0≤graphHeight N := Nat.cast_nonneg _

theorem graphConstant_one_le : 1≤graphConstant := by
  have hp := Real.log_pos (by norm_num : (1 : ℝ)<2)
  dsimp [graphConstant]
  have hh := one_div_pos.mpr hp
  linarith

theorem heightConstant_one_le : 1≤heightConstant := by
  have hp := Real.log_nonneg (by norm_num : (1 : ℝ)≤16)
  dsimp [heightConstant]
  linarith

theorem graphHeight_le_profileHeight (N : ℕ) (hN : 0<N) :
    graphHeight N≤graphConstant*profileHeight N := by
  let d := Nat.log2 (8*N)
  have hp : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h8 : 8*N≠0 := by omega
  have hpow : (2 : ℝ)^d≤8*(N : ℝ) := by exact_mod_cast Nat.log2_self_le h8
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) d) hpow
  rw [Real.log_pow] at hlog
  have hl : Real.log (8*(N : ℝ))≤Real.log (8*(N : ℝ)+8) :=
    Real.log_le_log (by positivity) (by linarith)
  have hd : (d : ℝ)≤profileHeight N/Real.log 2 :=
    (le_div_iff₀ hp).mpr (by dsimp [profileHeight]; linarith)
  have hL := height_one_le N
  simp only [graphHeight,Nat.cast_add,Nat.cast_ofNat]
  change (d : ℝ)+4≤graphConstant*profileHeight N
  calc
    _≤profileHeight N/Real.log 2+4*profileHeight N := by linarith
    _=_ := by dsimp [graphConstant]; field_simp [hp.ne']; ring

theorem logBudget_le_two_height (N D : ℕ) (hD : 1≤D) (hDN : D≤N) :
    logBudget D≤2*profileHeight N := by
  have hDp : (0 : ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have hlog : Real.log (D : ℝ)≤Real.log (8*(N : ℝ)+8) :=
    Real.log_le_log hDp (by exact_mod_cast (hDN.trans (by omega : N≤8*N+8)))
  have hL := height_one_le N
  dsimp [logBudget,profileHeight] at *
  linarith

theorem eventually_height_le_log :
    ∀ᶠ N : ℕ in atTop,profileHeight N≤heightConstant*Real.log (N : ℝ) := by
  filter_upwards [eventually_one_le_nat_log,eventually_ge_atTop (1 : ℕ)] with N hlog hN
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hu : 8*(N : ℝ)+8≤16*(N : ℝ) := by exact_mod_cast (by omega : 8*N+8≤16*N)
  have hh := Real.log_le_log (by positivity : (0 : ℝ)<8*(N : ℝ)+8) hu
  rw [Real.log_mul (by norm_num : (16 : ℝ)≠0) hNp.ne'] at hh
  have h16 := Real.log_nonneg (by norm_num : (1 : ℝ)≤16)
  have hx := mul_nonneg (show 0≤1+Real.log (16 : ℝ) by linarith) (sub_nonneg.mpr hlog)
  dsimp [profileHeight,heightConstant]
  nlinarith

theorem chart_block_cardinality (N cj j : ℕ) (hN : 0<N)
    (hcj : cj∈Finset.range (cutoffIndex (2*N)+1)) (hj : j<3) :
    ((blockWords (hbCap cj) (2*(j+1))).card : ℝ)≤graphHeight N^6 := by
  let d := Nat.log2 (2*N)
  have h2N : 2*N≠0 := by omega
  have h8N : 8*N≠0 := by omega
  have hc : cj≤d+1 := by
    have hh := Finset.mem_range.mp hcj
    dsimp [cutoffIndex,d] at *
    omega
  have hp : hbCap cj≤8*N := by
    calc
      _=2^(cj+1) := rfl
      _≤2^(d+2) := pow_le_pow_right₀ (by norm_num : (1 : ℕ)≤2) (by omega)
      _=4*2^d := by rw [pow_add]; norm_num; ring
      _≤8*N := by have hh := Nat.log2_self_le h2N; dsimp [d] at *; omega
  have hb : Nat.log2 (hbCap cj-1)+2≤Nat.log2 (8*N)+4 := by
    have hh := nat_log2_mono h8N ((Nat.sub_le _ 1).trans hp)
    omega
  have hbase : 1≤Nat.log2 (8*N)+4 := by omega
  have hcard : (blockWords (hbCap cj) (2*(j+1))).card≤(Nat.log2 (8*N)+4)^6 := by
    rw [blockWords_card]
    exact (pow_le_pow_left₀ (Nat.zero_le _) hb _).trans
      (pow_le_pow_right₀ hbase (by omega : 2*(j+1)≤6))
  exact_mod_cast hcard

theorem chart_count (N : ℕ) (hN : 0<N) :
    ((Finset.range (cutoffIndex (2*N)+1)).card : ℝ)≤graphHeight N := by
  have hh := nat_log2_mono (by omega : 8*N≠0) (by omega : 2*N≤8*N)
  exact_mod_cast (show (Finset.range (cutoffIndex (2*N)+1)).card≤Nat.log2 (8*N)+4 by
    simp only [Finset.card_range,cutoffIndex]; omega)

theorem original_HB_scalar_bound (j : ℕ) (hj : j<3) :
    ‖P5Z.SmoothChartHBDyadicPartition.scalar j‖≤3 := by
  have h : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases h with rfl | rfl | rfl <;>
    norm_num [P5Z.SmoothChartHBDyadicPartition.scalar]

def Y (N : ℕ) : ℝ := support canonicalEnvelope N
def epsilon (N : ℕ) : ℝ := gap (fun n=>2*L2 n) N

theorem actual_support_subpower : SubpowerSupport Y :=
  support_is_subpower canonicalEnvelope
    (eventually_canonical_envelope_bounds.mono (fun N h=>h.1))
    (eventually_canonical_envelope_bounds.mono (fun N h=>h.2.2))

theorem actual_gap_superlog : SuperLogGap epsilon := by
  apply gap_is_superlog
  filter_upwards [tendsto_L2.eventually (eventually_ge_atTop (0 : ℝ))] with N hN
  exact ⟨by positivity,le_rfl⟩

/-- The support reserve is a genuine small power. In contrast the gap
is paid at the explicitly preselected A+100 logarithmic order. -/
theorem selected_Brun_rates (A : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,0≤Y N ∧ Y N≤(N : ℝ)^supportReserve ∧
      epsilon N*Real.log (N : ℝ)^(brunGapAccuracy A)≤eta := by
  filter_upwards [actual_support_subpower supportReserve (by norm_num [supportReserve]),
    actual_gap_superlog (brunGapAccuracy A) eta heta] with N hY he
  exact ⟨hY.1,hY.2,he⟩

def rowBudget (N : ℕ) (Rrho zeta : ℝ) : ℝ :=
  (2*profileConstant*Rrho)*profileHeight N^78*logBudget (modulusCap N)^4*
    (10*Y N*(modulusCap N : ℝ)*(4*(N : ℝ))^(15*zeta)+4*epsilon N*(N : ℝ))

theorem rowBudget_nonneg (N : ℕ) (Rrho zeta : ℝ) (hR : 0≤Rrho)
    (hY : 0≤Y N) (he : 0≤epsilon N) : 0≤rowBudget N Rrho zeta := by
  have hC := profileConstant_nonneg
  have hL := zero_le_one.trans (height_one_le N)
  unfold rowBudget
  positivity

/-- This has no per-chart, per-block or per-short-vector N0 premise.
All numerical prerequisites come from the original source geometry and
the proved Mertens/canonical-envelope suppliers before Q/rho vary. -/
theorem eventually_actual_row_finite
    (kap zeta : ℝ) (hk : kap<1) (hzeta : 0<zeta) (K : ℕ) (Rrho : ℝ) (hR : 0≤Rrho) :
    ∀ᶠ N : ℕ in atTop,∀ (cj j : ℕ) (bs : List Block),j<3 →
      bs∈blockWords (hbCap cj) (2*(j+1)) →
      OneLong (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs →
      ∀ (Q : Finset ℕ) (rho : ℕ→ℂ),Q⊆Finset.Ioc 0 (modulusCap N) →
        (∀ q∈Q,N.Coprime q) → (∀ q∈Q,‖rho q‖≤Rrho) →
        ‖P1OriginalSingletonOneLongRectangle.occurrenceAtom kap 6 N cj K kap j bs Q rho‖≤
          rowBudget N Rrho zeta := by
  filter_upwards [eventually_original_cutoff_and_long_role kap zeta hk hzeta K,
    eventually_canonical_chart_primitives,eventually_ge_atTop (2 : ℕ)]
    with N hsource hprimitives hN cj j bs hj hbs hgate Q rho hQ hcop hrho
  obtain ⟨hEnv,hEnvLog,hH0,hH⟩ := hprimitives
  have hNp : 0<N := by omega
  have hD : 1≤modulusCap N := modulusCap_pos N (by omega)
  have hz := original_cutoff_nonneg K cj
  have hY : 0≤Y N := by dsimp [Y,support]; positivity
  have he : 0≤epsilon N := by dsimp [epsilon,gap]; positivity
  have hbudget0 := rowBudget_nonneg N Rrho zeta hR hY he
  let bsV := blockVector (2*(j+1)) bs
  by_cases hactive : ∃ n∈rectangle bsV,integerProfile kap 6 N cj kap n≠0
  · have hlen := (blockWords_spec _ _ _ hbs).1
    obtain ⟨a,haLong,hshort⟩ := selected_long_position bs hlen _ _ hgate
    have hshortSize := actual_short_size_bound kap hk N cj kap zeta hzeta j hj bs hlen hactive a hshort
    have hsourceN := hsource cj (2*(j+1)) bsV hactive
    have hprimeH := hH (Part3.RoughSlotCharacterLift20261026b.smallPrimes (beforeHBCutoff K [cj]))
      (fun p hp=>Part3.RoughSlotCharacterLift20261026b.smallPrimes_prime hp)
      (fun p hp=>((Part3.RoughSlotCharacterLift20261026b.mem_smallPrimes hz).mp hp).2.trans hsourceN.1)
    have hR1 : 1≤R cj := by dsimp [R]; exact one_le_pow₀ (by norm_num) _
    have hhigh : 1≤originalMediumHigh zeta [cj] := by
      rw [(original_singleton_thresholds zeta cj).2]
      exact Real.one_le_rpow hR1 (by positivity)
    have hmu : hbCutoff cj<(lower (bsV a) : ℝ) := by
      have hh := hsourceN.2
      rw [←(original_singleton_thresholds zeta cj).2] at hh
      exact hh.trans haLong
    cases hba : bsV a with
    | unit =>
      have : originalMediumHigh zeta [cj]<(1 : ℝ) := by simpa only [hba,lower] using haLong
      linarith
    | dyadic k =>
      have hgood (hr : rowRoles j a=.one ∨ rowRoles j a=.logarithm) :
          ‖P1OriginalSingletonOneLongRectangle.occurrenceAtom kap 6 N cj K kap j bs Q rho‖≤
            rowBudget N Rrho zeta := by
        rw [actual_occurrenceAtom_dictionary]
        have hf := actual_rectangle_finite kap hk N cj K (modulusCap N) ⌊L2 N^2⌋₊ kap
          j hj bsV a k hba hactive Q rho Rrho (canonicalEnvelope N) (2*L2 N)
          hNp hz hEnv hsourceN.1 hprimeH hD hQ hcop hR hrho hr
        have hs := mul_le_mul_of_nonneg_left hshortSize
          (show 0≤10*Y N*(modulusCap N : ℝ) by positivity)
        have hfactor : 0≤(2*profileConstant*Rrho)*profileHeight N^78*
            logBudget (modulusCap N)^4 := by
          have hC := profileConstant_nonneg
          have hL := zero_le_one.trans (height_one_le N)
          positivity
        apply hf.trans
        change _≤rowBudget N Rrho zeta
        unfold rowBudget
        simp only [Y,epsilon,support,gap,order] at hs ⊢
        exact mul_le_mul_of_nonneg_left (by nlinarith [hs]) hfactor
      cases hrole : rowRoles j a with
      | mobius =>
        have hzrow : rectangleValue kap 6 N cj K kap j bsV Q rho=0 := by
          apply Finset.sum_eq_zero
          intro n hn
          have hh := long_mobius_rectangle_zero (beforeHBCutoff K [cj]) (hbCutoff cj)
            j bsV a hrole hmu n hn
          simp only [rectangleValue,hh,zero_mul]
        rw [actual_occurrenceAtom_dictionary,hzrow,norm_zero]
        exact hbudget0
      | one => exact hgood (Or.inl hrole)
      | logarithm => exact hgood (Or.inr hrole)
  · rw [actual_occurrenceAtom_dictionary,rectangleValue_zero_of_not_active kap 6 N cj K kap j bsV Q rho hactive,
      norm_zero]
    exact hbudget0

/-- All three original HB scalars, every block word and the full original
singleton chart bank are counted explicitly. The seventh power is the
actual logarithmic chart count, not an assumed restoration licence. -/
theorem eventually_sourceChannel_finite
    (kap zeta : ℝ) (hk : kap<1) (hzeta : 0<zeta) (K : ℕ) (Rrho : ℝ) (hR : 0≤Rrho) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ→ℂ),
      Q⊆Finset.Ioc 0 (modulusCap N) → (∀ q∈Q,N.Coprime q) →
      (∀ q∈Q,‖rho q‖≤Rrho) →
      ‖sourceChannel kap N K zeta Q rho‖≤9*graphHeight N^7*rowBudget N Rrho zeta := by
  filter_upwards [eventually_actual_row_finite kap zeta hk hzeta K Rrho hR,
    eventually_canonical_chart_primitives,eventually_ge_atTop (2 : ℕ)]
    with N hrow hprimitives hN Q rho hQ hcop hrho
  have hNp : 0<N := by omega
  have hG := graphHeight_nonneg N
  have hL := zero_le_one.trans (height_one_le N)
  have hY : 0≤Y N := by dsimp [Y,support]; have := hprimitives.1; positivity
  have he : 0≤epsilon N := by dsimp [epsilon,gap]; have := hprimitives.2.2.1; positivity
  have hT := rowBudget_nonneg N Rrho zeta hR hY he
  have hchart (cj : ℕ) (hcj : cj∈Finset.range (cutoffIndex (2*N)+1)) :
      ‖occurrenceChart kap 6 N cj K kap (originalMediumLow zeta [cj])
        (originalMediumHigh zeta [cj]) Q rho‖≤9*graphHeight N^6*rowBudget N Rrho zeta := by
    unfold occurrenceChart
    apply (norm_sum_le _ _).trans
    have hterm (j : ℕ) (hj : j∈Finset.range 3) :
        ‖P5Z.SmoothChartHBDyadicPartition.scalar j*
          ∑ bs∈blockWords (hbCap cj) (2*(j+1)),
            if OneLong (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs then
              P1OriginalSingletonOneLongRectangle.occurrenceAtom kap 6 N cj K kap j bs Q rho else 0‖≤
          3*graphHeight N^6*rowBudget N Rrho zeta := by
      have hj3 := Finset.mem_range.mp hj
      have hb (bs : List Block) (hbs : bs∈blockWords (hbCap cj) (2*(j+1))) :
          ‖if OneLong (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs then
            P1OriginalSingletonOneLongRectangle.occurrenceAtom kap 6 N cj K kap j bs Q rho else 0‖≤
          rowBudget N Rrho zeta := by
        by_cases hg : OneLong (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs
        · simpa only [if_pos hg] using hrow cj j bs hj3 hbs hg Q rho hQ hcop hrho
        · simpa only [if_neg hg,norm_zero] using hT
      have hins : ‖∑ bs∈blockWords (hbCap cj) (2*(j+1)),
          if OneLong (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs then
            P1OriginalSingletonOneLongRectangle.occurrenceAtom kap 6 N cj K kap j bs Q rho else 0‖≤
          graphHeight N^6*rowBudget N Rrho zeta := by
        apply (norm_sum_le _ _).trans
        apply (Finset.sum_le_sum hb).trans
        simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right
          (chart_block_cardinality N cj j hNp hcj hj3) hT
      rw [norm_mul]
      have hh := mul_le_mul (original_HB_scalar_bound j hj3) hins (norm_nonneg _) (by norm_num)
      simpa only [mul_assoc] using hh
    calc
      _≤∑ _j∈Finset.range 3,3*graphHeight N^6*rowBudget N Rrho zeta :=
        Finset.sum_le_sum hterm
      _=9*graphHeight N^6*rowBudget N Rrho zeta := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        ring
  rw [sourceChannel_singletons kap hk]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hchart).trans
  calc
    _=((Finset.range (cutoffIndex (2*N)+1)).card : ℝ)*
        (9*graphHeight N^6*rowBudget N Rrho zeta) := by
          simp only [Finset.sum_const,nsmul_eq_mul]
    _≤graphHeight N*(9*graphHeight N^6*rowBudget N Rrho zeta) :=
      mul_le_mul_of_nonneg_right (chart_count N hNp) (by positivity)
    _=9*graphHeight N^7*rowBudget N Rrho zeta := by ring

/-- The exact finite restoration is absorbed using fixed logarithmic
accuracy 100. No logarithmic factor is replaced by N^eta. Only the genuine
Brun support uses the fixed positive power reserve. -/
theorem eventually_full_restoration_payment
    (zeta Rrho : ℝ) (hzeta : 0<zeta) (hsmall : zeta≤1/20000) (hR : 0≤Rrho)
    (A : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,9*graphHeight N^7*rowBudget N Rrho zeta≤
      eta*(N : ℝ)/Real.log (N : ℝ)^A := by
  let theta : ℝ := 15*zeta+599/1000
  let Cz : ℝ := (4 : ℝ)^(15*zeta)
  let C0 : ℝ := 288*profileConstant*Rrho*graphConstant^7
  let C : ℝ := 14*C0*Cz*heightConstant^100
  have hCprofile := profileConstant_nonneg
  have hGconst := graphConstant_one_le
  have hHconst := heightConstant_one_le
  have hGconst0 := zero_le_one.trans hGconst
  have hHconst0 := zero_le_one.trans hHconst
  have hCz : 1≤Cz := Real.one_le_rpow (by norm_num) (by positivity)
  have hC0 : 0≤C0 := by dsimp [C0]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have htheta : theta<1 := by
    have hh := small_zeta_margin hzeta hsmall
    dsimp [theta,supportReserve] at *
    linarith
  have hbudget := eventually_one_long_E5_budget Y epsilon C theta 100 A
    hC htheta actual_support_subpower actual_gap_superlog eta heta
  filter_upwards [hbudget,eventually_height_le_log,eventually_one_le_nat_log,
    eventually_canonical_chart_primitives,eventually_ge_atTop (2 : ℕ)]
    with N hpay hheight hlog hprimitives hN
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL1 := height_one_le N
  have hL0 := zero_le_one.trans hL1
  have hG := graphHeight_nonneg N
  have hY : 0≤Y N := by dsimp [Y,support]; have := hprimitives.1; positivity
  have he : 0≤epsilon N := by dsimp [epsilon,gap]; have := hprimitives.2.2.1; positivity
  have hD : 1≤modulusCap N := modulusCap_pos N (by omega)
  have hDlog := logBudget_le_two_height N (modulusCap N) hD (modulusCap_le_target N (by omega))
  have hgraph := graphHeight_le_profileHeight N (by omega)
  have hMD : (N : ℝ)^(15*zeta)*(modulusCap N : ℝ)≤(N : ℝ)^theta := by
    calc
      _≤(N : ℝ)^(15*zeta)*(N : ℝ)^(599/1000 : ℝ) :=
        mul_le_mul_of_nonneg_left (modulusCap_le_power N) (Real.rpow_nonneg hNp.le _)
      _=_ := by dsimp [theta]; rw [Real.rpow_add hNp]
  have hlog0 : 0≤Real.log (N : ℝ) := zero_le_one.trans hlog
  have hlarge : 1≤heightConstant*Real.log (N : ℝ) := by
    have hh := mul_le_mul hHconst hlog (by norm_num : (0 : ℝ)≤1) (by positivity)
    simpa only [one_mul] using hh
  have hheightPower : profileHeight N^89≤heightConstant^100*Real.log (N : ℝ)^100 := by
    calc
      _≤(heightConstant*Real.log (N : ℝ))^89 := pow_le_pow_left₀ hL0 hheight _
      _≤(heightConstant*Real.log (N : ℝ))^100 := pow_le_pow_right₀ hlarge (by norm_num)
      _=_ := mul_pow _ _ _
  have hscale : (4*(N : ℝ))^(15*zeta)=Cz*(N : ℝ)^(15*zeta) :=
    Real.mul_rpow (by norm_num) hNp.le
  let x := (N : ℝ)^(15*zeta)*Y N*(modulusCap N : ℝ)
  let y := (N : ℝ)*epsilon N
  have hx : 0≤x := by dsimp [x]; positivity
  have hy : 0≤y := by dsimp [y]; positivity
  have hbracket :
      10*Y N*(modulusCap N : ℝ)*(4*(N : ℝ))^(15*zeta)+4*epsilon N*(N : ℝ)≤
        14*Cz*(x+y) := by
    rw [hscale]
    calc
      _=10*Cz*x+4*y := by dsimp [x,y]; ring
      _≤14*Cz*(x+y) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hCz) hy,
          mul_nonneg (zero_le_one.trans hCz) hx]
  have hfinite : 9*graphHeight N^7*rowBudget N Rrho zeta≤
      C0*profileHeight N^89*
        (10*Y N*(modulusCap N : ℝ)*(4*(N : ℝ))^(15*zeta)+4*epsilon N*(N : ℝ)) := by
    unfold rowBudget
    calc
      _≤9*(graphConstant*profileHeight N)^7*
        ((2*profileConstant*Rrho)*profileHeight N^78*(2*profileHeight N)^4*
          (10*Y N*(modulusCap N : ℝ)*(4*(N : ℝ))^(15*zeta)+4*epsilon N*(N : ℝ))) := by
            gcongr
      _=_ := by dsimp [C0]; ring
  calc
    _≤C0*profileHeight N^89*(14*Cz*(x+y)) := hfinite.trans
      (mul_le_mul_of_nonneg_left hbracket (by positivity))
    _≤C0*(heightConstant^100*Real.log (N : ℝ)^100)*(14*Cz*(x+y)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hheightPower hC0) (by positivity)
    _=C*((N : ℝ)*epsilon N+(N : ℝ)^(15*zeta)*Y N*(modulusCap N : ℝ))*
        Real.log (N : ℝ)^100 := by dsimp [C,x,y]; ring
    _≤_ := hpay _ _ hMD

theorem eventually_actual_sourceChannel
    (kap zeta : ℝ) (hk : kap<1) (hzeta : 0<zeta) (hsmall : zeta≤1/20000)
    (K : ℕ) (Rrho : ℝ) (hR : 0≤Rrho) (A : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ→ℂ),
      Q⊆Finset.Ioc 0 (modulusCap N) → (∀ q∈Q,N.Coprime q) →
      (∀ q∈Q,‖rho q‖≤Rrho) →
      ‖sourceChannel kap N K zeta Q rho‖≤eta*(N : ℝ)/Real.log (N : ℝ)^A := by
  filter_upwards [eventually_sourceChannel_finite kap zeta hk hzeta K Rrho hR,
    eventually_full_restoration_payment zeta Rrho hzeta hsmall hR A eta heta]
    with N hfinite hpay Q rho hQ hcop hrho
  exact (hfinite Q rho hQ hcop hrho).trans hpay

/-- The requested uniform terminal, for BOTH original whole-modulus
channels and the SAME final-singleton one-long source. The factorial is
fixed by omega before N0. Every hypothesis is an original parameter
condition; no E5, profile norm, restoration mass or threshold supplier
is assumed. The bound with constant one is obtained by increasing the
constructed common N0 and is stronger than the stated O_A conclusion. -/
theorem original_one_long_two_channels
    (kap omega zeta : ℝ) (hkap0 : 0<kap) (hkap1 : kap<1) (homega : 0<omega)
    (hzeta : 0<zeta) (hsmall : zeta≤1/20000) (K : ℕ) (hK : 2≤K) (A : ℕ) :
    ∃ N0 : ℕ,2≤N0 ∧ ∀ P : Params,N0≤P.N → P.omega=omega →
      0≤P.e → P.ell<1/1000 → P.ell+P.T*(J0 omega : ℝ)<1/1000 →
      ‖physicalChannel P kap K zeta‖≤(P.N : ℝ)/Real.log (P.N : ℝ)^A ∧
        ‖freeChannel P kap K zeta‖≤(P.N : ℝ)/Real.log (P.N : ℝ)^A := by
  let Rrho : ℝ := ((J0 omega).factorial : ℝ)
  have hR : 0≤Rrho := Nat.cast_nonneg _
  have hR1 : 1≤Rrho := by
    exact_mod_cast (show 1≤(J0 omega).factorial from Nat.factorial_pos _)
  have hevent := eventually_actual_sourceChannel kap zeta hkap1 hzeta hsmall K Rrho hR A 1 (by norm_num)
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp (hevent.and (eventually_ge_atTop (2 : ℕ)))
  refine ⟨max 2 N1,le_max_left _ _,?_⟩
  intro P hN hOm he hell ht
  obtain ⟨hbound,hN2⟩ := hN1 P.N ((le_max_right _ _).trans hN)
  have hPN : 1<P.N := by omega
  have hPOm : 0<P.omega := by simpa only [hOm] using homega
  have hPt : P.ell+P.T*(J0 P.omega : ℝ)<1/1000 := by simpa only [hOm] using ht
  have hphysical := physical_data P hPN he hPOm hell hPt
  have hfree := free_data P hPN he hPOm hPt
  constructor
  · rw [physicalChannel_dictionary]
    have hh := hbound (live P) (fun q=>(P.rho q : ℂ)) hphysical.1 hphysical.2.1
      (fun q hq=>(hphysical.2.2 q hq).trans hR1)
    simpa only [one_mul] using hh
  · rw [freeChannel_dictionary]
    have hh := hbound (products P) (fun q=>(free P q : ℂ)) hfree.1 hfree.2.1
      (fun q hq=>by simpa only [hOm,Rrho] using hfree.2.2 q hq)
    simpa only [one_mul] using hh

end
end ImbalancedChen.P1OriginalSingletonOneLongConsumer
