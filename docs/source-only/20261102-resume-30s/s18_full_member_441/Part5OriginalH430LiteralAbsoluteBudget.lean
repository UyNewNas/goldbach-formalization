import ImbalancedChen.Part5OriginalH430CoefficientwiseBank

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The Pi-coordinate coefficients are identified atom by atom with R16's
literal scalar/pair coefficients. Therefore the absolute payment is for
R16's actual absoluteCoefficientError, not merely an equivalent signed
profile. The base discrepancy stays literal and is not assumed small.
The zero-Theta theorem is absolute and involves no division.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralAbsoluteBudget

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalAffineProfilePassage
open P2OriginalOldProfilePrimeLimits P2OriginalPhysicalOldProfileMass
open P2OriginalBankOldProfilePassage P2OriginalChildPhysicalNormalization
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430TrueAtomLimits Part5OriginalH430CoefficientwiseBank
open Part5OriginalH430ImmutableBankProfiles Part5OriginalH430LiteralBankBudget

/-- Half-open endpoint differences are removed only inside the real
integral. The finite prime coefficient retained every original endpoint. -/
theorem singleAtomIntegral_eq_literal {lo hi : ℝ}
    (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2) (s0 : ℝ) (b : FloorAtom) :
    singleAtomIntegral lo hi s0 b = singletonIntegralAtom lo hi s0 b := by
  have hDE := sandwich_ae singleForms (singleBounds lo hi) singleForms_ne
    (singleHalf_sandwich lo hi)
  rw [← single_as_affine] at hDE
  have hset : (singleHalf lo hi ∩ tablePullback true (singleRho s0) b) =ᵐ[volume]
      (singleDomain lo hi ∩ tablePullback true (singleRho s0) b) := by
    filter_upwards [hDE] with x hx
    exact and_congr_left (fun _ => hx)
  have hm : MeasurableSet (singleDomain lo hi) := by
    rw [single_as_affine]
    exact measurableSet_primeAffineGateRegion _ _
  have hpb : MeasurableSet (tablePullback true (singleRho s0) b) :=
    measurableSet_tablePullback true
      ((measurable_singletonProfile s0).comp (measurable_pi_apply (0 : Fin 1))) b
  have hscalar := measurableSet_tablePullback true (measurable_singletonProfile s0) b
  calc
    singleAtomIntegral lo hi s0 b = ∫ x in singleDomain lo hi ∩ tablePullback true (singleRho s0) b,
        residualSingle x * ∏ i, 1/x i := setIntegral_congr_set hset
    _ = ∫ x in singleDomain lo hi,
        (tablePullback true (singleRho s0) b).indicator
          (fun x => residualSingle x * ∏ i, 1/x i) x := (setIntegral_indicator hpb).symm
    _ = ∫ x in singleDomain lo hi,
        (tablePullback true (singletonProfile s0) b).indicator singletonKernel (x 0) := by
      apply setIntegral_congr_fun hm
      intro x hx
      by_cases hb : x ∈ tablePullback true (singleRho s0) b
      · have hb' : x 0 ∈ tablePullback true (singletonProfile s0) b := hb
        rw [indicator_of_mem hb,indicator_of_mem hb',single_kernel hhi hx,
          singletonKernel_eq_raw ⟨hlo.trans hx.1.le,hx.2.le.trans hhi⟩]
      · have hb' : x 0 ∉ tablePullback true (singletonProfile s0) b := hb
        rw [indicator_of_notMem hb,indicator_of_notMem hb']
    _ = ∫ u in Ioo lo hi,
        (tablePullback true (singletonProfile s0) b).indicator singletonKernel u :=
      single_integral_coordinates lo hi _
    _ = singletonIntegralAtom lo hi s0 b := setIntegral_indicator hscalar

theorem pairAtomIntegral_eq_literal {p : W2Parameters} (hp : W2Geometry p)
    (k : Fin 4) (b : FloorAtom) : pairAtomIntegral p k b = pairIntegralAtom p k b := by
  have hDE := sandwich_ae (pairForms k) (pairBounds p k) (pairForms_ne k)
    (pairHalf_sandwich p k)
  rw [← pair_as_affine] at hDE
  have hset : (pairHalf p k ∩ tablePullback false (pairProfile p k) b) =ᵐ[volume]
      (W2PairDomain p k ∩ tablePullback false (pairProfile p k) b) := by
    filter_upwards [hDE] with x hx
    exact and_congr_left (fun _ => hx)
  calc
    pairAtomIntegral p k b = ∫ x in W2PairDomain p k ∩ tablePullback false (pairProfile p k) b,
        residualPair x * ∏ i, 1/x i := setIntegral_congr_set hset
    _ = pairIntegralAtom p k b := by
      apply setIntegral_congr_fun ((measurableSet_W2PairDomain p k).inter
        (measurableSet_tablePullback false (measurable_pairProfile p k) b))
      intro x hx
      rw [pair_kernel hp k hx.1,pairKernel_eq_raw
        (W2PairDomain_geometry hp k hx.1).1 (W2PairDomain_geometry hp k hx.1).2]

theorem integralRow_eq_literal (a : Original106Action) (b : RowAtom) :
    integralRow a b = idealRow a b := by
  rcases a with ⟨i,j⟩ | j
  · cases b with
    | inl b => rfl
    | inr b =>
        change singleAtomIntegral _ _ _ b/2 = singletonIntegralAtom _ _ _ b/2
        rw [singleAtomIntegral_eq_literal (W1_endpoints i j).1 (W1_endpoints i j).2.1]
  · have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
    cases b with
    | inl b => simp only [integralRow,idealRow,pairAtomIntegral_eq_literal hp]
    | inr b =>
        change (∑ k : Fin 3, singleAtomIntegral _ _ _ b)/5 =
          (∑ k : Fin 3, singletonIntegralAtom _ _ _ b)/5
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact singleAtomIntegral_eq_literal hp.1 (W2_singleton_top hp k) _ b

theorem absoluteBankError_eq_literal {ι : Type*} (N : ℕ) (Q : ℝ) (S : Finset ι)
    (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ)
    (oldH oldh : Fin 200 → ℤ) (a : Original106Action) :
    absoluteBankError N Q S L d sigma oldH oldh a =
      absoluteCoefficientError N Q S L d sigma oldH oldh a := by
  simp only [absoluteBankError,absoluteCoefficientError,integralRow_eq_literal]

theorem literal_absoluteCoefficientError_nonneg {ι : Type*}
    (N : ℕ) (Q : ℝ) (S : Finset ι) (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ)
    (oldH oldh : Fin 200 → ℤ) (a : Original106Action) :
    0 ≤ absoluteCoefficientError N Q S L d sigma oldH oldh a :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Literal coefficientwise absolute error at all 430 immutable old
arrays, including positive marked families with zero total Theta. -/
theorem immutable430_literal_absoluteCoefficientError {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ g : Fin 430, ∀ Q : ℝ,
      ∀ {ι : Type*} (S : Finset ι) (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ),
      (∀ i ∈ S, L i ∈ Icc Lmin Lmax) → (∀ i ∈ S, 0 < d i) →
      (∀ i ∈ S, Q = (d i:ℝ)*(N:ℝ)^(L i)) → (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, 2 ≤ alpha (Real.log (d i:ℝ)/Real.log (N:ℝ)) (L i)) →
      ∀ a : Original106Action,
        absoluteCoefficientError N Q S L d sigma (precedingH g) (precedingh g) a ≤
          epsilon*parentTheta N Q S d sigma := by
  obtain ⟨T,hT⟩ := immutable430_absolute_bank_errors hmin hmax he
  refine ⟨T, ?_⟩
  intro N hN g Q ι S L d sigma hL hd hQ hsigma halpha a
  simpa only [absoluteBankError_eq_literal] using
    hT N hN g Q S L d sigma hL hd hQ hsigma halpha a

/-- One actual bound for production localBudget, with the entire base
discrepancy still displayed. This is not a theorem assuming hlocal. -/
theorem immutable430_literal_feedbackBudget {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ g : Fin 430, ∀ Q : ℝ,
      ∀ {ι : Type*} (S : Finset ι) (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ),
      (∀ i ∈ S, L i ∈ Icc Lmin Lmax) → (∀ i ∈ S, 0 < d i) →
      (∀ i ∈ S, Q = (d i:ℝ)*(N:ℝ)^(L i)) → (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, 2 ≤ alpha (Real.log (d i:ℝ)/Real.log (N:ℝ)) (L i)) →
      ∀ baseA baseB : Original106Action → ℝ, ∀ a : Original106Action,
        (0 < parentTheta N Q S d sigma →
          P5RenewalFiniteError.localBudget
            (fun _ : Original106Action => (Finset.univ : Finset RowAtom))
            (fun _ b => b) baseA baseB
            (fun a b => normalizedParentRow N Q S L d sigma (fun _ => a) b)
            idealRow (oldAtomValue (precedingH g) (precedingh g)) a ≤
              |baseA a-baseB a|+epsilon) ∧
        (parentTheta N Q S d sigma = 0 →
          absoluteCoefficientError N Q S L d sigma (precedingH g) (precedingh g) a = 0) := by
  obtain ⟨T,hT⟩ := immutable430_literal_absoluteCoefficientError hmin hmax he
  refine ⟨T, ?_⟩
  intro N hN g Q ι S L d sigma hL hd hQ hsigma halpha baseA baseB a
  have hh := hT N hN g Q S L d sigma hL hd hQ hsigma halpha a
  constructor
  · intro htheta
    rw [literal_localBudget_identity N Q S L d sigma (precedingH g) (precedingh g)
      baseA baseB a htheta]
    exact add_le_add_left ((div_le_iff₀ htheta).mpr hh) _
  · intro htheta
    rw [htheta,mul_zero] at hh
    exact le_antisymm hh
      (literal_absoluteCoefficientError_nonneg N Q S L d sigma (precedingH g) (precedingh g) a)

end
end ImbalancedChen.Part5OriginalH430LiteralAbsoluteBudget
