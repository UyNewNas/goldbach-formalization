import ImbalancedChen.P5ActualCommonRefinedRange
import ImbalancedChen.P5ActualDyadicRankPolynomial

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual common-refined policy8, actual signed rho, actual canonical source
cap and literal dyadic/rank union. Complete product=N is retained and paid
separately. All powers are integer WORD multiplicities, not prime-square
or prime-only multiplicities. No h6 or active-cap premise remains.
-/
namespace ImbalancedChen.P5Z.ActualCommonRefinedPayments
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open ImbalancedChen.P4BActualSmoothHyperbolaCorrection
open ImbalancedChen.P5Z.ProperPowerPhysicalPolynomialPayment
open ImbalancedChen.P5Z.ProperPowerSignedMeanHBTransport
open ImbalancedChen.P5Z.ProperPowerSignedModulusPayment
open ImbalancedChen.P5Z.ActualCommonRefinedRange
open ImbalancedChen.P5Z.ActualDyadicRankPolynomial
open ImbalancedChen.P5Z.OriginalDyadicRankUnion
open ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open ImbalancedChen.Part3.AllKLambdaChartCorrection
open ImbalancedChen.Part3.AllKFamilyLambdaCorrectionBound

/-- The concrete retain function is the frozen physical owner's actual
constructor, with target-dependent log coordinates and all eleven cells. -/
abbrev actualRetain (d : P5OriginalCommonRefinedConstructor.OriginalData) :
    ℕ → List ℕ → Bool := fun N => P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ) false

/-- Named divisor and reciprocal-totient primitives, now invoked with
NO active-range gate for this actual policy. Constants precede its data. -/
theorem actual_noncollision_row_subpower {delta : ℝ} (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 0 < U →
      ∀ (d : P5OriginalCommonRefinedConstructor.OriginalData), 0 ≤ d.e →
      ∀ (r epsilon : ℝ), epsilon ≤ 1/1000 → ∀ (cap : ℕ → ℕ) (N : ℕ), 2 ≤ N →
      ∀ b : ℕ, 1 ≤ b → b ≤ Nat.ceil (U*(N : ℝ)) → b ≠ N →
      ‖signedRow (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
        (physicalRho 1 r epsilon (actualRetain d) cap N) N b‖ ≤
        (C*(U+2)^delta + 4*(1+(599/1000 : ℝ)/delta))*(N : ℝ)^delta := by
  obtain ⟨C, hC, hrow⟩ := physical_noncollision_signedRow_subpower hd
  refine ⟨C, hC, ?_⟩
  intro U hU d he r epsilon hepsilon cap N hN b hb hbU hne
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hactual := actualActiveCap_le_inflatedTheta d he N r epsilon cap hN hepsilon
  have h := hrow U hU (599/1000) 1 r epsilon (by norm_num)
    (actualRetain d) cap N (by omega) hactual b hb hbU hne
  have hlog : Real.log (N : ℝ) ≤ (N : ℝ)^delta/delta :=
    Real.log_le_rpow_div (zero_le_one.trans hN1) hd
  have hone := Real.one_le_rpow hN1 hd.le
  have hmean : 4*(1+(599/1000 : ℝ)*Real.log (N : ℝ)) ≤
      (4*(1+(599/1000 : ℝ)/delta))*(N : ℝ)^delta := by nlinarith
  calc
    _ ≤ _ := h
    _ ≤ (C*(U+2)^delta)*(N : ℝ)^delta +
        (4*(1+(599/1000 : ℝ)/delta))*(N : ℝ)^delta := add_le_add_left hmean _
    _ = _ := by ring

/-- Product=N: tau(N)^rank and the SAME physical active-card/mean cost
are paid by their own named primitives, after the actual range proof. -/
theorem actual_collision_factor_polynomial (kStar : ℕ) {delta : ℝ} (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : P5OriginalCommonRefinedConstructor.OriginalData), 0 ≤ d.e →
      ∀ (r epsilon : ℝ), epsilon ≤ 1/1000 → ∀ (cap : ℕ → ℕ) (N j : ℕ),
        2 ≤ N → j ≤ kStar →
        (N.divisors.card^j : ℕ)*
          (((physicalQ 1 r epsilon (actualRetain d) cap N).card : ℝ)+
            meanBudget (physicalQ 1 r epsilon (actualRetain d) cap N)
              (physicalRho 1 r epsilon (actualRetain d) cap N)) ≤
          C*(N : ℝ)^((599/1000 : ℝ)+delta) := by
  obtain ⟨C, hC, h⟩ := physical_collision_factor_polynomial kStar
    (show (0 : ℝ) ≤ 599/1000 by norm_num) hd
  exact ⟨C, hC, fun d he r epsilon hepsilon cap N j hN hj =>
    h 1 r epsilon (actualRetain d) cap N j (by omega) hj
      (actualActiveCap_le_inflatedTheta d he N r epsilon cap hN hepsilon)⟩

def noncollisionKernel (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) (b : ℕ) : ℂ :=
  if b = N then 0 else signedRow Q rho N b

def collisionKernel (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) (b : ℕ) : ℂ :=
  if b = N then signedRow Q rho N b else 0

/-- Exact same-rho split, including the literal product=N summands. -/
theorem originalBankError_collision_split {kStar : ℕ} (F : Family kStar)
    (N cap : ℕ) (chi eta : ℝ → ℝ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    originalBankError F N cap chi eta kappa0 (signedRow Q rho N) =
      originalBankError F N cap chi eta kappa0 (noncollisionKernel N Q rho) +
      originalBankError F N cap chi eta kappa0 (collisionKernel N Q rho) := by
  unfold originalBankError
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro js hjs
  apply Finset.sum_congr rfl
  intro us hus
  by_cases h : us.prod = N <;> simp [noncollisionKernel, collisionKernel, h]

/-- Clipping the noncollision kernel is legitimate on the actual Family
support. Products outside the true complete scale have zero source weight. -/
theorem originalBankError_noncollision_clip {kStar : ℕ} (F : Family kStar)
    (N cap : ℕ) (chi eta : ℝ → ℝ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    originalBankError F N cap chi eta kappa0 (noncollisionKernel N Q rho) =
      originalBankError F N cap chi eta kappa0
        (fun b => if 1 ≤ b ∧ b ≤ Nat.ceil (F.upper*(N : ℝ)) then
          noncollisionKernel N Q rho b else 0) := by
  unfold originalBankError
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro js hjs
  apply Finset.sum_congr rfl
  intro us hus
  by_cases hz : chartTerm chi eta (bankWeight F N k) (N : ℝ) kappa0 js us = 0
  · simp [hz]
  · have hi := (Finset.mem_filter.mp hus).1
    obtain ⟨hlen, hmem⟩ := words_spec (Finset.Icc 1 cap) k.val us hi
    have hW : bankWeight F N k us ≠ 0 := by
      intro h
      apply hz
      simp [chartTerm, trimmedWeight, h]
    have hpos : 1 ≤ us.prod := List.prod_pos (fun n hn => by
      have := (Finset.mem_Icc.mp (hmem n hn)).1
      omega)
    have hscale : us.prod ≤ Nat.ceil (F.upper*(N : ℝ)) := by
      exact_mod_cast (bankWeight_support F N k hlen hW).2.trans (Nat.le_ceil _)
    simp only [if_pos ⟨hpos, hscale⟩]

/-- The actual all-rank noncollision source is paid with its real modulus
kernel, rather than assuming a global signed-row bound outside its scale. -/
theorem eventually_actual_noncollision_bank_bound {kStar : ℕ}
    (F : Family kStar) {delta : ℝ} (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
      ∀ (d : P5OriginalCommonRefinedConstructor.OriginalData), 0 ≤ d.e →
      ∀ (r epsilon : ℝ), epsilon ≤ 1/1000 → ∀ (cap : ℕ → ℕ)
      (chi eta : ℝ → ℝ), (∀ x, x ≤ 1 → chi x = 1) →
      (∀ x, 2 ≤ x → chi x = 0) → (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) →
      (∀ x, |eta x| ≤ 1) → ∀ kappa0 M : ℝ, 0 ≤ M →
      (∀ (k : Fin (kStar+1)) us, us.length = k.val → ‖bankWeight F N k us‖ ≤ M) →
      ‖originalBankError F N (Nat.ceil (F.upper*(N : ℝ))) chi eta kappa0
        (noncollisionKernel N (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
          (physicalRho 1 r epsilon (actualRetain d) cap N))‖ ≤
        C*M*Real.log (N : ℝ)^(kStar+1)*(N : ℝ)^(1-F.aStar/2+delta) := by
  obtain ⟨D, hD, hrow⟩ := actual_noncollision_row_subpower hd
  let H : ℝ := D*(F.upper+2)^delta+4*(1+(599/1000 : ℝ)/delta)
  have hH : 0 < H := by have := F.upper_pos; dsimp [H]; positivity
  let C := (unionConstant F*bankLogConstant^(kStar+1))*H+1
  have hC : 0 < C := by
    dsimp [C]
    have := unionConstant_nonneg F
    have := bankLogConstant_pos
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_actual_rank_union_bound F] with N hN
  refine ⟨hN.1, ?_⟩
  intro d he r epsilon hepsilon cap chi eta hone hzero hchi heta kappa0 M hM hamp
  let Q := attachedUpperModuli 1 r epsilon (actualRetain d) cap N
  let rho := physicalRho 1 r epsilon (actualRetain d) cap N
  let K : ℕ → ℂ := fun b => if 1 ≤ b ∧ b ≤ Nat.ceil (F.upper*(N : ℝ)) then
    noncollisionKernel N Q rho b else 0
  have hK : ∀ b, ‖K b‖ ≤ H*(N : ℝ)^delta := by
    intro b
    by_cases hb : 1 ≤ b ∧ b ≤ Nat.ceil (F.upper*(N : ℝ))
    · by_cases hne : b = N
      · simp only [K, if_pos hb, noncollisionKernel, if_pos hne, norm_zero]
        exact mul_nonneg hH.le (Real.rpow_nonneg (Nat.cast_nonneg N) delta)
      · simpa only [K, if_pos hb, noncollisionKernel, if_neg hne, H, Q, rho] using
          hrow F.upper F.upper_pos d he r epsilon hepsilon cap N hN.1 b hb.1 hb.2 hne
    · simp only [K, if_neg hb, norm_zero]
      exact mul_nonneg hH.le (Real.rpow_nonneg (Nat.cast_nonneg N) delta)
  rw [originalBankError_noncollision_clip]
  have hb := hN.2 chi eta hone hzero hchi heta kappa0 K M
    (H*(N : ℝ)^delta) hM (mul_nonneg hH.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hamp hK
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hconst : (unionConstant F*bankLogConstant^(kStar+1))*H ≤ C := by dsimp [C]; linarith
  calc
    _ ≤ _ := hb
    _ = ((unionConstant F*bankLogConstant^(kStar+1))*H)*M*
        Real.log (N : ℝ)^(kStar+1)*(N : ℝ)^(1-F.aStar/2+delta) := by
      rw [Real.rpow_add hN0]
      ring
    _ ≤ _ := by
      have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ N by omega))
      gcongr <;> assumption

/-- Actual ordered proper-power words of COMPLETE product=N, without
any marked-coordinate overcount and without a prime-only shortcut. -/
def fullCollisionWords (cap k N : ℕ) : Finset (List ℕ) :=
  (properChartWords cap k).filter (fun us => us.prod = N)

theorem fullCollisionWords_card_le (cap k N : ℕ) (hN : N ≠ 0) :
    (fullCollisionWords cap k N).card ≤ N.divisors.card^k := by
  let S := fullCollisionWords cap k N
  have hlen (us : S) : us.val.length = k :=
    (words_spec (Finset.Icc 1 cap) k us.val
      (Finset.mem_filter.mp (Finset.mem_filter.mp us.property).1).1).1
  have hdiv (us : S) (i : Fin k) : wordVector k us.val i ∈ N.divisors := by
    have hi : i.val < us.val.length := by simpa [hlen us] using i.isLt
    have hm : wordVector k us.val i ∈ us.val := by
      dsimp [wordVector]
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    have hp := (Finset.mem_filter.mp us.property).2
    exact Nat.mem_divisors.mpr ⟨hp ▸ List.dvd_prod hm, hN⟩
  let encode : S → (Fin k → N.divisors) := fun us i => ⟨wordVector k us.val i, hdiv us i⟩
  have hinj : Function.Injective encode := by
    intro us vs h
    apply Subtype.ext
    apply wordVector_injOn_length k (hlen us) (hlen vs)
    funext i
    exact congrArg (fun f : Fin k → N.divisors => (f i).val) h
  simpa only [Fintype.card_pi_const, Fintype.card_coe] using Fintype.card_le_of_injective encode hinj

/-- Whole true product=N chart, on the same primitive restriction of the
original displayed signed row. Its tau(N)^k multiplicity is explicit. -/
theorem actual_collision_chart_bound {kStar : ℕ} (F : Family kStar)
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N sourceCap : ℕ)
    (hN : N ≠ 0) (k : Fin (kStar+1)) (r epsilon : ℝ) (cap : ℕ → ℕ)
    (chi eta : ℝ → ℝ) (hchi : ∀ x, 0 ≤ chi x ∧ chi x ≤ 1)
    (heta : ∀ x, |eta x| ≤ 1) (kappa0 : ℝ) (js : List ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hamp : ∀ us, us.length = k.val → ‖bankWeight F N k us‖ ≤ M) :
    ‖∑ us ∈ properChartWords sourceCap k.val,
      lambdaWord us * chartTerm chi eta (bankWeight F N k) (N : ℝ) kappa0 js us *
        collisionKernel N (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
          (physicalRho 1 r epsilon (actualRetain d) cap N) us.prod‖ ≤
      M*(N.divisors.card^k.val : ℕ)*
        (((physicalQ 1 r epsilon (actualRetain d) cap N).card : ℝ)+
          meanBudget (physicalQ 1 r epsilon (actualRetain d) cap N)
            (physicalRho 1 r epsilon (actualRetain d) cap N)) := by
  let Q := physicalQ 1 r epsilon (actualRetain d) cap N
  let rho := physicalRho 1 r epsilon (actualRetain d) cap N
  let B : ℝ := (Q.card : ℝ)+meanBudget Q rho
  have hB : 0 ≤ B := by dsimp [B, meanBudget]; positivity
  have heq : (∑ us ∈ properChartWords sourceCap k.val,
      lambdaWord us * chartTerm chi eta (bankWeight F N k) (N : ℝ) kappa0 js us *
        collisionKernel N (attachedUpperModuli 1 r epsilon (actualRetain d) cap N) rho us.prod) =
      ∑ us ∈ fullCollisionWords sourceCap k.val N,
        lambdaWord us * chartTerm chi eta (bankWeight F N k) (N : ℝ) kappa0 js us *
          signedRow Q rho N N := by
    simp only [collisionKernel]
    simp_rw [physical_signedRow_eq_active]
    simp only [fullCollisionWords, Finset.sum_filter, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro us hus
    by_cases hp : us.prod = N <;> simp [hp, Q, rho]
  rw [heq]
  have hcard : ((fullCollisionWords sourceCap k.val N).card : ℝ) ≤
      (N.divisors.card^k.val : ℕ) := by exact_mod_cast fullCollisionWords_card_le sourceCap k.val N hN
  have hrow : ‖signedRow Q rho N N‖ ≤ B := by
    apply (norm_signedRow_le Q rho 1 (by norm_num)
      (fun q _ => physicalRho_norm_le_one 1 r epsilon (actualRetain d) cap N q) N N).trans_eq
    simp only [rowBudget, if_pos rfl, one_mul, B]
  calc
    _ ≤ ∑ us ∈ fullCollisionWords sourceCap k.val N,
        ‖lambdaWord us * chartTerm chi eta (bankWeight F N k) (N : ℝ) kappa0 js us *
          signedRow Q rho N N‖ := norm_sum_le _ _
    _ ≤ ∑ _us ∈ fullCollisionWords sourceCap k.val N, M*B := by
      apply Finset.sum_le_sum
      intro us hus
      have hlen := (words_spec (Finset.Icc 1 sourceCap) k.val us
        (Finset.mem_filter.mp (Finset.mem_filter.mp hus).1).1).1
      have hw : ‖lambdaWord us * chartTerm chi eta (bankWeight F N k)
          (N : ℝ) kappa0 js us‖ ≤ M := by
        rw [norm_mul]
        exact (mul_le_mul (lambdaWord_norm_le_one us)
          (bank_chart_amplitude F N k chi eta hchi heta M hM hamp kappa0 js us hlen)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      rw [norm_mul]
      exact mul_le_mul hw hrow (norm_nonneg _) hM
    _ = (M*((fullCollisionWords sourceCap k.val N).card : ℝ))*B := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hM) hB

/-- The actual product=N source is summed over the ENTIRE literal bank
and EVERY original rank, using the same concrete policy and active rho. -/
theorem eventually_actual_collision_bank_bound {kStar : ℕ}
    (F : Family kStar) {delta : ℝ} (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
      ∀ (d : P5OriginalCommonRefinedConstructor.OriginalData), 0 ≤ d.e →
      ∀ (r epsilon : ℝ), epsilon ≤ 1/1000 → ∀ (cap : ℕ → ℕ)
      (chi eta : ℝ → ℝ), (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) →
      (∀ x, |eta x| ≤ 1) → ∀ kappa0 M : ℝ, 0 ≤ M →
      (∀ (k : Fin (kStar+1)) us, us.length = k.val → ‖bankWeight F N k us‖ ≤ M) →
      ‖originalBankError F N (Nat.ceil (F.upper*(N : ℝ))) chi eta kappa0
        (collisionKernel N (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
          (physicalRho 1 r epsilon (actualRetain d) cap N))‖ ≤
        C*M*Real.log (N : ℝ)^kStar*(N : ℝ)^((599/1000 : ℝ)+delta) := by
  obtain ⟨D, hD, hfactor⟩ := actual_collision_factor_polynomial kStar hd
  let C : ℝ := ((kStar+1 : ℕ) : ℝ)*bankLogConstant^kStar*D+1
  have hC : 0 < C := by dsimp [C]; have := bankLogConstant_pos; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_actual_cutoffIndex_le_log F.upper F.upper_pos] with N hN
  refine ⟨hN.1, ?_⟩
  intro d he r epsilon hepsilon cap chi eta hchi heta kappa0 M hM hamp
  let sourceCap := Nat.ceil (F.upper*(N : ℝ))
  let J : ℝ := ((cutoffIndex sourceCap+2 : ℕ) : ℝ)
  let P : ℝ := (N : ℝ)^((599/1000 : ℝ)+delta)
  have hP : 0 ≤ P := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hJ : 1 ≤ J := by exact_mod_cast (show 1 ≤ cutoffIndex sourceCap+2 by omega)
  have hbank (k : Fin (kStar+1)) : ((chartBank sourceCap k.val).card : ℝ) ≤ J^kStar := by
    rw [actual_chartBank_card]
    push_cast
    have hb : ((cutoffIndex sourceCap+1 : ℕ) : ℝ) ≤ J := by dsimp [J]; push_cast; linarith
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hb _).trans
      (pow_le_pow_right₀ hJ (by have := k.isLt; omega))
  have hchart (k : Fin (kStar+1)) (js : List ℕ) :
      ‖∑ us ∈ properChartWords sourceCap k.val,
        lambdaWord us * chartTerm chi eta (bankWeight F N k) (N : ℝ) kappa0 js us *
          collisionKernel N (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
            (physicalRho 1 r epsilon (actualRetain d) cap N) us.prod‖ ≤ M*(D*P) := by
    apply (actual_collision_chart_bound F d N sourceCap (by omega) k r epsilon cap
      chi eta hchi heta kappa0 js M hM (hamp k)).trans
    have hf := hfactor d he r epsilon hepsilon cap N k.val hN.1 (by have := k.isLt; omega)
    simpa only [mul_assoc, P] using mul_le_mul_of_nonneg_left hf hM
  have hbound : ‖originalBankError F N sourceCap chi eta kappa0
      (collisionKernel N (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
        (physicalRho 1 r epsilon (actualRetain d) cap N))‖ ≤
      ((kStar+1 : ℕ) : ℝ)*J^kStar*(M*(D*P)) := by
    unfold originalBankError
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k : Fin (kStar+1), J^kStar*(M*(D*P)) := by
        apply Finset.sum_le_sum
        intro k hk
        calc
          _ ≤ ∑ js ∈ chartBank sourceCap k.val,
              ‖∑ us ∈ properChartWords sourceCap k.val,
                lambdaWord us * chartTerm chi eta (bankWeight F N k) (N : ℝ) kappa0 js us *
                  collisionKernel N (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
                    (physicalRho 1 r epsilon (actualRetain d) cap N) us.prod‖ := norm_sum_le _ _
          _ ≤ ∑ _js ∈ chartBank sourceCap k.val, M*(D*P) :=
            Finset.sum_le_sum (fun js _ => hchart k js)
          _ = ((chartBank sourceCap k.val).card : ℝ)*(M*(D*P)) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right (hbank k) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hJlog : J^kStar ≤ bankLogConstant^kStar*Real.log (N : ℝ)^kStar := by
    simpa only [mul_pow] using pow_le_pow_left₀ (zero_le_one.trans hJ) hN.2 kStar
  have hc : ((kStar+1 : ℕ) : ℝ)*bankLogConstant^kStar*D ≤ C := by dsimp [C]; linarith
  calc
    _ ≤ _ := hbound
    _ ≤ ((kStar+1 : ℕ) : ℝ)*(bankLogConstant^kStar*Real.log (N : ℝ)^kStar)*(M*(D*P)) := by
      gcongr <;> assumption
    _ = (((kStar+1 : ℕ) : ℝ)*bankLogConstant^kStar*D)*M*Real.log (N : ℝ)^kStar*P := by ring
    _ ≤ _ := by gcongr <;> assumption

/-- One genuine strict margin pays both exact-product collision and the
noncollision proper-power saving. The actual amplitude and full bank/rank
counts contribute fixed log powers; no scalar reconstruction or PP final
estimate is supplied as a premise. Threshold precedes all physical data,
modulus enumeration caps, cutoffs and same-source smoothing functions. -/
theorem eventually_actual_full_bank_small {kStar : ℕ} (F : Family kStar)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
      ∀ (d : P5OriginalCommonRefinedConstructor.OriginalData), 0 ≤ d.e →
      ∀ (r epsilon : ℝ), epsilon ≤ 1/1000 → ∀ (cap : ℕ → ℕ)
      (chi eta : ℝ → ℝ), (∀ x, x ≤ 1 → chi x = 1) →
      (∀ x, 2 ≤ x → chi x = 0) → (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) →
      (∀ x, |eta x| ≤ 1) → ∀ kappa0 : ℝ,
      ‖originalBankError F N (Nat.ceil (F.upper*(N : ℝ))) chi eta kappa0
        (signedRow (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
          (physicalRho 1 r epsilon (actualRetain d) cap N) N)‖ ≤
        tolerance*singularNormalization N := by
  let delta := commonMargin F (599/1000)
  have hd : 0 < delta := (commonMargin_actual_theta F).1
  have hpn : 1-F.aStar/2+delta < 1 := by
    have h := (commonMargin_actual_theta F).2.1
    change 1-F.aStar/2+2*delta < 1 at h
    linarith
  have hpc : (599/1000 : ℝ)+delta < 1 := by
    have h := (commonMargin_actual_theta F).2.2
    change (599/1000 : ℝ)+2*delta < 1 at h
    linarith
  obtain ⟨Cn, hCn, hnon⟩ := eventually_actual_noncollision_bank_bound F hd
  obtain ⟨Cc, hCc, hcol⟩ := eventually_actual_collision_bank_bound F hd
  obtain ⟨A, B, hA, hamp⟩ := all_rank_bank_amplitude F
  have hpnPay := eventually_powerLog_le_singularNormalization
    (Cn*(A : ℝ)*(2 : ℝ)^B) (1-F.aStar/2+delta) (B+(kStar+1)) hpn
    (tolerance/2) (half_pos htolerance)
  have hpcPay := eventually_powerLog_le_singularNormalization
    (Cc*(A : ℝ)*(2 : ℝ)^B) ((599/1000 : ℝ)+delta) (B+kStar) hpc
    (tolerance/2) (half_pos htolerance)
  filter_upwards [hnon, hcol, hpnPay, hpcPay] with N hn hc hpayn hpayc
  refine ⟨hn.1, ?_⟩
  intro d he r epsilon hepsilon cap chi eta hone hzero hchi heta kappa0
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hn.1
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hlogPlus : 0 ≤ Real.log ((N : ℝ)+2) := Real.log_nonneg (by linarith)
  have hlogCompare : Real.log ((N : ℝ)+2) ≤ 2*Real.log (N : ℝ) := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (N : ℝ)+2)
      (show (N : ℝ)+2 ≤ (N : ℝ)^2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  let M : ℝ := (A : ℝ)*Real.log ((N : ℝ)+2)^B
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMbound : M ≤ (A : ℝ)*(2 : ℝ)^B*Real.log (N : ℝ)^B := by
    have hp := pow_le_pow_left₀ hlogPlus hlogCompare B
    rw [mul_pow] at hp
    simpa only [M, mul_assoc] using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg A)
  have hbN := hn.2 d he r epsilon hepsilon cap chi eta hone hzero hchi heta kappa0 M hM (hamp N)
  have hbC := hc.2 d he r epsilon hepsilon cap chi eta hchi heta kappa0 M hM (hamp N)
  have hsN : ‖originalBankError F N (Nat.ceil (F.upper*(N : ℝ))) chi eta kappa0
      (noncollisionKernel N (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
        (physicalRho 1 r epsilon (actualRetain d) cap N))‖ ≤
      (tolerance/2)*singularNormalization N := by
    apply hbN.trans
    calc
      _ ≤ Cn*((A : ℝ)*(2 : ℝ)^B*Real.log (N : ℝ)^B)*Real.log (N : ℝ)^(kStar+1)*
          (N : ℝ)^(1-F.aStar/2+delta) := by gcongr <;> assumption
      _ = (Cn*(A : ℝ)*(2 : ℝ)^B)*(N : ℝ)^(1-F.aStar/2+delta)*
          Real.log (N : ℝ)^(B+(kStar+1)) := by rw [pow_add]; ring
      _ ≤ _ := hpayn
  have hsC : ‖originalBankError F N (Nat.ceil (F.upper*(N : ℝ))) chi eta kappa0
      (collisionKernel N (attachedUpperModuli 1 r epsilon (actualRetain d) cap N)
        (physicalRho 1 r epsilon (actualRetain d) cap N))‖ ≤
      (tolerance/2)*singularNormalization N := by
    apply hbC.trans
    calc
      _ ≤ Cc*((A : ℝ)*(2 : ℝ)^B*Real.log (N : ℝ)^B)*Real.log (N : ℝ)^kStar*
          (N : ℝ)^((599/1000 : ℝ)+delta) := by gcongr <;> assumption
      _ = (Cc*(A : ℝ)*(2 : ℝ)^B)*(N : ℝ)^((599/1000 : ℝ)+delta)*
          Real.log (N : ℝ)^(B+kStar) := by rw [pow_add]; ring
      _ ≤ _ := hpayc
  rw [originalBankError_collision_split]
  exact (norm_add_le _ _).trans (by linarith)

end
end ImbalancedChen.P5Z.ActualCommonRefinedPayments
