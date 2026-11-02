import ImbalancedChen.P2OriginalGammaDivisorNorm
import ImbalancedChen.P2GammaSmoothLogGrid
import ImbalancedChen.P2GammaRetainedInteriorGeometry
import ImbalancedChen.P5OriginalSingletonLowerTrimPaid

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal Gamma complete-product trim is paid, including its original
word/quotient multiplicity, unit quotient, signed modulus weights, and
exact coprime mean.  The singleton theorem is not applied to a Gamma
coefficient: only its already proved numerical cutoff bound is reused.
The two divisor subpower constants are supplied independently, one for
the actual Gamma product fibre and one for the nonzero target difference.
No source identity, trim estimate, or Gamma distribution estimate is an
input.  Sorting and upper-product walls are separate unpaid obligations.
-/

namespace ImbalancedChen.P2GammaCompleteProductTrimPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2OriginalU5ExactNormalizedSource
open P5OriginalU5CausalFinite (pairSupport)
open P5OriginalPrimeEndpoint P5OriginalSharpPrime
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def lowLabels (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ) (Y : ℕ) : Finset Label :=
  (rootLabels N t cs).filter (fun x => product (t.1*t.2) x ≤ Y)

def wordError (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (w : Label → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q * ∑ x ∈ rootLabels N t cs,
    w x * gammaKernel N q (product (t.1*t.2) x)

private theorem root_product_pos {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {cs : List ℕ} {x : Label}
    (hx : x ∈ rootLabels N t cs) : 0 < product (t.1*t.2) x := by
  have hd := rootLabels_data hx
  exact Nat.mul_pos (Nat.mul_pos
    (P2OriginalU5SmallPartnerRootPayment.pair_product_pos ht)
    (word_prod_pos hd.1)) hd.2.1

/-- This finite cardinal bound retains every original representation.
It is not an injectivity assertion about the complete-product map. -/
theorem lowLabels_card_le_divisor_sum {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (cs : List ℕ) (Y : ℕ) :
    ((lowLabels N t cs Y).card : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 Y, (fouvryTau (cs.length+2) m : ℝ) := by
  have hmap : ∀ x ∈ lowLabels N t cs Y,
      product (t.1*t.2) x ∈ Finset.Icc 1 Y := by
    intro x hx
    obtain ⟨hx,hY⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_Icc.mpr ⟨root_product_pos ht hx,hY⟩
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := lowLabels N t cs Y) (t := Finset.Icc 1 Y)
    (g := product (t.1*t.2)) hmap (fun _ => (1 : ℝ))
  calc
    _ = ∑ m ∈ Finset.Icc 1 Y,
        ∑ x ∈ lowLabels N t cs Y with product (t.1*t.2) x=m, (1 : ℝ) := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hf.symm
    _ ≤ ∑ m ∈ Finset.Icc 1 Y,
        ((rootProductFiber N t cs m).card : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      have hsub : (lowLabels N t cs Y).filter
          (fun x => product (t.1*t.2) x=m) ⊆ rootProductFiber N t cs m := by
        intro x hx
        obtain ⟨hx,heq⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,heq⟩
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using
        (show (((lowLabels N t cs Y).filter
          (fun x => product (t.1*t.2) x=m)).card : ℝ) ≤
            ((rootProductFiber N t cs m).card : ℝ) from
          by exact_mod_cast Finset.card_le_card hsub)
    _ ≤ _ := Finset.sum_le_sum (fun m hm => by
      exact_mod_cast card_rootProductFiber_le ht cs m)

/-- The AP part uses divisors of N-m only after m<N is established.
The second term is the exact coprime mean, bounded separately. -/
theorem kernel_absolute_modulus_sum_le {N m M : ℕ} (hm : m < N)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (hQ : Q ⊆ Finset.Icc 1 M)
    (hrho : ∀ q ∈ Q, |rho q| ≤ 1) :
    (∑ q ∈ Q, |rho q * gammaKernel N q m|) ≤
      ((N-m).divisors.card : ℝ) + 4*(1+Real.log (max 1 (M : ℝ))) := by
  have hp (q : ℕ) : |rho q * gammaKernel N q m| ≤
      (if Nat.ModEq q m N then |rho q| else 0) +
        |rho q|/(q.totient : ℝ) := by
    have hφ : 0 ≤ 1/(q.totient : ℝ) := by positivity
    have ha := abs_sub (if Nat.ModEq q m N then (1 : ℝ) else 0)
      ((if m.Coprime q then (1 : ℝ) else 0)/(q.totient : ℝ))
    rw [abs_mul,gammaKernel]
    calc
      _ ≤ |rho q| * (|(if Nat.ModEq q m N then (1 : ℝ) else 0)| +
          |(if m.Coprime q then (1 : ℝ) else 0)/(q.totient : ℝ)|) :=
        mul_le_mul_of_nonneg_left ha (abs_nonneg _)
      _ ≤ _ := by
        by_cases hc : Nat.ModEq q m N <;> by_cases hg : m.Coprime q <;>
          simp [hc,hg,abs_div,abs_of_nonneg (Nat.cast_nonneg (q.totient)),
            mul_add,mul_div_assoc] <;> positivity
  have hAP : (∑ q ∈ Q, if Nat.ModEq q m N then |rho q| else 0) ≤
      ((N-m).divisors.card : ℝ) := by
    rw [← Finset.sum_filter]
    simpa only [distance,if_pos hm.le] using
      sum_abs_rho_congruence_le_divisors Q rho N m hm.ne hrho
  have hmean : (∑ q ∈ Q, |rho q|/(q.totient : ℝ)) ≤
      4*(1+Real.log (max 1 (M : ℝ))) := by
    apply le_trans _ (sum_reciprocal_totient_subset_le_log Q M hQ)
    exact Finset.sum_le_sum (fun q hq =>
      div_le_div_of_nonneg_right (hrho q hq) (Nat.cast_nonneg _))
  exact (Finset.sum_le_sum (fun q _ => hp q)).trans
    (by rw [Finset.sum_add_distrib]; exact add_le_add hAP hmean)

/-- Fixed constants precede N, the old pair, all finite modulus choices,
and the actual perturbation of the source.  Both multiplicity and the
nonzero target difference are paid, with no x^o(1) charged to a BV norm. -/
theorem exists_word_low_product_budget (cs : List ℕ) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (N Y M : ℕ) (t : ℕ × ℕ), t ∈ pairSupport N →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (w : Label → ℝ),
      Y < N → Q ⊆ Finset.Icc 1 M →
      (∀ q ∈ Q, |rho q| ≤ 1) →
      (∀ x ∈ rootLabels N t cs, |w x| ≤ 1) →
      (∀ x ∈ rootLabels N t cs, Y < product (t.1*t.2) x → w x=0) →
      |wordError N t cs Q rho w| ≤
        (Y : ℝ)*(C*(N : ℝ)^eps)*
          (D*(N : ℝ)^eps+4*(1+Real.log (max 1 (M : ℝ)))) := by
  obtain ⟨C,hC,hsource⟩ :=
    Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
      (k := cs.length+2) (by omega) heps
  obtain ⟨D,hD,hdifference⟩ :=
    Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
      (k := 2) (by norm_num) heps
  refine ⟨C,D,hC,hD,?_⟩
  intro N Y M t ht Q rho w hYN hQ hrho hw hzero
  let B : ℝ := D*(N : ℝ)^eps+4*(1+Real.log (max 1 (M : ℝ)))
  have hB : 0 ≤ B := by
    have hl := Real.log_nonneg (le_max_left (1 : ℝ) (M : ℝ))
    dsimp [B]
    positivity
  have hcard : ((lowLabels N t cs Y).card : ℝ) ≤
      (Y : ℝ)*(C*(N : ℝ)^eps) := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 Y, (fouvryTau (cs.length+2) m : ℝ) :=
        lowLabels_card_le_divisor_sum ht cs Y
      _ ≤ ∑ _m ∈ Finset.Icc 1 Y, C*(N : ℝ)^eps := by
        apply Finset.sum_le_sum
        intro m hm
        have hmdata := Finset.mem_Icc.mp hm
        exact (hsource m hmdata.1).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _)
            (by exact_mod_cast hmdata.2.trans hYN.le) heps.le) hC.le)
      _ = _ := by simp
  have hk (x : Label) (hx : x ∈ rootLabels N t cs) :
      (∑ q ∈ Q, |rho q*gammaKernel N q (product (t.1*t.2) x)|) ≤ B := by
    have hm := (rootLabels_data hx).2.2.2
    have hdiff : ((N-product (t.1*t.2) x).divisors.card : ℝ) ≤
        D*(N : ℝ)^eps := by
      have hd := hdifference (N-product (t.1*t.2) x) (Nat.sub_pos_of_lt hm)
      have hd' : ((N-product (t.1*t.2) x).divisors.card : ℝ) ≤
          D*((N-product (t.1*t.2) x : ℕ) : ℝ)^eps := by
        simpa only [fouvryTau_two] using hd
      exact hd'.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _)
          (by exact_mod_cast Nat.sub_le N (product (t.1*t.2) x)) heps.le) hD.le)
    exact (kernel_absolute_modulus_sum_le hm Q rho hQ hrho).trans
      (add_le_add_right hdiff _)
  have heq : wordError N t cs Q rho w =
      ∑ x ∈ rootLabels N t cs, w x*
        ∑ q ∈ Q, rho q*gammaKernel N q (product (t.1*t.2) x) := by
    simp only [wordError,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [heq]
  calc
    _ ≤ ∑ x ∈ rootLabels N t cs,
        |w x*∑ q ∈ Q, rho q*gammaKernel N q (product (t.1*t.2) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ rootLabels N t cs,
        if product (t.1*t.2) x ≤ Y then B else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hlow : product (t.1*t.2) x ≤ Y
      · rw [if_pos hlow,abs_mul]
        exact (mul_le_mul (hw x hx) (Finset.abs_sum_le_sum_abs _ _)
          (abs_nonneg _) zero_le_one).trans (by simpa using hk x hx)
      · rw [if_neg hlow,hzero x hx (Nat.lt_of_not_ge hlow),zero_mul,abs_zero]
    _ = ((lowLabels N t cs Y).card : ℝ)*B := by
      rw [← Finset.sum_filter]
      simp only [lowLabels,Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB

/-- A concrete permitted smooth complete-product trim. -/
def smoothTrim (H : ℝ) (m : ℕ) : ℝ :=
  Real.smoothTransition ((m : ℝ)/H-1)

def trimRemainder (H : ℝ) (m : ℕ) : ℝ := 1-smoothTrim H m

theorem trimRemainder_range (H : ℝ) (m : ℕ) :
    0 ≤ trimRemainder H m ∧ trimRemainder H m ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg ((m : ℝ)/H-1)
  have h1 := Real.smoothTransition.le_one ((m : ℝ)/H-1)
  dsimp [trimRemainder,smoothTrim]
  constructor <;> linarith

theorem trimRemainder_eq_zero {H : ℝ} (hH : 0 < H) {m : ℕ}
    (hm : 2*H ≤ (m : ℝ)) : trimRemainder H m=0 := by
  have hdiv : 2 ≤ (m : ℝ)/H := (le_div_iff₀ hH).mpr hm
  simp only [trimRemainder,smoothTrim,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ (m : ℝ)/H-1),sub_self]

/-- The original coupled smooth trim is exactly constant on a retained
row whose COMPLETE lower endpoint is at least twice its trim scale. -/
theorem retained_chart_smoothTrim_plateau {N c : ℕ} {t : ℕ × ℕ}
    {cs : List ℕ} (ht : t ∈ pairSupport N) {T H δ : ℝ}
    (hT : 0 < T) (hH : 2*T ≤ H) (hδ : 0 < δ) {j l p : ℕ}
    (hp : p ∈ P2GammaOriginalCartesianMask.headCarrier N t c) {y : Label}
    (hy : y ∈ rootComplementLabels N t (c::cs))
    (hw : P2GammaSmoothLogGrid.complexWeight δ j p *
      P2GammaRetainedInteriorGeometry.betaLabel N t H δ j l y ≠ 0) :
    smoothTrim T (product (t.1*t.2) y*p) = 1 := by
  have hs := P2GammaRetainedInteriorGeometry.retained_row_complete_scale ht hδ hp hy hw
  have hlow : 2*T ≤ ((product (t.1*t.2) y*p : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact hH.trans hs.1.le
  have hz := trimRemainder_eq_zero hT hlow
  dsimp only [trimRemainder] at hz
  linarith

/-- The literal smooth complete-product weight is removed by its proved
plateau, not hidden inside an allegedly separated arithmetic test. -/
theorem original_retained_trimmed_row_eq_cartesian {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (c : ℕ) (cs : List ℕ) {T H δ : ℝ}
    (hT : 0 < T) (hH : 2*T ≤ H) (hδ : 0 < δ) (j l : ℕ) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs),
      (P2GammaSmoothLogGrid.complexWeight δ j (labelHead x) *
        P2GammaRetainedInteriorGeometry.betaLabel N t H δ j l (labelComplement x)) *
          (smoothTrim T (product (t.1*t.2) x) : ℂ) * F (product (t.1*t.2) x)) =
      ∑ p ∈ P2GammaOriginalCartesianMask.headCarrier N t c,
        ∑ y ∈ rootComplementLabels N t (c::cs),
          (P2GammaSmoothLogGrid.complexWeight δ j p *
            P2GammaRetainedInteriorGeometry.betaLabel N t H δ j l y) *
              F (product (t.1*t.2) y*p) := by
  rw [← P2GammaRetainedInteriorGeometry.original_retained_row_eq_cartesian
    ht c cs hδ j l F]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hw : P2GammaSmoothLogGrid.complexWeight δ j (labelHead x) *
      P2GammaRetainedInteriorGeometry.betaLabel N t H δ j l (labelComplement x) = 0
  · simp only [hw,zero_mul]
  · have hp := P2GammaOriginalCartesianMask.original_head_mem_carrier hx
    have hy : labelComplement x ∈ rootComplementLabels N t (c::cs) :=
      Finset.mem_image_of_mem (fun z : Label => (z.1.tail,z.2)) hx
    have hs := retained_chart_smoothTrim_plateau ht hT hH hδ hp hy hw
    rw [← original_label_head_product (by simp) hx] at hs
    rw [hs,Complex.ofReal_one,mul_one]

/-- The discarded source is below the ORIGINAL complete-product cut;
no quotient or sparse old pair is substituted for this argument. -/
theorem eventually_word_smoothTrim_logAccuracy (cs : List ℕ)
    (kappa : ℝ) (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ pairSupport N, ∀ (M : ℕ)
      (Q : Finset ℕ) (rho : ℕ → ℝ),
      M ≤ N → Q ⊆ Finset.Icc 1 M → (∀ q ∈ Q, |rho q| ≤ 1) →
      |wordError N t cs Q rho
        (fun x => trimRemainder ((N : ℝ)^(1-kappa)) (product (t.1*t.2) x))| ≤
          eta*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨C,D,hC,hD,hbudget⟩ := exists_word_low_product_budget cs
    (show 0 < kappa/4 by positivity)
  filter_upwards
    [P5OriginalSingletonLowerTrimPaid.eventually_originalLowerCut_lt kappa hkappa hkappa1,
      eventually_powerLog_le_logAccuracy (3*C*D) (1-kappa/2) 0 A
        (by linarith) (eta/3) (by positivity),
      eventually_powerLog_le_logAccuracy (12*C) (1-3*kappa/4) 0 A
        (by linarith) (eta/3) (by positivity),
      eventually_powerLog_le_logAccuracy (12*C) (1-3*kappa/4) 1 A
        (by linarith) (eta/3) (by positivity),
      eventually_ge_atTop (2 : ℕ)] with N hcut hAP hM0 hM1 hN
  intro t ht M Q rho hMN hQ hrho
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hH : 0 < (N : ℝ)^(1-kappa) := Real.rpow_pos_of_pos hNpos _
  have hw (x : Label) :
      |trimRemainder ((N : ℝ)^(1-kappa)) (product (t.1*t.2) x)| ≤ 1 := by
    have h := trimRemainder_range ((N : ℝ)^(1-kappa)) (product (t.1*t.2) x)
    simpa only [abs_of_nonneg h.1] using h.2
  have hz (x : Label) (hx : originalLowerCut kappa N < product (t.1*t.2) x) :
      trimRemainder ((N : ℝ)^(1-kappa)) (product (t.1*t.2) x)=0 := by
    apply trimRemainder_eq_zero hH
    exact (Nat.le_ceil (2*(N : ℝ)^(1-kappa))).trans
      (by exact_mod_cast hx.le)
  have hbound := hbudget N (originalLowerCut kappa N) M t ht Q rho _
    hcut.1 hQ hrho (fun x _ => hw x) (fun x _ hx => hz x hx)
  have hlog : Real.log (max 1 (M : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hN1 (by exact_mod_cast hMN))
  have hB0 : 0 ≤ D*(N : ℝ)^(kappa/4)+4*(1+Real.log (max 1 (M : ℝ))) := by
    have hl := Real.log_nonneg (le_max_left (1 : ℝ) (M : ℝ))
    positivity
  have hp1 : (N : ℝ)^(1-kappa)*(N : ℝ)^(kappa/4) =
      (N : ℝ)^(1-3*kappa/4) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hp2 : (N : ℝ)^(1-3*kappa/4)*(N : ℝ)^(kappa/4) =
      (N : ℝ)^(1-kappa/2) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  calc
    _ ≤ (3*(N : ℝ)^(1-kappa))*(C*(N : ℝ)^(kappa/4))*
        (D*(N : ℝ)^(kappa/4)+4*(1+Real.log (N : ℝ))) := by
      apply hbound.trans
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hcut.2 (by positivity))
        (by linarith) hB0 (by positivity)
    _ = 3*C*D*(N : ℝ)^(1-kappa/2)+12*C*(N : ℝ)^(1-3*kappa/4)+
        12*C*(N : ℝ)^(1-3*kappa/4)*Real.log (N : ℝ) := by
      calc
        _ = 3*C*D*((N : ℝ)^(1-kappa)*(N : ℝ)^(kappa/4))*(N : ℝ)^(kappa/4)+
            12*C*((N : ℝ)^(1-kappa)*(N : ℝ)^(kappa/4))+
            12*C*((N : ℝ)^(1-kappa)*(N : ℝ)^(kappa/4))*Real.log (N : ℝ) := by ring
        _ = _ := by rw [hp1]; rw [mul_assoc (3*C*D),hp2]
    _ ≤ _ := by
      simp only [pow_zero,pow_one,mul_one] at hAP hM0 hM1
      linarith

/-- Exact same-q source reconstruction for the chosen smooth trim. -/
theorem gammaDiscrepancy_eq_trim_add_remainder (N : ℕ) (t : ℕ × ℕ)
    (q : ℕ) (H : ℝ) :
    gammaDiscrepancy N t q =
      sourceTest N t (fun m => smoothTrim H m*gammaKernel N q m)+
      sourceTest N t (fun m => trimRemainder H m*gammaKernel N q m) := by
  have hrem : (fun m => trimRemainder H m*gammaKernel N q m) =
      (fun m => gammaKernel N q m-smoothTrim H m*gammaKernel N q m) := by
    funext m
    dsimp [trimRemainder]
    ring
  rw [hrem,sourceTest_sub]
  unfold gammaDiscrepancy
  ring

def listTrimError (L : List (List ℕ)) (N : ℕ) (t : ℕ × ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (H : ℝ) : ℝ :=
  (L.map (fun cs => wordError N t cs Q rho
    (fun x => trimRemainder H (product (t.1*t.2) x)))).sum

/-- Finite occurrence assembly uses induction on the actual list.  It
does not evaluate a finite guard or erase repeated colour words. -/
theorem eventually_list_smoothTrim_logAccuracy (L : List (List ℕ))
    (kappa : ℝ) (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (A : ℕ) :
    ∀ eta : ℝ, 0 < eta →
      ∀ᶠ N : ℕ in atTop, ∀ t ∈ pairSupport N, ∀ (M : ℕ)
        (Q : Finset ℕ) (rho : ℕ → ℝ),
        M ≤ N → Q ⊆ Finset.Icc 1 M → (∀ q ∈ Q, |rho q| ≤ 1) →
        |listTrimError L N t Q rho ((N : ℝ)^(1-kappa))| ≤
          eta*(N : ℝ)/Real.log (N : ℝ)^A := by
  induction L with
  | nil =>
      intro eta heta
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      intro t ht M Q rho hMN hQ hrho
      have hlog : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
      simp only [listTrimError,List.map_nil,List.sum_nil,abs_zero]
      positivity
  | cons cs L ih =>
      intro eta heta
      filter_upwards
        [eventually_word_smoothTrim_logAccuracy cs kappa hkappa hkappa1 A
          (eta/2) (by positivity), ih (eta/2) (by positivity)] with N hword htail
      intro t ht M Q rho hMN hQ hrho
      have hw := hword t ht M Q rho hMN hQ hrho
      have hl := htail t ht M Q rho hMN hQ hrho
      change |wordError N t cs Q rho
        (fun x => trimRemainder ((N : ℝ)^(1-kappa)) (product (t.1*t.2) x))+
          listTrimError L N t Q rho ((N : ℝ)^(1-kappa))| ≤ _
      exact (abs_add _ _).trans ((add_le_add hw hl).trans_eq (by ring))

private theorem list_mul_sum {α : Type*} (L : List α) (r : ℝ) (f : α → ℝ) :
    r*(L.map f).sum = (L.map (fun a => r*f a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,mul_add,ih]

private theorem list_finset_comm {α : Type*} (L : List α) (Q : Finset ℕ)
    (f : ℕ → α → ℝ) :
    (∑ q ∈ Q, (L.map (f q)).sum) =
      (L.map (fun a => ∑ q ∈ Q, f q a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

private theorem list_flatMap_sum {α β : Type*} (I : List α)
    (J : α → List β) (f : β → ℝ) :
    ((I.flatMap J).map f).sum =
      (I.map (fun i => ((J i).map f).sum)).sum := by
  induction I with
  | nil => simp
  | cons i I ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,ih]

def originalMotherOccurrences : List (List ℕ) :=
  Wu2008DoubleSieve.secondFunctionalMotherPrefixIndices.flatMap
    Wu2008DoubleSieve.secondFunctionalMotherGammaWords

/-- This equality binds the finite-list theorem to sourceTest itself.
No numerical occurrence count or deduplicated set is substituted. -/
theorem gamma_trim_sum_eq_literal_list (N : ℕ) (t : ℕ × ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (H : ℝ) :
    (∑ q ∈ Q, rho q * sourceTest N t
      (fun m => trimRemainder H m * gammaKernel N q m)) =
        listTrimError originalMotherOccurrences N t Q rho H := by
  have hsource (q : ℕ) : rho q * sourceTest N t
      (fun m => trimRemainder H m * gammaKernel N q m) =
      (originalMotherOccurrences.map (fun cs => rho q *
        ∑ x ∈ rootLabels N t cs,
          trimRemainder H (product (t.1*t.2) x)*
            gammaKernel N q (product (t.1*t.2) x))).sum := by
    unfold sourceTest originalMotherOccurrences
    rw [list_flatMap_sum]
    rw [list_mul_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    exact list_mul_sum _ _ _
  simp_rw [hsource]
  rw [list_finset_comm]
  rfl

/-- FULL original mother-list smooth-trim payment.  A single threshold
precedes every old marked pair, q-set, and bounded signed coefficient.
This is only the lower complete-product restoration, not full Gamma BV. -/
theorem eventually_original_Gamma_smoothTrim_logAccuracy
    (kappa : ℝ) (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ pairSupport N, ∀ (M : ℕ)
      (Q : Finset ℕ) (rho : ℕ → ℝ),
      M ≤ N → Q ⊆ Finset.Icc 1 M → (∀ q ∈ Q, |rho q| ≤ 1) →
      |∑ q ∈ Q, rho q * (gammaDiscrepancy N t q -
        sourceTest N t (fun m => smoothTrim ((N : ℝ)^(1-kappa)) m *
          gammaKernel N q m))| ≤ eta*(N : ℝ)/Real.log (N : ℝ)^A := by
  filter_upwards [eventually_list_smoothTrim_logAccuracy originalMotherOccurrences
    kappa hkappa hkappa1 A eta heta] with N hN
  intro t ht M Q rho hMN hQ hrho
  have hsplit (q : ℕ) : gammaDiscrepancy N t q -
      sourceTest N t (fun m => smoothTrim ((N : ℝ)^(1-kappa)) m *
        gammaKernel N q m) =
      sourceTest N t (fun m => trimRemainder ((N : ℝ)^(1-kappa)) m *
        gammaKernel N q m) := by
    rw [gammaDiscrepancy_eq_trim_add_remainder N t q ((N : ℝ)^(1-kappa))]
    ring
  simp_rw [hsplit]
  rw [gamma_trim_sum_eq_literal_list]
  exact hN t ht M Q rho hMN hQ hrho

end
end ImbalancedChen.P2GammaCompleteProductTrimPayment
