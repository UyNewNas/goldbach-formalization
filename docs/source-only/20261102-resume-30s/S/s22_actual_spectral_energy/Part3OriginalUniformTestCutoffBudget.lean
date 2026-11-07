import ImbalancedChen.Part3OriginalFullModulusTestJets
import ImbalancedChen.Part3OriginalSixTailPhysicalPayment
import ImbalancedChen.Part3OriginalAdditionalSpectralCosts

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original full-modulus test family is bound at its actual Poisson
ratio V*M/N, for every one of the six physical pieces.  The same eta/2
cutoff is used for the original six-tail.  No spectral data, energy
inequality, PacketData adapter, or Bessel replacement is introduced.

Fix the test-derivative order first.  Its already proved Fourier cost
is 4*(n+3)*eta.  Multiplication by the degree-two cutoff debit gives
(4*(n+3)+2)*eta: 14*eta at n=0, 30*eta at n=4.  These are alternative
orders of the SAME test family, not extra charges to add to an already
paid 28*eta J estimate.  The final +eta absorbs the fixed constant.

The final theorem selects eta, then the unrelated Schwartz-tail order,
then one threshold before all moving original-source parameters.  It
does not supply normalized Kuznetsov, A/J, regular norms, ABL, a gap,
zero-lane normalization, or the total outer-family cost.
-/

noncomputable section
open Classical Finset Filter
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff spectralTest)
open P3ActualWeightedSpectralBudgetSourceOnly
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalFullModulusSupport20261102
open ImbalancedChen.Part3.OriginalFullModulusTestJets20261102
open ImbalancedChen.Part3.OriginalSixTailBinding20261102
open ImbalancedChen.Part3.OriginalSixTailPhysicalPayment20261102
open ImbalancedChen.Part3.OriginalAdditionalSpectralCosts20261102

namespace ImbalancedChen.Part3.OriginalUniformTestCutoffBudget20261102

/-- The derivative mass already proved for the actual Fourier family,
together with the single degree-two cutoff inflation. -/
def testCutoffOrder (n : ℕ) : ℕ := 4 * (n + 3) + 2

theorem testCutoffOrder_zero : testCutoffOrder 0 = 14 := by
  norm_num [testCutoffOrder]

theorem testCutoffOrder_four : testCutoffOrder 4 = 30 := by
  norm_num [testCutoffOrder]

/-- Monotonicity is proved for the actual Fourier coefficients.  Thus
lower derivative orders use the same W_d, not additional Fourier fees. -/
theorem actualW_mono_order (rho sign : ℝ) {n d : ℕ} (hnd : n ≤ d) :
    actualW rho sign n ≤ actualW rho sign d := by
  change (∑' ell : D4 → ℤ, ‖actualCoeff rho sign ell‖ *
      (1 + |(ell 0 : ℝ)|) ^ n) ≤
    ∑' ell : D4 → ℤ, ‖actualCoeff rho sign ell‖ * (1 + |(ell 0 : ℝ)|) ^ d
  apply (actual_mode_weight_summable rho sign n).tsum_le_tsum
    (fun ell => ?_) (actual_mode_weight_summable rho sign d)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith [abs_nonneg (ell 0 : ℝ)]) hnd) (norm_nonneg _)

def normalizedTestJetMass (d : ℕ) (rho sign Y q : ℝ) : ℝ :=
  ∑ n ∈ range (d + 1), Y ^ n *
    (∑' ell : D4 → ℤ, ‖actualCoeff rho sign ell‖ *
      ‖iteratedDeriv n (spectralTest ell Y) q‖)

def finiteTestJetConstant (d : ℕ) : ℝ :=
  1 + ∑ n ∈ range (d + 1), testJetConstant n

theorem finiteTestJetConstant_pos (d : ℕ) : 0 < finiteTestJetConstant d := by
  have hs : 0 ≤ ∑ n ∈ range (d + 1), testJetConstant n :=
    sum_nonneg (fun n _ => (testJetConstant_pos n).le)
  unfold finiteTestJetConstant
  linarith

/-- At each common q, the whole normalized finite derivative mass has
ONE W_d, uniformly in q.  This is not the sum of per-mode supremum
norms.  Orders zero through four jointly use W_4 and its 28*eta cost. -/
theorem normalizedTestJetMass_le (d : ℕ) (rho sign q : ℝ)
    {Y : ℝ} (hY : 0 < Y) :
    normalizedTestJetMass d rho sign Y q ≤
      finiteTestJetConstant d * actualW rho sign d := by
  have hterm (n : ℕ) (hn : n ∈ range (d + 1)) :
      Y ^ n * (∑' ell : D4 → ℤ, ‖actualCoeff rho sign ell‖ *
        ‖iteratedDeriv n (spectralTest ell Y) q‖) ≤
      testJetConstant n * actualW rho sign d := by
    have hnd : n ≤ d := by have := mem_range.mp hn; omega
    have hh := (actual_weighted_test_jets_budget rho sign n hY q).trans
      (mul_le_mul_of_nonneg_left (actualW_mono_order rho sign hnd)
        (div_nonneg (testJetConstant_pos n).le (pow_nonneg hY.le n)))
    apply (mul_le_mul_of_nonneg_left hh (pow_nonneg hY.le n)).trans_eq
    field_simp [pow_ne_zero n hY.ne'] <;> ring
  calc
    _ ≤ ∑ n ∈ range (d + 1), testJetConstant n * actualW rho sign d :=
      sum_le_sum hterm
    _ = (∑ n ∈ range (d + 1), testJetConstant n) * actualW rho sign d := by
      rw [Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (actualW_nonneg rho sign d)
      unfold finiteTestJetConstant
      linarith

/-- One constant for the actual tests at the actual ratio of every
original six-piece scale.  There is no assumed rho or derivative bound.
The original eta/2 cutoff, including its ceil endpoint, supplies rho. -/
theorem exists_original_six_jet_cutoff_constant (n : ℕ) {eta : ℝ}
    (heta : 0 < eta) :
    ∃ K X : ℝ, 0 < K ∧ 1 ≤ X ∧
      ∀ (D : OriginalData) (x : ℝ), X ≤ x →
      ∀ (j : ℕ) (M N : ℝ), 0 < M → 0 < N →
        M ≤ 2 * D.bScale → D.cScale ≤ N →
        (commonMBlock (globalCutoff D x (eta / 2)) j).Nonempty →
      ∀ sign : ℝ, |sign| ≤ 1 → ∀ Y : ℝ, 0 < Y → ∀ q : ℝ,
        x ^ (2 * eta) *
          (∑' ell : D4 → ℤ,
            ‖actualCoeff ((((2 : ℕ) ^ j : ℝ) * M) / N) sign ell‖ *
              ‖iteratedDeriv n (spectralTest ell Y) q‖) ≤
          K * x ^ ((testCutoffOrder n : ℝ) * eta) / Y ^ n := by
  obtain ⟨B, hB, hbudget⟩ := actual_uniform_xeta_weighted_budget n
  obtain ⟨X, hX, hrho⟩ := exists_globalCutoff_six_rho_threshold heta
  refine ⟨testJetConstant n * B, X,
    mul_pos (testJetConstant_pos n) hB, hX, ?_⟩
  intro D x hx j M N hM hN hMB hCN hne sign hsign Y hY q
  have hx1 : 1 ≤ x := hX.trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  let rho : ℝ := (((2 : ℕ) ^ j : ℝ) * M) / N
  have hrho0 : 0 ≤ rho := by dsimp [rho]; positivity
  have hrhox : rho ≤ x ^ eta := hrho D x hx j M N hM hN hMB hCN hne
  have hw : actualW rho sign n ≤ B * x ^ ((4 * (n + 3) : ℕ) * eta) :=
    (hbudget x hx1 eta heta.le rho hrho0 hrhox sign hsign).2.1
  have hj := actual_weighted_test_jets_budget rho sign n hY q
  have hj' := hj.trans (mul_le_mul_of_nonneg_left hw
    (div_nonneg (testJetConstant_pos n).le (pow_nonneg hY.le n)))
  have hh := mul_le_mul_of_nonneg_left hj' (Real.rpow_nonneg hx0.le (2 * eta))
  change x ^ (2 * eta) *
    (∑' ell : D4 → ℤ, ‖actualCoeff rho sign ell‖ *
      ‖iteratedDeriv n (spectralTest ell Y) q‖) ≤ _
  apply hh.trans_eq
  have he : 2 * eta + (4 * (n + 3) : ℕ) * eta =
      (testCutoffOrder n : ℝ) * eta := by
    unfold testCutoffOrder
    push_cast
    ring
  calc
    _ = (testJetConstant n * B) *
        (x ^ (2 * eta) * x ^ ((4 * (n + 3) : ℕ) * eta)) / Y ^ n := by ring
    _ = _ := by rw [← Real.rpow_add hx0, he]

/-- All derivatives through the fixed order d are paid simultaneously,
at the original ratio V*M/N and the common eta/2 cutoff. -/
theorem exists_original_six_testSeminorm_cutoff_constant (d : ℕ) {eta : ℝ}
    (heta : 0 < eta) :
    ∃ K X : ℝ, 0 < K ∧ 1 ≤ X ∧
      ∀ (D : OriginalData) (x : ℝ), X ≤ x →
      ∀ (j : ℕ) (M N : ℝ), 0 < M → 0 < N →
        M ≤ 2 * D.bScale → D.cScale ≤ N →
        (commonMBlock (globalCutoff D x (eta / 2)) j).Nonempty →
      ∀ sign : ℝ, |sign| ≤ 1 → ∀ Y : ℝ, 0 < Y → ∀ q : ℝ,
        x ^ (2 * eta) *
          normalizedTestJetMass d ((((2 : ℕ) ^ j : ℝ) * M) / N) sign Y q ≤
          K * x ^ ((testCutoffOrder d : ℝ) * eta) := by
  obtain ⟨B, hB, hbudget⟩ := actual_uniform_xeta_weighted_budget d
  obtain ⟨X, hX, hrho⟩ := exists_globalCutoff_six_rho_threshold heta
  refine ⟨finiteTestJetConstant d * B, X,
    mul_pos (finiteTestJetConstant_pos d) hB, hX, ?_⟩
  intro D x hx j M N hM hN hMB hCN hne sign hsign Y hY q
  have hx1 : 1 ≤ x := hX.trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  let rho : ℝ := (((2 : ℕ) ^ j : ℝ) * M) / N
  have hrho0 : 0 ≤ rho := by dsimp [rho]; positivity
  have hrhox : rho ≤ x ^ eta := hrho D x hx j M N hM hN hMB hCN hne
  have hw : actualW rho sign d ≤ B * x ^ ((4 * (d + 3) : ℕ) * eta) :=
    (hbudget x hx1 eta heta.le rho hrho0 hrhox sign hsign).2.1
  have hj := (normalizedTestJetMass_le d rho sign q hY).trans
    (mul_le_mul_of_nonneg_left hw (finiteTestJetConstant_pos d).le)
  have hh := mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hx0.le (2 * eta))
  apply hh.trans_eq
  have he : 2 * eta + (4 * (d + 3) : ℕ) * eta =
      (testCutoffOrder d : ℝ) * eta := by
    unfold testCutoffOrder
    push_cast
    ring
  calc
    _ = (finiteTestJetConstant d * B) *
        (x ^ (2 * eta) * x ^ ((4 * (d + 3) : ℕ) * eta)) := by ring
    _ = _ := by rw [← Real.rpow_add hx0, he]

/-- Reserve only the requested allowance and the original sigma/10
margin.  This does not assert that the remaining outer costs fit here. -/
def testAllowance (epsilon sigma : ℝ) : ℝ := min epsilon (sigma / 10)

def testEta (n : ℕ) (epsilon sigma : ℝ) : ℝ :=
  testAllowance epsilon sigma / ((testCutoffOrder n : ℝ) + 1)

theorem testEta_hierarchy (n : ℕ) {epsilon sigma : ℝ}
    (hepsilon : 0 < epsilon) (hsigma : 0 < sigma) :
    0 < testEta n epsilon sigma ∧
      testEta n epsilon sigma ≤ epsilon ∧
      testEta n epsilon sigma ≤ sigma / 10 ∧
      ((testCutoffOrder n : ℝ) + 1) * testEta n epsilon sigma =
        testAllowance epsilon sigma := by
  have ha : 0 < testAllowance epsilon sigma :=
    lt_min hepsilon (div_pos hsigma (by norm_num))
  have hd : 0 < (testCutoffOrder n : ℝ) + 1 := by positivity
  have hd1 : 1 ≤ (testCutoffOrder n : ℝ) + 1 := by
    have hd0 : (0 : ℝ) ≤ (testCutoffOrder n : ℝ) := Nat.cast_nonneg _
    linarith
  have he : 0 < testEta n epsilon sigma := div_pos ha hd
  have hle : testEta n epsilon sigma ≤ testAllowance epsilon sigma := by
    change testAllowance epsilon sigma / ((testCutoffOrder n : ℝ) + 1) ≤ _
    exact div_le_self ha.le hd1
  refine ⟨he, hle.trans (min_le_left _ _), hle.trans (min_le_right _ _), ?_⟩
  unfold testEta
  field_simp [hd.ne'] <;> ring

/-- Simultaneous original-source preparation.  The one threshold serves
both the actual test family (including the cutoff debit) and the existing
actual six-tail.  The reserve parameters epsilon and sigma are fixed;
X precedes b, admissibility s, kappa, c0, atom, atlas, labels and modes.
The tail order is selected after eta and affects a constant only; it is
not the test-derivative order n and is not put back into testCutoffOrder.

This is a theorem about the stated two actual costs, not the whole
spectral return.  The retained phase, one D, zero lanes, classical norms,
normalization and outer signed/scalar multiplicities remain separate.
-/
theorem exists_original_six_test_and_tail_threshold (n : ℕ)
    (epsilon sigma A : ℝ) (hepsilon : 0 < epsilon) (hsigma : 0 < sigma)
    (hA : 0 ≤ A) :
    ∃ dord : ℕ, 2 ≤ dord ∧
      34 + A ≤ (testEta n epsilon sigma / 2) * ((dord - 1 : ℕ) : ℝ) ∧
      ∃ X : ℝ, 1 ≤ X ∧
      (∀ (D : OriginalData) (x : ℝ), X ≤ x →
        ∀ (j : ℕ) (M N : ℝ), 0 < M → 0 < N →
          M ≤ 2 * D.bScale → D.cScale ≤ N →
          (commonMBlock (globalCutoff D x (testEta n epsilon sigma / 2)) j).Nonempty →
        ∀ sign : ℝ, |sign| ≤ 1 → ∀ Y : ℝ, 0 < Y → ∀ q : ℝ,
          x ^ (2 * testEta n epsilon sigma) *
            normalizedTestJetMass n ((((2 : ℕ) ^ j : ℝ) * M) / N) sign Y q ≤
            x ^ (testAllowance epsilon sigma)) ∧
      (∀ (b : ℕ) (s kappa c0 : ℝ) (atom : MediumAtom)
        (hAdm : MediumAdmissible b s kappa c0 atom),
        0 ≤ s → X ≤ atom.scale →
        ∀ (z y : ℝ) (k : Key), k ∈ keyBank atom z y →
        ∀ (Csep : ℕ) (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k)
          (negative : Bool) (rectangle : Rectangle) (st st' : ℕ × ℕ)
          (polarS polarR polarN : Fin 4),
        let D := tightOriginalData atom z y k hAdm Csep j small hd negative
          rectangle st st' polarS polarR polarN
        ∀ r : ZMod (prefixPeriod D.key),
          ‖sixTail D r (globalCutoff D atom.scale (testEta n epsilon sigma / 2))‖ ≤
            atom.scale ^ (-A)) := by
  have heta := (testEta_hierarchy n hepsilon hsigma).1
  obtain ⟨K, Xjet, hK, hXjet, hjets⟩ :=
    exists_original_six_testSeminorm_cutoff_constant n heta
  obtain ⟨dord, hdord, horder, Xtail, hXtail, htail⟩ :=
    exists_tight_original_sixTail_threshold A (testEta n epsilon sigma) hA heta
  obtain ⟨Xconst, hconst⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop heta).eventually_ge_atTop K)
  let X := max Xjet (max Xtail Xconst)
  refine ⟨dord, hdord, horder, X, hXjet.trans (le_max_left _ _), ?_, ?_⟩
  · intro D x hx j M N hM hN hMB hCN hne sign hsign Y hY q
    have hxjet : Xjet ≤ x := (le_max_left _ _).trans hx
    have hx1 : 1 ≤ x := hXjet.trans hxjet
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have hxconst : Xconst ≤ x :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
    have hKx : K ≤ x ^ (testEta n epsilon sigma) := hconst x hxconst
    have hh := hjets D x hxjet j M N hM hN hMB hCN hne sign hsign Y hY q
    have he : testEta n epsilon sigma +
        (testCutoffOrder n : ℝ) * testEta n epsilon sigma =
        testAllowance epsilon sigma := by
      have hh := (testEta_hierarchy n hepsilon hsigma).2.2.2
      nlinarith only [hh]
    apply hh.trans
    calc
      _ ≤ x ^ (testEta n epsilon sigma) *
          x ^ ((testCutoffOrder n : ℝ) * testEta n epsilon sigma) :=
        mul_le_mul_of_nonneg_right hKx (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0, he]
  · intro b s kappa c0 atom hAdm hs hx z y k hk Csep j small hd
      negative rectangle st st' polarS polarR polarN
    have hxtail : Xtail ≤ atom.scale :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
    exact htail b s kappa c0 atom hAdm hs hxtail z y k hk Csep j small hd
      negative rectangle st st' polarS polarR polarN

end ImbalancedChen.Part3.OriginalUniformTestCutoffBudget20261102
end
