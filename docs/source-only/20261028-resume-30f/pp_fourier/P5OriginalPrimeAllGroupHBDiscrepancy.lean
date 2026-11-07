import ImbalancedChen.P5IndependentPrimeSourceWordDictionary
import ImbalancedChen.P5ActualEtaPsiOccurrenceBudget

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
An identity for the ORIGINAL independent prime-test discrepancy, through
the actual ALL-group rough Lambda/log HB atlas. Trim, rough-projector and
proper-prime-power corrections are explicit sums on independent u, never
physical modulus residuals. The physical Q/rho and exact coprime mean stay
unchanged. No correction estimate, final source identity or PP conclusion
is a premise. This still precedes the occurrence flattening and the real
log-normalized smooth profile needed to apply the paid Fourier tail.
-/
namespace ImbalancedChen.P5Z.OriginalPrimeAllGroupHBDiscrepancy
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open IndependentPrimeSourceWordDictionary LicensedOriginalIntegerProfile
open ExactOriginalSmoothDyadicPartition ActualLabelledPrimeSmoothCharts
open PerGroupIntegerHBAtlasPushforward
open ImbalancedChen.Part3.AllKLambdaChartCorrection
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open AdmissibleAllRankIntegerGeometricFamily

theorem actual_chi_one {s : ℝ} (hs : s ≤ 1) : ActualEtaPsiOccurrenceBudget.chi s = 1 := by
  simp only [ActualEtaPsiOccurrenceBudget.chi, ActualEtaPsiOccurrenceBudget.eta_zero hs, sub_zero]

theorem actual_chi_zero {s : ℝ} (hs : 2 ≤ s) : ActualEtaPsiOccurrenceBudget.chi s = 0 := by
  simp only [ActualEtaPsiOccurrenceBudget.chi, ActualEtaPsiOccurrenceBudget.eta_one hs, sub_self]

/-- This is the manuscript cutoff f(2^(6K+2) Xplus), fixed from ORIGINAL
smooth chart labels before HB order, variables and any selected slot. -/
theorem original_cutoff_nonneg (K : ℕ) (js : List ℕ) : 0 ≤ beforeHBCutoff K js := by
  unfold beforeHBCutoff OriginalChartRoughCutoff.chartCutoff OriginalChartRoughCutoff.roughF
  apply Real.rpow_nonneg
  unfold OriginalChartRoughCutoff.argument
  apply mul_nonneg (by positivity)
  apply mul_nonneg (by positivity)
  apply List.prod_nonneg
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact (R_pos j).le

def originalChart {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (T : ℕ) (κ₀ : ℝ) (js ps : List ℕ) : ℂ :=
  chartTerm ActualEtaPsiOccurrenceBudget.chi ActualEtaPsiOccurrenceBudget.eta
    (fun u => (listExtension L u : ℂ)) (T : ℝ) κ₀ js ps

/-- The actual full group atlas, still indexed by the original complete
word ps. Each row factors ONE original independent coordinate; its real
HB cutoff and every original group denominator log(n_i) are retained. -/
def allGroupAtlas {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (K cap T : ℕ) (κ₀ : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ integerWords cap k,
    atlasEval ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K js) js ps (fun rows =>
      (listExtension L (originalProducts rows) : ℂ) *
        (ActualEtaPsiOccurrenceBudget.eta
          (((originalProducts rows).prod : ℝ) / (T : ℝ) ^ (1 - κ₀)) : ℂ) *
        wordKernel Q rho T (originalProducts rows))

def properPowerReserve {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (K cap T : ℕ) (κ₀ : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ properChartWords cap k, lambdaWord ps * originalChart L T κ₀ js ps *
    (roughWord (beforeHBCutoff K js) ps * wordKernel Q rho T ps)

def roughPrimeReserve {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (K cap T : ℕ) (κ₀ : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) : ℂ :=
  ∑ ps ∈ primeTuples cap k, originalChart L T κ₀ js ps *
    (1 - roughWord (beforeHBCutoff K js) ps) * wordKernel Q rho T ps

def trimReserve {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (cap T : ℕ) (κ₀ : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) : ℂ :=
  ∑ ps ∈ primeTuples cap k,
    (1 - (ActualEtaPsiOccurrenceBudget.eta ((ps.prod : ℝ) / (T : ℝ) ^ (1 - κ₀)) : ℂ)) *
      (listExtension L ps : ℂ) * wordKernel Q rho T ps

/-- Reuses the independently proved ALL-group atlas pushforward and
the actual Lambda/log prime-versus-proper-power dictionary. The reserve
is its actual proper-prime-power carrier, not a named unknown error. -/
theorem allGroupAtlas_prime_proper {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (K cap T : ℕ) (κ₀ : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) :
    allGroupAtlas L K cap T κ₀ Q rho js =
      (∑ ps ∈ primeTuples cap k, originalChart L T κ₀ js ps *
        (roughWord (beforeHBCutoff K js) ps * wordKernel Q rho T ps)) +
      properPowerReserve L K cap T κ₀ Q rho js := by
  simpa only [allGroupAtlas, originalChart, properPowerReserve] using
    licensed_atlas_all_k_prime_plus_proper L cap ActualEtaPsiOccurrenceBudget.chi
      ActualEtaPsiOccurrenceBudget.eta (fun _ hs => actual_chi_one hs)
      (fun _ hs => actual_chi_zero hs) (original_cutoff_nonneg K js)
      (T : ℝ) κ₀ js [] (fun _ ps => wordKernel Q rho T ps)

theorem original_chart_allGroup_exact {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (K cap T : ℕ) (κ₀ : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (js : List ℕ) :
    (∑ ps ∈ primeTuples cap k, originalChart L T κ₀ js ps * wordKernel Q rho T ps) =
      allGroupAtlas L K cap T κ₀ Q rho js - properPowerReserve L K cap T κ₀ Q rho js +
        roughPrimeReserve L K cap T κ₀ Q rho js := by
  have hsplit :
      (∑ ps ∈ primeTuples cap k, originalChart L T κ₀ js ps * wordKernel Q rho T ps) =
      (∑ ps ∈ primeTuples cap k, originalChart L T κ₀ js ps *
        (roughWord (beforeHBCutoff K js) ps * wordKernel Q rho T ps)) +
        roughPrimeReserve L K cap T κ₀ Q rho js := by
    unfold roughPrimeReserve
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ps hps
    ring
  rw [allGroupAtlas_prime_proper]
  calc
    _ = _ := hsplit
    _ = _ := by ring

/-- The original Part3 prime-test source is reconstructed, with every
original dyadic chart and every group HB-expanded. There is no equality
premise between an independently defined source and a proposed atlas.
The same signed rho occurs inside ALL three explicit corrections. -/
theorem original_prime_allGroup_discrepancy {k : ℕ}
    {Wprime : (Fin k → ℕ) → ℝ} (L : Licence k Wprime)
    (K cap T : ℕ) (κ₀ : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (Part3.primeProductSignedError k cap T Q rho
      (fun u => Wprime (fun i => (u i).val)) : ℂ) =
      trimReserve L cap T κ₀ Q (fun q => (rho q : ℂ)) +
        ∑ js ∈ chartBank cap k,
          (allGroupAtlas L K cap T κ₀ Q (fun q => (rho q : ℂ)) js -
            properPowerReserve L K cap T κ₀ Q (fun q => (rho q : ℂ)) js +
              roughPrimeReserve L K cap T κ₀ Q (fun q => (rho q : ℂ)) js) := by
  rw [licensed_original_discrepancy_words L cap T Q rho]
  change (∑ ps ∈ primeTuples cap k, (listExtension L ps : ℂ) *
    wordKernel Q (fun q => (rho q : ℂ)) T ps) = _
  let W : List ℕ → ℂ := fun ps => (listExtension L ps : ℂ)
  let F : List ℕ → ℂ := wordKernel Q (fun q => (rho q : ℂ)) T
  have htrim :
      (∑ ps ∈ primeTuples cap k, W ps * F ps) =
      trimReserve L cap T κ₀ Q (fun q => (rho q : ℂ)) +
        ∑ ps ∈ primeTuples cap k, trimmedWeight ActualEtaPsiOccurrenceBudget.eta W (T : ℝ) κ₀ ps * F ps := by
    unfold trimReserve trimmedWeight
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ps hps
    dsimp [W, F]
    ring
  rw [htrim, original_prime_sum_charts ActualEtaPsiOccurrenceBudget.chi
    ActualEtaPsiOccurrenceBudget.eta W F (fun _ hs => actual_chi_one hs)
    (fun _ hs => actual_chi_zero hs) cap k (T : ℝ) κ₀]
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  exact original_chart_allGroup_exact L K cap T κ₀ Q (fun q => (rho q : ℂ)) js

/-- All genuinely PRESENT original test ranks can be restored with their
unchanged signed scalars. The rank carrier is independent data; this
This does not manufacture an actual caller/rank coverage certificate. -/
theorem present_rank_original_allGroup {kStar : ℕ} (A : Family kStar)
    (ranks : Finset (Fin (kStar + 1))) (scalar : Fin (kStar + 1) → ℂ)
    (cap T : ℕ) (κ₀ : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ k ∈ ranks, scalar k *
      (Part3.primeProductSignedError k.val cap T Q rho
        (fun u => originalWeight A T k (fun i => (u i).val)) : ℂ)) =
      ∑ k ∈ ranks, scalar k *
        (trimReserve (licence A T k) cap T κ₀ Q (fun q => (rho q : ℂ)) +
          ∑ js ∈ chartBank cap k.val,
            (allGroupAtlas (licence A T k) kStar cap T κ₀ Q (fun q => (rho q : ℂ)) js -
              properPowerReserve (licence A T k) kStar cap T κ₀ Q (fun q => (rho q : ℂ)) js +
                roughPrimeReserve (licence A T k) kStar cap T κ₀ Q (fun q => (rho q : ℂ)) js)) := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [original_prime_allGroup_discrepancy (licence A T k) kStar cap T κ₀ Q rho]

end
end ImbalancedChen.P5Z.OriginalPrimeAllGroupHBDiscrepancy
