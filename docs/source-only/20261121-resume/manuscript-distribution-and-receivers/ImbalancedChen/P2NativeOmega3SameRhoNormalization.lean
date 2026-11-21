import ImbalancedChen.P2NativeOmega3RankTupleReceiver
import MathlibNt.Wu2008DoubleSieve.OmegaSwitchedIntegral
import ImbalancedChen.CurrentChenInitialSource

/-!
SOURCE ONLY / UNCOMPILED.

The NEW independent prime family's unsifted mass is bounded by the existing
closed native X, then transported by the already proved Buchstab/integral/
Theta suppliers. No switched-sieve count estimate is reused as a product-K
estimate. The physical density hypothesis is exactly the existing same-rho
primitive; signed PP, coprime and small-prime terms remain explicit.

K is a density coefficient parameter. It is not identified here with
currentK, historical K1, K2, or an endpoint/table coefficient.
-/
namespace ImbalancedChen.P2NativeOmega3SameRhoNormalization

noncomputable section
open Finset Real Wu2008DoubleSieve
open P2NativeOmega3PrimeOutputFamily
open scoped Classical BigOperators

/-- Exact source mass reindexing, followed only by the native closed-p3
enlargement. The convolution coefficient remains once per cofactor label. -/
theorem source_mass_le_native_X {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    p5z_labelledMass (labels N δ s t W) (weight W) ≤ omega3SieveX N δ s t W := by
  have hreindex :
      p5z_labelledMass (labels N δ s t W) (weight W) =
        ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1:ℝ) *
          ((omega3CofactorPrimeFibre N δ s c).card:ℝ) := by
    simpa only [p5z_labelledMass,labels,weight,mul_one,sum_const,nsmul_eq_mul,mul_one]
      using omega3_cofactor_first_sum N δ s t W (fun _ => 1)
  rw [hreindex]
  unfold omega3SieveX
  apply sum_le_sum
  intro c hc
  rcases c with ⟨d,p2,p1,n⟩
  obtain ⟨hd',h2,h1,_hnN,hn,_hsize,_hgood⟩ := mem_omega3CofactorLabels.mp hc
  have he : 0 < omega3CofactorValue ⟨d,p2,p1,n⟩ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hd d hd') hn) (mem_primeWindow.mp h1).1.pos)
      (mem_primeWindow.mp h2).1.pos
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (omega3_prime_fibre_subset_closed he)

/-- Actual mass-to-Theta normalization, at arbitrary fixed depth. All
three analytic mass suppliers already exist; their errors are added, not
replaced by an assumed target integral bound. -/
theorem uniform_mass_to_Theta (k : ℕ) {δ K τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hK : 0 < K) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        p5z_labelledMass (labels N δ s t W) (weight W) *
            (K*wuSingularSeries N/log N) ≤
          ((1+τ)*K/4*omega3XIntegralEnvelope s t+ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) W := by
  obtain ⟨T1,hT14,hT1⟩ := omega3X_buchstab_scaled k hδ hδhi hK (half_pos hε)
  obtain ⟨T2,_hT24,hT2⟩ := omega3XBuchstabMain_scaled_integral k hδ hδhi hK (half_pos hε)
  obtain ⟨T3,_hT34,hT3⟩ := omega3XIntegralMain_scaled_uniform k hδ hδhi hK.le hτ
  refine ⟨max (max T1 T2) T3,
    hT14.trans ((le_max_left T1 T2).trans (le_max_left _ _)),?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hN12 := (le_max_left (max T1 T2) T3).trans hN
  have hN1 := (le_max_left T1 T2).trans hN12
  have hN2 := (le_max_right T1 T2).trans hN12
  have hN3 := (le_max_right (max T1 T2) T3).trans hN
  have h4 := hT14.trans hN1
  have hscalar : 0 ≤ K*wuSingularSeries N/log N := by
    have hC := wuSingularSeries_pos N (by omega)
    have hlog := Real.log_pos (show (1:ℝ)<N by exact_mod_cast (show 1<N by omega))
    positivity
  have hmass := source_mass_le_native_X N δ s t (convolutionWuWindows N Δ V)
    (fun d hd => (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1)
  have hm := mul_le_mul_of_nonneg_right hmass hscalar
  have h1 := hT1 N hN1 i Δ V hb s t hs hst ht
  have h2 := hT2 N hN2 i Δ V hb s t hs hst ht
  have h3 := hT3 N hN3 i Δ V hb s t hs hst ht
  dsimp only at h1 h2 h3 ⊢
  nlinarith only [hm,h1,h2,h3]

/-- The two already-defined genuine singular products agree with no
factor two and no assumed normalizer identification. -/
theorem current_singular_eq_wu {N : ℕ} (hN : 0 < N) :
    singularSeries N=wuSingularSeries N := by
  rw [currentChen_singularSeries_eq_liuSingularSeries,wuSingularSeries_eq_liu N hN]

/-- Honest same-rho density consumption. The input is a density bound on
the physical coefficient, never U99 or an endpoint-shaped count premise. -/
theorem uniform_density_main_to_Theta (k : ℕ) {δ K τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hK : 0 < K) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ (D : Finset ℕ) (rho : ℕ → ℝ),
        physicalDensitySum D rho ≤ K*(singularSeries N/log N) →
        let W := convolutionWuWindows N Δ V
        p5z_labelledMass (labels N δ s t W) (weight W)*physicalDensitySum D rho ≤
          ((1+τ)*K/4*omega3XIntegralEnvelope s t+ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) W := by
  obtain ⟨T,hT4,hT⟩ := uniform_mass_to_Theta k hδ hδhi hK hτ hε
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb s t hs hst ht D rho hdensity
  have h4 := hT4.trans hN
  have hmass0 : 0 ≤ p5z_labelledMass
      (labels N δ s t (convolutionWuWindows N Δ V))
      (weight (convolutionWuWindows N Δ V)) :=
    sum_nonneg (fun a _ => weight_nonneg _ a)
  have hmain := mul_le_mul_of_nonneg_left hdensity hmass0
  rw [current_singular_eq_wu (by omega)] at hmain
  have hscaled := hT N hN i Δ V hb s t hs hst ht
  dsimp only at hscaled ⊢
  exact hmain.trans (by simpa only [mul_div_assoc] using hscaled)

/-- The new native prime family is now attached to actual rho AND Theta.
Only the original same-rho density primitive is consumed. Coprime, PP and
small-prime losses remain the literal finite functions of this family.
This is not a completed K estimate, and hPP is not silently supplied. -/
theorem uniform_actual_rho_normalized_comparison (k : ℕ) {δ K τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hK : 0 < K) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ (nu r e : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      0 < nu → 0 < e → e ≤ 1 → e^2 ≤ r →
      (N:ℝ)^(nu*r) ≤ (cap N:ℝ) →
        let W := convolutionWuWindows N Δ V
        let S := labels N δ s t W
        let D := attachedUpperModuli nu r e retain cap N
        let rho := attachedUpperCoefficient nu r e retain cap N
        let z := Nat.ceil ((N:ℝ)^(nu*r))
        physicalDensitySum D rho ≤ K*(singularSeries N/log N) →
        wuOmega3Sum N δ s t W ≤
          ((1+τ)*K/4*omega3XIntegralEnvelope s t+ε) *
              boxTheta N ((N:ℝ)^(1/2-δ)) W +
          p5z_labelledCoprimeCorrection S sourceProduct (weight W) D rho +
          p5z_labelledDistributionError S sourceProduct (weight W) N D rho +
          p5z_labelledSmallPrimeMass S sourceProduct (weight W) N z := by
  obtain ⟨T1,hT14,hT1⟩ := uniform_actual_rho_finite_comparison k hδ hδhi (half_pos hε)
  obtain ⟨T2,_hT24,hT2⟩ := uniform_density_main_to_Theta k hδ
    (by linarith : δ<1/2) hK hτ (half_pos hε)
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb s t hs hst ht nu r e retain cap hnu he' he1 heR hcap
  dsimp only
  intro hdensity
  have hfinite := hT1 N ((le_max_left T1 T2).trans hN) he i Δ V hb s t hs hst ht
    nu r e retain cap hnu he' he1 heR hcap
  have hmain := hT2 N ((le_max_right T1 T2).trans hN) i Δ V hb s t hs hst ht
    (attachedUpperModuli nu r e retain cap N)
    (attachedUpperCoefficient nu r e retain cap N) hdensity
  dsimp only at hfinite hmain
  nlinarith only [hfinite,hmain]

end
end ImbalancedChen.P2NativeOmega3SameRhoNormalization
