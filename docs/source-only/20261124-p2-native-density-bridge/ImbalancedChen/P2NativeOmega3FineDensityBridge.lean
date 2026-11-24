import ImbalancedChen.P2NativeOmega3SameRhoNormalization
import ImbalancedChen.P4BOriginalFineAttachedUpper

/-!
SOURCE ONLY / UNCOMPILED / NO NEW KERNEL CREDIT.

Supply the existing native Omega3 receiver's density input from the
already-defined Fine selection. The physical coefficient and its modulus
set are definitionally the same ones used by Selection.attached_K:
nu = 1, r = 19/96, e = selection.beta, the selection's retention, cap = id.

The second theorem constructs the selection using exists_counting_selection;
it does not assume a density bound, a PP estimate, hRows, or a count bound.
The choice is fixed before the native depth, delta, error parameters, N and
all source boxes. Only the two existing eventual thresholds are combined.

This supplies density wiring only. The actual coprime, signed distribution
and small-prime terms remain in the conclusion, on the same coefficient.
It is neither a full positive-product estimate nor a marked-family licence
nor an H247/bank/seed conclusion. It preserves the existing receiver's box
quantifiers without asserting any new uniform PP target. Both imported
source-only dependency graphs require their own same-source acceptance.
-/

namespace ImbalancedChen.P2NativeOmega3FineDensityBridge

noncomputable section
open Filter Real Wu2008DoubleSieve
open P2NativeOmega3PrimeOutputFamily
open P4BOriginalFineAttachedUpper (Selection retention)

/-- The selected physical density discharges the receiver's hdensity input.
The surviving three errors retain the original labels, weights and rho. -/
theorem selected_omega3_comparison
    {m r n q : ℕ} {e : ℚ} {a etaPP betaMax extra : ℝ} {ft : ℝ → ℝ}
    (selection : Selection m r n e q a 1 (19/96) etaPP betaMax extra ft)
    (k : ℕ) {δ τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        let S := labels N δ s t W
        let f := retention m r n e q a (1 * selection.beta ^ 2)
        let D := attachedUpperModuli 1 (19/96) selection.beta f id N
        let rho := attachedUpperCoefficient 1 (19/96) selection.beta f id N
        let z := Nat.ceil ((N : ℝ) ^ (1 * (19/96 : ℝ)))
        wuOmega3Sum N δ s t W ≤
          ((1+τ)*currentK/4*omega3XIntegralEnvelope s t+ε) *
              boxTheta N ((N : ℝ)^(1/2-δ)) W +
          p5z_labelledCoprimeCorrection S sourceProduct (weight W) D rho +
          p5z_labelledDistributionError S sourceProduct (weight W) N D rho +
          p5z_labelledSmallPrimeMass S sourceProduct (weight W) N z := by
  obtain ⟨Tnative, hnative4, hnative⟩ :=
    P2NativeOmega3SameRhoNormalization.uniform_actual_rho_normalized_comparison
      (K := currentK) k hδ hδhi (by norm_num [currentK]) hτ hε
  obtain ⟨Tdensity, hdensity⟩ := eventually_atTop.mp selection.attached_K
  refine ⟨max Tnative Tdensity, hnative4.trans (le_max_left _ _), ?_⟩
  intro N hN hEven i Δ V hbox s t hs hst ht
  have hNnative := (le_max_left Tnative Tdensity).trans hN
  have hNdensity := (le_max_right Tnative Tdensity).trans hN
  have hN4 : 4 ≤ N := hnative4.trans hNnative
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcap : (N : ℝ) ^ (1 * (19/96 : ℝ)) ≤ (N : ℝ) := by
    simpa only [one_mul, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNreal (by norm_num : (19/96 : ℝ) ≤ 1)
  have hbeta : selection.beta ≤ 1 :=
    selection.lt_eighth.le.trans (by norm_num : (1/8 : ℝ) ≤ 1)
  exact hnative N hNnative hEven i Δ V hbox s t hs hst ht
    1 (19/96) selection.beta (retention m r n e q a (1 * selection.beta ^ 2)) id
    zero_lt_one selection.pos hbeta selection.square_lt.le hcap
    (hdensity N hNdensity hEven)

/-- Construct the original Fine witness before every source-box/error choice.
All hypotheses are the original finite-policy selection parameters; no
density or distribution estimate is requested from the caller. -/
theorem exists_selected_omega3_comparison
    (a zeta betaMax : ℝ) (ha : 0 < a) (haMax : a ≤ 1/800)
    (hzeta : 0 < zeta) (hbetaMax : 0 < betaMax)
    (ft : ℝ → ℝ) (hft : ∀ x : ℝ, 0 < x → 0 < ft x)
    (qMin mMin : ℕ) :
    ∃ (m r n : ℕ) (e : ℚ) (q : ℕ) (etaPP : ℝ),
      0 < e ∧ (e : ℝ) < 1/2048 ∧ qMin ≤ q ∧ 0 < q ∧ 256 ∣ q ∧
      mMin ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q ∧
      0 < etaPP ∧
      etaPP ≤ P4AOriginalFiniteFallbackCommonGroups.gap m
        (P4AOriginalNewFifthUnion.data e q a) ∧
      ∃ selection : Selection m r n e q a 1 (19/96) etaPP betaMax zeta ft,
      ∀ (k : ℕ) (δ τ ε : ℝ),
        0 < δ → δ ≤ 1/10 → 0 < τ → 0 < ε →
        ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
          ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
            let W := convolutionWuWindows N Δ V
            let S := labels N δ s t W
            let f := retention m r n e q a (1 * selection.beta ^ 2)
            let D := attachedUpperModuli 1 (19/96) selection.beta f id N
            let rho := attachedUpperCoefficient 1 (19/96) selection.beta f id N
            let z := Nat.ceil ((N : ℝ) ^ (1 * (19/96 : ℝ)))
            wuOmega3Sum N δ s t W ≤
              ((1+τ)*currentK/4*omega3XIntegralEnvelope s t+ε) *
                  boxTheta N ((N : ℝ)^(1/2-δ)) W +
              p5z_labelledCoprimeCorrection S sourceProduct (weight W) D rho +
              p5z_labelledDistributionError S sourceProduct (weight W) N D rho +
              p5z_labelledSmallPrimeMass S sourceProduct (weight W) N z := by
  obtain ⟨m, r, n, e, q, etaPP, he, hehi, hqMin, hq, hdiv, hmesh,
      hetaPP, hgap, hselection⟩ :=
    P4BOriginalFineAttachedUpper.exists_counting_selection
      a zeta betaMax ha haMax hzeta hbetaMax ft hft qMin mMin
  obtain ⟨selection⟩ := hselection
  refine ⟨m, r, n, e, q, etaPP, he, hehi, hqMin, hq, hdiv, hmesh,
    hetaPP, hgap, selection, ?_⟩
  intro k δ τ ε hδ hδhi hτ hε
  exact selected_omega3_comparison selection k hδ hδhi hτ hε

end
end ImbalancedChen.P2NativeOmega3FineDensityBridge
