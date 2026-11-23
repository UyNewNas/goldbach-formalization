import ImbalancedChen.P1Full87HistoricalMiddleSmoothing
import ImbalancedChen.P4BOriginalFineAttachedUpper

/-! Start with the literal prime receiver and both original old/new
physical kernels. On the actual two policy differences and the separate
Fine coefficient, only the displayed above-BV smooth prime sum survives. -/
namespace ImbalancedChen.P1Full87PhysicalKernelSmoothing
noncomputable section
open Filter Topology VariableEnvelope
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87UnilateralStoppedLevel (eventPolicy)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy policy)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest densityTest gain primeMass)
open P1Original87SharpMiddleReserve (comparisonReceiver)
open P1OriginalSharpFiniteReceiver (literal)
open P1Full87HistoricalMiddleSmoothing (policyRemaining smoothRemaining exists_full87_simultaneous_smoothing)
open P4BOriginalFineAttachedUpper (Selection meshWidth retention)
open P4AOriginalFiniteAll22FineDensity (modulusFamily coefficientFamily)
open P4AOriginalFull87RawChronology (cutoff)

private theorem combine {u H x y z : ℝ} (h1 : |x-y| ≤ u/2*H) (h2 : |y-z| ≤ u/2*H) :
    |x-z| ≤ u*H := by
  calc
    _ = |(x-y)+(y-z)| := by rw [show (x-y)+(y-z) = x-z by ring]
    _ ≤ |x-y|+|y-z| := abs_add_le _ _
    _ ≤ u/2*H+u/2*H := add_le_add h1 h2
    _ = _ := by ring

/-- All signed physical contributions have the same universal BV cutoff.
The first projection retains the original historical source and all
three omission budgets. The second has exactly the compiled Fine rho,
whose support condition is supplied by its own receipt. -/
theorem exists_original_kernel_receivers :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ kappa : ℝ, 0 < kappa → kappa < 1 →
      (∀ u epsSource epsBox epsSixth : ℝ, 0 < u → 0 < epsSource → 0 < epsBox → 0 < epsSixth →
        ∃ s r : ℕ, ∃ E : ℝ, 0 < E ∧ E ≤ 11/64000 ∧
        P4AOriginalFull87SixthMarginIntegration.totalSixthOmitted s (fun _ _ => (1:ℝ)) < epsSixth ∧
        P4AOriginalFull87TrimOmission.totalOmitted r (fun _ _ => (1:ℝ)) < epsSource ∧
        ∀ e : ℚ, 0 < e → (e:ℝ) < E → ∃ q0 : ℕ, 0 < q0 ∧ ∀ q ≥ q0,
        ∀ a : ℝ, a ≤ 1/100 → ∃ n0 : ℕ, ∀ n ≥ n0, ∃ m0 : ℕ, ∀ m ≥ m0,
        P4AOriginalFull87AllRankBoxedProvenance.allOmitted n e q a m (fun _ _ => (1:ℝ)) < epsBox ∧
        FilteredSourceSupply s r n e q a ∧
        ∀ᶠ N : ℕ in atTop, Even N → ∀ (cap : ℕ) (w z ell : ℝ),
        w ≤ (N:ℝ)^(53/13824 : ℝ) → (N:ℝ)^mu ≤ z → z ≤ cap → 0 < ell → ell ≤ 1/1000 →
          let L := (N:ℝ)^ell
          let R := eventPolicy true (width r) n e q a N
          let S := eventPolicy false (width r) n e q a N
          let six := sixthPolicy n e q a (N : ℝ)
          let eight := policy (width r) n e q a (N : ℝ)
          |comparisonReceiver r n e q a N cap w z L (receiverTest N) -
            primeMass N * comparisonReceiver r n e q a N cap w z L densityTest -
            policyRemaining B kappa (S false) (R false) N cap w z L| ≤ u * singularNormalization N ∧
          |gain (width r) n e q a N cap w z L (receiverTest N) -
            primeMass N * gain (width r) n e q a N cap w z L densityTest -
            policyRemaining B kappa (eight false) (six false) N cap w z L| ≤ u * singularNormalization N) ∧
      (∀ {m r n q : ℕ} {e : ℚ} {a nu v etaPP betaMax zeta : ℝ} {ft : ℝ → ℝ}
        (s : Selection m r n e q a nu v etaPP betaMax zeta ft) (u : ℝ), 0 < u →
        ∀ᶠ N : ℕ in atTop, Even N →
          let Q := modulusFamily nu s.beta 0 N
          let c := coefficientFamily m r n e q a nu s.beta s.k 0 N
          |literal N Q c - primeMass N * physicalDensitySum Q c - smoothRemaining B kappa N Q c| ≤
            u * singularNormalization N) := by
  obtain ⟨B, hB, htransfer⟩ := exists_full87_simultaneous_smoothing
  refine ⟨B, hB, ?_⟩
  intro kappa hk hk1
  constructor
  · intro u epsSource epsBox epsSixth hu hsrc hbox hsix
    obtain ⟨s, r, E, hE, hEmax, hOm6, hOm, hChoose⟩ :=
      P1Original87SharpMiddleReserve.exists_original_reserves (u/2) epsSource epsBox epsSixth
        (half_pos hu) hsrc hbox hsix
    refine ⟨s, r, E, hE, hEmax, hOm6, hOm, ?_⟩
    intro e he heE
    obtain ⟨q0, hq0, hq⟩ := hChoose e he heE
    refine ⟨q0, hq0, ?_⟩
    intro q hqq a ha
    obtain ⟨n0, hn⟩ := hq q hqq a ha
    refine ⟨n0, ?_⟩
    intro n hnn
    obtain ⟨m0, hm⟩ := hn n hnn
    refine ⟨m0, ?_⟩
    intro m hmm
    obtain ⟨hBox, hHist, hOrig⟩ := hm m hmm
    refine ⟨hBox, hHist, ?_⟩
    filter_upwards [hOrig, htransfer kappa hk hk1 (u/2) (half_pos hu)] with N hO hT
    intro hev cap w z ell hw hz hc hell hell1
    obtain ⟨hR, hS⟩ := hO hev cap w z ell hw hz hc hell hell1
    rw [← P1OriginalSharpFiniteReceiver.same_normalization N] at hR hS
    obtain ⟨tR, tS, _⟩ := hT hev r n e q a cap w z ((N : ℝ)^ell)
    exact ⟨combine hR tR, combine hS tS⟩
  · intro m r n q e a nu v etaPP betaMax zeta ft s u hu
    filter_upwards [eventually_ge_atTop s.N0,
      P1OriginalSharpFiniteReceiver.eventual_receiver (u/2) (half_pos hu),
      htransfer kappa hk hk1 (u/2) (half_pos hu)] with N hN hLit hT
    intro hev
    let Q := modulusFamily nu s.beta 0 N
    let c := coefficientFamily m r n e q a nu s.beta s.k 0 N
    have h := hLit hev Q c (fun d hd => ⟨P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hd,
      P4AUpperTaggedBetaAttachment.support_coprime_target _ _ _ _ hd,
      P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d⟩)
    have hsupp := (s.receipt N hN hev).2.2.2.2.2.1
    rw [P1OriginalSharpFiniteReceiver.above_eq_middle N Q c (fun d _ => hsupp d),
      P1OriginalSharpFiniteReceiver.read_density, ← P1OriginalSharpFiniteReceiver.same_normalization N] at h
    have hm := (hT hev r n e q a N ((N:ℝ)^(nu*s.beta^2)) (cutoff N) ((N:ℝ)^(nu*s.beta))).2.2
      (retention m r n e q a (nu*s.beta^2) N) (fun _ => []) (meshWidth m e q a s.k)
    exact combine h hm

end
end ImbalancedChen.P1Full87PhysicalKernelSmoothing
