import ImbalancedChen.P4BActualIntegerOuterUpperAssembly
import ImbalancedChen.P4BLabelledOuterPushforward
import ImbalancedChen.P4BLogSavingBudget
import ImbalancedChen.P4BOuterCoprimeElimination

/-!
# A labelled outer PP target feeds the actual real upper count

YELLOW / SOURCE-ONLY / UNCOMPILED (2026-10-24).
All P4B imports are intended future normal modules for companion drafts.

V is the actual precision-indexed labelled outer weight. Its integer
weight is the complete product-fibre sum, on the complete product image.
Products above N remain present. The integer-shift outer sieve assembly
uses this full carrier, so no artificial product truncation is imposed.

The final theorem derives geometry from nonnegativity and W<=V, mass from
the actual arithmetic labelled-mass surplus, and the primitive error from
the original UniformPrimeProductTarget at rank two and labelled cap N.
The exact signed pushforward retains every modulus sign inside one norm.
It consumes PP at A=3 and pays C*N/(log N)^3 by the proved log budget.

This remains conditional on the displayed actual P4A density estimate,
the arithmetic outer boundary/mass estimate, the same-rho outer signed
coprime correction, and the genuine PP target for V. No PP theorem,
licensing, smoothness or envelope construction is proved. The correction
is explicit; a separate helper derives it from nonzero labelled-support
prime roughness and the proved manuscript sieve gate. Roughness of an
arbitrary V is not inferred from that of the smaller exact source.
-/

namespace ImbalancedChen.P4BLabelledOuterPPUpperAssembly

noncomputable section
open Filter Topology
open scoped BigOperators
open Part3 P4BLabelledOuterPushforward

/-- The original PP target for V supplies the full pushed-forward signed
primitive budget, including every outer product above N. -/
theorem eventually_signed_productWeight_le_of_uniformPP
    (Q : ℕ → Finset ℕ) (rho : ℕ → ℕ → ℝ)
    (V : (N : ℕ) → (Fin 2 → Fin (N + 1)) → ℝ)
    (hUniformPP : UniformPrimeProductTarget (ι := Unit) 2 (fun N : ℕ => N)
      Q rho (fun N _ => V N))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ Q N, rho N d * finitePrimitiveDiscrepancy
        (productCarrier N) (productWeight N (V N)) N d| ≤
          delta * singularNormalization N := by
  obtain ⟨C, hC, N0, hPP⟩ := hUniformPP (3 : ℝ) (by norm_num)
  filter_upwards
    [eventually_logSaving_le_singularNormalization C hC.le 3 (by norm_num)
      delta hdelta, eventually_ge_atTop N0] with N hbudget hN
  intro hEven
  rw [signed_productWeight_eq_primeProductSignedError]
  have hraw : |primeProductSignedError 2 N N (Q N) (rho N) (V N)| ≤
      C * (N : ℝ) / (Real.log (N : ℝ)) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (Real.log (N : ℝ)) (3 : ℕ)]
    exact hPP N hN hEven Unit.unit
  exact hraw.trans hbudget.2

/-- An optional drop-in supplier for the explicit correction premise.
Only nonzero labelled contributions need the displayed prime roughness;
the product fibre then has the required roughness wherever its sum is
nonzero. No sign or positivity assumption on V is needed for this step. -/
theorem labelled_outer_hcoprime_of_manuscript_prime_roughness
    {b kappa nu r : ℝ} (hb : 0 < b) (hnu : 0 < nu) (hr : 0 ≤ r)
    (hgap : nu * r < (1 - kappa) * (b / (1 + b)))
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (V : ℝ → (N : ℕ) → (Fin 2 → Fin (N + 1)) → ℝ)
    (hepsilonR : ∀ delta : ℝ, 0 < delta → (epsilon delta) ^ 2 ≤ r)
    (hrough : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ t ∈ labelledPrimeTuples 2 N, V delta N t ≠ 0 →
        ∀ ell : ℕ, Nat.Prime ell → ell ∣ labelledProduct t →
          (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) < (ell : ℝ)) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          ((finiteCoprimeMass (productCarrier N) (productWeight N (V delta N)) d -
              finiteSourceMass (productCarrier N) (productWeight N (V delta N))) /
            (Nat.totient d : ℝ))| ≤ delta * singularNormalization N := by
  classical
  apply P4BOuterCoprimeElimination.actual_outer_hcoprime_of_manuscript_roughness
    hb hnu hr hgap epsilon retain cap (fun _ N => productCarrier N)
    (fun delta N => productWeight N (V delta N)) hepsilonR
  intro delta hdelta
  filter_upwards [hrough delta hdelta] with N hroughN
  intro hEven m _hm hweight ell hell hdvd
  by_contra hnot
  apply hweight
  unfold productWeight
  apply Finset.sum_eq_zero
  intro t ht
  obtain ⟨htprime, hproduct⟩ := Finset.mem_filter.mp ht
  by_contra hV
  apply hnot
  apply hroughN hEven t htprime hV ell hell
  rw [hproduct]
  exact hdvd

/-- Conditional fixed-real-b hUpper from a genuine labelled outer PP
target. No primitive-error or hUpper premise occurs. The signed coprime
correction is displayed in full; the preceding helper can supply it when
the chosen V has the required nonzero-support prime roughness. -/
theorem eventually_RealB_le_of_actual_labelled_outer_uniformPP
    {b kappa nu r : ℝ}
    (hb : 0 < b) (hbOne : b < 1) (hkappa : 0 < kappa)
    (hnu : 0 < nu) (hr : 0 < r) (hsieve : nu * r < 1)
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (V : ℝ → (N : ℕ) → (Fin 2 → Fin (N + 1)) → ℝ)
    (hepsilon : ∀ delta : ℝ, 0 < delta →
      0 < epsilon delta ∧ epsilon delta ≤ 1 ∧ (epsilon delta) ^ 2 ≤ r)
    (hcap : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (nu * r) ≤ (cap delta N : ℝ))
    (hVnonneg : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ t ∈ labelledPrimeTuples 2 N, 0 ≤ V delta N t)
    (hWV : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ t ∈ labelledPrimeTuples 2 N,
        P4BLabelledPairDictionary.W b N (manuscriptHalfProductCutoff kappa N) t ≤
          V delta N t)
    (hlabelledMass : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (∑ t ∈ labelledPrimeTuples 2 N, V delta N t) ≤
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
          delta * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N) ≤
          (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          ((finiteCoprimeMass (productCarrier N) (productWeight N (V delta N)) d -
              finiteSourceMass (productCarrier N) (productWeight N (V delta N))) /
            (Nat.totient d : ℝ))| ≤ delta * singularNormalization N)
    (hUniformPP : ∀ delta : ℝ, 0 < delta →
      UniformPrimeProductTarget (ι := Unit) 2 (fun N : ℕ => N)
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
        (fun N _ => V delta N)) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  apply P4B.eventually_RealB_le_of_actual_integer_outer_primitive_inputs
    hb hbOne hkappa hnu hr hsieve epsilon retain cap
    (fun _ N => productCarrier N) (fun delta N => productWeight N (V delta N))
    hepsilon hcap
  · intro delta hdelta
    filter_upwards [hVnonneg delta hdelta, hWV delta hdelta] with N hnonnegN hWVN
    intro hEven
    exact actual_outer_pushforward_majorant b N (manuscriptHalfProductCutoff kappa N)
      (V delta N) (hnonnegN hEven) (hWVN hEven)
  · intro delta hdelta
    filter_upwards [hlabelledMass delta hdelta] with N hmassN
    intro hEven
    rw [finiteSourceMass_eq_labelled]
    exact hmassN hEven
  · exact hdensity
  · exact hcoprime
  · intro delta hdelta
    exact eventually_signed_productWeight_le_of_uniformPP
      (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
      (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
      (V delta) (hUniformPP delta hdelta) delta hdelta

end
end ImbalancedChen.P4BLabelledOuterPPUpperAssembly
