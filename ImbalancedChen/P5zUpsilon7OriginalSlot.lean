import ImbalancedChen.P5zMixedMarkedPrimeFamilyActualBridge
import ImbalancedChen.P5U7OriginalPhysicalPP
import ImbalancedChen.P5U7OriginalOmegaIntegral
import ImbalancedChen.P5OriginalFixedDensitySupplierAssembly

/-! SOURCE ONLY / UNCOMPILED. Original U7 uses TWO physical ranks and ONE
combined normal mass, at the SAME literal actual rho. No U7 mean is a
premise. The remaining source mass, policy integral/certificate, licence,
active scope and signed mixed PP suppliers are genuine OPEN obligations.
The original ledger coefficient TWO is preserved explicitly below. -/
namespace ImbalancedChen
noncomputable section
open Filter
open scoped BigOperators
open Classical
open P5U7OriginalPhysicalPP

/-- Delete only zero-weight labels, so roughness holds at every source label. -/
def p5z_u7MarkedSource (rank N : ℕ)
    (W : (Fin rank → Fin (N + 1)) → ℝ) : Finset (Fin rank → Fin (N + 1)) :=
  (Part3.labelledPrimeTuples rank N).filter (fun u => W u ≠ 0)

theorem p5z_u7MarkedSource_subset (rank N : ℕ) (W : (Fin rank → Fin (N + 1)) → ℝ) :
    p5z_u7MarkedSource rank N W ⊆ Part3.labelledPrimeTuples rank N := Finset.filter_subset _ _

theorem p5z_u7Marked_test_sum (rank N : ℕ)
    (W G : (Fin rank → Fin (N + 1)) → ℝ) :
    (∑ u ∈ p5z_u7MarkedSource rank N W, W u * G u) =
      ∑ u ∈ Part3.labelledPrimeTuples rank N, W u * G u := by
  unfold p5z_u7MarkedSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : W u = 0 <;> simp [h]

theorem p5z_u7MarkedPhysicalPP_eq (rank N : ℕ)
    (W : (Fin rank → Fin (N + 1)) → ℝ) (D : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError rank N N D rho
      (p5z_markedPhysicalWeight (p5z_u7MarkedSource rank N W) W) =
        Part3.primeProductSignedError rank N N D rho W := by
  unfold Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  have heq : p5z_markedPhysicalWeight (p5z_u7MarkedSource rank N W) W u = W u := by
    by_cases h : W u = 0
    · simp only [p5z_markedPhysicalWeight, h, ite_self]
    · have hs : u ∈ p5z_u7MarkedSource rank N W := Finset.mem_filter.mpr ⟨hu, h⟩
      simp only [p5z_markedPhysicalWeight, if_pos hs]
  rw [heq]

def p5z_u7Source3 (N : ℕ) := p5z_u7MarkedSource 3 N (weight3 N)
def p5z_u7Source4 (N : ℕ) := p5z_u7MarkedSource 4 N (weight4 N)

/-- A single combined source mass. This is not a receiver-prime mean. -/
theorem p5z_u7_combinedMarked_mass_eq (N : ℕ) :
    p5z_labelledMass (p5z_u7Source3 N) (weight3 N) +
      p5z_labelledMass (p5z_u7Source4 N) (weight4 N) =
        ((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ) := by
  have h3 := weight3_sum N (fun _ => 1)
  have h4 := weight4_sum N (fun _ => 1)
  have hm3 := p5z_u7Marked_test_sum 3 N (weight3 N) (fun _ => 1)
  have hm4 := p5z_u7Marked_test_sum 4 N (weight4 N) (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h3 h4 hm3 hm4
  change (∑ u ∈ p5z_u7MarkedSource 3 N (weight3 N), weight3 N u) +
    (∑ u ∈ p5z_u7MarkedSource 4 N (weight4 N), weight4 N u) = _
  rw [hm3, hm4, ← h3, ← h4]

/-- Literal original U7, retaining every repeated terminal label and units. -/
theorem p5z_u7_eq_mixedMarkedPrimeMass_add_units (N : ℕ) :
    currentChenUpsilon7 N =
      (p5z_labelledPrimeMass (p5z_u7Source3 N) Part3.labelledProduct (weight3 N) N +
        p5z_labelledPrimeMass (p5z_u7Source4 N) Part3.labelledProduct (weight4 N) N) +
          ((currentChenUpsilon7UnitFibres N).card : ℝ) := by
  let G : ℕ → ℝ := fun m => if m < N ∧ Nat.Prime (N - m) then 1 else 0
  have hprod := p5U7Arithmetic_product_weighted_Fubini N G
  have h3 := weight3_sum N G
  have h4 := weight4_sum N G
  have hm3 := p5z_u7Marked_test_sum 3 N (weight3 N) (fun u => G (Part3.labelledProduct u))
  have hm4 := p5z_u7Marked_test_sum 4 N (weight4 N) (fun u => G (Part3.labelledProduct u))
  have hsum := hprod.trans (congrArg₂ (fun x y : ℝ => x + y)
    (h3.trans hm3.symm) (h4.trans hm4.symm))
  have hgate : p5U7ArithmeticWeightedPrimeGate N (fun _ => True) =
      ∑ m ∈ Finset.range N, p5U7ArithmeticProductWeight N m * G m := by
    apply Finset.sum_congr rfl
    intro m hm
    have hlt := Finset.mem_range.mp hm
    simp only [G, hlt, true_and, and_true, mul_ite, mul_one, mul_zero]
  rw [p5U7_original_eq_weighted_prime_source_add_unit, hgate, hsum]
  simp only [G, mul_ite, mul_one, mul_zero]
  rfl

/-- Raw actual-rho U7 route. Only ONE combined normal source-mass supplier
is assumed. All small-prime/coprime/majorant/unit suppliers are discharged;
the PP condition is the signed rank-three PLUS rank-four expression. -/
theorem p5z_eventually_u7_le_kJ_of_fixed_actual_rho
    (J k nu r e scopeNu : ℝ) (hJ : 0 ≤ J) (hk : 0 ≤ k)
    (hnu : 0 < nu) (he : 0 < e) (he8 : e < 1 / 8) (heR : e ^ 2 ≤ r)
    (hnur : nu * r < 1) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      ((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ) ≤
        (J + eta) * ((N : ℝ) / Real.log (N : ℝ)))
    (hlicensed : ∀ᶠ N : ℕ in atTop, Even N → Licensed N)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) ≤ k * (singularSeries N / Real.log (N : ℝ)))
    (hPP : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (weight3 N) +
        Part3.primeProductSignedError 4 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (weight4 N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤ (k * J + eta) * singularNormalization N := by
  have hW3 : ∀ N, ∀ u ∈ p5z_u7Source3 N, 0 ≤ weight3 N u ∧ weight3 N u ≤ 1 := by
    intro N u hu
    rcases weight3_zero_or_one N u with h | h <;> rw [h] <;> norm_num
  have hW4 : ∀ N, ∀ u ∈ p5z_u7Source4 N, 0 ≤ weight4 N u ∧ weight4 N u ≤ 1 := by
    intro N u hu
    rcases weight4_zero_or_one N u with h | h <;> rw [h] <;> norm_num
  have hcap3 : ∀ N, ∀ u ∈ p5z_u7Source3 N, Part3.labelledProduct u ≤ N := by
    intro N u hu
    exact (weight3_sorted_primitive (Finset.mem_filter.mp hu).2).2.2.1.le
  have hcap4 : ∀ N, ∀ u ∈ p5z_u7Source4 N, Part3.labelledProduct u ≤ N := by
    intro N u hu
    exact (weight4_sorted_primitive (Finset.mem_filter.mp hu).2).2.2.2.1.le
  have hrough3 : ∀ᶠ N : ℕ in atTop, Even N → ∀ u ∈ p5z_u7Source3 N, ∀ i,
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ ((u i).val : ℝ) :=
    Filter.Eventually.of_forall (fun N _ u hu i => weight3_lower_power (Finset.mem_filter.mp hu).2 i)
  have hrough4 : ∀ᶠ N : ℕ in atTop, Even N → ∀ u ∈ p5z_u7Source4 N, ∀ i,
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ ((u i).val : ℝ) :=
    Filter.Eventually.of_forall (fun N _ u hu i => weight4_lower_power (Finset.mem_filter.mp hu).2 i)
  have hmassMarked : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (p5z_u7Source3 N) (weight3 N) +
        p5z_labelledMass (p5z_u7Source4 N) (weight4 N) ≤
          (J + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro eta heta
    filter_upwards [hmass eta heta] with N hN
    rw [p5z_u7_combinedMarked_mass_eq]
    exact hN
  have hPPmarked : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N)
          (p5z_markedPhysicalWeight (p5z_u7Source3 N) (weight3 N)) +
        Part3.primeProductSignedError 4 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N)
          (p5z_markedPhysicalWeight (p5z_u7Source4 N) (weight4 N))| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
    obtain ⟨C, hC, hbound⟩ := hPP
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with N hN
    intro hEven hL
    change |Part3.primeProductSignedError 3 N N _ _
      (p5z_markedPhysicalWeight (p5z_u7MarkedSource 3 N (weight3 N)) (weight3 N)) +
      Part3.primeProductSignedError 4 N N _ _
      (p5z_markedPhysicalWeight (p5z_u7MarkedSource 4 N (weight4 N)) (weight4 N))| ≤ _
    rw [p5z_u7MarkedPhysicalPP_eq, p5z_u7MarkedPhysicalPP_eq]
    exact hN hEven hL
  have hprime := p5z_eventually_mixedMarkedFamily_upper_of_actual_rho k hk 3 4
    p5z_u7Source3 p5z_u7Source4 weight3 weight4
    (fun N => p5z_u7MarkedSource_subset 3 N (weight3 N))
    (fun N => p5z_u7MarkedSource_subset 4 N (weight4 N))
    1 J (59 / 250) (by norm_num) hJ (by norm_num) hW3 hW4 hcap3 hcap4 hrough3 hrough4
    hmassMarked nu r e scopeNu hnu he he8 heR hnur hscopeNu
    retain cap Licensed hlicensed hcap hscope hdensity hPPmarked
  intro eta heta
  have hhalf := half_pos heta
  filter_upwards [hprime (eta / 2) hhalf,
    p5U7Arithmetic_eventually_error_budget (eta / 2) hhalf] with N hpN heN
  intro hEven
  have hu0 : (0 : ℝ) ≤ (currentChenUpsilon7UnitFibres N).card := Nat.cast_nonneg _
  have hs30 : (0 : ℝ) ≤ ((currentChenUpsilon7PrimeTriples N).filter (fun x =>
      ((N - p5U7ThreeProduct x : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))).card := Nat.cast_nonneg _
  have hs40 : (0 : ℝ) ≤ ((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x =>
      ((N - p5U7FourProduct x : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))).card := Nat.cast_nonneg _
  have hu : ((currentChenUpsilon7UnitFibres N).card : ℝ) ≤
      (eta / 2) * singularNormalization N := by
    unfold p5U7ArithmeticSmallUnitError at heN
    linarith only [heN, hu0, hs30, hs40]
  rw [p5z_u7_eq_mixedMarkedPrimeMass_add_units]
  have hp := hpN hEven
  linarith only [hp, hu]

/-- Literal ledger identity: TWO copies of the entire mixed-rank source
and TWO unit contributions. There is no mean or half-integral premise. -/
theorem p5z_u7_two_ledger_identity (N : ℕ) :
    2 * currentChenUpsilon7 N =
      2 * (p5z_labelledPrimeMass (p5z_u7Source3 N) Part3.labelledProduct (weight3 N) N +
        p5z_labelledPrimeMass (p5z_u7Source4 N) Part3.labelledProduct (weight4 N) N) +
          2 * ((currentChenUpsilon7UnitFibres N).card : ℝ) := by
  rw [p5z_u7_eq_mixedMarkedPrimeMass_add_units]
  ring

end
end ImbalancedChen

namespace ImbalancedChen.P5OriginalCoefficientArithmetic
noncomputable section
open Filter
open P5U7OriginalPhysicalPP

/-- The literal original Buchstab integral at unit density. -/
def p5z_originalU7LiteralJ : ℝ := p5U7OriginalOmegaIntegral 1
def p5z_originalU7UpperIntegralEndpoint : ℝ := savedU7 / K0
def p5z_originalU7LowerIntegralEndpoint : ℝ := lowerU7AtK0 / K0

theorem p5z_originalU7_integral_endpoints_exact :
    p5z_originalU7UpperIntegralEndpoint =
      ((1672464594622060236183097 : ℝ) / 1208925819614629174706176) / ((67619 : ℝ) / 10000) ∧
    p5z_originalU7LowerIntegralEndpoint =
      ((7183180737282426411788973366247539 : ℝ) / 5192296858534827628530496329220096) /
        ((67619 : ℝ) / 10000) := by
  norm_num [p5z_originalU7UpperIntegralEndpoint, p5z_originalU7LowerIntegralEndpoint,
    savedU7, lowerU7AtK0, K0]

/-- Independent P2 upper integral endpoint and LOWER Simpson slope.
Neither of these numerical integral certificates is proved here. -/
theorem p5z_originalU7_envelope_of_integral_certificates
    (hUpper : p5z_originalU7LiteralJ ≤ p5z_originalU7UpperIntegralEndpoint)
    (hLower : p5z_originalU7LowerIntegralEndpoint ≤ p5z_originalU7LiteralJ) :
    fixedProductDensityCoefficient * p5z_originalU7LiteralJ ≤
      U7Envelope fixedProductDensityCoefficient := by
  have hK0 : 0 < K0 := by norm_num [K0]
  have hup : K0 * p5z_originalU7LiteralJ ≤ savedU7 := by
    simpa only [mul_comm] using (le_div_iff₀ hK0).mp hUpper
  have hk : fixedProductDensityCoefficient ≤ K0 := allowedDensityDelta_below_original_anchors.2.le
  exact complete_switched_cost_envelope p5z_originalU7LiteralJ savedU7 lowerU7AtK0
    fixedProductDensityCoefficient hup hLower hk

/-- Exact original fixedAssembly h7 slot. ONE actual e/rho is selected by
full-policy density limits and reused for both ranks, licence and PP.
Only the legitimate combined arithmetic normal mass is left as a source
supplier; there is no U7 mean, J3, J4, small-prime, coprime or unit premise.
The original downstream ledger applies TWO copies of this exact h7. -/
theorem p5z_original_h7_of_actual_full_policy
    (nu r epsilonMax rawBound scopeNu : ℝ) (hnu : 0 < nu) (hr : 0 < r) (hnur : nu * r < 1)
    (hepsilonMax : 0 < epsilonMax) (hscopeNu : 0 ≤ scopeNu)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (integral : ℝ → ℝ) (Licensed : ℝ → ℕ → Prop)
    (hUpper : p5z_originalU7LiteralJ ≤ p5z_originalU7UpperIntegralEndpoint)
    (hLower : p5z_originalU7LowerIntegralEndpoint ≤ p5z_originalU7LiteralJ)
    (hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      ((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ) ≤
        (p5z_originalU7LiteralJ + eta) * ((N : ℝ) / Real.log (N : ℝ)))
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hIntegral : ∀ e : ℝ, 0 < e → e < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd e N) N (cap N) 0 ((N : ℝ) ^ (nu * r)))
          (fixedRoughCoefficient (retainOdd e N) N (cap N) 0 ((N : ℝ) ^ (nu * r))) *
            Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (nhds (integral e)))
    (hCertificate : ∀ e : ℝ, 0 < e → e < epsilonMax → integral e ≤ rawBound)
    (hgap : rawBound < fixedProductDensityCoefficient)
    (hlicensed : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ᶠ N : ℕ in atTop, Even N → Licensed e N)
    (hscope : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ᶠ N : ℕ in atTop, Even N → Licensed e N → ∀ d : ℕ,
        d ∈ attachedUpperModuli nu r e (retainOdd e) cap N →
        attachedUpperCoefficient nu r e (retainOdd e) cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hPP : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e (retainOdd e) cap N)
            (attachedUpperCoefficient nu r e (retainOdd e) cap N) (weight3 N) +
          Part3.primeProductSignedError 4 N N (attachedUpperModuli nu r e (retainOdd e) cap N)
            (attachedUpperCoefficient nu r e (retainOdd e) cap N) (weight4 N)| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N → currentChenUpsilon7 N ≤
      (U7Envelope fixedProductDensityCoefficient + delta) * singularNormalization N := by
  have hcapF : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    rw [Filter.eventually_inf_principal]
    filter_upwards [hcap] with N hN
    exact fun hposEven => hN hposEven.2
  obtain ⟨e, he, he8, heMax, heR, N₀, _hN₀, hdensity⟩ :=
    exists_actualSmallRoughRho_density_le_of_full_policy_limits nu r epsilonMax rawBound
      fixedProductDensityCoefficient hnu hr hepsilonMax retainOdd cap integral
      hcapF hIntegral hCertificate hgap
  have hcapFixed : ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    filter_upwards [hcap] with N hN
    exact fun hEven _ => hN hEven
  have hdensityFixed : ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
      physicalDensitySum (attachedUpperModuli nu r e (retainOdd e) cap N)
        (attachedUpperCoefficient nu r e (retainOdd e) cap N) ≤
          fixedProductDensityCoefficient * (singularSeries N / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    exact fun hEven _ => hdensity N hN hEven
  have hk : 0 ≤ fixedProductDensityCoefficient := by
    norm_num [fixedProductDensityCoefficient, currentK, allowedDensityDelta]
  have hJ : 0 ≤ p5z_originalU7LiteralJ :=
    (show 0 ≤ p5z_originalU7LowerIntegralEndpoint by
      norm_num [p5z_originalU7LowerIntegralEndpoint, lowerU7AtK0, K0]).trans hLower
  have hraw := p5z_eventually_u7_le_kJ_of_fixed_actual_rho p5z_originalU7LiteralJ
    fixedProductDensityCoefficient nu r e scopeNu hJ hk hnu he he8 heR hnur hscopeNu
    (retainOdd e) cap (Licensed e) hmass (hlicensed e he he8 heMax heR) hcapFixed
    (hscope e he he8 heMax heR) hdensityFixed (hPP e he he8 heMax heR)
  have hcoef := p5z_originalU7_envelope_of_integral_certificates hUpper hLower
  intro delta hdelta
  filter_upwards [hraw delta hdelta] with N hN
  intro hEven
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (hN hEven).trans (mul_le_mul_of_nonneg_right (add_le_add_right hcoef delta) hH)

end
end ImbalancedChen.P5OriginalCoefficientArithmetic

