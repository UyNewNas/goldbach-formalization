import ImbalancedChen.P5PresievedFineLabelPrimeBoxes
import ImbalancedChen.P5OriginalAllSixteenPresievedEndpointGates

/-!
# Fixed prime groups: endpoint ratios including common-beta variation
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Prefix primes keep their OWN log box; rough primes keep finePrimeSet and
its lowered ceiling. Both group maps are fixed on the whole box. Group3
has fixed endpoint N^ell, although its actual beta integer may be1.
The honest budget is ell+(4+r)*mesh<=tau. No ell<=delta/8 substitution,
group assignment, Medium gate, SW or PP conclusion is assumed or claimed.
-/

namespace ImbalancedChen.P5Z.PresievedFixedGroupBetaEndpointRatios
noncomputable section
open Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open PresievedFineLabelPrimeBoxes

def assignedProduct {r : ℕ} (t : Four) (p : Fin r → ℕ) (e : ℕ)
    (GP : Fin 4 → Fin 3) (GR : Fin r → Fin 3) (g : Fin 3) : ℕ :=
  (∏ i ∈ groupIndices GP g, slots t i) * (∏ i ∈ groupIndices GR g, p i) *
    (if g = 2 then e else 1)

def fixedEndpoint {ι : Type*} {r : ℕ} (N : ℕ) (ell : ℝ)
    (bP : Fin 4 → ℝ) (bR : ι → ℝ) (labels : Fin r → ι)
    (GP : Fin 4 → Fin 3) (GR : Fin r → Fin 3) (g : Fin 3) : ℝ :=
  (N : ℝ) ^ ((∑ i ∈ groupIndices GP g, bP i) +
    (∑ i ∈ groupIndices GR g, bR (labels i)) + (if g = 2 then ell else 0))

private theorem product_window {k N : ℕ} (hN : 1 < N) (S : Finset (Fin k))
    (p : Fin k → ℕ) (a b : Fin k → ℝ)
    (hlo : ∀ i, (N : ℝ) ^ a i ≤ (p i : ℝ))
    (hhi : ∀ i, (p i : ℝ) ≤ (N : ℝ) ^ b i) :
    ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ (N : ℝ) ^ (∑ i ∈ S, b i) ∧
      (N : ℝ) ^ (∑ i ∈ S, b i) ≤
        (N : ℝ) ^ (∑ i ∈ S, b i - a i) * ((∏ i ∈ S, p i : ℕ) : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hl : (N : ℝ) ^ (∑ i ∈ S, a i) ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.rpow_sum_of_pos hNp]
    exact Finset.prod_le_prod (fun i _ => Real.rpow_nonneg hNp.le _) (fun i _ => hlo i)
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_prod, Real.rpow_sum_of_pos hNp]
    exact Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hhi i)
  · calc
      _ = (N : ℝ) ^ (∑ i ∈ S, b i - a i) * (N : ℝ) ^ (∑ i ∈ S, a i) := by
        rw [← Real.rpow_add hNp, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hNp.le _)

private theorem group_width_le {k : ℕ} (groups : Fin k → Fin 3) (g : Fin 3)
    (a b : Fin k → ℝ) {mesh : ℝ} (hm : 0 ≤ mesh)
    (hwidth : ∀ i, b i - a i ≤ mesh) :
    (∑ i ∈ groupIndices groups g, b i - a i) ≤ (k : ℝ) * mesh := by
  have hsum : (∑ i ∈ groupIndices groups g, b i - a i) ≤
      ((groupIndices groups g).card : ℝ) * mesh := by
    calc
      _ ≤ ∑ _i ∈ groupIndices groups g, mesh := Finset.sum_le_sum (fun i _ => hwidth i)
      _ = _ := by simp
  have hsub : groupIndices groups g ⊆ (Finset.univ : Finset (Fin k)) := Finset.filter_subset _ _
  have hcard : (groupIndices groups g).card ≤ k := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsub
  exact hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hm)

/-- Actual fine-label membership yields BOTH endpoint bounds. Beta
variation is charged in group3 even when the actual integer equals1. -/
theorem actual_fixed_group_endpoint_ratios {ι : Type*} {r N : ℕ}
    (hN : 1 < N) (cap : ℕ) (w Z ell mesh tau : ℝ)
    (aP bP : Fin 4 → ℝ) (aR bR : ι → ℝ) (labels : Fin r → ι)
    (GP : Fin 4 → Fin 3) (GR : Fin r → Fin 3)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (hpbox : coordinates N t ∈ logPrimeBox aP bP) (p : Fin r → ℕ)
    (hrbox : List.ofFn p ∈ actualPrimeSlotBox
      (fun i => finePrimeSet N cap w Z (aR i) (bR i)) (List.ofFn labels))
    (e : ℕ) (he1 : 1 ≤ e) (heupper : (e : ℝ) ≤ (N : ℝ) ^ ell)
    (hell : 0 ≤ ell) (hmesh : 0 ≤ mesh)
    (hPwidth : ∀ i, bP i - aP i ≤ mesh)
    (hRwidth : ∀ i, bR (labels i) - aR (labels i) ≤ mesh)
    (hbudget : ell + ((4 + r : ℕ) : ℝ) * mesh ≤ tau) :
    ∀ g : Fin 3, (assignedProduct t p e GP GR g : ℝ) ≤ fixedEndpoint N ell bP bR labels GP GR g ∧
      fixedEndpoint N ell bP bR labels GP GR g ≤ (N : ℝ) ^ tau * (assignedProduct t p e GP GR g : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hn
  have hPlo (i : Fin 4) : (N : ℝ) ^ aP i ≤ (slots t i : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hn.le (mem_logPrimeBox.mp hpbox i).1
    simpa only [coordinates, actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht)] using h
  have hPhi (i : Fin 4) : (slots t i : ℝ) ≤ (N : ℝ) ^ bP i := by
    have h := Real.rpow_le_rpow_of_exponent_le hn.le (mem_logPrimeBox.mp hpbox i).2.le
    simpa only [coordinates, actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht)] using h
  have hmem := (mem_primeSlotBox_ofFn _ labels p).mp hrbox
  have hRlo (i : Fin r) : (N : ℝ) ^ aR (labels i) ≤ (p i : ℝ) :=
    (Finset.mem_filter.mp (hmem i)).2.1
  have hRhi (i : Fin r) : (p i : ℝ) ≤ (N : ℝ) ^ bR (labels i) :=
    (Finset.mem_filter.mp (hmem i)).2.2.le
  intro g
  let SP := groupIndices GP g
  let SR := groupIndices GR g
  let P : ℝ := ((∏ i ∈ SP, slots t i : ℕ) : ℝ)
  let R : ℝ := ((∏ i ∈ SR, p i : ℕ) : ℝ)
  let LP := ∑ i ∈ SP, bP i
  let LR := ∑ i ∈ SR, bR (labels i)
  let DP := ∑ i ∈ SP, bP i - aP i
  let DR := ∑ i ∈ SR, bR (labels i) - aR (labels i)
  let beta : ℕ := if g = 2 then e else 1
  let Lb : ℝ := if g = 2 then ell else 0
  obtain ⟨hP, hPratio⟩ := product_window hN SP (slots t) aP bP hPlo hPhi
  have hR := fixed_group_length hN cap w Z aR bR labels GR p hrbox g
  have hRratio := (product_window hN SR p (fun i => aR (labels i))
    (fun i => bR (labels i)) hRlo hRhi).2
  have hbeta : (beta : ℝ) ≤ (N : ℝ) ^ Lb := by
    by_cases hg : g = 2
    · simpa only [beta, Lb, if_pos hg] using heupper
    · simp [beta, Lb, hg]
  have hbeta1 : (1 : ℝ) ≤ beta := by
    have hb : 1 ≤ beta := by dsimp [beta]; split_ifs <;> omega
    exact_mod_cast hb
  have hLb : Lb ≤ ell := by dsimp [Lb]; split_ifs <;> linarith
  have hDP : DP ≤ (4 : ℝ) * mesh := group_width_le GP g aP bP hmesh hPwidth
  have hDR : DR ≤ (r : ℝ) * mesh :=
    group_width_le GR g (fun i => aR (labels i)) (fun i => bR (labels i)) hmesh hRwidth
  have hexp : DP + DR + Lb ≤ tau := by
    simp only [Nat.cast_add, Nat.cast_ofNat] at hbudget
    linarith
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hQeq : fixedEndpoint N ell bP bR labels GP GR g =
      (N : ℝ) ^ LP * (N : ℝ) ^ LR * (N : ℝ) ^ Lb := by
    dsimp [fixedEndpoint, LP, LR, Lb, SP, SR]
    rw [Real.rpow_add hNp, Real.rpow_add hNp]
  have hFeq : (assignedProduct t p e GP GR g : ℝ) = P * R * beta := by
    simp only [assignedProduct, Nat.cast_mul]
    rfl
  constructor
  · rw [hFeq, hQeq]
    exact mul_le_mul (mul_le_mul hP hR hR0 (Real.rpow_nonneg hNp.le _)) hbeta
      (Nat.cast_nonneg beta) (mul_nonneg (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _))
  · rw [hFeq, hQeq]
    calc
      _ ≤ ((N : ℝ) ^ DP * P) * ((N : ℝ) ^ DR * R) * (N : ℝ) ^ Lb :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hPratio hRratio (Real.rpow_nonneg hNp.le _)
            (mul_nonneg (Real.rpow_nonneg hNp.le _) hP0)) (Real.rpow_nonneg hNp.le _)
      _ = (N : ℝ) ^ (DP + DR + Lb) * (P * R) := by
        rw [Real.rpow_add hNp, Real.rpow_add hNp]
        ring
      _ ≤ (N : ℝ) ^ tau * (P * R) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn.le hexp) (mul_nonneg hP0 hR0)
      _ ≤ (N : ℝ) ^ tau * (P * R * beta) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (mul_nonneg hP0 hR0) hbeta1)
          (Real.rpow_nonneg hNp.le _)

/-- The fixed dyadic factor2 is retained, not silently absorbed into ell
or the individual label widths. -/
theorem dyadic_ratio_of_fixed_ratio {F Q D P : ℝ}
    (hF : 0 ≤ F) (hP : 0 ≤ P) (hlo : F ≤ Q) (hhi : Q ≤ P * F)
    (hDlo : Q ≤ D) (hDhi : D ≤ 2 * Q) : F ≤ D ∧ D ≤ 2 * P * F := by
  refine ⟨hlo.trans hDlo, ?_⟩
  calc
    D ≤ 2 * Q := hDhi
    _ ≤ 2 * (P * F) := mul_le_mul_of_nonneg_left hhi (by norm_num)
    _ = _ := by ring

/-- The actual coefficient's constructor witnesses accept a fixed-group
encoding and literal box membership. The encoding is a FINITE PRODUCT
IDENTITY to be supplied by PrimeBox; it is not an endpoint or Medium gate
premise. No arbitrary fixed partition is claimed to encode the constructor.
Common-beta variation has the SAME physical level nu0*epsilon throughout. -/
theorem exists_actual_coefficient_fixed_box_length_threshold
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (nu0 epsilon : ℝ)
    (hnu : 0 < nu0) (hepsilon : 0 < epsilon)
    (heBudget : epsilon < OriginalCommonBetaActualParameters.epsilonBudget n eta nu0)
    {c C kappa kappa0 : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hk0 : 0 < kappa) (hk : kappa ≤ U1011OriginalFifteenMediumNumericGates.sigma n eta / 200)
    (ht0 : 0 < kappa0) (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      ∀ U : ℝ, x ^ (2 * U1011OriginalFifteenMediumNumericGates.zeta n eta) ≤ U →
      U ≤ x ^ (1 / 3 + U1011OriginalFifteenMediumNumericGates.zeta n eta / 2) →
      ∀ (E : ℕ × ℕ → Prop) (q : ℕ),
      OriginalJointPresievedCompiler.jointPresievedSigma n N eta
        ((N : ℝ) ^ (nu0 * epsilon ^ 2)) ((N : ℝ) ^ (nu0 * epsilon)) E q ≠ 0 →
      ∃ a b c : ℕ, a * b * c = q ∧
        ∀ {ι : Type*} {r : ℕ} (cap : ℕ) (w Z mesh : ℝ)
          (aP bP : Fin 4 → ℝ) (aR bR : ι → ℝ) (labels : Fin r → ι)
          (GP : Fin 4 → Fin 3) (GR : Fin r → Fin 3) (t : Four),
          t ∈ jointSelector N E → coordinates N t ∈ logPrimeBox aP bP →
          ∀ (p : Fin r → ℕ), List.ofFn p ∈ actualPrimeSlotBox
            (fun i => finePrimeSet N cap w Z (aR i) (bR i)) (List.ofFn labels) →
          ∀ e : ℕ, U1011OriginalW16SmallBetaMonomials.SmallBetaActive N cap e
            ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (nu0 * epsilon) →
          0 ≤ mesh → (∀ i, bP i - aP i ≤ mesh) →
          (∀ i, bR (labels i) - aR (labels i) ≤ mesh) →
          nu0 * epsilon + ((4 + r : ℕ) : ℝ) * mesh ≤
            OriginalAllSixteenPresievedEndpointGates.endpointTau n eta →
          (∀ g : Fin 3, assignedProduct t p e GP GR g = (![a, b, c] : Fin 3 → ℕ) g) →
          ∀ D : Fin 3 → ℝ,
            (∀ g, fixedEndpoint N (nu0 * epsilon) bP bR labels GP GR g ≤ D g) →
            (∀ g, D g ≤ 2 * fixedEndpoint N (nu0 * epsilon) bP bR labels GP GR g) →
            1 ≤ D 0 ∧ 1 ≤ D 1 ∧ 1 ≤ D 2 ∧
              U1011OriginalFifteenMediumNumericGates.NumericGates N x U
                (D 0) (D 1) (D 2) (U1011OriginalFifteenMediumNumericGates.sigma n eta) := by
  obtain ⟨_, N0, hN0, hlengths⟩ :=
    OriginalAllSixteenPresievedEndpointGates.exists_actual_all16_endpoint_medium_threshold
      n eta heta nu0 epsilon hnu hepsilon heBudget hc hC hk0 hk ht0 ht
  refine ⟨N0, hN0, ?_⟩
  intro N hN x hlow hupp U hUlo hUhi E q hq
  have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < N0) hN
  obtain ⟨_, _, _, hU⟩ := hlengths N hN x hlow hupp
  obtain ⟨a, b, c, hprod, hendpoint⟩ := hU U hUlo hUhi E q hq
  refine ⟨a, b, c, hprod, ?_⟩
  intro ι r cap w Z mesh aP bP aR bR labels GP GR t htup hpbox p hrbox e he
    hmesh hPwidth hRwidth hbudget hencode D hDlo hDhi
  obtain ⟨hepos, hesize, _⟩ := U1011OriginalW16SmallBetaMonomials.active_small_beta_data he
  have he1 : 1 ≤ e := by omega
  have hell : 0 ≤ nu0 * epsilon := (mul_pos hnu hepsilon).le
  have hratio := actual_fixed_group_endpoint_ratios hNN cap w Z (nu0 * epsilon) mesh
    (OriginalAllSixteenPresievedEndpointGates.endpointTau n eta)
    aP bP aR bR labels GP GR htup hpbox p hrbox e he1 hesize.le hell hmesh hPwidth hRwidth hbudget
  have hD (g : Fin 3) :
      ((![a, b, c] : Fin 3 → ℕ) g : ℝ) ≤ D g ∧
        D g ≤ 2 * (N : ℝ) ^ (OriginalAllSixteenPresievedEndpointGates.endpointTau n eta) *
          ((![a, b, c] : Fin 3 → ℕ) g : ℝ) := by
    have hr := hratio g
    rw [hencode g] at hr
    exact dyadic_ratio_of_fixed_ratio (Nat.cast_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _) hr.1 hr.2 (hDlo g) (hDhi g)
  have h0 := hD 0
  have h1 := hD 1
  have h2 := hD 2
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using
    hendpoint (D 0) (D 1) (D 2) h0.1 h0.2 h1.1 h1.2 h2.1 h2.2

end
end ImbalancedChen.P5Z.PresievedFixedGroupBetaEndpointRatios
