import ImbalancedChen.P4BOriginalSquarefreeP2
import ImbalancedChen.Part3TwoLongJointP2ModulusMoment
import ImbalancedChen.Part3TwoLongActualLowerCorePayment
import ImbalancedChen.P4BOriginalAllRankClassicalRange

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The original two-long EXPANDED Brun core, on any subset of the actual
P4 Q, is paid using the same signed final coefficient and exact mean.
The short coefficient is the existing signed ordered HB pushforward;
norms are taken only after the complete count-minus-mean has been formed.
All positive Brun divisor pairs, including nonprimitive short products,
are kept. The Poisson modulus is q itself, never c^2*d.

This pays the M*y^2*D^(3/2) term of original PP (E4). It does not identify
the rough pair with its upper Brun polynomial. The E1/E3 exact mean,
individual endpoint strips, original no-medium selection and final
mother integration remain separate obligations.
-/
namespace ImbalancedChen.P4BOriginalTwoLongExpandedCore
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P4BOriginalFiniteSmoothCount (Q coefficient)
open Part3.TwoLongHBMellinBrunProfiles
open Part3.TwoLongActualHBShortMass
open Part3.TwoLongActualLowerBrunMoment (brunSupport brunSupport_bounds brunPairCoefficient brunPair_mass)
open Part3.TwoLongActualThreeBrunP2Receiver (modulusBudget tau modulusBudget_nonneg)
open Part3.TwoLongActualLowerCorePayment (moment_log_budget)
open Part3.TwoLongMellinLogBudget
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualRoughHeathBrownWords (Role)

abbrev rho (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (L : ℝ)
    (v : ℕ) : ℂ := (coefficient m r n e q a omega k N L v : ℂ)

theorem actual_modulus_class (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N : ℕ) (L : ℝ) {v : ℕ} (hv : v ∈ Q omega N) :
    0 < v ∧ Nat.Coprime N v ∧ Squarefree v ∧ ‖rho m r n e q a omega k N L v‖ ≤ 1 := by
  have hsf := P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hv
  refine ⟨Nat.pos_of_ne_zero hsf.ne_zero,
    (P4AUpperTaggedBetaAttachment.support_coprime_target _ _ _ _ hv).symm, hsf, ?_⟩
  simpa only [rho, Complex.norm_real, Real.norm_eq_abs] using
    P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ v

/-- Inactive rectangular moduli cost zero. The fourth divisor moment is
used on the real active subset, retaining the exact physical rho. -/
theorem actual_modulus_moment (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N D : ℕ) (L : ℝ) (S : Finset ℕ) (hS : S ⊆ Q omega N)
    (hlevel : ∀ v ∈ S, coefficient m r n e q a omega k N L v ≠ 0 → v ≤ D) :
    (∑ v ∈ S, ‖rho m r n e q a omega k N L v‖ * modulusBudget v) ≤
      ((D : ℝ) * Real.sqrt D + 1) * (4 * (1 + Real.log (max 1 (D : ℝ))))^16 := by
  let c := rho m r n e q a omega k N L
  let A := S.filter (fun v => coefficient m r n e q a omega k N L v ≠ 0)
  have heq : (∑ v ∈ S, ‖c v‖ * modulusBudget v) =
      ∑ v ∈ A, ‖c v‖ * modulusBudget v := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hvA
    have hz : coefficient m r n e q a omega k N L v = 0 := by
      by_contra hn
      exact hvA (Finset.mem_filter.mpr ⟨hv, hn⟩)
    simp only [c, rho, hz, Complex.ofReal_zero, norm_zero, zero_mul]
  have hA : A ⊆ Finset.Icc 1 D := by
    intro v hv
    obtain ⟨hvS, hvn⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_Icc.mpr
      ⟨(actual_modulus_class m r n e q a omega k N L (hS hvS)).1, hlevel v hvS hvn⟩
  have hp := Part3.TwoLongJointP2ModulusMoment.squarefree_p2_modulus_moment A D c hA
    (fun v hv => (actual_modulus_class m r n e q a omega k N L
      (hS (Finset.mem_filter.mp hv).1)).2.2.1)
    (fun v hv => (actual_modulus_class m r n e q a omega k N L
      (hS (Finset.mem_filter.mp hv).1)).2.2.2)
  change (∑ v ∈ S, ‖c v‖ * modulusBudget v) ≤ _
  rw [heq]
  simpa only [modulusBudget, tau] using hp

def brunCore (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (L Z : ℝ)
    (S : Finset ℕ) (j : ℕ) (b₁ b₂ : Bool) (delta U V t₁ t₂ : ℝ)
    (label : Fin 3) (log₁ log₂ : Bool) (alpha : ℂ) (short : ℕ) : ℂ :=
  ∑ v ∈ S, rho m r n e q a omega k N L v *
    ∑ d ∈ (brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1)),
      brunPairCoefficient Z j b₁ b₂ d *
        mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha short d.1 d.2 N v

/-- A concrete P4 coefficient and the original two-long source. No Weil,
P2, discrepancy or coprime-mean bound is taken as an assumption. -/
theorem actual_Brun_P2 (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N D : ℕ) (L : ℝ) (S : Finset ℕ) (hS : S ⊆ Q omega N)
    (hlevel : ∀ v ∈ S, coefficient m r n e q a omega k N L v ≠ 0 → v ≤ D)
    {Z delta U V H t₁ t₂ : ℝ} (hZ : 1 ≤ Z) (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (j : ℕ) (b₁ b₂ : Bool) (label : Fin 3) (log₁ log₂ : Bool) (alpha : ℂ) (short : ℕ) :
    ‖brunCore m r n e q a omega k N L Z S j b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ alpha short‖ ≤
      pairCost delta U V H * ((Z^(2*j+1))^2 * ‖alpha‖) *
        (((D : ℝ) * Real.sqrt D + 1) * (4 * (1 + Real.log (max 1 (D : ℝ))))^16) := by
  let c := rho m r n e q a omega k N L
  let R := (brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1))
  have hpoint (v : ℕ) (hv : v ∈ S) (d : ℕ×ℕ) (hdr : d ∈ R) :
      ‖mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha short d.1 d.2 N v‖ ≤
        pairCost delta U V H * ‖alpha‖ * modulusBudget v := by
    obtain ⟨hvpos, hcop, hsf, _⟩ := actual_modulus_class m r n e q a omega k N L (hS hv)
    exact P4BOriginalSquarefreeP2.mellinBrunCore_internalP2 hsf hd hs hU hV hH ht₁ ht₂
      label log₁ log₂ alpha short d.1 d.2 N
      (brunSupport_bounds hZ _ (Finset.mem_product.mp hdr).1).1
      (brunSupport_bounds hZ _ (Finset.mem_product.mp hdr).2).1 hvpos hcop
  have hfinite : ‖brunCore m r n e q a omega k N L Z S j b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ alpha short‖ ≤
      pairCost delta U V H * (∑ d ∈ R, ‖brunPairCoefficient Z j b₁ b₂ d‖ * ‖alpha‖) *
        (∑ v ∈ S, ‖c v‖ * modulusBudget v) := by
    unfold brunCore
    calc
      _ ≤ ∑ v ∈ S, ‖c v‖ * ∑ d ∈ R, ‖brunPairCoefficient Z j b₁ b₂ d‖ *
          ‖mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha short d.1 d.2 N v‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
      _ ≤ ∑ v ∈ S, ‖c v‖ * ∑ d ∈ R, ‖brunPairCoefficient Z j b₁ b₂ d‖ *
          (pairCost delta U V H * ‖alpha‖ * modulusBudget v) := by
        apply Finset.sum_le_sum
        intro v hv
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Finset.sum_le_sum
        intro d hdr
        exact mul_le_mul_of_nonneg_left (hpoint v hv d hdr) (norm_nonneg _)
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro d hdr
        ring
  exact hfinite.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (brunPair_mass hZ j b₁ b₂ alpha) (pairCost_nonneg _ _ _ _))
    (actual_modulus_moment m r n e q a omega k N D L S hS hlevel)
    (Finset.sum_nonneg (fun v hv => mul_nonneg (norm_nonneg _) (modulusBudget_nonneg _)))
    (mul_nonneg (pairCost_nonneg _ _ _ _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowCore (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (L Z : ℝ)
    (S : Finset ℕ) (j : ℕ) (b₁ b₂ : Bool) (delta U V t₁ t₂ : ℝ)
    (label : Fin 3) (log₁ log₂ : Bool) (bs : ι → Block)
    (y xi : ι → ℝ) (rs : ι → Role) : ℂ :=
  ∑ short ∈ shortSupport bs,
    brunCore m r n e q a omega k N L Z S j b₁ b₂ delta U V t₁ t₂ label log₁ log₂
      (shortSequence bs Z y xi rs short) short

theorem rowCore_bound (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N D : ℕ) (L : ℝ) (S : Finset ℕ) (hS : S ⊆ Q omega N)
    (hlevel : ∀ v ∈ S, coefficient m r n e q a omega k N L v ≠ 0 → v ≤ D)
    {Z X delta U V H t₁ t₂ : ℝ} (hZ : 1 ≤ Z) (hX : 1 ≤ X)
    (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (j : ℕ) (b₁ b₂ : Bool) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role)
    (hcap : ∀ i, 2 * (lower (bs i) : ℝ) ≤ X) :
    ‖rowCore m r n e q a omega k N L Z S j b₁ b₂ delta U V t₁ t₂ label log₁ log₂ bs y xi rs‖ ≤
      pairCost delta U V H * ((shortScale bs : ℝ) * (Z^(2*j+1))^2) *
        (((D : ℝ) * Real.sqrt D + 1) * (4 * (1 + Real.log (max 1 (D : ℝ))))^16) *
          (1 + Real.log X)^Fintype.card ι := by
  let T := ((D : ℝ) * Real.sqrt D + 1) * (4 * (1 + Real.log (max 1 (D : ℝ))))^16
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hm := shortSequence_mass bs Z y xi rs hX hcap
  calc
    _ ≤ ∑ short ∈ shortSupport bs,
        pairCost delta U V H * ((Z^(2*j+1))^2 * ‖shortSequence bs Z y xi rs short‖) * T := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun short _ => actual_Brun_P2 m r n e q a omega k N D L S
        hS hlevel hZ hd hs hU hV hH ht₁ ht₂ j b₁ b₂ label log₁ log₂ _ short)
    _ = (pairCost delta U V H * (Z^(2*j+1))^2 * T) *
        ∑ short ∈ shortSupport bs, ‖shortSequence bs Z y xi rs short‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro short hshort
      ring
    _ ≤ (pairCost delta U V H * (Z^(2*j+1))^2 * T) *
        ((shortScale bs : ℝ) * (1 + Real.log X)^Fintype.card ι) :=
      mul_le_mul_of_nonneg_left hm
        (mul_nonneg (mul_nonneg (pairCost_nonneg _ _ _ _) (sq_nonneg _)) hT)
    _ = _ := by dsimp [T]; ring

theorem short_log_budget {s : ℕ} (hs : s ≤ 12) {x : ℝ} (hlog : 1 ≤ Real.log x) :
    (1 + Real.log x)^s ≤ 4096 * (Real.log x)^12 := by
  calc
    _ ≤ (1 + Real.log x)^12 := pow_le_pow_right₀ (by linarith) hs
    _ ≤ (2 * Real.log x)^12 := pow_le_pow_left₀ (by linarith) (by linarith) 12
    _ = _ := by ring

/-- The actual P4 two-long expanded core has arbitrary logarithmic saving.
The allowance 12 covers the original TWO order-three HB mothers; it is
not the older single-mother rank-six bound. The support and complete-scale
conditions are geometric gates, never assumed discrepancy estimates. -/
theorem eventually_actual_upper_core_paid (B K A : ℕ) (hB : 1 ≤ B)
    (c : ℝ) (hc : 0 < c) (zeta theta epsilon : ℝ) (hepsilon : 0 < epsilon)
    (htheta : theta ≤ 1) (hmargin : 40*zeta + 2*epsilon + 3*theta/2 < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N D : ℕ) (L : ℝ)
        (S : Finset ℕ) (Z U V t₁ t₂ : ℝ) (j : ℕ) (b₁ b₂ : Bool) (label : Fin 3)
        (log₁ log₂ : Bool) (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role),
      Fintype.card ι ≤ 12 → S ⊆ Q omega N → 1 ≤ D → 1 ≤ Z →
      (∀ v ∈ S, coefficient m r n e q a omega k N L v ≠ 0 → v ≤ D) →
      (D : ℝ) ≤ x^theta → (shortScale bs : ℝ) ≤ x^(40*zeta) → Z^(2*j+1) ≤ x^epsilon →
      (∀ i, 2 * (lower (bs i) : ℝ) ≤ x) → 1 ≤ U → 1 ≤ V → U ≤ c*x → V ≤ c*x →
      |t₁| ≤ (Real.log x)^K → |t₂| ≤ (Real.log x)^K →
      ‖rowCore m r n e q a omega k N L Z S j b₁ b₂ ((Real.log x)^B)⁻¹ U V t₁ t₂
        label log₁ log₂ bs y xi rs‖ ≤ x/(Real.log x)^A := by
  filter_upwards [eventually_schedule B hB,
    eventually_twoLong_E4_monomial B K 29 A c hc zeta theta epsilon hepsilon hmargin,
    Real.tendsto_log_atTop.eventually_ge_atTop (8192 * 8^16 : ℝ)]
    with x hsched hpay hlarge
  intro ι instF instD m r n e q a omega k N D L S Z U V t₁ t₂ j b₁ b₂ label log₁ log₂
    bs y xi rs hrank hS hD hZ hlevel hDx hMx hyx hcap hU hV hUx hVx ht₁ ht₂
  have hx := hpay.1
  have hlog := hpay.2.1
  have hl0 : 0 ≤ Real.log x := zero_le_one.trans hlog
  have hDX : (D : ℝ) ≤ x := hDx.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx htheta)
  have hp := rowCore_bound m r n e q a omega k N D L S hS hlevel hZ hx
    hsched.2.1 hsched.2.2 (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV)
    (pow_nonneg hl0 K) ht₁ ht₂ j b₁ b₂ label log₁ log₂ bs y xi rs hcap
  have hM : 0 ≤ (shortScale bs : ℝ) := Nat.cast_nonneg _
  have hy : 0 ≤ Z^(2*j+1) := pow_nonneg (zero_le_one.trans hZ) _
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K) *
        ((shortScale bs : ℝ) * (Z^(2*j+1))^2) *
        ((2*8^16 : ℝ)*(D : ℝ)^(3/2 : ℝ)*(Real.log x)^16) *
        (4096*(Real.log x)^12) := by
      apply hp.trans
      gcongr
      · exact moment_log_budget hD hlog hDX
      · exact short_log_budget hrank hlog
    _ = pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K) *
        ((shortScale bs : ℝ) * (Z^(2*j+1))^2 * (D : ℝ)^(3/2 : ℝ)) *
        ((8192*8^16 : ℝ)*(Real.log x)^28) := by ring
    _ ≤ pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K) *
        ((shortScale bs : ℝ) * (Z^(2*j+1))^2 * (D : ℝ)^(3/2 : ℝ)) *
        (Real.log x)^29 := by
      apply mul_le_mul_of_nonneg_left _ (by
        exact mul_nonneg (pairCost_nonneg _ _ _ _)
          (mul_nonneg (mul_nonneg hM (sq_nonneg _)) (Real.rpow_nonneg hD0 _)))
      calc
        _ ≤ Real.log x * (Real.log x)^28 :=
          mul_le_mul_of_nonneg_right hlarge (pow_nonneg hl0 _)
        _ = _ := by ring
    _ ≤ _ := hpay.2.2 (shortScale bs) (Z^(2*j+1)) D U V hM hy hD0
      hMx hyx hDx hU hV hUx hVx

end
end ImbalancedChen.P4BOriginalTwoLongExpandedCore
