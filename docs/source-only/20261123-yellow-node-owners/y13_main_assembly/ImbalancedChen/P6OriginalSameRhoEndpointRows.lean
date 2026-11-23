import ImbalancedChen.P6OriginalFineOuterRow
import ImbalancedChen.P5OriginalFineSwitchedCosts
import ImbalancedChen.P6OriginalMarkedIntegralPrices
import ImbalancedChen.P6StrictCoefficientThreshold
import ImbalancedChen.P6OriginalEndpointAssembly

/-! Quantitative count receipts at the three printed exponents. Every physical
PP row uses the very same attached family and coefficient. The five grouped
costs and three integral comparisons are displayed on the original weight scale.
The outstanding rows have no assumed sign or distribution estimate. -/
namespace ImbalancedChen.P6OriginalSameRhoEndpointRows

noncomputable section
open Filter
open P4BOriginalFineAttachedUpper (Selection)
open P4BOuterRampRoughness (baseline)
open P6OriginalFineOuterRow (outerRow exists_width_signed_upper)
open P5OriginalFineSwitchedCosts (seventhError eighthError ninthError)
open P5OriginalCoefficientArithmetic
open P6OriginalMarkedIntegralPrices (Mesh)

variable {m r n q : ℕ} {e : ℚ} {a η B z : ℝ} {ft : ℝ → ℝ}

/-- Each group is compared with its own original endpoint. Favorable signed
fluctuations in a group do not erase another group's unpaid cost. -/
def remainingGroupCost (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  let H := singularNormalization N
  max (originalGroupedStarts*H - (3*currentChenUpsilon1 N + currentChenUpsilon2 N)) 0 +
  max (currentChenUpsilon3 N + currentChenUpsilon4 N - originalGroupedU34*H) 0 +
  max (savedL5*H - currentChenUpsilon5 N) 0 +
  max (originalRetainedL6*H - currentChenUpsilon6 N E) 0 +
  max (currentChenUpsilon10 N + currentChenUpsilon11 N E -
    originalJointRawCost fixedProductDensityCoefficient*H) 0

/-- Signed arithmetic rows are left on their physical source. The conversion
from weight scale to count scale is performed in the endpoint inequality. -/
def weightCost (g : Mesh) (s : Selection m r n e q a 1 (19/96) η B z ft) (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  remainingGroupCost N E + g.rate*singularNormalization N + 2*seventhError s N + eighthError s N + ninthError s N

private theorem count_with_weight_cost (g : Mesh) (s : Selection m r n e q a 1 (19/96) η B z ft)
    (he : 0 ≤ e) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ E : ℕ × ℕ → Prop,
      (4*currentC - t)*singularNormalization N ≤ 4*(D12 N : ℝ) + weightCost g s N E := by
  have hd : 0 < t/5 := by linarith
  filter_upwards [P5OriginalFineSwitchedCosts.three_costs s he zero_lt_one (by norm_num) hd hd hd,
    eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12 (t/5) hd,
    eventually_singularNormalization_pos] with N hsw hbridge hH
  intro hev E
  obtain ⟨h7, h8, h9⟩ := hsw hev
  have hcount := hbridge E
  rw [currentChenPairedPrimeSum_eq_upsilon] at hcount
  let H := singularNormalization N
  let k := fixedProductDensityCoefficient
  have hc := mul_le_mul_of_nonneg_right fixed_originalGroupedCoefficient_gt_currentC.le hH.le
  have hraw := mul_le_mul_of_nonneg_right (originalJointFinalCost_is_weakening k) hH.le
  have hs := le_max_left (originalGroupedStarts*H - (3*currentChenUpsilon1 N+currentChenUpsilon2 N)) 0
  have h34 := le_max_left (currentChenUpsilon3 N+currentChenUpsilon4 N-originalGroupedU34*H) 0
  have h5 := le_max_left (savedL5*H-currentChenUpsilon5 N) 0
  have h6 := le_max_left (originalRetainedL6*H-currentChenUpsilon6 N E) 0
  have h1011 := le_max_left (currentChenUpsilon10 N+currentChenUpsilon11 N E-originalJointRawCost k*H) 0
  have hi := g.integral_prices hH.le
  dsimp only [originalGroupedCoefficient] at hc
  dsimp only [weightCost, remainingGroupCost]
  dsimp only [H, k] at hs h34 h5 h6 h1011 hraw
  linarith only [hc,hraw,hs,h34,h5,h6,h1011,hi,h7,h8,h9,hcount]

/-- Half the original strict margin remains available for actual arithmetic costs. -/
def credit (b target : ℝ) := (currentC - currentK*Real.log (1/b) - target)/2

/-- A strict numerical margin fixes one legal physical width for the given
exponent. The remaining weight-scale costs enter with 1/4, the bad row with 1. -/
theorem exists_width_count_receipt (g : Mesh) (s : Selection m r n e q a 1 (19/96) η B z ft) (he : 0 ≤ e)
    {b target : ℝ} (hb : (1/2 : ℝ) < b) (hb1 : b < 1)
    (hmargin : target < currentC-currentK*Real.log (1/b)) :
    ∃ w : ℝ, 0 < w ∧ 2*w ≤ baseline b (1/4) - 1*(19/96) ∧
      ∀ᶠ N : ℕ in atTop, Even N → ∀ E : ℕ × ℕ → Prop,
        (target + credit b target)*singularNormalization N ≤
          (RealDb b N : ℝ) + outerRow s b w N + weightCost g s N E/4 := by
  let d := (currentC - currentK*Real.log (1/b) - target)/4
  have hd : 0 < d := by dsimp [d]; linarith only [hmargin]
  obtain ⟨w,hw,hg,hu⟩ := exists_width_signed_upper s hb hb1 hd
  refine ⟨w,hw,hg,?_⟩
  filter_upwards [hu, count_with_weight_cost g s he (show 0 < 4*d by linarith)] with N huN hlN
  intro hev E
  have hl := hlN hev E
  have hupper := huN hev
  rw [RealDb_cast_eq_D12_sub_RealB]
  unfold credit
  dsimp only [d] at hl hupper
  linarith only [hl,hupper]

/-- A count receipt on one physical target and a literal representation when
the three displayed scales fit inside its positive strict margin. -/
def AtEndpoint (g : Mesh) (s : Selection m r n e q a 1 (19/96) η B z ft)
    (b target w : ℝ) (N : ℕ) (E : ℕ × ℕ → Prop) (lowerCount : ℝ) : Prop :=
  let H := singularNormalization N
  let cost := outerRow s b w N + weightCost g s N E/4
  lowerCount + credit b target*H ≤ (RealDb b N : ℝ) + cost ∧
    (cost ≤ credit b target*H →
      lowerCount ≤ (RealDb b N : ℝ) ∧
      ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^b)

private theorem atEndpoint_of_count {g : Mesh} {s : Selection m r n e q a 1 (19/96) η B z ft}
    {b target w : ℝ} {N : ℕ} {E : ℕ × ℕ → Prop} {L : ℝ}
    (hb : 0 ≤ b) (hL : L = target*singularNormalization N) (hp : 0 < L)
    (hc : (target + credit b target)*singularNormalization N ≤
      (RealDb b N : ℝ) + outerRow s b w N + weightCost g s N E/4) :
    AtEndpoint g s b target w N E L := by
  dsimp only [AtEndpoint]
  have h : L + credit b target*singularNormalization N ≤
      (RealDb b N : ℝ) + (outerRow s b w N + weightCost g s N E/4) := by
    rw [hL]
    linarith only [hc]
  refine ⟨h, ?_⟩
  intro hPaid
  have hcount : L ≤ (RealDb b N : ℝ) := by linarith only [h,hPaid]
  have hreal : (0 : ℝ) < (RealDb b N : ℝ) := hp.trans_le hcount
  have hnat : 0 < RealDb b N := by exact_mod_cast hreal
  exact ⟨hcount, P6.exists_literal_representation_of_realDb_pos hb hnat⟩

/-- The Fine policy is obtained for the prescribed mesh and beta cap. A single
threshold >= 4 serves every original mask and all three exponents. Widths
may differ, while all nine physical tests share the attached Q and rho. -/
theorem exists_three_original_endpoint_receipts (g : Mesh) (a z B : ℝ) (ha : 0 < a) (ha1 : a ≤ 1/800)
    (hz : 0 < z) (hB : 0 < B) (ft : ℝ → ℝ) (hft : ∀ x : ℝ, 0 < x → 0 < ft x) (qMin mMin : ℕ) :
    ∃ (m r n : ℕ) (e : ℚ) (q : ℕ) (η : ℝ) (s : Selection m r n e q a 1 (19/96) η B z ft),
      qMin ≤ q ∧ mMin ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q ∧
      ∃ w₁ w₂ w₃ : ℝ,
        (0 < w₁ ∧ 2*w₁ ≤ baseline (18704241/25000000) (1/4) - 1*(19/96)) ∧
        (0 < w₂ ∧ 2*w₂ ≤ baseline (14963373/20000000) (1/4) - 1*(19/96)) ∧
        (0 < w₃ ∧ 2*w₃ ≤ baseline (9/10) (1/4) - 1*(19/96)) ∧
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N → ∀ E : ℕ × ℕ → Prop,
          AtEndpoint g s (18704241/25000000) (1/100000) w₁ N E (singularNormalization N/100000) ∧
          AtEndpoint g s (14963373/20000000) (1/1000000) w₂ N E (singularNormalization N/1000000) ∧
          AtEndpoint g s (9/10) (124889/100000) w₃ N E ((124889/100000)*singularNormalization N) := by
  obtain ⟨m,r,n,e,q,η,he,_,hq,_,_,hm,_,_,⟨s⟩⟩ :=
    P4BOriginalFineAttachedUpper.exists_counting_selection a z B ha ha1 hz hB ft hft qMin mMin
  obtain ⟨w₁,hw₁,hg₁,h₁⟩ := exists_width_count_receipt g s he.le
    P6.current_exponent_74816964_domain.1 P6.current_exponent_74816964_domain.2 P6.currentCoefficient_gap_74816964
  obtain ⟨w₂,hw₂,hg₂,h₂⟩ := exists_width_count_receipt g s he.le
    P6.current_exponent_74816865_domain.1 P6.current_exponent_74816865_domain.2 P6.currentCoefficient_gap_74816865
  obtain ⟨w₃,hw₃,hg₃,h₃⟩ := exists_width_count_receipt g s he.le
    P6.current_exponent_09_domain.1 P6.current_exponent_09_domain.2 P6.currentCoefficient_gap_09
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (4 : ℕ)).and
    (eventually_singularNormalization_pos.and (h₁.and (h₂.and h₃))))
  refine ⟨m,r,n,e,q,η,s,hq,hm,w₁,w₂,w₃,⟨hw₁,hg₁⟩,⟨hw₂,hg₂⟩,⟨hw₃,hg₃⟩,N₀,(hN₀ N₀ le_rfl).1,?_⟩
  intro N hN hev E
  obtain ⟨_,hH,hA,hB',hC⟩ := hN₀ N hN
  refine ⟨atEndpoint_of_count (by norm_num) (by ring) (div_pos hH (by norm_num)) (hA hev E),
    atEndpoint_of_count (by norm_num) (by ring) (div_pos hH (by norm_num)) (hB' hev E),
    atEndpoint_of_count (by norm_num) rfl (mul_pos (by norm_num) hH) (hC hev E)⟩

end
end ImbalancedChen.P6OriginalSameRhoEndpointRows
