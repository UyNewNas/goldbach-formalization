import ImbalancedChen.Part5OriginalH430ClassicalSmoothPhysicalCharts
import ImbalancedChen.Part5OriginalH430ClassicalFixedClampCredit

/-! Pre-target mixed orders and log-size summation for the original
positive classical word family. U* receives the enlarged ordinary price
J+eta. No tested distribution or signed PP estimate is assumed here. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothFamilyLicence
noncomputable section
open Finset Filter Set Real Wu2008DoubleSieve
open P2SeedOmegaLiteralFunctional (switchCost)
open Part5OriginalH430RootIntervalTheta (clampLevel clampMass)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum words_const words_mono)
open Part5OriginalH430ClassicalFixedClampMarks (count frozen_bounds)
open Part5OriginalH430ClassicalFixedClampSeedPrice (J geometric_raw_J)
open Part5OriginalH430ClassicalFixedClampCredit (paper_upper_price_fits)
open Part5OriginalH430ClassicalRadialTupleCount (absolute_radial_payment)
open Part5OriginalH430ClassicalProperWallSeedCredit (absolute_proper_payment)
open Part5OriginalH430ClassicalThinRadialTail (absolute_thin_payment lower_wall_in_tail)
open Part5OriginalH430ClassicalAllBoundaryCredit (totalAmbient)
open Part5OriginalH430ClassicalRadialMarkedRanks (transition_floor)
open Part5OriginalH430ClassicalSmoothSharpGates (code)
open Part5OriginalH430ClassicalSmoothRankCoordinates (rank)
open Part5OriginalH430ClassicalSmoothRankAccounting (tails)
open Part5OriginalH430ClassicalSmoothMarkedFamily (smoothCount dominates ordinary_excess)
open Part5OriginalH430ClassicalSmoothDyadicFamily (Rect rectangle_count)
open Part5OriginalH430ClassicalSmoothEulerProfile (Param chart chart_budget)
open Part5OriginalH430ClassicalSmoothPhysicalCharts (centre primeChart realRectangle chart_identity)
open scoped Classical Topology BigOperators ContDiff

/-- A single constant for each full Fréchet order, all ranks and every
physical location. The finite set is used only for the maximum bound;
the real source still sums every repeated word. -/
theorem common_chart_budget (ν : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hc : 0<c) (d : ℕ) :
    ∃ B : ℝ,0≤B ∧ ∀ (j : Fin 13) (cs : List ℕ),cs∈secondFunctionalMotherGammaWords (9+j.val) →
      ∀ r∈tails cs.length,∀ (N : ℕ),2≤N → ∀ (b : Rect (rank cs.length r) N)
      (u : Fin (rank cs.length r) → ℝ),
        ‖iteratedFDeriv ℝ d (fun v => realRectangle (code cs) b ν δ h c (primeChart b v)) u‖≤B := by
  let S := (univ : Finset (Fin 13)).biUnion (fun j => (secondFunctionalMotherGammaWords (9+j.val)).toFinset)
  choose C hC hbound using (fun (cs : List ℕ) (r : ℕ) => (chart_budget (r:=r) (code cs) ν hd hh hc).2 d)
  let Cword := fun cs : List ℕ => ∑ r∈tails cs.length,C cs r
  have hword (cs : List ℕ) : 0≤Cword cs := sum_nonneg (fun r _ => hC cs r)
  refine ⟨∑ cs∈S,Cword cs,sum_nonneg (fun cs _ => hword cs),?_⟩
  intro j cs hj r hr N hN b u
  have hw : cs∈S := mem_biUnion.mpr ⟨j,mem_univ _,List.mem_toFinset.mpr hj⟩
  have he : (fun v => realRectangle (code cs) b ν δ h c (primeChart b v))=
      chart (code cs) ν δ h c (⟨N,hN⟩,centre b) := funext (chart_identity hN (code cs) b ν δ h c)
  rw [he]
  exact ((hbound cs r (⟨N,hN⟩,centre b) u).trans (single_le_sum (fun q _ => hC cs q) hr)).trans
    (single_le_sum (fun cs _ => hword cs) hw)

theorem all_rectangles (N : ℕ) (hN : 1≤N) :
    wordsSum (fun cs => ∑ r∈tails cs.length,(Fintype.card (Rect (rank cs.length r) N):ℝ))≤
      20*201*(3+log (N:ℝ)/log 2)^200 := by
  let X := 3+log (N:ℝ)/log 2
  have hX : 1≤X := by
    have hx := div_nonneg (log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N))
      (log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp only [X]
    linarith only [hx]
  have H := words_mono (F:=fun cs => ∑ r∈tails cs.length,(Fintype.card (Rect (rank cs.length r) N):ℝ))
    (G:=fun _ => 201*X^200) (by
      intro _ cs _
      have hh := sum_le_sum (s:=tails cs.length) (fun r hr => (rectangle_count (rank cs.length r) N hN).trans
        (pow_le_pow_right₀ hX (mem_filter.mp hr).2))
      have ht : (tails cs.length).card≤201 := (card_le_card (filter_subset _ _)).trans_eq (card_range 201)
      simp only [sum_const,nsmul_eq_mul] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (pow_nonneg (zero_le_one.trans hX) _)))
  rw [words_const] at H
  simpa only [X,mul_assoc] using H

/-- For each desired original price tolerance one fixed smooth family
dominates the prime count, has limsup at most J+eta, and leaves a positive
absolute normalized allowance for the physical positive theorem's errors. -/
theorem original_positive_family {n : ℕ} {τ κ ε : ℝ} (ht : 0≤τ) (ht' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hk : 0<κ) (hk' : κ≤1/112) (he : 0<ε) :
    let ν := clampLevel n τ
    ∃ h δ c η γ : ℝ,0<h ∧ h≤1/8 ∧ 0<δ ∧ 0<c ∧ c≤1/8 ∧ 0<η ∧ 0<γ ∧
      (∀ᶠ N : ℕ in atTop,∀ tested : Bool,count tested 1 N ν κ≤smoothCount tested N ν δ h c) ∧
      (∀ e : ℝ,0<e → ∀ᶠ N : ℕ in atTop,(log (N:ℝ)/(N:ℝ))*smoothCount false N ν δ h c≤(J ν+η)+e) ∧
      (∀ᶠ N : ℕ in atTop,((8452171/1250000)*(J ν+η)+γ)*singularNormalization N≤
        switchCost*clampMass N n τ+ε*clampMass N n τ) := by
  let ν := clampLevel n τ
  let K : ℝ := 8452171/1250000
  have hK : 0<K := by norm_num [K]
  obtain ⟨β,hβ,hprice⟩ := paper_upper_price_fits ht ht' hn he
  let η := β/(2*K)
  have hη : 0<η := div_pos hβ (mul_pos (by norm_num) hK)
  let γ := β/2
  have hγ : 0<γ := half_pos hβ
  have heq : K*(J ν+η)+γ=K*J ν+β := by
    unfold η γ
    field_simp [hK.ne'] <;> ring
  have hthird : 0<η/3 := by positivity
  obtain ⟨h,hh,hh',hrad⟩ := absolute_radial_payment hthird
  obtain ⟨δ,hδ,hproper⟩ := absolute_proper_payment ν hthird
  obtain ⟨c,hc,hc',hthin⟩ := absolute_thin_payment hthird
  obtain ⟨hν,hν'⟩ := frozen_bounds ht ht' hn
  refine ⟨h,δ,c,η,γ,hh,hh',hδ,hc,hc',hη,hγ,?_,?_,?_⟩
  · filter_upwards [eventually_gt_atTop (1:ℕ)] with N hN
    exact fun tested => dominates tested hN hν hν' hk' hδ hh
  · intro e he'
    filter_upwards [geometric_raw_J hν hν' hk' he',hrad,hproper,hthin,transition_floor,
      lower_wall_in_tail hk (half_pos hc),eventually_gt_atTop (1:ℕ)]
      with N hJ hradN hproperN hthinN hz hlow hN
    have hNr : (1:ℝ)<N := by exact_mod_cast hN
    have hnonneg := div_nonneg (log_pos hNr).le (Nat.cast_nonneg N)
    have hpay := mul_le_mul_of_nonneg_left (ordinary_excess hN hν hν' hk' hδ hh hh' hc hc' hlow hz) hnonneg
    dsimp only [totalAmbient] at hpay
    simp only [mul_add] at hpay
    dsimp only [Part5OriginalH430ClassicalRadialRoughMass.norm] at hradN
    linarith only [hpay,hJ,hradN,hproperN,hthinN]
  · simpa only [←heq] using hprice

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothFamilyLicence

