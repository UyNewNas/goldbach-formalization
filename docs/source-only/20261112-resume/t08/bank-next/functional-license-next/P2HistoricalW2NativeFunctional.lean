import ImbalancedChen.P2HistoricalLowTargetEdges
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledFeedbackRows

/-! The genuine fixed-delta second functional at each of the 3+33
historical parameter tuples, with its own physical mother and signed cost. -/
namespace ImbalancedChen.P2HistoricalW2NativeFunctional

noncomputable section
open Set MeasureTheory Wu2008DoubleSieve
open P2HistoricalSourceJSON P2Historical248Authentication P2HistoricalScheduledPointReads
open P2HistoricalNativePointCounts P2HistoricalLowTargetEdges P2HistoricalHighPointAncestry
open P2HistoricalLowerBankAncestry P2TableActionSourceOnly
open scoped Interval

def param (v : Value) (j : ℕ) : ℚ := rational (at (field v "parameters") j)
def native (v : Value) : SecondFunctionalParameters :=
  ⟨(param v 0 : ℝ), (anchor0 v : ℝ), (anchor1 v : ℝ), (param v 3 : ℝ), (param v 4 : ℝ)⟩
def ordered (v : Value) : Bool := decide
  (2 < param v 0 ∧ param v 0 ≤ 3 ∧ 3 ≤ anchor0 v ∧ anchor0 v ≤ 5 ∧
    param v 0 ≤ param v 4 ∧ param v 4 < param v 3 ∧
    param v 3 < anchor1 v ∧ anchor1 v ≤ anchor0 v)

/-- Coordinates only; neither the effective base nor any table or kernel
value is inspected. -/
private theorem coordinate_order : (oldRows ++ addedRows).all ordered = true := by decide

private theorem left_repriced {vs us : List Value} {b : Tagged} (hb : b ∈ reprice vs us) : b.1∈vs := by
  induction vs generalizing us with
  | nil => simp [reprice] at hb
  | cons v vs ih =>
    cases us with
    | nil => simp [reprice] at hb
    | cons u us =>
      change b ∈ _ :: reprice vs us at hb
      rcases List.mem_cons.mp hb with he | he
      · subst b; exact List.mem_cons_self
      · exact List.mem_cons_of_mem v (ih he)

private theorem left_tagged {vs : List Value} {b : Tagged} (hb : b∈tag vs) : b.1∈vs := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  exact hv

theorem original_parameters (g : ℕ) {b : Tagged} (hb : b∈taggedW2 g) : b.1∈oldRows++addedRows := by
  unfold taggedW2 at hb
  split_ifs at hb
  · simp at hb
  · exact List.mem_append.mpr (Or.inl (left_tagged hb))
  · exact List.mem_append.mpr (Or.inl (left_repriced hb))
  · exact List.mem_append.mpr (Or.inl (left_repriced hb))
  · rcases List.mem_append.mp hb with h | h
    · exact List.mem_append.mpr (Or.inl (left_repriced h))
    · exact List.mem_append.mpr (Or.inr (left_tagged h))

theorem admitted {v : Value} (hv : v∈oldRows++addedRows) : MotherPair.AnalyticParameters (native v) := by
  have hp := of_decide_eq_true (List.all_eq_true.mp coordinate_order v hv)
  rcases hp with ⟨hs,h3,hS,h5,hs3,h32,h21,h1S⟩
  have hsR : (2 : ℝ)<(param v 0 : ℝ) := by exact_mod_cast hs
  have hSR : (anchor0 v : ℝ)≤5 := by exact_mod_cast h5
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · change 1 ≤ (param v 0 : ℝ); linarith
  · change (param v 0 : ℝ) ≤ (param v 4 : ℝ); exact_mod_cast hs3
  · change (param v 4 : ℝ) < (param v 3 : ℝ); exact_mod_cast h32
  · change (param v 3 : ℝ) < (anchor1 v : ℝ); exact_mod_cast h21
  · change (anchor1 v : ℝ) ≤ (anchor0 v : ℝ); exact_mod_cast h1S
  · change (anchor0 v : ℝ) ≤ 10; linarith
  · exact hsR
  · change (param v 0 : ℝ) ≤ 3; exact_mod_cast h3
  · change 3 ≤ (anchor0 v : ℝ); exact_mod_cast hS
  · exact hSR

def oldFirst := at (field jsonOldW2 "actions") 0

theorem old_first_eq_native_row_one : native oldFirst = SecondFunctionalParameters.row1 := by
  have ho : param oldFirst 0=11/5 ∧ anchor0 oldFirst=227/50 ∧ anchor1 oldFirst=353/100 ∧
      param oldFirst 3=29/10 ∧ param oldFirst 4=61/25 := by decide
  unfold native SecondFunctionalParameters.row1
  rw [ho.1,ho.2.1,ho.2.2.1,ho.2.2.2.1,ho.2.2.2.2] <;> norm_num

open SecondFunctionalCoupledFeedback (gain cost density)
open FourthRowPhiOmega2 (J)

def Mother (k : ℕ) (δ ε : ℝ) (v : Value) (T : ℕ) : Prop :=
  ∀ N, T≤N → Even N → ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
    5*wuBoxPhi N δ (convolutionWuWindows N Δ V) (native v).s ≤
      (cost (native v) δ-gain (native v) δ+ε)*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)

private theorem common_mothers (vs : List Value) (k : ℕ) (δ ε : ℝ)
    (hs : ∀ v∈vs, ∃ T, 4≤T ∧ Mother k δ ε v T) :
    ∃ T, 4≤T ∧ ∀ v∈vs, Mother k δ ε v T := by
  induction vs with
  | nil => exact ⟨4,le_rfl,by simp⟩
  | cons v vs ih =>
    obtain ⟨A,hA,hv⟩ := hs v List.mem_cons_self
    obtain ⟨B,_,ht⟩ := ih (fun w hw => hs w (List.mem_cons_of_mem v hw))
    refine ⟨max A B,hA.trans (le_max_left _ _),?_⟩
    intro w hw N hN hn i Δ V hb
    rcases List.mem_cons.mp hw with rfl|hw
    · exact hv N ((le_max_left _ _).trans hN) hn i Δ V hb
    · exact ht w hw N ((le_max_right _ _).trans hN) hn i Δ V hb

/-- One threshold before every physical mother, including all schedules
and both early and repriced appearances of the same original tuple. -/
theorem all_original_mothers (k : ℕ) (hk : 1≤k) {δ ε : ℝ}
    (hd : 0<δ) (hd' : δ≤1/10) (he : 0<ε) :
    ∃ T, 4≤T ∧ ∀ g (b : Tagged), b∈taggedW2 g → Mother k δ ε b.1 T := by
  obtain ⟨T,hT,hs⟩ := common_mothers (oldRows++addedRows) k δ ε (fun v hv =>
    SecondFunctionalCoupledFeedback.mother (native v) (admitted hv) k hk hd hd' he)
  exact ⟨T,hT,fun g b hb => hs b.1 (original_parameters g hb)⟩

theorem original_limit (g : ℕ) {b : Tagged} (hb : b∈taggedW2 g) {δ : ℝ}
    (hd : 0<δ) (hd' : δ≤1/10) : wuUpperCoefficient (native b.1).s +
      (gain (native b.1) δ-cost (native b.1) δ)/5 ≤ H δ (native b.1).s :=
  SecondFunctionalCoupledFeedback.actual_limit (native b.1) (admitted (original_parameters _ hb)) hd hd'

/-- The four physical two-prime pair integrals with their native
insertion gates give exactly the positive H-density of this tuple. -/
theorem four_original_pair_integrals (g : ℕ) {b : Tagged} (hb : b∈taggedW2 g)
    {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10) :
    let p := native b.1
    (∫ v in (1 : ℝ)..3, H δ v*density p v) =
      MotherPair.gainIntegral p .gammaFive δ + MotherPair.gainIntegral p .gammaSix δ +
      MotherPair.gainIntegral p .gammaSeven δ + MotherPair.gainIntegral p .gammaEight δ := by
  dsimp only
  have hp := admitted (original_parameters _ hb)
  have hhalf : δ<1/2 := by linarith
  have h5 := MotherPair.feedback_log_actual_integrable hp .gammaFive hd hhalf
  have h6 := MotherPair.feedback_log_actual_integrable hp .gammaSix hd hhalf
  have h7 := MotherPair.feedback_log_actual_integrable hp .gammaSeven hd hhalf
  have h8 := MotherPair.feedback_log_actual_integrable hp .gammaEight hd hhalf
  unfold H density
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add ((h5.add h6).add h7) h8,
    intervalIntegral.integral_add (h5.add h6) h7, intervalIntegral.integral_add h5 h6,
    MotherPair.gainIntegral_feedbackLog hp .gammaFive hd hhalf,
    MotherPair.gainIntegral_feedbackLog hp .gammaSix hd hhalf,
    MotherPair.gainIntegral_feedbackLog hp .gammaSeven hd hhalf,
    MotherPair.gainIntegral_feedbackLog hp .gammaEight hd hhalf]

private theorem high_at_point (n : ℕ) {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    (he : ∀ i : Fin 200, i.val∈edges → readGain n i ≤ H δ (tableGrid (i.val+1)))
    {i : Fin 200} {x : ℚ} (hp : HighPoint i x) : readGain (n+2) i ≤ H δ (x : ℝ) := by
  have prev := upper_endpoints_from_low designatedW1 designatedW2 hd hd' designated_low_writes n
    (low_of_edges n hd hd' he) n le_rfl
  have hh := high_endpoint_two_generations designatedW1 designatedW2 hd hd' designated_low_writes n prev i hp.1
  have hx : (3 : ℝ) < (x : ℝ) := by exact_mod_cast hp.2.1
  have hcmp : (x : ℝ) ≤ ((gridAt (i.val+1) : ℚ) : ℝ) := by exact_mod_cast hp.2.2.2
  have hright : (x : ℝ) ≤ tableGrid (i.val+1) := by simpa [gridAt,tableGrid] using hcmp
  have hg := tableGrid_bounds (show i.val+1≤200 by omega)
  exact hh.trans (wuImprovementLimit_upper_antitone hd hd' ⟨by linarith,by linarith [hg.2]⟩
    ⟨hg.1,hg.2.trans (by norm_num)⟩ hright)

/-- The two genuine historical integer slots, with their 4:1 multiplicity,
can replace the native H point terms in the complete native inequality. -/
theorem native_limit_with_historical_points (n : ℕ) {b : Tagged} (hb : b∈taggedW2 (n+2))
    {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10)
    (he : ∀ i : Fin 200, i.val∈edges → readGain n i ≤ H δ (tableGrid (i.val+1))) :
    let p := native b.1
    wuUpperCoefficient p.s + ((sourcePointSum (outputAt (n+2)) b.2.points : ℝ)/tableQ +
      J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S +
      (∫ v in (1 : ℝ)..3, H δ v*density p v) - cost p δ)/5 ≤ H δ p.s := by
  obtain ⟨p,r,hrs,hm,hn,hp,hr⟩ := scheduled_w2_points _ hb
  have h1 := high_at_point n hd hd' he hp
  have h2 := high_at_point n hd hd' he hr
  have hraw : (sourcePointSum (outputAt (n+2)) b.2.points : ℝ)/tableQ ≤
      4*H δ (anchor0 b.1 : ℝ) + H δ (anchor1 b.1 : ℝ) := by
    have hident : (sourcePointSum (outputAt (n+2)) b.2.points : ℝ)/tableQ =
        4*readGain (n+2) p.index + readGain (n+2) r.index := by
      simp only [hrs,sourcePointSum,hm,hn,mul_one,add_zero,Int.cast_add,Int.cast_mul,Int.cast_ofNat,readGain]
      ring
    rw [hident]
    linarith only [h1,h2]
  have hfull := original_limit (n+2) hb hd hd'
  change _ ≤ 4*H δ (native b.1).S+H δ (native b.1).kappa1 at hraw
  dsimp only
  simp only [gain,H] at hraw hfull ⊢
  linarith only [hraw, hfull]

end
end ImbalancedChen.P2HistoricalW2NativeFunctional
