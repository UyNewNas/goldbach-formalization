import ImbalancedChen.P2HistoricalScheduledPointReads
import ImbalancedChen.P2ClassicalSeedCountAttachment

/-!
Physical (unfiltered) Wu source boxes, at their own Q=N^(1/2-δ). The W1
parent anchor and both W2 Γ1 terms retain their original labelled tuple
counts, denominator and common threshold. Only these point terms are
at issue: no signed singleton, pair or switched cost is inferred.
-/
namespace ImbalancedChen.P2HistoricalNativePointCounts

noncomputable section
open Wu2008DoubleSieve P2TableActionSourceOnly P2SimultaneousTableSourceOnly
open P2HistoricalBankLogWeights P2HistoricalLowerBankAncestry P2HistoricalHighPointAncestry
open P2Historical248Authentication P2HistoricalScheduledPointReads
open P2FrozenReceiverCountActions (markedPhi)
open P2ActualMarkedCountState (markedTheta)
open P2ClassicalSeedCountAttachment (tupleProduct labelled_count_eq_wuBoxPhi labelled_Theta_eq_boxTheta)
open scoped BigOperators

abbrev QueryPair := Fin 200 × ℚ
abbrev Tagged := P2HistoricalSourceJSON.Value × W2Action
def pointKeys (b : Tagged) : List QueryPair :=
  match b.2.points with
  | [p,r] => [(p.index,anchor0 b.1),(r.index,anchor1 b.1)]
  | _ => []
def keys (g : ℕ) : List QueryPair :=
  (sourceW1Schedule g).map (fun a => (a.pointIndex,a.s0)) ++ (taggedW2 g).flatMap pointKeys

private theorem key_high (g : ℕ) {z : QueryPair} (hz : z ∈ keys g) : HighPoint z.1 z.2 := by
  rcases List.mem_append.mp hz with h | h
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    exact scheduled_w1_point _ ha
  · obtain ⟨b,hb,hz⟩ := List.mem_flatMap.mp h
    obtain ⟨p,r,he,_,_,hp,hr⟩ := scheduled_w2_points _ hb
    simp only [pointKeys, he, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact hp
    · exact hr

def readGain (g : ℕ) (j : Fin 200) : ℝ := (outputAt g true j : ℝ)/tableQ
def boxCount {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) (s : ℝ) : ℝ :=
  markedPhi N ((N:ℝ)^(1/2-δ)) (Fintype.piFinset W) tupleProduct (fun _ => 1) (fun _ _ => True) s
def boxMass {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  markedTheta N ((N:ℝ)^(1/2-δ)) (Fintype.piFinset W) tupleProduct (fun _ => 1)

def gammaOneCount {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) (b : Tagged) : ℝ :=
  (4 * boxCount N δ W (anchor0 b.1) + boxCount N δ W (anchor1 b.1)) / 5
def gammaOneCoefficient (g : ℕ) (b : Tagged) : ℝ :=
  (4*wuUpperCoefficient (anchor0 b.1) + wuUpperCoefficient (anchor1 b.1))/5 -
    (sourcePointSum (outputAt g) b.2.points : ℝ)/(5*tableQ)

/-- Keep the exact finite source ordinals and (possibly repeated) point
slots. For fixed g,k,epsilon there is just one threshold for all of them. -/
def PointPrices (g k : ℕ) (δ ε : ℝ) : Prop :=
  ∃ T : ℕ, ∀ N, T ≤ N → 4 ≤ N → Even N → ∀ i Δ (V : Fin i → ℝ),
    wuSourceBox (k+1) δ N i Δ V →
    (∀ a ∈ sourceW1Schedule g, boxCount N δ (convolutionWuWindows N Δ V) a.s0 ≤
      (wuUpperCoefficient a.s0 - readGain g a.pointIndex + ε) *
        boxMass N δ (convolutionWuWindows N Δ V)) ∧
    (∀ b ∈ taggedW2 g, gammaOneCount N δ (convolutionWuWindows N Δ V) b ≤
      (gammaOneCoefficient g b + ε) * boxMass N δ (convolutionWuWindows N Δ V))

private def Admits (charge : QueryPair → ℝ) (k : ℕ) (δ ε : ℝ) (z : QueryPair) (T : ℕ) : Prop :=
  charge z - ε ∈ wuAdmissibleImprovements true (k+1) δ z.2 T

private theorem common_threshold (charge : QueryPair → ℝ) (k : ℕ) (δ ε : ℝ) (xs : List QueryPair)
    (hp : ∀ z ∈ xs, ∃ T, Admits charge k δ ε z T) :
    ∃ T, ∀ z ∈ xs, Admits charge k δ ε z T := by
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons z zs ih =>
    obtain ⟨T,hT⟩ := hp z (by simp)
    obtain ⟨U,hU⟩ := ih (fun q hq => hp q (List.mem_cons_of_mem z hq))
    refine ⟨max T U,?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact wuAdmissibleImprovements_mono_threshold true (k+1) δ _ (le_max_left T U) hT
    · exact wuAdmissibleImprovements_mono_threshold true (k+1) δ _ (le_max_right T U) (hU q hq)

private theorem real_range {z : QueryPair} (hp : HighPoint z.1 z.2) :
    1 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ tableGrid (z.1.val+1) ∧ tableGrid (z.1.val+1) ≤ 5 := by
  have hx : (3:ℝ) < (z.2 : ℝ) := by exact_mod_cast hp.2.1
  have hcast : ((gridAt (z.1.val+1) : ℚ) : ℝ) = tableGrid (z.1.val+1) := by
    simp [gridAt, tableGrid]
  have hr : (z.2 : ℝ) ≤ ((gridAt (z.1.val+1) : ℚ) : ℝ) := by exact_mod_cast hp.2.2.2
  exact ⟨by linarith, hr.trans hcast.le, (tableGrid_bounds (show z.1.val+1 ≤ 200 by omega)).2⟩

private theorem physical_at {charge : QueryPair → ℝ} {k N T i : ℕ} {δ ε Δ : ℝ}
    {V : Fin i → ℝ} {z : QueryPair} (hz : Admits charge k δ ε z T)
    (hNT : T ≤ N) (hN : 4 ≤ N) (he : Even N) (hb : wuSourceBox (k+1) δ N i Δ V) :
    boxCount N δ (convolutionWuWindows N Δ V) z.2 ≤
      (wuUpperCoefficient z.2 - charge z + ε)*boxMass N δ (convolutionWuWindows N Δ V) := by
  let W := convolutionWuWindows N Δ V
  have hh := hz N hNT hN he i Δ V hb
  change wuBoxPhi N δ W z.2 ≤
    (wuUpperCoefficient z.2 - (charge z-ε))*boxTheta N ((N:ℝ)^(1/2-δ)) W at hh
  rw [show wuUpperCoefficient z.2 - (charge z-ε) = wuUpperCoefficient z.2 - charge z + ε by ring] at hh
  simpa only [boxCount, boxMass, labelled_count_eq_wuBoxPhi, labelled_Theta_eq_boxTheta] using hh

/-- No bank endpoint, seed or earlier table is assumed. The native upper
profile actually pays the two parent counts at the raw W2 parameters, on
all boxes of fixed depth with one threshold for the whole generation. -/
theorem native_point_and_gamma_one (g k : ℕ) {δ ε : ℝ} (hd : 0<δ) (hd' : δ≤1/10) (hε : 0<ε) :
    ∃ T : ℕ, ∀ N, T ≤ N → 4 ≤ N → Even N → ∀ i Δ (V : Fin i → ℝ),
      wuSourceBox (k+1) δ N i Δ V →
      (∀ a ∈ sourceW1Schedule g, boxCount N δ (convolutionWuWindows N Δ V) a.s0 ≤
        (wuUpperCoefficient a.s0 - H δ a.s0 + ε)*boxMass N δ (convolutionWuWindows N Δ V)) ∧
      (∀ b ∈ taggedW2 g, gammaOneCount N δ (convolutionWuWindows N Δ V) b ≤
        ((4*(wuUpperCoefficient (anchor0 b.1)-H δ (anchor0 b.1)) +
             (wuUpperCoefficient (anchor1 b.1)-H δ (anchor1 b.1)))/5+ε)*
          boxMass N δ (convolutionWuWindows N Δ V)) := by
  obtain ⟨T,hT⟩ := common_threshold (fun z => H δ z.2) k δ ε (keys g) (by
    intro z hz
    obtain ⟨hl,hr,hu⟩ := real_range (key_high g hz)
    have hten : (z.2:ℝ) ≤ 10 := by linarith
    exact wuImprovementLimit_sub_mem true k hd (by linarith : δ<1/2) hl hten hε)
  refine ⟨T,?_⟩
  intro N hNT hN he i Δ V hb
  have hc (z : QueryPair) (hz : z ∈ keys g) := physical_at (hT z hz) hNT hN he hb
  constructor
  · intro a ha
    exact hc (a.pointIndex,a.s0) (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩)))
  · intro b hbank
    obtain ⟨p,r,heq,_,_,_,_⟩ := scheduled_w2_points _ hbank
    have hk (z : QueryPair) (hz : z ∈ pointKeys b) : z ∈ keys g :=
      List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨b,hbank,hz⟩))
    have h0 := hc (p.index, anchor0 b.1) (hk _ (by simp [pointKeys,heq]))
    have h1 := hc (r.index, anchor1 b.1) (hk _ (by simp [pointKeys,heq]))
    dsimp only at h0 h1
    unfold gammaOneCount
    linarith

private theorem prices_of_high (g k : ℕ) {δ ε : ℝ} (hd : 0<δ) (hd' : δ≤1/10) (hε : 0<ε)
    (hhigh : ∀ j : Fin 200, 100 ≤ j.val → readGain g j ≤ H δ (tableGrid (j.val+1))) :
    PointPrices g k δ ε := by
  have hhalf : δ < 1/2 := by linarith
  obtain ⟨T,hT⟩ := common_threshold (fun z => readGain g z.1) k δ ε (keys g) (by
    intro z hz
    have hp := key_high g hz
    obtain ⟨h1,hr,h5⟩ := real_range hp
    have h10 : (z.2 : ℝ) ≤ 10 := by linarith
    have hmono := wuImprovementLimit_upper_antitone hd hd' ⟨h1,h10⟩
      ⟨h1.trans hr,h5.trans (by norm_num)⟩ hr
    have hprior := (hhigh z.1 hp.1).trans hmono
    exact wuEventualImprovements_downward true (k+1) (by omega) hd hhalf h1 h10
      (sub_le_sub_right hprior ε) (wuImprovementLimit_sub_mem true k hd hhalf h1 h10 hε))
  refine ⟨T,?_⟩
  intro N hNT hN he i Δ V hb
  let W := convolutionWuWindows N Δ V
  have hc (z : QueryPair) (hz : z ∈ keys g) :
      boxCount N δ W z.2 ≤ (wuUpperCoefficient z.2 - readGain g z.1 + ε)*boxMass N δ W :=
    physical_at (hT z hz) hNT hN he hb
  constructor
  · intro a ha
    exact hc (a.pointIndex,a.s0) (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩)))
  · intro b hb'
    obtain ⟨p,r,he,hm,hm',_,_⟩ := scheduled_w2_points _ hb'
    have hk (z : QueryPair) (hz : z ∈ pointKeys b) : z ∈ keys g :=
      List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨b,hb',hz⟩))
    have h0 := hc (p.index, anchor0 b.1) (hk _ (by simp [pointKeys,he]))
    have h1 := hc (r.index, anchor1 b.1) (hk _ (by simp [pointKeys,he]))
    change boxCount N δ W (anchor0 b.1) ≤
      (wuUpperCoefficient (anchor0 b.1)-readGain g p.index+ε)*boxMass N δ W at h0
    change boxCount N δ W (anchor1 b.1) ≤
      (wuUpperCoefficient (anchor1 b.1)-readGain g r.index+ε)*boxMass N δ W at h1
    calc gammaOneCount N δ W b ≤
        (4*((wuUpperCoefficient (anchor0 b.1)-readGain g p.index+ε)*boxMass N δ W) +
            (wuUpperCoefficient (anchor1 b.1)-readGain g r.index+ε)*boxMass N δ W)/5 := by
          unfold gammaOneCount
          linarith
      _ = (gammaOneCoefficient g b + ε)*boxMass N δ W := by
        simp only [gammaOneCoefficient,he,sourcePointSum,hm,hm',mul_one,add_zero,Int.cast_add,
          Int.cast_mul,Int.cast_ofNat,readGain]
        have hq : (tableQ:ℝ) ≠ 0 := by exact_mod_cast tableQ_pos.ne'
        field_simp [hq] <;> ring

/-- Actual first two high generations: no adopted low seed or previous
analytic licence is assumed. The original lower seed is literally zero. -/
theorem initial_point_prices (g k : ℕ) (hg : g ≤ 1) {δ ε : ℝ}
    (hd : 0<δ) (hd' : δ≤1/10) (hε : 0<ε) : PointPrices g k δ ε := by
  apply prices_of_high g k hd hd' hε
  intro j hj
  have hb := tableGrid_bounds (show j.val+1 ≤ 200 by omega)
  have hzero : outputAt g true j = 0 := by
    rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl
    · simp [outputAt,iterate,originalSeed,show ¬j.val<60 by omega]
    · rw [show outputAt 1 true j = _ from high_last_suffix _ _ designated_low_writes 0 j hj]
      simp [outputAt, iterate, suffixNumerator, read, originalSeed]
  simpa [readGain, hzero, H] using wuImprovementLimit_nonneg true hd
    (by linarith : δ<1/2) hb.1 (hb.2.trans (by norm_num))

/-- For all later classical point reads, the only open inequalities are
the low upper entries *two generations earlier*. In particular reading the
247th table here does not take the 247th upper invariant as a premise. -/
theorem later_point_prices (n k : ℕ) {δ ε : ℝ} (hd : 0<δ) (hd' : δ≤1/10) (hε : 0<ε)
    (low : ∀ j : Fin 200, j.val < 100 → readGain n j ≤ H δ (tableGrid (j.val+1))) :
    PointPrices (n+2) k δ ε := by
  apply prices_of_high (n+2) k hd hd' hε
  exact high_endpoint_two_generations _ _ hd hd' designated_low_writes n
    (upper_endpoints_from_low _ _ hd hd' designated_low_writes n low n le_rfl)

/-- Nonnegative owners of full native boxes may repeat the same physical
box. They are summed as labels. No division by their total mass and no
positivity premise on that total occurs. No within-box filter is licensed. -/
theorem owned_gamma_one {g k : ℕ} {δ ε : ℝ} (hp : PointPrices g k δ ε) :
    ∃ T : ℕ, ∀ N, T ≤ N → 4 ≤ N → Even N → ∀ {ι : Type} (S : Finset ι)
      (w : ι → ℝ) (rank : ι → ℕ) (Δ : ι → ℝ) (V : (o : ι) → Fin (rank o) → ℝ),
      (∀ o ∈ S, 0 ≤ w o) → (∀ o ∈ S, wuSourceBox (k+1) δ N (rank o) (Δ o) (V o)) →
      ∀ b ∈ taggedW2 g,
        (∑ o ∈ S, w o * gammaOneCount N δ (convolutionWuWindows N (Δ o) (V o)) b) ≤
        (gammaOneCoefficient g b + ε) *
          ∑ o ∈ S, w o * boxMass N δ (convolutionWuWindows N (Δ o) (V o)) := by
  obtain ⟨T,hT⟩ := hp
  refine ⟨T,?_⟩
  intro N hNT hN he ι S w rank Δ V hw hv b hb
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun o ho => (mul_le_mul_of_nonneg_left
    ((hT N hNT hN he (rank o) (Δ o) (V o) (hv o ho)).2 b hb) (hw o ho)).trans_eq (by ring)

end
end ImbalancedChen.P2HistoricalNativePointCounts
