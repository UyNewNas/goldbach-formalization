import ImbalancedChen.P4ACatalogFiveSmallThirdPayment
import ImbalancedChen.P4AOriginalFiniteFallbackRange

namespace ImbalancedChen.P4AOriginalFiniteFallbackSmallThird
noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
open P4ACatalogFiveSmallThirdMass
open P1OriginalSmallCutoffActualLowerTail P1OriginalFifthMovingHarmonicEnvelope
open P1OriginalFifthMovingScaleLimit P1FifthMiddleNormalizedPointwise

def floorLevel : ℝ := 1/2-1/1024
def small : ℝ := 1/1024
def quotient (N : ℕ) (p : Fin 3 → ℕ) (L : ℝ) := (N:ℝ)^L/(∏ i,p i : ℕ)
def diff (N : ℕ) (p : Fin 3 → ℕ) (a b : ℝ) :=
  actualPrimeTupleOwnCubeMinus N N b p-actualPrimeTupleOwnCubeMinus N N a p

theorem gaps {N : ℕ} (hN : 1<N) {h : ℝ} (hh : h≤small) {p : Fin 3 → ℕ}
    (hp : p∈tailBox N h) {L : ℝ} (hL : floorLevel≤L) :
    (∏ i,p i : ℕ)*(p 2:ℝ)^2<(N:ℝ)^L ∧ (N:ℝ)^((19/96:ℝ)/2)≤quotient N p L := by
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i,0<p i := fun i => (hpi i).1.pos
  have ht := mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff hN lower (upper h) p).mp hp).2
  have hx : actualPrimeTupleLog N p 0<19/96 := (ht 0).2
  have hy : actualPrimeTupleLog N p 1<19/96 := (ht 1).2
  have hz : actualPrimeTupleLog N p 2<h := (ht 2).2
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hprod : (0:ℝ)<(∏ i,p i : ℕ) := by exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  dsimp only [small,floorLevel] at hh hL
  constructor
  · apply (actualPrimeTupleOwnCube_iff hN p hpos L).mpr
    simp only [primeTupleOwnCubeForm,Fin.sum_univ_three]
    linarith
  · have heq : quotient N p L=(N:ℝ)^(L-∑ i,actualPrimeTupleLog N p i) := by
      rw [actualPrimeTupleLog_sum_prod p hpos]
      exact (residual_rpow_level_div (N:ℝ) (∏ i,p i : ℕ) L hn hprod).symm
    rw [heq]
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    rw [Fin.sum_univ_three]; linarith

theorem eq_actual {N : ℕ} {p : Fin 3 → ℕ} {a b : ℝ}
    (ha : (∏ i,p i : ℕ)*(p 2:ℝ)^2<(N:ℝ)^a) (hb : (∏ i,p i : ℕ)*(p 2:ℝ)^2<(N:ℝ)^b) :
    diff N p a b=(actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p b)-
      actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p a))*Real.log (N:ℝ)/singularSeries N := by
  unfold diff actualPrimeTupleOwnCubeMinus quotient
  rw [if_pos hb,if_pos ha]
  ring

theorem pointwise :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      1 < N ∧ ∀ h : ℝ, h ≤ small → Even N →
      ∀ p ∈ tailBox N h, ∀ a b : ℝ,floorLevel≤a → floorLevel≤b →
        |diff N p a b| ≤
          A*|Real.log (N:ℝ)/singularSeries N|*Real.exp (-movingBudget N)+
            B*(actualPrimeTupleLog N p 2)^2 := by
  obtain ⟨A0,B0,K,hA0,hB0,_hK,hsource⟩ := exists_actualMinus_pair_exp_bound
  obtain ⟨C,hC,hmiddle⟩ := exists_eventually_actualMinus_middle_quadratic_bound
  let A := 2*(A0+B0*Real.exp (Real.sqrt K))
  let B := C/(19/96:ℝ)^3
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A,B,hA,hB,?_⟩
  filter_upwards [eventually_moving_scale_budgets (19/96:ℝ) (by norm_num),
    hmiddle (19/96:ℝ) (by norm_num)] with N hb hmid
  obtain ⟨hN,_,_,hT,haT,hbudget,hlog⟩ := hb
  have hN1 : 1 < N := by omega
  have hNr : (1:ℝ) < N := by exact_mod_cast hN1
  refine ⟨hN1,?_⟩
  intro h hsmall hEven p hp a b ha hbb
  have hh : h≤(19/96:ℝ)/6 := hsmall.trans (by norm_num [small])
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have ht := (mem_actualPrimeBoxTuples_log_iff hN1 lower (upper h) p).mp hp
  have hz : actualPrimeTupleLog N p 2 < h := by
    simpa [upper] using (mem_logPrimeBox.mp ht.2 2).2
  obtain ⟨hgo,hRo⟩ := gaps hN1 hsmall hp ha
  obtain ⟨hgn,hRn⟩ := gaps hN1 hsmall hp hbb
  have hy : (1:ℝ) < p 2 := by exact_mod_cast (hpi 2).1.one_lt
  have hcap : (p 2:ℝ) ≤ N := by
    have hph : (p 2:ℝ) < (N:ℝ)^h := by simpa [upper] using (hpi 2).2.2.2
    exact hph.le.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith : h ≤ 1))
  by_cases hsmall : actualPrimeTupleLog N p 2 < movingCutoff (19/96:ℝ) N
  · have hcut : (p 2:ℝ) ≤ (N:ℝ)^movingCutoff (19/96:ℝ) N := by
      rw [← actualPrimeTupleLog_rpow hN1 p hpos 2]
      exact Real.rpow_le_rpow_of_exponent_le hNr.le hsmall.le
    have ho := P1ActualVariableFifthTailPointwise.sourceBudget_of_power_cutoff N hN1
      (19/96:ℝ) (movingCutoff (19/96:ℝ) N) (movingBudget N) (p 2:ℝ) (quotient N p a)
      (Nat.cast_nonneg _) hcut hRo hT haT hbudget hlog
    have hn := P1ActualVariableFifthTailPointwise.sourceBudget_of_power_cutoff N hN1
      (19/96:ℝ) (movingCutoff (19/96:ℝ) N) (movingBudget N) (p 2:ℝ) (quotient N p b)
      (Nat.cast_nonneg _) hcut hRn hT haT hbudget hlog
    have hypow : (p 2:ℝ) ≤ (p 2:ℝ)^movingBudget N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy.le (by linarith : 1 ≤ movingBudget N)
    have hpair := hsource N N hEven (p 2:ℝ) (quotient N p a) (quotient N p b)
      (movingBudget N) (movingBudget N) hcap hy
      (hypow.trans ho.2.1) (hypow.trans hn.2.1) ho.1 hn.1 ho.2.1 hn.2.1
      ho.2.2.1 hn.2.2.1 ho.2.2.2 hn.2.2.2
    have he : (1:ℝ) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (0:ℝ) ≤ 1)
    have hto := tailEnvelope_le_uniform_exp A0 B0 K (quotient N p a)
      (movingBudget N) (movingBudget N) hA0.le hB0.le le_rfl (he.trans ho.2.2.2)
    have htn := tailEnvelope_le_uniform_exp A0 B0 K (quotient N p b)
      (movingBudget N) (movingBudget N) hA0.le hB0.le le_rfl (he.trans hn.2.2.2)
    have hraw : |actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p b)-
        actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p a)| ≤ A*Real.exp (-movingBudget N) := by
      calc
        _ ≤ actualSmallEulerProduct N N (p 2:ℝ) *
            (tailEnvelope A0 B0 K (quotient N p a) (movingBudget N)+
              tailEnvelope A0 B0 K (quotient N p b) (movingBudget N)) := hpair
        _ ≤ actualSmallEulerProduct N N (p 2:ℝ) * (A*Real.exp (-movingBudget N)) := by
          apply mul_le_mul_of_nonneg_left _ (actualSmallEulerProduct_pos N N _ hEven).le
          dsimp [A]
          linarith
        _ ≤ 1*(A*Real.exp (-movingBudget N)) :=
          mul_le_mul_of_nonneg_right (actualSmallEulerProduct_le_one N N _) (by positivity)
        _ = _ := one_mul _
    rw [eq_actual hgo hgn,mul_div_assoc,abs_mul]
    have hnrm := mul_le_mul_of_nonneg_right hraw (abs_nonneg (Real.log (N:ℝ)/singularSeries N))
    have hq : 0 ≤ B*(actualPrimeTupleLog N p 2)^2 := mul_nonneg hB.le (sq_nonneg _)
    nlinarith only [hnrm,hq]
  · have hbound := hmid N hEven (p 2:ℝ) (quotient N p a) (quotient N p b) h
      (by exact_mod_cast hpos 2) hcap hh (le_of_not_gt hsmall) hz hRo hRn
    rw [eq_actual hgo hgn]
    change |(actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p b)-
      actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p a))*Real.log (N:ℝ)/singularSeries N| ≤ _
    have hE : 0 ≤ A*|Real.log (N:ℝ)/singularSeries N|*Real.exp (-movingBudget N) := by positivity
    change _ ≤ B*(actualPrimeTupleLog N p 2)^2 at hbound
    linarith


def total (N : ℕ) (h : ℝ) (A : Finset (Fin 3 → ℕ)) (a b : (Fin 3 → ℕ) → ℝ) :=
  ∑ p∈A,(∏ i,1/((p i:ℝ)-1))*|diff N p (a p) (b p)|

/-- Covers every subfamily, including the disabled physical cutoff, with
levels varying on the individual true prime tuples. -/
theorem uniform :
    ∃ D : ℝ,0<D ∧ ∀ h : ℝ,0<h → h≤small → ∃ N0 : ℕ,2≤N0 ∧
      ∀ N≥N0,Even N → ∀ (S : Finset (Fin 3 → ℕ)), S⊆tailBox N h →
      ∀ a b : (Fin 3 → ℕ) → ℝ,(∀ p∈S,floorLevel≤a p ∧ floorLevel≤b p) →
        total N h S a b<D*h := by
  obtain ⟨A,B,hA,hB,hpoint⟩ := pointwise
  obtain ⟨M,hM,Nm,hNm,hmoment⟩ := exists_uniform_secondMoment_bound
  let D := 1+B*M
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro h hh hsmall
  have hhr : h≤(19/96:ℝ)/6 := hsmall.trans (by norm_num [small])
  have htiny : ∀ᶠ N : ℕ in atTop, A*normalizedMovingMajorant N < h := by
    have ht := normalizedMovingMajorant_tendsto_zero.const_mul A
    simpa only [mul_zero] using ht.eventually (gt_mem_nhds hh)
  have hpower : ∀ᶠ N : ℕ in atTop, 2 ≤ (N:ℝ)^h :=
    ((tendsto_rpow_atTop hh).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2:ℝ))
  obtain ⟨Np,hNp⟩ := eventually_atTop.mp hpoint
  obtain ⟨Nt,hNt⟩ := eventually_atTop.mp htiny
  obtain ⟨Nh,hNh⟩ := eventually_atTop.mp hpower
  refine ⟨max Nm (max Np (max Nt Nh)),hNm.trans (le_max_left _ _),?_⟩
  intro N hN hEven S hS a b hab
  have hNm' : Nm ≤ N := by omega
  have hNp' : Np ≤ N := by omega
  have hNt' : Nt ≤ N := by omega
  have hNh' : Nh ≤ N := by omega
  have hN1 := (hNp N hNp').1
  let E := A*|Real.log (N:ℝ)/singularSeries N|*Real.exp (-movingBudget N)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hfinite : total N h S a b ≤
      E*(∑ p ∈ tailBox N h, ∏ i, 1/((p i:ℝ)-1))+B*secondMoment N h := by
    calc
      total N h S a b ≤ ∑ p ∈ tailBox N h,
          (∏ i, 1/((p i:ℝ)-1))*(E+B*(actualPrimeTupleLog N p 2)^2) := by
        apply (Finset.sum_le_sum (s:=S) (fun p hp => mul_le_mul_of_nonneg_left
          ((hNp N hNp').2 h hsmall hEven p (hS hp) _ _ (hab p hp).1 (hab p hp).2)
          (actualPrimeBoxWeight_nonneg (hS hp)))).trans
        exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun p hp _ =>
          mul_nonneg (actualPrimeBoxWeight_nonneg hp) (add_nonneg hE (mul_nonneg hB.le (sq_nonneg _))))
      _ = _ := by
        rw [Finset.mul_sum,secondMoment,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hmass := tailBox_mass_le_harmonic N hN1 h (by linarith)
  have hHp : (harmonicFactor N)^3 ≤ (harmonicFactor N)^5 :=
    pow_le_pow_right₀ (harmonicFactor_ge_one N hN1) (by norm_num : (3:ℕ) ≤ 5)
  have htinyBound : E*(∑ p ∈ tailBox N h, ∏ i, 1/((p i:ℝ)-1)) ≤
      A*normalizedMovingMajorant N := by
    have hh' := mul_le_mul_of_nonneg_left (hmass.trans hHp) hE
    convert hh' using 1 <;> dsimp [E,normalizedMovingMajorant] <;> ring
  have hm := hmoment N hNm' h hh (hNh N hNh')
  have hquad : h^2 ≤ h := by nlinarith
  calc
    total N h S a b ≤ A*normalizedMovingMajorant N+B*(M*h^2) :=
      hfinite.trans (add_le_add htinyBound (mul_le_mul_of_nonneg_left hm hB.le))
    _ < h+B*(M*h^2) := add_lt_add_right (hNt N hNt') _
    _ ≤ h+B*(M*h) := add_le_add_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hquad hM.le) hB.le) _
    _ = D*h := by dsimp [D]; ring


end
end ImbalancedChen.P4AOriginalFiniteFallbackSmallThird
