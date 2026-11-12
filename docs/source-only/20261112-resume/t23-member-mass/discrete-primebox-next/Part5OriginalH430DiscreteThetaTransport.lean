import ImbalancedChen.Part5OriginalH430PrimeProgramWord

namespace ImbalancedChen.Part5OriginalH430DiscreteThetaTransport
noncomputable section
open scoped Classical BigOperators
open Set Filter MeasureTheory Topology Wu2008DoubleSieve
open P2OriginalChildPhysicalNormalization P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedLowerPhysicalNode P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430NativeQueryPaths Part5OriginalH430IntegerItineraries Part5OriginalH430OwnedRootCounts
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenPerturbation
open Part5OriginalH430FrozenRootMass Part5OriginalH430PhysicalMassPerturbation Part5OriginalH430FullRootAmplitude
open Part5OriginalH430NativeMovingDensity Part5OriginalH430FixedPrimeScreen Part5OriginalH430FixedProgramL1
open Part5OriginalH430SharpPrimeBox Part5OriginalH430PrimeProgramWord
open Part5OriginalH430OwnedThetaWord Part5OriginalH430SelectedBankCarrierSupply
open Part5OriginalH430AbsoluteWordBox Part5OriginalH430RootIntervalTheta (literalScale)
open Part5OriginalH430SameQHistoryCells Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalUpsilon5CausalDictionary (FloorAtom)

variable {r mesh d : ℕ}

/-- Arithmetic weight on its actual complete fixed Program, actual
root-band prime, actual word product, and its own frozen or ideal Q. -/
def charged (N : ℕ) (k : Root) (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code))
    (lower : Bool) (atom : FloorAtom) (v : Option ℕ) (p : Fin r → ℕ) : ℝ :=
  let x := view e (actualPrimeTupleLog N p)
  if p (e.symm (.inl ())) ∈ originalBand N k ∧ x ∈ fixedSet k code lower atom v then
    thetaAtom N (actualQ N k v (nativeRootCoordinate x)) (originalWord code e p).prod /
      singularNormalization N else 0

theorem frozenQ_is_original_fibre {N n m p : ℕ} {k : Root} (hN : 2 ≤ N)
    (hn : meshError n ≤ 11/384) (hp : p ∈ originalBand N k) :
    actualQ N k (some n) (physicalPrime N p) =
      cellQ N n (keyAt N n m k (finiteTau n) p).1 := by
  let c := keyAt N n m k (finiteTau n) p
  have hf : p ∈ rootFibre N n m k (finiteTau n) c := Finset.mem_filter.mpr ⟨hp,rfl⟩
  exact (original_fibre_geometry hN (finiteTau_pos n).le (finiteTau_le n) hn hf).1.symm

private theorem common_factor {N : ℕ} (hN : 1 < N) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (v : Option ℕ) (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime ∧ 2 < p i ∧ (p i).Coprime N) (hlogprod : (∏ i, actualPrimeTupleLog N p i) ≠ 0) :
    let x := view e (actualPrimeTupleLog N p)
    let w := originalWord code e p
    thetaAtom N (actualQ N k v (nativeRootCoordinate x)) w.prod / singularNormalization N =
      (literalScale N * wordFactor 1 w * (∏ i, actualPrimeTupleLog N p i)) *
        physicalWeight (node k code v x) := by
  let w := originalWord code e p
  let x := view e (actualPrimeTupleLog N p)
  let Q := actualQ N k v (nativeRootCoordinate x)
  let L := residual (node k code v x)
  have hpos : 0 < N := by omega
  have hl := Real.log_pos (show (1:ℝ)<N by exact_mod_cast hN)
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hpos
  have hden : Real.log (Q/(w.prod:ℝ)) = L*Real.log N := by
    have he := literal_level hN k code v e p (fun i => (hp i).1.pos)
    change L = Real.log (Q/(w.prod:ℝ)) / Real.log N at he
    exact ((eq_div_iff hl.ne').mp he).symm
  have hpr (q) (hq : q ∈ w) : q.Prime ∧ 2 < q ∧ q.Coprime N := by
    obtain ⟨i,rfl⟩ := letters_in_range code e p hq
    exact hp i
  have har : wuSingularSeries (w.prod*N)/(Nat.totient w.prod:ℝ) = singularSeries N * wordFactor 1 w := by
    simpa only [one_mul,Nat.totient_one,Nat.cast_one,div_one,wuSingularSeries_eq_liu N hpos,
      ← currentChen_singularSeries_eq_liuSingularSeries N] using inserted_word hpos w hpr (d := 1) (by decide)
  change thetaAtom N Q w.prod / singularNormalization N = _ * physicalWeight (node k code v x)
  unfold thetaAtom physicalWeight
  rw [← div_div,har,hden,log_product]
  change _ = (literalScale N * wordFactor 1 w * _) * (4/(_*L))
  by_cases hL : L = 0
  · simp [hL]
  · unfold singularNormalization literalScale
    field_simp [hL,hl.ne',hNr.ne',hlogprod,(singularSeries_pos N).ne'] <;> ring

private theorem rate_nn (n : ℕ) : 0 ≤ rate n := by
  unfold rate levelError
  exact div_nonneg (mul_nonneg (div_nonneg (by norm_num) productFloor_pos.le)
    (add_nonneg (finiteTau_pos n).le (meshError_pos n).le)) (mul_self_nonneg _)
private theorem env_nn : 0 ≤ envelope :=
  div_nonneg (by norm_num) (mul_nonneg productFloor_pos.le frozenResidualFloor_pos.le)

private theorem localized {N n : ℕ} {a : ℝ} (ha : 0 < a) (hN : 1 < N) (hd : d ≤ 440)
    (hn : meshError n ≤ 11/384) (hA : 4 ≤ (N:ℝ)^a) (hlit : |literalScale N| ≤ 2)
    (k : Root) (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code))
    (lower : Bool) (atom : FloorAtom) (p : Fin r → ℕ)
    (hp : p ∈ actualPrimeBoxTuples N (fun _ => a) (fun _ => 1)) :
    |charged N k code e lower atom none p - charged N k code e lower atom (some n) p| ≤
      (2*2^r)*atomWeight p*(rate n+envelope*
        (screen k code e lower atom n).indicator (fun _ => (1:ℝ)) (actualPrimeTupleLog N p)) := by
  let z := actualPrimeTupleLog N p
  let x := view e z
  let w := originalWord code e p
  let J := ∏ i, z i
  let K := literalScale N * wordFactor 1 w * J
  let E := screen k code e lower atom n
  let I := fixedSet k code lower atom none
  let S := fixedSet k code lower atom (some n)
  let W := physicalWeight (node k code none x)
  let V := physicalWeight (node k code (some n) x)
  have hbox := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp
  have hz (i) := mem_logPrimeBox.mp hbox.2 i
  have hj : 0 < J := Finset.prod_pos (fun i _ => ha.trans_le (hz i).1)
  have hj1 : J ≤ 1 := Finset.prod_le_one (fun i _ => (ha.trans_le (hz i).1).le) (fun i _ => (hz i).2.le)
  have hpr (i) : (p i).Prime ∧ 2 < p i ∧ (p i).Coprime N := by
    have h4 := hA.trans ((mem_actualPrimeBoxTuples_iff.mp hp i).2.2.1)
    exact ⟨(hbox.1 i).1,by exact_mod_cast (show (2:ℝ)<p i by linarith),
      ((hbox.1 i).1.coprime_iff_not_dvd).mpr (hbox.1 i).2⟩
  have hratio := word_ratio code e p hp hA
  have hK : |K| ≤ (2*2^r) * atomWeight p := by
    rw [show |K| = |literalScale N| * wordFactor 1 w * J by
      simp only [K,abs_mul,abs_of_nonneg hratio.1,abs_of_nonneg hj.le]]
    calc
      _ ≤ 2 * (2^r * atomWeight p) * 1 :=
        mul_le_mul (mul_le_mul hlit hratio.2 hratio.1 (by norm_num)) hj1 hj.le
          (by have h := actualPrimeBoxWeight_nonneg hp; unfold atomWeight; positivity)
      _ = _ := by ring
  have hnon : 0 ≤ rate n+envelope*(E.indicator (fun _ => (1:ℝ)) z) :=
    add_nonneg (rate_nn n) (mul_nonneg env_nn (indicator_nonneg (fun _ _ => zero_le_one) _))
  have hcoeff : 0 ≤ (2*2^r:ℝ)*atomWeight p := (abs_nonneg K).trans hK
  by_cases hroot : p (e.symm (.inl ())) ∈ originalBand N k
  · have ht : nativeRootCoordinate x ∈ rootBand k := original_band_geometry (by omega : 2≤N) hroot
    have hcube : x ∈ region k (shapes code) :=
      ⟨⟨fun i => ha.le.trans (hz (e.symm i)).1,fun i => (hz (e.symm i)).2.le⟩,ht⟩
    have hrow (v) : charged N k code e lower atom v p =
        K * (if x ∈ fixedSet k code lower atom v then physicalWeight (node k code v x) else 0) := by
      by_cases hv : x ∈ fixedSet k code lower atom v
      · simpa only [charged,hroot,true_and,if_pos hv] using common_factor hN k code e v p hpr hj.ne'
      · simp only [charged,hroot,true_and,if_neg hv,mul_zero]
    rw [hrow,hrow,← mul_sub,abs_mul]
    apply mul_le_mul hK _ (abs_nonneg _) hcoeff
    change |(if x ∈ I then W else 0) - (if x ∈ S then V else 0)| ≤ rate n+envelope*E.indicator _ z
    have hE : z ∈ E ↔ (x ∈ I ∧ x ∉ S) ∨ (x ∈ S ∧ x ∉ I) := by
      change (x ∈ region k (shapes code) ∧ _) ↔ _
      exact and_iff_right hcube
    by_cases hi : x ∈ I <;> by_cases hs : x ∈ S
    · have he : z ∉ E := by simp [hE,hi,hs]
      simpa only [if_pos hi,if_pos hs,indicator_of_notMem he,mul_zero,add_zero] using
        (frozen_admitted_density_error ht hd hn hs.1 : |W-V| ≤ rate n)
    · have he := hE.mpr (Or.inl ⟨hi,hs⟩)
      have hw : |W| ≤ envelope := ideal_weight_bound ht hd hi.1
      simpa only [if_pos hi,if_neg hs,sub_zero,indicator_of_mem he,mul_one] using
        hw.trans (le_add_of_nonneg_left (rate_nn n))
    · have he := hE.mpr (Or.inr ⟨hs,hi⟩)
      have hw : |V| ≤ envelope := frozen_weight_bound ht hd hn hs.1
      simpa only [if_neg hi,if_pos hs,zero_sub,abs_neg,indicator_of_mem he,mul_one] using
        hw.trans (le_add_of_nonneg_left (rate_nn n))
    · simpa only [if_neg hi,if_neg hs,sub_zero,abs_zero] using hnon
  · simpa only [charged,hroot,false_and,if_false,sub_zero,abs_zero] using mul_nonneg hcoeff hnon

def markedError (N n : ℕ) (a : ℝ) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool) (atom : FloorAtom)
    (mark : (Fin r → ℕ) → ℝ) := ∑ p ∈ actualPrimeBoxTuples N (fun _ => a) (fun _ => 1),
  |mark p| * |charged N k code e lower atom none p - charged N k code e lower atom (some n) p|

private theorem sum_bound {N n : ℕ} {a : ℝ} (ha : 0<a) (hN : 1<N) (hd : d≤440)
    (hn : meshError n ≤ 11/384) (hA : 4≤(N:ℝ)^a) (hlit : |literalScale N|≤2)
    (k : Root) (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code))
    (lower : Bool) (atom : FloorAtom) (mark : (Fin r → ℕ) → ℝ)
    (hm : ∀ p ∈ actualPrimeBoxTuples N (fun _ => a) (fun _ => 1), |mark p| ≤ 1) :
    markedError N n a k code e lower atom mark ≤
      (2*2^r)*(rate n*total r N a + envelope*badMass N a (screen k code e lower atom n)) := by
  let E := screen k code e lower atom n
  let A := actualPrimeBoxTuples N (fun _ : Fin r => a) (fun _ => 1)
  let K : ℝ := 2*2^r
  calc
    _ ≤ ∑ p ∈ A, K*atomWeight p*(rate n+envelope*E.indicator (fun _ => (1:ℝ)) (actualPrimeTupleLog N p)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact ((mul_le_mul_of_nonneg_right (hm p hp) (abs_nonneg _)).trans_eq (one_mul _)).trans
        (localized ha hN hd hn hA hlit k code e lower atom p hp)
    _ = _ := by
      unfold total actualPrimeBoxMass badMass actualPrimeBoxTestSum
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      dsimp [K,atomWeight,E]
      ring

/-- First choose the precision for a fixed absolute error. For EACH
such precision one arithmetic threshold works for all larger targets
and all bounded jointly applied marks, including changing prefix masks. -/
theorem fixed_program_arithmetic_threshold {a eps : ℝ} (ha : 0<a) (ha1 : a<1) (he : 0<eps)
    (hd : d ≤ 440) (k : Root) (code : Program mesh d) (e : Fin r ≃ NativeSlot (shapes code))
    (lower : Bool) (atom : FloorAtom) :
    ∃ T : ℕ, ∀ n ≥ T, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ mark : (Fin r → ℕ) → ℝ,
      (∀ p ∈ actualPrimeBoxTuples N (fun _ => a) (fun _ => 1), |mark p| ≤ 1) →
      markedError N n a k code e lower atom mark < eps := by
  let K : ℝ := 2*2^r
  let M := (Real.log (1/a))^r+1
  have hK : 0<K := by dsimp [K]; positivity
  have hM : 0<M := by
    have h := Real.log_nonneg ((one_le_div ha).mpr ha1.le)
    dsimp [M]; positivity
  let delta := eps/(K*(M+envelope+1))
  have hD : 0 < K*(M+envelope+1) := mul_pos hK (by linarith only [hM,env_nn])
  have hδ : 0 < delta := div_pos he hD
  have hb : ∀ᶠ N : ℕ in atTop, total r N a < M := by
    have hh := tendsto_actualPrimeBoxMass (fun _ : Fin r => a) (fun _ => 1)
      (fun _ => ha) (fun _ => ha1)
    simpa only [M,total,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      hh.eventually (eventually_lt_nhds (lt_add_one _))
  have hf : ∀ᶠ N : ℕ in atTop, 4 ≤ (N:ℝ)^a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hl : ∀ᶠ N : ℕ in atTop, |literalScale N| ≤ 2 :=
    literalScale_tendsto.abs.eventually_le_const (by norm_num : |(1:ℝ)| < 2)
  apply eventually_atTop.1
  filter_upwards [eventually_fine_mesh,rate_tendsto.eventually (eventually_lt_nhds hδ),
    fixed_screen_primebox hd k code e lower atom ha ha1 hδ] with n hn hr hmass
  apply eventually_atTop.1
  filter_upwards [hb,hf,hl,hmass,eventually_gt_atTop (1:ℕ)] with N hM' hA hl hmass hN
  intro mark hw
  apply (sum_bound ha hN hd hn hA hl k code e lower atom mark hw).trans_lt
  have h1 : rate n * total r N a ≤ delta*M :=
    (mul_le_mul_of_nonneg_left hM'.le (rate_nn n)).trans (mul_le_mul_of_nonneg_right hr.le hM.le)
  have h2 := mul_le_mul_of_nonneg_left hmass.le env_nn
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK.le
  have h4 := (div_mul_cancel₀ eps hD.ne' : delta*(K*(M+envelope+1))=eps)
  have hdK := mul_pos hK hδ
  calc
    _ ≤ K*(delta*M+envelope*delta) := h3
    _ < delta*(K*(M+envelope+1)) := by nlinarith only [hdK]
    _ = eps := h4

end
end ImbalancedChen.Part5OriginalH430DiscreteThetaTransport
