import ImbalancedChen.Part3OriginalRegularCumulativePrice

/-! The true height exhaustion for the two weight-zero spectral
measures. The initial interval contains the eigenvalue 1/4. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCumulativeMeasures20261113
open Real Set Filter MeasureTheory Finset
open scoped MatrixGroups Classical
open ActualFullCuspEigenbasis20261026b
open ActualUnitBandSpectralMass20261112 (exceptional height)
open OriginalRegularPacketTest20261113 (Dyadic energy energy_nonneg mark discreteRow lineMass lineMass_nonneg)
open OriginalRegularBaseCumulative20261113 (baseTerm lineTerm baseConstant baseConstant_pos base_cumulative)
open OriginalCumulativeContinuousRemoval20261110 (marked_density_cont)
open OriginalRegularGaussianSpectralWindow20261113 (window windowMeasure window_measurable)
open OriginalRegularMarkedDyadic20261113 (marked_shell)
open OriginalRegularCumulativePrice20261113
open OriginalHolomorphicInfinityPacket20261113 (start)
open private nonnegative_sum from ImbalancedChen.Part3ActualUnitBandSpectralMass

private theorem line_step {T : ℝ} (hT : 2≤T) {F : ℝ→ℝ} (fc : Continuous F) (nn : ∀ t,0≤F t) :
    (∫ t in Icc (-(2*T)) (2*T),F t)≤(∫ t in Icc (-T) T,F t)+(∫ t in window (2*T),F t) := by
  classical
  let A := Icc (-T) T
  let B := window (2*T)
  let U := Icc (-(2*T)) (2*T)
  have au : IntegrableOn F U := fc.continuousOn.integrableOn_compact isCompact_Icc
  have ia : IntegrableOn F A := fc.continuousOn.integrableOn_compact isCompact_Icc
  have ib : IntegrableOn F B := au.mono_set (fun _ h => abs_le.mp h.2.2)
  have iA := ia.integrable_indicator (measurableSet_Icc : MeasurableSet A)
  have iB := ib.integrable_indicator (window_measurable (2*T))
  have iU := au.integrable_indicator (measurableSet_Icc : MeasurableSet U)
  have point (t : ℝ) : U.indicator F t≤A.indicator F t+B.indicator F t := by
    by_cases u : t∈U
    · rw [indicator_of_mem u]
      by_cases a : t∈A
      · rw [indicator_of_mem a]
        exact le_add_of_nonneg_right (by by_cases b : t∈B <;> simp [indicator,b,nn t])
      · have v : T<|t| := lt_of_not_ge (fun h => a (abs_le.mp h))
        have b : t∈B := ⟨hT.trans v.le,by linarith only [v],abs_le.mpr u⟩
        simp only [indicator_of_notMem a,indicator_of_mem b,zero_add,le_refl]
    · rw [indicator_of_notMem u]
      by_cases a : t∈A <;> by_cases b : t∈B <;> simp [indicator,a,b,nn t,add_nonneg (nn t) (nn t)]
  have I := integral_mono iU (iA.add iB) point
  rw [integral_add iA iB,integral_indicator (measurableSet_Icc : MeasurableSet U),
    integral_indicator (measurableSet_Icc : MeasurableSet A),integral_indicator (window_measurable (2*T))] at I
  exact I

private theorem line_mono {T K : ℝ} (h : K≤T) {F : ℝ→ℝ} (fc : Continuous F) (nn : ∀ t,0≤F t) :
    (∫ t in Icc (-K) K,F t)≤∫ t in Icc (-T) T,F t :=
  setIntegral_mono_set (fc.continuousOn.integrableOn_compact isCompact_Icc) (ae_of_all _ nn)
    (ae_of_all _ (fun _ ht => ⟨(neg_le_neg h).trans ht.1,ht.2.trans h⟩))

variable (N : ℕ) [NeZero N] (one neg : Bool) (S : Finset ℕ) (a : ℕ→ℂ)
private abbrev Idx := actualCuspBasisIndex N (NeZero.pos N)

private theorem discrete_step {T : ℝ} (hT : 2≤T) (J : Finset (Idx N)) :
    let A := fun i : Idx N => ¬exceptional N i ∧ height N i∈window (2*T)
    let f := fun i => ‖discreteRow N one neg S a i‖^2/cosh (π*height N i)
    (∑ i∈J,baseTerm N one neg (2*T) S a i)≤
      (∑ i∈J,baseTerm N one neg T S a i)+∑ i∈J.filter A,f i := by
  classical
  intro A f
  rw [sum_filter,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  have f0 : 0≤f i := div_nonneg (sq_nonneg _) (cosh_pos _).le
  have h0 : 0≤height N i := Real.sqrt_nonneg _
  by_cases hi : ¬exceptional N i ∧ height N i≤2*T
  · rw [baseTerm,if_pos hi]
    by_cases low : height N i≤T
    · rw [baseTerm,if_pos ⟨hi.1,low⟩]
      exact le_add_of_nonneg_right (by split <;> first | exact f0 | exact le_refl 0)
    · have Ahi : A i := ⟨hi.1,by
        change 2≤|height N i| ∧ 2*T/2≤|height N i| ∧ |height N i|≤2*T
        rw [abs_of_nonneg h0]
        exact ⟨hT.trans (le_of_not_ge low),by linarith only [le_of_not_ge low],hi.2⟩⟩
      rw [baseTerm,if_neg (fun h => low h.2),if_pos Ahi,zero_add]
  · rw [baseTerm,if_neg hi]
    have B : 0≤baseTerm N one neg T S a i := by unfold baseTerm;split <;> positivity
    exact add_nonneg B (by split <;> first | exact f0 | exact le_refl 0)

private theorem discrete_mono {K T : ℝ} (h : K≤T) (i : Idx N) :
    baseTerm N one neg K S a i≤baseTerm N one neg T S a i := by
  by_cases ok : ¬exceptional N i ∧ height N i≤K
  · simp only [baseTerm,if_pos ok,if_pos (And.intro ok.1 (ok.2.trans h)),le_refl]
  · rw [baseTerm,if_neg ok,baseTerm]
    split <;> positivity

/-- The original cumulative Maass and continuous measures, on both
observation cusps, over the full signed height interval. -/
theorem manuscript_weight_zero (e : ℝ) (he : 0<e) : ∃ D : ℝ,0<D ∧
    ∀ (q : ℕ) [NeZero q] (one neg : Bool) {K L : ℝ},1≤K → 1/2≤L →
    ∀ (S : Finset ℕ) (a : ℕ→ℂ),Dyadic L S →
      Summable (baseTerm q one neg K S a) ∧
      (∑' i,baseTerm q one neg K S a i)≤D*(K^2+L^(1+e)/(q:ℝ))*energy S a ∧
      IntegrableOn (lineTerm q one neg S a) (Icc (-K) K) ∧
      (∫ t in Icc (-K) K,lineTerm q one neg S a t)≤D*(K^2+L^(1+e)/(q:ℝ))*energy S a := by
  let d := e/2
  have hd : 0<d := half_pos he
  have ed : 2*d=e := by dsimp only [d];ring
  obtain ⟨C,c0,high⟩ := marked_shell
  let B := common C d
  have bp : 0<B := common_positive C d
  refine ⟨B*finalCost d,mul_pos bp (final_positive hd),?_⟩
  intro q inst one neg K L hK hL S a bd
  classical
  let q' : ℕ+ := ⟨q,NeZero.pos q⟩
  let X := (start L:ℝ)^(1+d)/(q:ℝ)
  let E := energy S a
  let F := lineTerm q one neg S a
  let A := fun (T : ℝ) (J : Finset (Idx q)) => ∑ i∈J,baseTerm q one neg T S a i
  have zp : 0<(q:ℝ) := by exact_mod_cast NeZero.pos q
  have x0 : 0≤X := div_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) zp.le
  have e0 := energy_nonneg S a
  have fc : Continuous F := marked_density_cont q S a (mark neg) one
  have f0 (t : ℝ) : 0≤F t := div_nonneg (lineMass_nonneg q one neg S a t) (cosh_pos _).le
  have nonneg (T : ℝ) (i : Idx q) : 0≤baseTerm q one neg T S a i := by unfold baseTerm;split <;> positivity
  let P := fun n : ℕ => B*(2*(cut n)^2+((n:ℝ)+1)*X)*E
  have result (n : ℕ) : (∀ J,A (cut n) J≤P n) ∧ (∫ t in Icc (-(cut n)) (cut n),F t)≤P n := by
    induction n with
    | zero =>
      obtain ⟨summ,D,_,G⟩ := base_cumulative q one neg (by linarith only [hL]) (le_refl 2) S a bd
      have len : L/(q:ℝ)≤X := div_le_div_of_nonneg_right (initial_length hd) zp.le
      have v : baseConstant*(1+L/(q:ℝ))*E≤P 0 := by
        have p : 0≤1+L/(q:ℝ) := by
          have lp : 0≤L := by linarith only [hL]
          positivity
        apply mul_le_mul_of_nonneg_right _ e0
        apply (mul_le_mul_of_nonneg_right (common_base C d) p).trans
        apply mul_le_mul_of_nonneg_left _ bp.le
        rw [first]
        norm_num only [Nat.cast_zero,zero_add,one_mul]
        linarith only [len]
      rw [first]
      exact ⟨fun J => ((summ.sum_le_tsum J (fun i _ => nonneg 2 i)).trans D).trans v,G.trans v⟩
    | succ n ih =>
      let T := cut n
      have hT : 2≤T := two_le n
      have h2 : 2≤2*T := by linarith only [hT]
      obtain ⟨ds,cs⟩ := high hd h2 q' one neg hL S a bd
      have price := mul_le_mul_of_nonneg_right (common_shell (C:=C) (d:=d) c0.le (sq_nonneg (2*T)) x0) e0
      have hs : P n+B*((2*T)^2+X)*E≤P (n+1) := by
        have V := mul_nonneg (mul_nonneg bp.le (sq_nonneg T)) e0
        change B*(2*T^2+((n:ℝ)+1)*X)*E+B*((2*T)^2+X)*E≤_
        simp only [P]
        rw [twice,Nat.cast_succ]
        change _≤B*(2*(2*T)^2+(((n:ℝ)+1)+1)*X)*E
        nlinarith only [V]
      have gstep := (line_step hT fc f0).trans (add_le_add ih.2 (cs.trans price))
      rw [twice]
      refine ⟨?_,gstep.trans hs⟩
      intro J
      let pred := fun i : Idx q => ¬exceptional q i ∧ height q i∈window (2*T)
      have band := ds (J.filter pred) (fun i h => (mem_filter.mp h).2)
      have disc := (discrete_step q one neg S a hT J).trans (add_le_add (ih.1 J) (band.trans price))
      exact disc.trans hs
  obtain ⟨n,cover,kcut⟩ := locate hK
  have total : P n≤(B*finalCost d)*(K^2+L^(1+e)/(q:ℝ))*E := by
    have w := cumulative_price (q:=q') hd hL kcut
    rw [ed] at w
    have b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left w bp.le) e0
    convert b using 1 <;> ring
  obtain ⟨sum,cap⟩ := nonnegative_sum (nonneg K) (A:=(B*finalCost d)*(K^2+L^(1+e)/(q:ℝ))*E) (by
    intro J
    exact ((sum_le_sum (fun i _ => discrete_mono q one neg S a cover i)).trans ((result n).1 J)).trans total)
  exact ⟨sum,cap,fc.continuousOn.integrableOn_compact isCompact_Icc,
    ((line_mono cover fc f0).trans (result n).2).trans total⟩

end ImbalancedChen.Part3.OriginalRegularCumulativeMeasures20261113
end
