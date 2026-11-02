import ImbalancedChen.P2OriginalBankChildPrimeMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Removal of the exact singular-series/totient local multiplier error.
The complete prefix d may vary arbitrarily with N: the finite bound has
no dependence on d. The residual exponent L is fixed before N. The
stronger uniform-in-moving-L statement needed by an arbitrary marked
family is not claimed.
-/
namespace ImbalancedChen.P2OriginalBankThetaMassLimits

noncomputable section
open MeasureTheory Filter Set
open P5OriginalActionMassBound
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open scoped Classical BigOperators Topology

theorem local_error {A : ℝ} {d p : ℕ} (hA : 4≤A) (hp : A≤(p:ℝ)) :
    |localPrimeFactor d p-1/((p:ℝ)-1)|≤(2/A)*(1/((p:ℝ)-1)) := by
  have hp1 : (0:ℝ)<p-1 := by linarith
  have he : localPrimeFactor d p-1/((p:ℝ)-1) =
      (localPrimeFactor d p*((p:ℝ)-1)-1)*(1/((p:ℝ)-1)) := by
    field_simp [hp1.ne']
    ring
  rw [he,abs_mul,abs_of_pos (one_div_pos.mpr hp1)]
  exact mul_le_mul_of_nonneg_right (localPrimeFactor_relative_error hA hp)
    (one_div_pos.mpr hp1).le

theorem local_le_twice {A : ℝ} {d p : ℕ} (hA : 4≤A) (hp : A≤(p:ℝ)) :
    localPrimeFactor d p≤2*(1/((p:ℝ)-1)) := by
  have h := (abs_le.mp (local_error (d:=d) hA hp)).2
  have hp1 : (0:ℝ)<p-1 := by linarith
  have he : 2/A≤1 := (div_le_one (by linarith : 0<A)).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right he (one_div_pos.mpr hp1).le
  linarith

theorem pair_local_error {A : ℝ} {d p q : ℕ}
    (hA : 4≤A) (hp : A≤(p:ℝ)) (hq : A≤(q:ℝ)) :
    |localPrimeFactor d p*localPrimeFactor (d*p) q-
      (1/((p:ℝ)-1))*(1/((q:ℝ)-1))| ≤
      (6/A)*((1/((p:ℝ)-1))*(1/((q:ℝ)-1))) := by
  let a := localPrimeFactor d p
  let b := localPrimeFactor (d*p) q
  let x : ℝ := 1/((p:ℝ)-1)
  let y : ℝ := 1/((q:ℝ)-1)
  have hb : 0≤b := (localPrimeFactor_pos (by linarith : (2:ℝ)<q)).le
  have hx : 0≤x := (one_div_pos.mpr (by linarith : (0:ℝ)<p-1)).le
  have hy : 0≤y := (one_div_pos.mpr (by linarith : (0:ℝ)<q-1)).le
  have he : 0≤2/A := by positivity
  have h1 : |a-x|≤(2/A)*x := local_error hA hp
  have h2 : |b-y|≤(2/A)*y := local_error hA hq
  have h3 : b≤2*y := local_le_twice hA hq
  change |a*b-x*y|≤(6/A)*(x*y)
  calc
    _ = |(a-x)*b+x*(b-y)| := by congr 1; ring
    _ ≤ |(a-x)*b|+|x*(b-y)| := abs_add _ _
    _ = |a-x|*b+x*|b-y| := by rw [abs_mul,abs_mul,abs_of_nonneg hb,abs_of_nonneg hx]
    _ ≤ ((2/A)*x)*(2*y)+x*((2/A)*y) :=
      add_le_add (mul_le_mul h1 h3 hb (mul_nonneg he hx))
        (mul_le_mul_of_nonneg_left h2 hx)
    _ = _ := by ring

theorem residualSingle_bounds (x : Coord 1) :
    0≤residualSingle x ∧ residualSingle x≤10 := by
  have hd : (0:ℝ)<max (1/10:ℝ) (1-x 0) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨(one_div_pos.mpr hd).le,?_⟩
  unfold residualSingle
  apply (div_le_iff₀ hd).mpr
  linarith [le_max_left (1/10:ℝ) (1-x 0)]

theorem residualPair_bounds (x : Coord 2) :
    0≤residualPair x ∧ residualPair x≤10 := by
  have hd : (0:ℝ)<max (1/10:ℝ) (1-x 0-x 1) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨(one_div_pos.mpr hd).le,?_⟩
  unfold residualPair
  apply (div_le_iff₀ hd).mpr
  linarith [le_max_left (1/10:ℝ) (1-x 0-x 1)]

theorem indicator_bounds {d : ℕ} (D : Set (Coord d)) (f : Coord d → ℝ)
    (hf : ∀x,0≤f x ∧ f x≤10) (x : Coord d) :
    0≤D.indicator f x ∧ D.indicator f x≤10 := by
  by_cases hx : x∈D
  · simpa only [indicator_of_mem hx] using hf x
  · simp only [indicator_of_notMem hx]; norm_num

def trueSingleMass (N : ℕ) (L : ℝ) (d : ℕ) (lo hi : ℝ) : ℝ :=
  ∑ p∈actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5),
    localPrimeFactor d (p 0)*
      (singleDomain lo hi).indicator residualSingle (L⁻¹ • actualPrimeTupleLog N p)

def truePairMass (N : ℕ) (L : ℝ) (d : ℕ) (a : W2Parameters) (k : Fin 4) : ℝ :=
  ∑ p∈actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
    (localPrimeFactor d (p 0)*localPrimeFactor (d*p 0) (p 1))*
      (W2PairDomain a k).indicator residualPair (L⁻¹ • actualPrimeTupleLog N p)

theorem physical_log_ratio {N d : ℕ} {L : ℝ} (hN : 1<N) (hd : 0<d)
    (hL : 0<L) {k : ℕ} (p : Fin k → ℕ) (i : Fin k) :
    Real.log (p i:ℝ)/Real.log (((d:ℝ)*(N:ℝ)^L)/d) =
      (L⁻¹ • actualPrimeTupleLog N p) i := by
  have hdR : (d:ℝ)≠0 := (Nat.cast_pos.mpr hd).ne'
  have hNR : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hres : ((d:ℝ)*(N:ℝ)^L)/d=(N:ℝ)^L := by field_simp [hdR]
  rw [hres,Real.log_rpow hNR]
  simp only [Pi.smul_apply,smul_eq_mul,actualPrimeTupleLog]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Exact normalization at Q=d*N^L. Multiplication by the parent atom
avoids dividing by li(N) or by a possibly zero marked normalizer. -/
theorem trueSingleMass_is_child_Theta {N d : ℕ} {L lo hi : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (hhi : hi≤1/2)
    (hA : 4≤(N:ℝ)^(L/10)) :
    (∑ p∈actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5),
      if L⁻¹ • actualPrimeTupleLog N p∈singleDomain lo hi then
        thetaAtom N ((d:ℝ)*(N:ℝ)^L) (d*p 0) else 0) =
      thetaAtom N ((d:ℝ)*(N:ℝ)^L) d*trueSingleMass N L d lo hi := by
  have hdR : (d:ℝ)≠0 := (Nat.cast_pos.mpr hd).ne'
  have hR : 1<((d:ℝ)*(N:ℝ)^L)/d := by
    have he : ((d:ℝ)*(N:ℝ)^L)/d=(N:ℝ)^L := by field_simp [hdR]
    rw [he]
    exact Real.one_lt_rpow (by exact_mod_cast hN) hL
  unfold trueSingleMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 := mem_actualPrimeBoxTuples_iff.mp hp 0
  have hp2 : 2<p 0 := by
    have hh := hA.trans hp0.2.2.1
    exact_mod_cast (show (2:ℝ)<p 0 by linarith)
  by_cases hx : L⁻¹ • actualPrimeTupleLog N p∈singleDomain lo hi
  · rw [if_pos hx,indicator_of_mem hx,
      thetaAtom_single (by omega) hd hp0.1 hp2 (hp0.1.coprime_iff_not_dvd.mpr hp0.2.1) hR,
      physical_log_ratio hN hd hL p 0]
    have hden : (1/10:ℝ)≤1-(L⁻¹ • actualPrimeTupleLog N p) 0 := by
      linarith [hx.2]
    rw [residualSingle,max_eq_right hden]
    ring
  · simp only [if_neg hx,indicator_of_notMem hx,mul_zero]

theorem truePairMass_is_child_Theta {N d : ℕ} {L : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (a : W2Parameters) (ha : W2Geometry a)
    (k : Fin 4) (hA : 4≤(N:ℝ)^(L/10)) :
    (∑ p∈actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
      if L⁻¹ • actualPrimeTupleLog N p∈W2PairDomain a k then
        thetaAtom N ((d:ℝ)*(N:ℝ)^L) (d*p 0*p 1) else 0) =
      thetaAtom N ((d:ℝ)*(N:ℝ)^L) d*truePairMass N L d a k := by
  have hdR : (d:ℝ)≠0 := (Nat.cast_pos.mpr hd).ne'
  have hR : 1<((d:ℝ)*(N:ℝ)^L)/d := by
    have he : ((d:ℝ)*(N:ℝ)^L)/d=(N:ℝ)^L := by field_simp [hdR]
    rw [he]
    exact Real.one_lt_rpow (by exact_mod_cast hN) hL
  unfold truePairMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 := mem_actualPrimeBoxTuples_iff.mp hp 0
  have hp1 := mem_actualPrimeBoxTuples_iff.mp hp 1
  have hp2 : 2<p 0 := by
    have hh := hA.trans hp0.2.2.1
    exact_mod_cast (show (2:ℝ)<p 0 by linarith)
  have hq2 : 2<p 1 := by
    have hh := hA.trans hp1.2.2.1
    exact_mod_cast (show (2:ℝ)<p 1 by linarith)
  by_cases hx : L⁻¹ • actualPrimeTupleLog N p∈W2PairDomain a k
  · rw [if_pos hx,indicator_of_mem hx,
      thetaAtom_pair (by omega) hd hp0.1 hp1.1 hp2 hq2
        (hp0.1.coprime_iff_not_dvd.mpr hp0.2.1)
        (hp1.1.coprime_iff_not_dvd.mpr hp1.2.1) hR,
      physical_log_ratio hN hd hL p 0,physical_log_ratio hN hd hL p 1]
    have hden := pair_residual_floor ha k hx
    rw [residualPair,max_eq_right (show (1/10:ℝ)≤
      1-(L⁻¹ • actualPrimeTupleLog N p) 0-(L⁻¹ • actualPrimeTupleLog N p) 1 by linarith)]
    ring
  · simp only [if_neg hx,indicator_of_notMem hx,mul_zero]

theorem single_mass_difference {N : ℕ} {L : ℝ} (d : ℕ) (lo hi : ℝ)
    (hA : 4≤(N:ℝ)^(L/10)) :
    |trueSingleMass N L d lo hi-
      scaledPrimeSum N L (singleDomain lo hi) residualSingle| ≤
      (20/(N:ℝ)^(L/10))*
        actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  unfold trueSingleMass scaledPrimeSum actualPrimeBoxTestSum actualPrimeBoxMass
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hfloor := (mem_actualPrimeBoxTuples_iff.mp hp 0).2.2.1
  have hw : 0≤1/((p 0:ℝ)-1) := by
    have hp1 : (1:ℝ)<p 0 := by exact_mod_cast (mem_actualPrimeBoxTuples_iff.mp hp 0).1.one_lt
    exact (one_div_pos.mpr (by linarith)).le
  have hb := indicator_bounds (singleDomain lo hi) residualSingle residualSingle_bounds
    (L⁻¹ • actualPrimeTupleLog N p)
  simp only [Fin.prod_univ_one,← sub_mul,abs_mul,abs_of_nonneg hb.1]
  calc
    _ ≤ ((2/(N:ℝ)^(L/10))*(1/((p 0:ℝ)-1)))*10 :=
      mul_le_mul (local_error hA hfloor) hb.2 hb.1 (mul_nonneg (by positivity) hw)
    _ = _ := by ring

theorem pair_mass_difference {N : ℕ} {L : ℝ} (d : ℕ) (a : W2Parameters) (k : Fin 4)
    (hA : 4≤(N:ℝ)^(L/10)) :
    |truePairMass N L d a k-W2PairPrimeMass N L a k| ≤
      (60/(N:ℝ)^(L/10))*
        actualPrimeBoxMass N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5) := by
  unfold truePairMass W2PairPrimeMass scaledPrimeSum actualPrimeBoxTestSum actualPrimeBoxMass
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hf0 := (mem_actualPrimeBoxTuples_iff.mp hp 0).2.2.1
  have hf1 := (mem_actualPrimeBoxTuples_iff.mp hp 1).2.2.1
  have hw := actualPrimeBoxWeight_nonneg hp
  simp only [Fin.prod_univ_two] at hw
  have hb := indicator_bounds (W2PairDomain a k) residualPair residualPair_bounds
    (L⁻¹ • actualPrimeTupleLog N p)
  simp only [Fin.prod_univ_two,← sub_mul,abs_mul,abs_of_nonneg hb.1]
  calc
    _ ≤ ((6/(N:ℝ)^(L/10))*((1/((p 0:ℝ)-1))*(1/((p 1:ℝ)-1))))*10 :=
      mul_le_mul (pair_local_error hA hf0 hf1) hb.2 hb.1 (mul_nonneg (by positivity) hw)
    _ = _ := by ring

theorem error_bound_tendsto {L : ℝ} (hL : 0<L) (d : ℕ) (C : ℝ) :
    Tendsto (fun N : ℕ => (C/(N:ℝ)^(L/10))*
      actualPrimeBoxMass N (fun _ : Fin d => L/10) (fun _ => 3*L/5))
      atTop (𝓝 0) := by
  have hi := tendsto_nat_log_pow_div_rpow 0 (show 0<L/10 by positivity)
  simp only [pow_zero] at hi
  have hm := tendsto_actualPrimeBoxMass
    (fun _ : Fin d => L/10) (fun _ => 3*L/5)
    (fun _ => by positivity) (fun _ => by linarith)
  have hh := (hi.const_mul C).mul hm
  simpa only [mul_zero,zero_mul,mul_one_div] using hh

theorem true_single_difference_tendsto {L : ℝ} (hL : 0<L)
    (d : ℕ → ℕ) (lo hi : ℝ) :
    Tendsto (fun N : ℕ => trueSingleMass N L (d N) lo hi-
      scaledPrimeSum N L (singleDomain lo hi) residualSingle) atTop (𝓝 0) := by
  have hpower : Tendsto (fun N : ℕ => (N:ℝ)^(L/10)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0<L/10)).comp tendsto_natCast_atTop_atTop
  have herr := error_bound_tendsto hL 1 20
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using herr.neg) herr
  · filter_upwards [hpower.eventually (eventually_ge_atTop (4:ℝ))] with N hN
    exact (abs_le.mp (single_mass_difference (d N) lo hi hN)).1
  · filter_upwards [hpower.eventually (eventually_ge_atTop (4:ℝ))] with N hN
    exact (abs_le.mp (single_mass_difference (d N) lo hi hN)).2

theorem true_pair_difference_tendsto {L : ℝ} (hL : 0<L)
    (d : ℕ → ℕ) (a : W2Parameters) (k : Fin 4) :
    Tendsto (fun N : ℕ => truePairMass N L (d N) a k-W2PairPrimeMass N L a k)
      atTop (𝓝 0) := by
  have hpower : Tendsto (fun N : ℕ => (N:ℝ)^(L/10)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0<L/10)).comp tendsto_natCast_atTop_atTop
  have herr := error_bound_tendsto hL 2 60
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using herr.neg) herr
  · filter_upwards [hpower.eventually (eventually_ge_atTop (4:ℝ))] with N hN
    exact (abs_le.mp (pair_mass_difference (d N) a k hN)).1
  · filter_upwards [hpower.eventually (eventually_ge_atTop (4:ℝ))] with N hN
    exact (abs_le.mp (pair_mass_difference (d N) a k hN)).2

theorem all70_true_single_mass {L : ℝ} (hL : 0<L) (d : ℕ → ℕ)
    (i : Fin 7) (j : Fin 10) :
    Tendsto (fun N : ℕ => trueSingleMass N L (d N) (1/W1Anchor j) (1/W1Target i))
      atTop (𝓝 (∫ x in singleDomain (1/W1Anchor j) (1/W1Target i),
        1/(x 0*(1-x 0)))) := by
  have h := (true_single_difference_tendsto hL d (1/W1Anchor j) (1/W1Target i)).add
    (all70_W1_prime_mass hL i j)
  simpa only [W1PrimeMass,sub_add_cancel,zero_add] using h

theorem all36_true_singleton_mass {L : ℝ} (hL : 0<L) (d : ℕ → ℕ)
    (j : Fin 36) (k : Fin 3) :
    Tendsto (fun N : ℕ => trueSingleMass N L (d N)
      (a0 (originalW2At j)) (singletonTop (originalW2At j) k)) atTop
      (𝓝 (∫ x in singleDomain (a0 (originalW2At j)) (singletonTop (originalW2At j) k),
        1/(x 0*(1-x 0)))) := by
  have h := (true_single_difference_tendsto hL d _ _).add
    (all36_three_singleton_prime_masses hL j k)
  simpa only [W2SingletonPrimeMass,sub_add_cancel,zero_add] using h

theorem all36_true_good_pair_mass {L : ℝ} (hL : 0<L) (d : ℕ → ℕ)
    (j : Fin 36) (k : Fin 4) :
    Tendsto (fun N : ℕ => truePairMass N L (d N) (originalW2At j) k) atTop
      (𝓝 (∫ x in W2PairDomain (originalW2At j) k,
        1/(x 0*x 1*(1-x 0-x 1)))) := by
  have h := (true_pair_difference_tendsto hL d (originalW2At j) k).add
    (all36_four_good_pair_prime_masses hL j k)
  simpa only [sub_add_cancel,zero_add] using h

theorem all70_original_single_integral {L : ℝ} (hL : 0<L) (d : ℕ → ℕ)
    (i : Fin 7) (j : Fin 10) :
    Tendsto (fun N : ℕ => trueSingleMass N L (d N) (1/W1Anchor j) (1/W1Target i))
      atTop (𝓝 (∫ u in W1Domain i j,1/(u*(1-u)))) := by
  have ht := all70_true_single_mass hL d i j
  rw [single_integral_coordinates] at ht
  exact ht

theorem all36_original_single_integral {L : ℝ} (hL : 0<L) (d : ℕ → ℕ)
    (j : Fin 36) (k : Fin 3) :
    Tendsto (fun N : ℕ => trueSingleMass N L (d N)
      (a0 (originalW2At j)) (singletonTop (originalW2At j) k)) atTop
      (𝓝 (∫ u in W2SingletonDomain (originalW2At j) k,1/(u*(1-u)))) := by
  have ht := all36_true_singleton_mass hL d j k
  rw [single_integral_coordinates] at ht
  have he : Ioo (a0 (originalW2At j)) (singletonTop (originalW2At j) k)=
      W2SingletonDomain (originalW2At j) k := by
    fin_cases k <;> rfl
  rwa [he] at ht

def trueW1FeedbackMass (N : ℕ) (L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10) : ℝ :=
  1+trueSingleMass N L d (1/W1Anchor j) (1/W1Target i)/2

theorem all70_true_feedback_mass {L : ℝ} (hL : 0<L) (d : ℕ → ℕ)
    (i : Fin 7) (j : Fin 10) :
    Tendsto (fun N : ℕ => trueW1FeedbackMass N L (d N) i j) atTop
      (𝓝 (W1FeedbackMass i j)) := by
  rw [W1FeedbackMass_eq_original]
  exact tendsto_const_nhds.add ((all70_original_single_integral hL d i j).div_const 2)

def trueW2FeedbackMass (N : ℕ) (L : ℝ) (d : ℕ) (a : W2Parameters) : ℝ :=
  (4+1+trueSingleMass N L d (a0 a) (b a)+
    trueSingleMass N L d (a0 a) (a2 a)+trueSingleMass N L d (a0 a) (a3 a)+
    truePairMass N L d a 0+truePairMass N L d a 1+
    truePairMass N L d a 2+truePairMass N L d a 3)/5

/-- All original multiplicities, unchanged-prefix atoms and the one
division by five survive in the limiting genuine child mass. This is
a mass theorem, not a licence to replace old upper/lower counts. -/
theorem all36_true_feedback_mass {L : ℝ} (hL : 0<L) (d : ℕ → ℕ) (j : Fin 36) :
    Tendsto (fun N : ℕ => trueW2FeedbackMass N L (d N) (originalW2At j)) atTop
      (𝓝 (W2FeedbackMass (originalW2At j))) := by
  have h2 := all36_original_single_integral hL d j 0
  have h3 := all36_original_single_integral hL d j 1
  have h4 := all36_original_single_integral hL d j 2
  have h5 := all36_true_good_pair_mass hL d j 0
  have h6 := all36_true_good_pair_mass hL d j 1
  have h7 := all36_true_good_pair_mass hL d j 2
  have h8 := all36_true_good_pair_mass hL d j 3
  rw [W2FeedbackMass_eq_original (originalRepairedW2Bank_geometry _ (originalW2At_mem j))]
  exact (((((((tendsto_const_nhds.add h2).add h3).add h4).add h5).add h6).add h7).add h8).div_const 5

/-- Quantifier order is stronger than a limit for one fixed prefix:
one threshold precedes every natural prefix and every finite window.
The residual exponent remains fixed before that threshold. -/
theorem fixed_L_uniform_single_family {ι : Type*} [Finite ι]
    {L epsilon : ℝ} (hL : 0<L) (hepsilon : 0<epsilon)
    (lo hi : ι → ℝ) (hlo : ∀i,(1/5:ℝ)≤lo i) (hhi : ∀i,hi i≤1/2) :
    ∃ T : ℕ,∀N : ℕ,T≤N → ∀d : ℕ,∀i : ι,
      |trueSingleMass N L d (lo i) (hi i)-
        (∫ x in singleDomain (lo i) (hi i),1/(x 0*(1-x 0)))|<epsilon := by
  have hpower : Tendsto (fun N : ℕ => (N:ℝ)^(L/10)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0<L/10)).comp tendsto_natCast_atTop_atTop
  have he := (error_bound_tendsto hL 1 20).eventually
    (gt_mem_nhds (by positivity : (0:ℝ)<epsilon/2))
  have hm : ∀ᶠN : ℕ in atTop,∀i : ι,
      |scaledPrimeSum N L (singleDomain (lo i) (hi i)) residualSingle-
        (∫ x in singleDomain (lo i) (hi i),1/(x 0*(1-x 0)))|<epsilon/2 := by
    apply eventually_all.mpr
    intro i
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_single_mass hL (hlo i) (hhi i)) (epsilon/2) (by positivity)
  have hall : ∀ᶠN : ℕ in atTop,∀d : ℕ,∀i : ι,
      |trueSingleMass N L d (lo i) (hi i)-
        (∫ x in singleDomain (lo i) (hi i),1/(x 0*(1-x 0)))|<epsilon := by
    filter_upwards [hpower.eventually (eventually_ge_atTop (4:ℝ)),he,hm] with N hA hE hM d i
    have hb := single_mass_difference d (lo i) (hi i) hA
    have ht := abs_sub_le (trueSingleMass N L d (lo i) (hi i))
      (scaledPrimeSum N L (singleDomain (lo i) (hi i)) residualSingle)
      (∫ x in singleDomain (lo i) (hi i),1/(x 0*(1-x 0)))
    linarith [hM i]
  exact eventually_atTop.mp hall

theorem all36_fixed_L_uniform_pair_mass {L epsilon : ℝ}
    (hL : 0<L) (hepsilon : 0<epsilon) :
    ∃ T : ℕ,∀N : ℕ,T≤N → ∀d : ℕ,∀j : Fin 36,∀k : Fin 4,
      |truePairMass N L d (originalW2At j) k-
        (∫ x in W2PairDomain (originalW2At j) k,1/(x 0*x 1*(1-x 0-x 1)))|<epsilon := by
  have hpower : Tendsto (fun N : ℕ => (N:ℝ)^(L/10)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0<L/10)).comp tendsto_natCast_atTop_atTop
  have he := (error_bound_tendsto hL 2 60).eventually
    (gt_mem_nhds (by positivity : (0:ℝ)<epsilon/2))
  have hm : ∀ᶠN : ℕ in atTop,∀j : Fin 36,∀k : Fin 4,
      |W2PairPrimeMass N L (originalW2At j) k-
        (∫ x in W2PairDomain (originalW2At j) k,1/(x 0*x 1*(1-x 0-x 1)))|<epsilon/2 := by
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro k
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (all36_four_good_pair_prime_masses hL j k) (epsilon/2) (by positivity)
  have hall : ∀ᶠN : ℕ in atTop,∀d : ℕ,∀j : Fin 36,∀k : Fin 4,
      |truePairMass N L d (originalW2At j) k-
        (∫ x in W2PairDomain (originalW2At j) k,1/(x 0*x 1*(1-x 0-x 1)))|<epsilon := by
    filter_upwards [hpower.eventually (eventually_ge_atTop (4:ℝ)),he,hm] with N hA hE hM d j k
    have hb := pair_mass_difference d (originalW2At j) k hA
    have ht := abs_sub_le (truePairMass N L d (originalW2At j) k)
      (W2PairPrimeMass N L (originalW2At j) k)
      (∫ x in W2PairDomain (originalW2At j) k,1/(x 0*x 1*(1-x 0-x 1)))
    linarith [hM j k]
  exact eventually_atTop.mp hall

theorem all70_fixed_L_uniform_single_mass {L epsilon : ℝ}
    (hL : 0<L) (hepsilon : 0<epsilon) :
    ∃ T : ℕ,∀N : ℕ,T≤N → ∀d : ℕ,∀i : Fin 7,∀j : Fin 10,
      |trueSingleMass N L d (1/W1Anchor j) (1/W1Target i)-
        (∫ u in W1Domain i j,1/(u*(1-u)))|<epsilon := by
  have hlo (ij : Fin 7 × Fin 10) : (1/5:ℝ)≤1/W1Anchor ij.2 := by
    have hj : (ij.2.val:ℝ)≤9 := by exact_mod_cast (show ij.2.val≤9 by omega)
    exact one_div_le_one_div_of_le (by unfold W1Anchor; positivity)
      (by unfold W1Anchor; linarith)
  have hhi (ij : Fin 7 × Fin 10) : 1/W1Target ij.1≤(1/2:ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    unfold W1Target
    linarith [show (0:ℝ)≤ij.1.val from Nat.cast_nonneg _]
  obtain ⟨T,hT⟩ := fixed_L_uniform_single_family hL hepsilon
    (fun ij : Fin 7 × Fin 10 => 1/W1Anchor ij.2)
    (fun ij : Fin 7 × Fin 10 => 1/W1Target ij.1) hlo hhi
  refine ⟨T,?_⟩
  intro N hN d i j
  have hh := hT N hN d (i,j)
  rw [single_integral_coordinates] at hh
  exact hh

theorem all36_fixed_L_uniform_singleton_mass {L epsilon : ℝ}
    (hL : 0<L) (hepsilon : 0<epsilon) :
    ∃ T : ℕ,∀N : ℕ,T≤N → ∀d : ℕ,∀j : Fin 36,∀k : Fin 3,
      |trueSingleMass N L d (a0 (originalW2At j)) (singletonTop (originalW2At j) k)-
        (∫ u in W2SingletonDomain (originalW2At j) k,1/(u*(1-u)))|<epsilon := by
  have hlo (jk : Fin 36 × Fin 3) : (1/5:ℝ)≤a0 (originalW2At jk.1) :=
    (originalRepairedW2Bank_geometry _ (originalW2At_mem jk.1)).1
  have hhi (jk : Fin 36 × Fin 3) : singletonTop (originalW2At jk.1) jk.2≤1/2 := by
    rcases originalRepairedW2Bank_geometry _ (originalW2At_mem jk.1) with
      ⟨h0,h01,h12,h23,h3,hb,hg6,hg7,hg8⟩
    rcases jk with ⟨j,k⟩
    fin_cases k <;> simp only [singletonTop,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two] <;> linarith
  obtain ⟨T,hT⟩ := fixed_L_uniform_single_family hL hepsilon
    (fun jk : Fin 36 × Fin 3 => a0 (originalW2At jk.1))
    (fun jk : Fin 36 × Fin 3 => singletonTop (originalW2At jk.1) jk.2) hlo hhi
  refine ⟨T,?_⟩
  intro N hN d j k
  have hh := hT N hN d (j,k)
  rw [single_integral_coordinates] at hh
  have he : Ioo (a0 (originalW2At j)) (singletonTop (originalW2At j) k)=
      W2SingletonDomain (originalW2At j) k := by
    fin_cases k <;> rfl
  rwa [he] at hh

end
end ImbalancedChen.P2OriginalBankThetaMassLimits
