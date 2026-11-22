import ImbalancedChen.P2WuProductInnerProfile
import ImbalancedChen.P2NativeOmega3RankTupleReceiver
import MathlibNt.Wu2008DoubleSieve.BoxMassTheta

/-!
SOURCE ONLY / UNCOMPILED.

The finite complete-product collar is paid on the ORIGINAL native Theta
scale. The derivative width exponent is 5*k+3, one greater than the proved
Theta logarithmic exponent. The finite prime-tuple multiplicity constant
depends on R, but the threshold is chosen before ALL BoxIndex parameters.

No distribution, density, PP, U99 or endpoint bound is a premise. This
inserts one smooth complete-product cap; all other sharp masks remain.
-/
namespace ImbalancedChen.P2WuProductInnerThetaPayment

noncomputable section
open Classical Set Filter Topology Real Finset Wu2008DoubleSieve
open scoped BigOperators
open P2WuProductInnerProfile
open P2NativeOmega3RankTupleReceiver
open P5Z.ActualSingletonLogCollarFamily

def rankMultiplicity (R : ℕ) : ℕ := ∑ r ∈ Finset.range (R+1), r^r

def collarExponent (k : ℕ) : ℕ := 5*k+3

theorem rankMultiplicity_pos (R : ℕ) : 0 < rankMultiplicity R := by
  have h0 : 0 ∈ Finset.range (R+1) := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum (fun r (_ : r ∈ Finset.range (R+1)) => Nat.zero_le (r^r)) h0
  change 0^0 ≤ rankMultiplicity R at h
  norm_num only [Nat.pow_zero] at h
  omega

/-- A fixed finite-rank raw collar cost is epsilon*Theta uniformly over
all legal shrinking boxes. There is no conversion through global H_N. -/
theorem uniform_collar_scale (k R : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (rankMultiplicity R:ℝ) *
          (Nat.ceil (logWidth (collarExponent k) N * (N:ℝ)):ℝ) ≤
        ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨c,hc,T0,hTheta⟩ := wu_boxTheta_lower k hδ (by linarith : δ<1/2)
  let m := 5*k+2
  let B := collarExponent k
  let M : ℝ := rankMultiplicity R
  have hM : 0 < M := by exact_mod_cast rankMultiplicity_pos R
  have hB : B=m+1 := by dsimp [B,m,collarExponent]; omega
  have hlogt : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglarge : ∀ᶠ N : ℕ in atTop,
      max 1 (2*M/(ε*c)) ≤ Real.log (N:ℝ) :=
    hlogt.eventually (eventually_ge_atTop _)
  have hround := box_eventually_log_power_budget m
    (show 0 < 2*M/(ε*c) by positivity) (by norm_num : (0:ℝ)<1)
  have hgood : ∀ᶠ N : ℕ in atTop,
      ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        M*(Nat.ceil (logWidth B N*(N:ℝ)):ℝ) ≤
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    filter_upwards [hloglarge,hround,eventually_ge_atTop (max 4 T0)]
      with N hlarge hroundN hN
    intro i Δ V hb
    have hN4 := (le_max_left 4 T0).trans hN
    have hN0 := (le_max_right 4 T0).trans hN
    have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    let L := Real.log (N:ℝ)
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
    have hL : 0 < L := by linarith
    have hlogs : L ≤ Real.log ((N:ℝ)+2) :=
      Real.log_le_log hNr (by linarith)
    have hwidth : logWidth B N ≤ 1/L^(m+1) := by
      calc
        _ ≤ 1/Real.log ((N:ℝ)+2)^B := logWidth_le_inverse_log B (by omega)
        _ ≤ 1/L^B := one_div_le_one_div_of_le (pow_pos hL B)
          (pow_le_pow_left₀ hL.le hlogs B)
        _ = _ := by rw [hB]
    have hratio : M/L ≤ ε*c/2 := by
      have hpre : 2*M/(ε*c) ≤ L := (le_max_right _ _).trans hlarge
      have hpay := (div_le_iff₀ (mul_pos hε hc)).mp hpre
      apply (div_le_iff₀ hL).mpr
      nlinarith only [hpay]
    have hmain : M*(logWidth B N*(N:ℝ)) ≤ (ε/2)*(c*(N:ℝ)/L^m) := by
      calc
        _ ≤ M*((1/L^(m+1))*(N:ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hwidth hNr.le) hM.le
        _ = (M/L)*((N:ℝ)/L^m) := by
          rw [pow_succ]
          field_simp [hL.ne']
          ring
        _ ≤ (ε*c/2)*((N:ℝ)/L^m) :=
          mul_le_mul_of_nonneg_right hratio (div_nonneg hNr.le (pow_nonneg hL.le m))
        _ = _ := by ring
    have hround0 : (2*M/(ε*c))*L^m ≤ (N:ℝ) := by
      simpa only [Real.rpow_one] using hroundN
    have hpay : 2*M*L^m ≤ ε*c*(N:ℝ) := by
      calc
        _ = (ε*c)*((2*M/(ε*c))*L^m) := by
          field_simp [(mul_pos hε hc).ne']
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hround0 (mul_nonneg hε.le hc.le)
    have hconstant : M ≤ (ε/2)*(c*(N:ℝ)/L^m) := by
      calc
        M ≤ (ε*c*(N:ℝ)/2)/L^m := by
          apply (le_div_iff₀ (pow_pos hL m)).mpr
          nlinarith only [hpay]
        _ = _ := by ring
    have hw0 : 0 ≤ logWidth B N := (logWidth_bounds B (by omega)).1.le
    have hceil : (Nat.ceil (logWidth B N*(N:ℝ)):ℝ) ≤ logWidth B N*(N:ℝ)+1 :=
      (Nat.ceil_lt_add_one (mul_nonneg hw0 hNr.le)).le
    have hThetaN := hTheta N hN0 i hb.1 Δ hb.2.1 hb.2.2.1 V
      hb.2.2.2.2.1 hb.2.2.2.2.2
    have hscale : c*(N:ℝ)/L^m ≤
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := hThetaN
    calc
      _ ≤ M*(logWidth B N*(N:ℝ)+1) := mul_le_mul_of_nonneg_left hceil hM.le
      _ ≤ ε*(c*(N:ℝ)/L^m) := by nlinarith only [hmain,hconstant]
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale hε.le
  obtain ⟨T,hT⟩ := eventually_atTop.mp hgood
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN i Δ V hb
  exact hT N ((le_max_right 4 T).trans hN) i Δ V hb

/-- The actual source74 indexed families receive a uniformly paid INNER
complete-product cutoff. No bound on PP, density or endpoint values occurs. -/
theorem uniform_indexed_inner_cut_loss (k R : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 →
        (∑ r ∈ Finset.range (R+1),
          p5z_labelledPrimeMass (indexedFamily k δ r N b) Part3.labelledProduct
            (fun _ => 1) N) ≤
        (∑ r ∈ Finset.range (R+1),
          p5z_labelledPrimeMass (indexedFamily k δ r N b) Part3.labelledProduct
            (innerWeight (collarExponent k) N) N) +
        ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2) := by
  obtain ⟨T,hT4,hT⟩ := uniform_collar_scale k R hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN b hb
  have hN4 := hT4.trans hN
  have hw := logWidth_bounds (collarExponent k) (by omega : 2≤N)
  have hrow (r : ℕ) :=
    finite_inner_cut_loss (by omega : 2≤N) (indexedFamily k δ r N b)
      (indexedFamily_prime k δ r N b)
      (by
        simp only [indexedFamily,if_pos hb]
        exact family_product_cap (fun j p hp => (mem_convolutionWuWindows.mp hp).1))
      hw.1 hw.2
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range (R+1)) => hrow r)
  have hcost : (∑ r ∈ Finset.range (R+1),
      (r^r:ℕ)*(Nat.ceil (logWidth (collarExponent k) N*(N:ℝ)):ℝ)) =
      (rankMultiplicity R:ℝ)*(Nat.ceil (logWidth (collarExponent k) N*(N:ℝ)):ℝ) := by
    rw [←Finset.sum_mul]
    simp only [rankMultiplicity,Nat.cast_sum,Nat.cast_pow]
  rw [Finset.sum_add_distrib,hcost] at hsum
  have hpaid := hT N hN b.1 b.2.1 b.2.2 hb
  exact hsum.trans (add_le_add_left hpaid _)

/-- Apply the new paid cap to the already-established original count
dictionary. The only hypotheses are the original source range and epsilon. -/
theorem uniform_original_with_product_inner_cut (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ R T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 →
        wuOmega3Sum N δ 3 (16/5) (convolutionWuWindows N b.2.1 b.2.2) ≤
          (∑ r ∈ Finset.range (R+1),
            p5z_labelledPrimeMass (indexedFamily k δ r N b) Part3.labelledProduct
              (innerWeight (collarExponent k) N) N) +
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2) := by
  obtain ⟨R,T1,hT14,hT1⟩ := uniform_original_count_dictionary k hδ hδhi (half_pos hε)
  obtain ⟨T2,_hT24,hT2⟩ := uniform_indexed_inner_cut_loss k R hδ hδhi (half_pos hε)
  refine ⟨R,max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he b hb
  have h1 := hT1 N ((le_max_left T1 T2).trans hN) he b hb
  have h2 := hT2 N ((le_max_right T1 T2).trans hN) b hb
  nlinarith only [h1,h2]

end
end ImbalancedChen.P2WuProductInnerThetaPayment
