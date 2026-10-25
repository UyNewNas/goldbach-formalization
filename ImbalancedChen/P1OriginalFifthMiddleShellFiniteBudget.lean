import ImbalancedChen.P1OriginalFifthMiddleShellBinMoment
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Complete finite summation of the original fifth middle-shell quadratic
moment. The shell lower endpoint delta may depend on N. Its occupied
reciprocal indices are the image of the ACTUAL original carrier, are paid
once each, and lie below a/delta. Thus the target-uniform interval error is
paid at most a/delta+1 times, without any residual-floor multiplicity.

The result is O(a+(a/delta+1)/log N), with the fixed first-three reciprocal
prime masses retained. In particular it does not take a fixed-delta prime
limit and then substitute a moving delta. The only scale condition is the
displayed physical endpoint N^(a/(a/delta+1)) >= 2.
-/

namespace ImbalancedChen.P1OriginalFifthMiddleShellFiniteBudget

noncomputable section
open scoped Classical BigOperators
open Finset
open P1OriginalCoarseFifthContinuation
open P1OriginalFifthMiddleShellBinMoment

def occupied (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (N cap : ℕ) (j : Label5 m) : Finset ℕ :=
  (shellCell e chi m omega delta a N cap j).image (owner a N)

def shellMoment (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (N cap : ℕ) (j : Label5 m) : ℝ :=
  ∑ p ∈ shellCell e chi m omega delta a N cap j,
    (∏ i,1/((p i:ℝ)-1))*(actualPrimeTupleLog N p 4)^2

/-- Every original tuple has exactly one natural reciprocal owner. -/
theorem shellMoment_eq_occupied_bin_sum
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (N cap : ℕ) (j : Label5 m) :
    shellMoment e chi m omega delta a N cap j =
      ∑ r ∈ occupied e chi m omega delta a N cap j,
        quadraticMoment e chi m omega delta a N cap j r := by
  let S := shellCell e chi m omega delta a N cap j
  let R := occupied e chi m omega delta a N cap j
  have hcover : S = R.biUnion (fun r => S.filter (fun p => owner a N p=r)) := by
    ext p
    constructor
    · intro hp
      exact mem_biUnion.mpr ⟨owner a N p,mem_image.mpr ⟨p,hp,rfl⟩,
        mem_filter.mpr ⟨hp,rfl⟩⟩
    · intro hp
      obtain ⟨r,_,hp⟩ := mem_biUnion.mp hp
      exact (mem_filter.mp hp).1
  unfold shellMoment quadraticMoment shellBin
  change (∑ p ∈ S,_) = ∑ r ∈ R,∑ p ∈ S.filter (fun p => owner a N p=r),_
  calc
    _ = ∑ p ∈ R.biUnion (fun r => S.filter (fun p => owner a N p=r)),
        (∏ i,1/((p i:ℝ)-1))*(actualPrimeTupleLog N p 4)^2 :=
      congrArg (fun T : Finset Tuple => ∑ p∈T,
        (∏ i,1/((p i:ℝ)-1))*(actualPrimeTupleLog N p 4)^2) hcover
    _ = _ := by
      apply Finset.sum_biUnion
      intro r _ s _ hrs
      rw [Finset.disjoint_left]
      intro p hpr hps
      exact hrs ((mem_filter.mp hpr).2.symm.trans (mem_filter.mp hps).2)

/-- The actual finite owner set has a target-independent upper bound
a/delta; delta is not required to be fixed across targets. -/
theorem occupied_bounds
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (hd : 0<delta) (ha : 0<a) (J5 : Finset (Label5 m))
    (N cap : ℕ) (hN : 1<N) (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ))
    (j : Label5 m) (hj : j∈selectedFifthCells e chi m omega J5)
    (r : ℕ) (hr : r∈occupied e chi m omega delta a N cap j) :
    1≤r ∧ (r:ℝ)≤a/delta := by
  obtain ⟨p,hpS,how⟩ := mem_image.mp hr
  have hpbin : p∈shellBin e chi m omega delta a N cap j r :=
    mem_filter.mpr ⟨hpS,how⟩
  have hpbox := shellBin_subset_prime_box e chi m omega delta a ha
    J5 N cap hN hcap j hj r hpbin
  obtain ⟨_,hdelta,hta,_⟩ := mem_filter.mp hpS
  have ht : 0<actualPrimeTupleLog N p 4 := hd.trans_le hdelta
  have hcuts := owner_bounds a _ ht hta r how
  have hfloor : (r:ℝ)≤a/actualPrimeTupleLog N p 4 := by
    rw [← how]
    exact Nat.floor_le (div_nonneg ha.le ht.le)
  exact ⟨hcuts.1,hfloor.trans
    (div_le_div_of_nonneg_left ha.le hd hdelta)⟩

/-- One explicit scale inequality supplies every occupied physical lower
endpoint, including when the shell cutoff is chosen as a function of N. -/
theorem occupied_lower_endpoint
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ)
    (hd : 0<delta) (ha : 0<a) (J5 : Finset (Label5 m))
    (N cap : ℕ) (hN : 1<N) (hcap : (N:ℝ)^(19/96:ℝ)≤(cap:ℝ))
    (j : Label5 m) (hj : j∈selectedFifthCells e chi m omega J5)
    (hscale : 2≤(N:ℝ)^(a/(a/delta+1)))
    (r : ℕ) (hr : r∈occupied e chi m omega delta a N cap j) :
    2≤(N:ℝ)^(a/((r:ℝ)+1)) := by
  have hb := occupied_bounds e chi m omega delta a hd ha J5 N cap hN hcap j hj r hr
  have hrp : (0:ℝ)<(r:ℝ)+1 := by positivity
  have he : a/(a/delta+1)≤a/((r:ℝ)+1) :=
    div_le_div_of_nonneg_left ha.le hrp (by linarith [hb.2])
  exact hscale.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1≤N by omega)) he)

private theorem reciprocal_square_sum_le_two (B : ℕ) :
    (∑ r ∈ Icc 1 B,((r:ℝ)⁻¹)^2)≤2 := by
  by_cases hB : 1≤B
  · calc
      _ ≤ ∑ r ∈ Icc 1 B,2*((r:ℝ)⁻¹-((r:ℝ)+1)⁻¹) := by
        apply sum_le_sum
        intro r hr
        have hr1 : (1:ℝ)≤r := by exact_mod_cast (mem_Icc.mp hr).1
        have hr0 : (0:ℝ)<r := by linarith
        have hrp : (0:ℝ)<(r:ℝ)+1 := by linarith
        calc
          _ = 1/(r:ℝ)^2 := by simp only [one_div,inv_pow]
          _ ≤ 2/((r:ℝ)*((r:ℝ)+1)) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos hr0) (mul_pos hr0 hrp)).mpr
            nlinarith
          _ = _ := by field_simp; ring
      _ = 2*((1:ℝ)⁻¹-((B:ℝ)+1)⁻¹) := by
        rw [← mul_sum]
        congr 1
        have ht := sum_Icc_sub hB (fun r : ℕ => (r:ℝ)⁻¹)
        simp only [Nat.cast_add,Nat.cast_one] at ht
        have hneg : (∑ r∈Icc 1 B,(((r:ℝ)+1)⁻¹-(r:ℝ)⁻¹)) =
            -(∑ r∈Icc 1 B,((r:ℝ)⁻¹-((r:ℝ)+1)⁻¹)) := by
          rw [← sum_neg_distrib]
          apply sum_congr rfl
          intro r _
          ring
        linarith
      _ ≤ 2 := by
        have hb0 : 0≤((B:ℝ)+1)⁻¹ := inv_nonneg.mpr (by positivity)
        nlinarith
  · rw [Icc_eq_empty_of_lt (Nat.lt_of_not_ge hB),sum_empty]
    norm_num

/-- The finite moving-window arithmetic error is paid once per occupied
natural index. This bound makes its delta dependence explicit. -/
theorem finite_index_budget (R : Finset ℕ) (a delta K L : ℝ)
    (ha : 0≤a) (hd : 0<delta) (hK : 0≤K) (hL : 0<L)
    (hR : ∀ r∈R,1≤r ∧ (r:ℝ)≤a/delta) :
    (∑ r∈R,2*a/(r:ℝ)^2+6*K/L) ≤
      4*a+(a/delta+1)*(6*K/L) := by
  have hT : 0≤a/delta := div_nonneg ha hd.le
  have hsub : R⊆Icc 1 (Nat.floor (a/delta)) := by
    intro r hr
    exact mem_Icc.mpr ⟨(hR r hr).1,(Nat.le_floor_iff hT).mpr (hR r hr).2⟩
  have hsquares : (∑ r∈R,((r:ℝ)⁻¹)^2)≤2 :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
      (reciprocal_square_sum_le_two _)
  have hcardN : R.card≤Nat.floor (a/delta)+1 := by
    have hs : R⊆range (Nat.floor (a/delta)+1) := by
      intro r hr
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp (hsub hr)).2)
    simpa only [card_range] using card_le_card hs
  have hcard : (R.card:ℝ)≤a/delta+1 := by
    have hh : (R.card:ℝ)≤(Nat.floor (a/delta):ℝ)+1 := by exact_mod_cast hcardN
    exact hh.trans (add_le_add_right (Nat.floor_le hT) 1)
  calc
    _ = 2*a*(∑ r∈R,((r:ℝ)⁻¹)^2)+(R.card:ℝ)*(6*K/L) := by
      simp only [div_eq_mul_inv,inv_pow,sum_add_distrib,← mul_sum,
        sum_const,nsmul_eq_mul]
    _ ≤ 4*a+(a/delta+1)*(6*K/L) := by
      have hm := mul_le_mul_of_nonneg_left hsquares (by positivity : 0≤2*a)
      have he := mul_le_mul_of_nonneg_right hcard (by positivity : 0≤6*K/L)
      nlinarith

/-- An unconditional quantitative actual-carrier shell moment. K is
selected before every moving cutoff and target; only physical scale and
geometry conditions occur in the inputs. -/
theorem exists_uniform_original_middle_shell_moment_bound :
    ∃ K : ℝ,1<K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega delta a : ℝ),
      0<delta → 0<a → a≤(19/96:ℝ) →
      ∀ (J5 : Finset (Label5 m)) (N cap : ℕ),1<N → Even N →
      (N:ℝ)^(19/96:ℝ)≤(cap:ℝ) → ∀ (j : Label5 m),
      j∈selectedFifthCells e chi m omega J5 →
      2≤(N:ℝ)^(a/(a/delta+1)) →
      shellMoment e chi m omega delta a N cap j ≤
        (actualPrimeReciprocalMass N omega (19/96:ℝ))^3 *
          (2*((19/96:ℝ)*(1+K/Real.log 2))) *
          (4*a+(a/delta+1)*(6*K/Real.log (N:ℝ))) := by
  obtain ⟨K,hK,hbin⟩ := exists_uniform_original_shell_quadratic_bin_bound
  refine ⟨K,hK,?_⟩
  intro e chi m omega delta a hd ha haRho J5 N cap hN hEven hcap j hj hscale
  let R := occupied e chi m omega delta a N cap j
  let C := (actualPrimeReciprocalMass N omega (19/96:ℝ))^3 *
    (2*((19/96:ℝ)*(1+K/Real.log 2)))
  have hM : 0≤actualPrimeReciprocalMass N omega (19/96:ℝ) := by
    unfold actualPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    have hp1 : (1:ℝ)<p := by exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
    positivity
  have hC : 0≤C := by
    have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
    have hK0 : 0≤K := by linarith
    dsimp [C]
    positivity
  have hlogN : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hbounds : ∀ r∈R,1≤r ∧ (r:ℝ)≤a/delta :=
    occupied_bounds e chi m omega delta a hd ha J5 N cap hN hcap j hj
  rw [shellMoment_eq_occupied_bin_sum]
  calc
    _ ≤ ∑ r∈R,C*(2*a/(r:ℝ)^2+6*K/Real.log (N:ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hbin e chi m omega delta a ha haRho J5 N cap hN hEven hcap j hj r
        (hbounds r hr).1
        (occupied_lower_endpoint e chi m omega delta a hd ha J5
          N cap hN hcap j hj hscale r hr)
    _ = C*(∑ r∈R,2*a/(r:ℝ)^2+6*K/Real.log (N:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (finite_index_budget R a delta K (Real.log (N:ℝ)) ha.le hd (by linarith)
        hlogN hbounds) hC

end
end ImbalancedChen.P1OriginalFifthMiddleShellFiniteBudget
