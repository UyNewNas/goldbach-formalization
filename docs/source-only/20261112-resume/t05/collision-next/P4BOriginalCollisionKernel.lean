import ImbalancedChen.P4BOriginalCollisionTensor
import ImbalancedChen.P4BOriginalHighRankPostModulusCount

/-! The complete modulus remains in the congruence, central product, and
coprime mean.  Apply the original rough-square budget once, after joining
all coarse words and the original small factors. -/
namespace ImbalancedChen.P4BOriginalCollisionKernel
noncomputable section
open Classical Filter
open scoped BigOperators
open ImbalancedChen.PrimeProducts.MellinInsertion20261028 (residueKernel exactDiscrepancy functional)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (products free error bad difference error_bound error_support)
open P4AHeldTaggedCompilerSupport (J0)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots hbSlots_norm_le hb_fibre_card_le)
open P5Z.ActualCompleteModulusFourierTail (residueKernel_norm_le)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le scaleFactor scaleFactor_one_le)
open P5Z.RoughSquareWeightedBudget (rough_square_kernel_budget)
open P5Z.RoughSquarePowerPayment (eventually_presieve_kernel_power_payment)
open P5Z.ProperPowerPhysicalPolynomialPayment (tau_word_rank_subpower)

def bound (Y q : ℕ) := (Y:ℝ)/(q:ℝ)+1+(Y:ℝ)/(q.totient:ℝ)
theorem bound_nonneg (Y q : ℕ) : 0≤bound Y q := by unfold bound; positivity

/-- The +1 includes the complete product equal to the target. -/
theorem progression (Y N q : ℕ) (hq : 0<q) :
    (((Finset.Icc 1 Y).filter (fun x => Nat.ModEq q x N)).card:ℝ)≤(Y:ℝ)/(q:ℝ)+1 := by
  let R := (Finset.Icc 1 Y).filter (fun x => Nat.ModEq q x N)
  have hc : R.card≤Y/q+1 := by
    calc
      R.card≤(Finset.range (Y/q+1)).card := Finset.card_le_card_of_injOn (fun n : ℕ => n/q)
        (fun n hn => Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2)))
        (fun n hn m hm hh => by
          have ht : n%q=m%q := (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
          have hn' := Nat.mod_add_div n q
          have hm' := Nat.mod_add_div m q
          change n/q=m/q at hh
          rw [ht,hh] at hn'; exact hn'.symm.trans hm')
      _=_ := Finset.card_range _
  have hdiv : ((Y/q:ℕ):ℝ)≤(Y:ℝ)/(q:ℝ) := (le_div_iff₀ (Nat.cast_pos.mpr hq)).mpr
    (by exact_mod_cast Nat.div_mul_le_self Y q)
  exact (by exact_mod_cast hc : (R.card:ℝ)≤((Y/q:ℕ):ℝ)+1).trans (by linarith)

theorem kernel_sum (Y N q : ℕ) (hq : 0<q) :
    (∑ x∈Finset.Icc 1 Y,‖residueKernel q N x‖)≤bound Y q := by
  have term (x : ℕ) : ‖residueKernel q N x‖≤(if Nat.ModEq q x N then (1:ℝ) else 0)+1/(q.totient:ℝ) := by
    apply (residueKernel_norm_le q N x).trans
    apply add_le_add_left
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    split <;> norm_num
  apply (Finset.sum_le_sum (fun x _ => term x)).trans
  rw [Finset.sum_add_distrib,←Finset.sum_filter]
  have hcard : (Finset.Icc 1 Y).card=Y := by simp
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hcard]
  calc
    _=(((Finset.Icc 1 Y).filter (fun x => Nat.ModEq q x N)).card:ℝ)+(Y:ℝ)/(q.totient:ℝ) := by ring
    _≤_ := add_le_add_right (progression Y N q hq) ((Y:ℝ)/(q.totient:ℝ))

def row {ι : Type*} (I : Finset ι) (prod : ι→ℕ) (w : ι→ℂ) (N q : ℕ) :=
  ∑ y∈I,w y*residueKernel q N (prod y)

theorem reindex {ι : Type*} (I : Finset ι) (prod : ι→ℕ) (w : ι→ℂ) (N : ℕ) (S : Finset ℕ) (c : ℕ→ℝ) :
    exactDiscrepancy I S (fun q => (c q:ℂ)) prod N w=∑ q∈S,(c q:ℂ)*row I prod w N q := by
  unfold exactDiscrepancy functional row
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun y _ => by ring))

theorem complex_difference (P : Params) (hN : 1<P.N) (F : ℕ→ℂ) :
    (∑ t∈products P,(free P t:ℂ)*F t)-(∑ t∈P.S,(P.rho t:ℂ)*F t)=
      ∑ t∈products P,(error P t:ℂ)*F t := by
  apply Complex.ext
  · simpa only [Complex.sub_re,Complex.re_sum,Complex.re_ofReal_mul] using difference P hN (fun t => (F t).re)
  · simpa only [Complex.sub_im,Complex.im_sum,Complex.im_ofReal_mul] using difference P hN (fun t => (F t).im)

theorem row_bound {ι : Type*} (I : Finset ι) (prod : ι→ℕ) (w : ι→ℂ) (Y N q : ℕ) (hq : 0<q)
    (hp : ∀y∈I,prod y∈Finset.Icc 1 Y) {B : ℝ} (hB : 0≤B)
    (hm : ∀n∈Finset.Icc 1 Y,(∑ y∈I.filter (fun y => prod y=n),‖w y‖)≤B) :
    ‖row I prod w N q‖≤B*bound Y q := by
  apply (norm_sum_le _ _).trans
  simp_rw [norm_mul]
  rw [←Finset.sum_fiberwise_of_maps_to hp (fun y => ‖w y‖*‖residueKernel q N (prod y)‖)]
  apply le_trans _ (mul_le_mul_of_nonneg_left (kernel_sum Y N q hq) hB)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have H : (∑ y∈I.filter (fun y => prod y=n),‖w y‖*‖residueKernel q N (prod y)‖)=
      (∑ y∈I.filter (fun y => prod y=n),‖w y‖)*‖residueKernel q N n‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.mp hy).2])
  rw [H]; exact mul_le_mul_of_nonneg_right (hm n hn) (norm_nonneg _)

theorem full_difference (P : Params) (hN : 1<P.N) (he : 0≤P.e) (ho : 0<P.omega)
    (ht : P.ell+P.T*(J0 P.omega:ℝ)<1/1000) {ι : Type*} (I : Finset ι) (prod : ι→ℕ)
    (w : ι→ℂ) (Y : ℕ) (hp : ∀y∈I,prod y∈Finset.Icc 1 Y) {B : ℝ} (hB : 0≤B)
    (hm : ∀n∈Finset.Icc 1 Y,(∑ y∈I.filter (fun y => prod y=n),‖w y‖)≤B) :
    ‖exactDiscrepancy I (products P) (fun q => (free P q:ℂ)) prod P.N w-
      exactDiscrepancy I P.S (fun q => (P.rho q:ℂ)) prod P.N w‖≤
      ((J0 P.omega).factorial:ℝ)*B*∑ d∈bad P,bound Y d := by
  rw [reindex,reindex,complex_difference P hN (row I prod w P.N)]
  have hz (t : ℕ) (ht' : t∉bad P) : error P t=0 := by
    by_contra h; exact ht' (error_support P hN he ho ht h).1
  let A := (products P).filter (fun t => t∈bad P)
  have cut : (∑ t∈products P,(error P t:ℂ)*row I prod w P.N t)=
      ∑ t∈A,(error P t:ℂ)*row I prod w P.N t := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t ht1 ht2
    have hn : t∉bad P := fun hh => ht2 (Finset.mem_filter.mpr ⟨ht1,hh⟩)
    simp [hz t hn]
  rw [cut]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (show A⊆bad P from fun q h => (Finset.mem_filter.mp h).2)
    (fun q _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (bound_nonneg Y q)))
  apply Finset.sum_le_sum
  intro t ht'
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
  exact mul_le_mul (error_bound P hN he ho t)
    (row_bound I prod w Y P.N t (mem_roughSquareExceptions.mp (Finset.mem_filter.mp ht').2).1 hp hB hm)
    (norm_nonneg _) (Nat.cast_nonneg _)

def Y (N : ℕ) := Nat.floor (6*countingScale N)

theorem kernel_power (omega eps : ℝ) (ho : 0<omega) (hep : 0<eps) :
    ∀ᶠ N : ℕ in atTop,∀ P : Params,P.N=N → P.omega=omega →
    (∑ d∈bad P,bound (Y N) d)≤(2*(1+6*scaleFactor))*(N:ℝ)*(N:ℝ)^(eps-omega) := by
  filter_upwards [eventually_presieve_kernel_power_payment (599/1000) omega eps (by norm_num) ho hep] with N H
  intro P hN ho'
  have hN2 := H.1
  have hn : (1:ℝ)<N := by exact_mod_cast (by omega : 1<N)
  let D := Nat.floor ((N:ℝ)^(599/1000:ℝ))
  have hd : (D:ℝ)≤(N:ℝ)^(599/1000:ℝ) := Nat.floor_le (by positivity)
  have hdN := hd.trans (show (N:ℝ)^(599/1000:ℝ)≤N by simpa using
    Real.rpow_le_rpow_of_exponent_le hn.le (show (599/1000:ℝ)≤1 by norm_num))
  have hY0 : (Y N:ℝ)≤6*countingScale N := Nat.floor_le (by dsimp [countingScale,scaleFactor]; positivity)
  have hY : (Y N:ℝ)≤6*scaleFactor*N := by simpa only [countingScale,mul_assoc] using hY0
  have hK := rough_square_kernel_budget D (Real.one_lt_rpow hn ho) (Nat.cast_nonneg (Y N))
  have hP := H.2 D (Y N) hd (Nat.cast_nonneg _)
  change (∑ d∈roughSquareExceptions (Nat.floor ((P.N:ℝ)^(599/1000:ℝ))) ((P.N:ℝ)^P.omega),
    (Y N:ℝ)/(d:ℝ)+1+(Y N:ℝ)/(d.totient:ℝ))≤_
  rw [hN,ho']
  apply (hK.trans hP).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  linarith only [hdN,hY]

end
end ImbalancedChen.P4BOriginalCollisionKernel
