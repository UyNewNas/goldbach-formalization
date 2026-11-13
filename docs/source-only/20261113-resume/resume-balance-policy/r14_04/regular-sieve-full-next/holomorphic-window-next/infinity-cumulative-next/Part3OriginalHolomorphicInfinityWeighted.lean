import ImbalancedChen.Part3OriginalHolomorphicInfinityGram

/-! The corrected all-height positive Petersson spectrum and both sums
of the already estimated same-observation double series. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicInfinityWeighted20261113
open Finset Real
open scoped ComplexConjugate
open OriginalHolomorphicInfinityGram20261113
open OriginalRegularHolomorphicCumulative20261113 (WeightBasis)
open OriginalHolomorphicOddWindow20261113 (weight weight_nonnegative)
open OriginalHolomorphicPoissonHeight20261113 (oddDiagonal corrected_diagonal_bound)
open OriginalHolomorphicPhysicalCosine20261113 (argument scale form)
open OriginalHolomorphicInfinityProgression20261113 (progressionEntry progressionEntry_eq)
open OriginalHolomorphicBesselOffDiagonal20261113 (nativeTerm geometricTerm native_bessel_off_diagonal)
open OriginalHolomorphicHeightModulusFubini20261113 (matrixEntry original_height_modulus_fubini)
open OriginalAllParameterKloosterman20261113 (dyadEnergy)
open OriginalHolomorphicShortOscillation20261113 (rowProduct)
open OriginalHolomorphicAngularOffDiagonal20261113 (cost)

def spectralTerm (z M : ℕ) [NeZero z] (t : ℝ) (a : ℕ → ℂ) (bases : ∀ j,WeightBasis z j) (h : ℕ) : ℝ :=
  if Odd h then weight t h*naturalShell z M (h/2) a (bases (h/2)) else 0

theorem spectralTerm_nonnegative (z M : ℕ) [NeZero z] {t : ℝ} (ht1 : t≤1)
    (a : ℕ → ℂ) (bases : ∀ j,WeightBasis z j) (h : ℕ) : 0≤spectralTerm z M t a bases h := by
  by_cases odd : Odd h
  · have hn : 1≤h := by obtain ⟨v,hv⟩ := odd; omega
    rw [spectralTerm,if_pos odd]
    exact mul_nonneg (weight_nonnegative ht1 hn) (shell_nonnegative z M (h/2) a _)
  · simp [spectralTerm,odd]

private theorem weighted_orbit (z M j h l : ℕ) (hj : 2*j+1=h) (oh : Odd h)
    (t : ℝ) (a : ℕ → ℂ) :
    (π:ℂ)*matrixEntry M z t (fun m => conj (a m)) a h l =
      (((h:ℝ)*weight t h:ℝ):ℂ)*packet M a (fun m n => progressionEntry z j m n l) := by
  let c := z*(l+1)
  have ph : (-Complex.I)^(2*(j+1))=Complex.I^(h+1) := by
    rw [pow_mul,neg_sq,←pow_mul,show 2*(j+1)=h+1 by omega]
  have arg (m n : ℕ) : OriginalPeterssonLipschitz20261112.argument (sqrt m) (sqrt n) c=
      argument c m n := by dsimp only [OriginalPeterssonLipschitz20261112.argument,argument,scale]; ring
  simp only [matrixEntry,form,packet,progressionEntry_eq]
  simp only [sum_div,mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro k _
  simp only [hj,ph,nativeTerm,if_pos oh,show z*(l+1)=c from rfl,arg]
  push_cast <;> ring

theorem weighted_height {z M : ℕ} [NeZero z] (hM : 0<M) (t : ℝ)
    (a : ℕ → ℂ) (bases : ∀ j,WeightBasis z j) (h : ℕ) :
    ((4*π*spectralTerm z M t a bases h:ℝ):ℂ) =
      ((oddDiagonal t h*dyadEnergy M a:ℝ):ℂ)+
        (π:ℂ)*∑' l,matrixEntry M z t (fun m => conj (a m)) a h l := by
  by_cases oh : Odd h
  · let j := h/2
    have hj : 2*j+1=h := by
      obtain ⟨k,hk⟩ := oh
      dsimp only [j]
      omega
    have jr : 2*(j:ℝ)+1=(h:ℝ) := by exact_mod_cast hj
    have ga : Gamma (2*(j:ℝ)+2)=(h:ℝ)*Gamma (2*(j:ℝ)+1) := by
      rw [show 2*(j:ℝ)+2=(2*(j:ℝ)+1)+1 by ring,Gamma_add_one (by positivity : 2*(j:ℝ)+1≠0),jr]
    let d := (h:ℝ)*weight t h
    have T := (packed_trace (z:=z) hM j a).mul_left (d:ℂ)
    have Q := (T.congr_fun (fun l => weighted_orbit z M j h l hj oh t a)).tsum_eq
    rw [tsum_mul_left,packet_spectrum z M j a (bases j)] at Q
    simp only [spectralTerm,if_pos oh,oddDiagonal,naturalShell,show h/2=j from rfl,ga]
    dsimp only [d] at Q
    push_cast at Q ⊢
    linear_combination -Q
  · simp [spectralTerm,oddDiagonal,oh,matrixEntry,form,nativeTerm]

private theorem energy_nonnegative (M : ℕ) (a : ℕ → ℂ) : 0≤dyadEnergy M a :=
  sum_nonneg fun _ _ => sq_nonneg _

private theorem row_self (M : ℕ) (a : ℕ → ℂ) :
    rowProduct M (fun n => conj (a n)) a = dyadEnergy M a := by
  have D : dyadEnergy M (fun n => conj (a n))=dyadEnergy M a := by simp [dyadEnergy]
  rw [rowProduct,D,←sq,sq_sqrt (energy_nonnegative M a)]

/-- Exact positive all-height normalization and the uniform unrestricted
dyadic estimate, for every original Petersson ONB. -/
theorem weighted_infinity_bound {e : ℝ} (he : 0<e) {K : ℝ} (hK : 1≤K)
    (z M : ℕ) [NeZero z] (hM : 0<M) (a : ℕ → ℂ) (bases : ∀ j,WeightBasis z j) :
    Summable (fun h => 4*π*spectralTerm z M (1/K) a bases h) ∧
      (∑' h,4*π*spectralTerm z M (1/K) a bases h) ≤
        (4*K^2+2*cost e*((M:ℝ)^(1+e)/z))*dyadEnergy M a := by
  let t := 1/K
  let b := fun m => conj (a m)
  let F := fun h => ∑' l,matrixEntry M z t b a h l
  have kp := zero_lt_one.trans_le hK
  have tp : 0<t := one_div_pos.mpr kp
  have t1 : t≤1 := (div_le_one kp).mpr hK
  obtain ⟨D,dmax⟩ := corrected_diagonal_bound hK
  obtain ⟨A,swap⟩ := original_height_modulus_fubini hM (NeZero.pos z) tp t1 b a
  obtain ⟨G,gmax⟩ := native_bessel_off_diagonal he M z hM (NeZero.pos z) tp t1 b a
  have S : Summable F := A.of_norm.prod
  have Q := ((D.hasSum.mul_right (dyadEnergy M a)).add
    ((Complex.reCLM.hasSum S.hasSum).mul_left π))
  have terms (h : ℕ) : 4*π*spectralTerm z M t a bases h =
      oddDiagonal t h*dyadEnergy M a+π*(F h).re := by
    have eq := congrArg Complex.re (weighted_height hM t a bases h)
    simpa only [Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,zero_mul,sub_zero,
      Complex.add_re,F,b] using eq
  have E := (Q.congr_fun terms)
  refine ⟨E.summable,?_⟩
  rw [E.tsum_eq]
  have trade : (∑' h,F h)=∑' l,geometricTerm M z t b a l := swap
  rw [trade]
  have g := ((Complex.re_le_norm _).trans (norm_tsum_le_tsum_norm G)).trans gmax
  change _ ≤ ((2/π)*cost e)*((M:ℝ)^(1+e)/z)*rowProduct M (fun n => conj (a n)) a at g
  rw [row_self] at g
  have en := energy_nonnegative M a
  have V := add_le_add (mul_le_mul_of_nonneg_right dmax en) (mul_le_mul_of_nonneg_left g pi_pos.le)
  convert V using 1 <;> field_simp [pi_ne_zero] <;> ring

end ImbalancedChen.Part3.OriginalHolomorphicInfinityWeighted20261113
end
