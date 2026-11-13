import ImbalancedChen.Part3OriginalRegularHolomorphicWeight
import ImbalancedChen.Part3OriginalRegularBaseCumulative

/-! Complete original holomorphic ONB sum on every unbounded cutoff in
two genuine scale ranges. The same result covers the bounded base for
all lengths. The unrestricted all-length/all-height sieve is not asserted. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularHolomorphicCumulative20261113
open Set MeasureTheory Complex Matrix
open scoped MatrixGroups UpperHalfPlane BigOperators InnerProductSpace
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalPeterssonPretrace20261112 ActualContinuousPoincarePairing20261110
open OriginalRegularPacketTest20261113 (Dyadic energy energy_nonneg)
open OriginalRegularHolomorphicWeight20261113
open OriginalRegularBaseCumulative20261113

def functional (z j : ℕ) [NeZero z] (one : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (f : Forms z (j+1)) : ℂ :=
  ∑ n∈S,a n*frameR z (NeZero.pos z) (j+1) f (originalFrame one) n

abbrev WeightBasis (z j : ℕ) [NeZero z] := OrthonormalBasis (BasisIndex z (j+1)) ℂ (Forms z (j+1))

def shell (z j : ℕ) [NeZero z] (one : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (basis : WeightBasis z j) : ℝ :=
  Real.Gamma (2*(j:ℝ)+2)*∑ i,‖functional z j one S a (basis i)‖^2

/-- Every member of the orthonormal basis is present; taking the finite
coefficient functional's own Riesz vector avoids a dimension factor. -/
theorem shell_bound (z j : ℕ) [NeZero z] (one : Bool) {L : ℝ} (hL : 0<L)
    (S : Finset ℕ) (a : ℕ→ℂ) (band : Dyadic L S) (basis : WeightBasis z j) :
    shell z j one S a basis ≤ fixedBill z j L*energy S a := by
  let g := originalFrame one
  let F := functional z j one S a
  let v : Forms z (j+1) := ∑ n∈S,star (a n) • Rvector z (j+1) g n
  let G := Real.Gamma (2*(j:ℝ)+2)
  let B := fixedBill z j L
  have gp : 0≤G := (Real.Gamma_pos_of_pos (by positivity)).le
  have bp : 0≤B := by
    have := Real.log_pos (by norm_num : (1:ℝ)<3/2)
    dsimp [B,fixedBill]; positivity
  have eval (f : Forms z (j+1)) : inner ℂ v f=F f := by
    rw [show v=∑ n∈S,star (a n) • Rvector z (j+1) g n from rfl,sum_inner]
    apply Finset.sum_congr rfl
    intro n _
    rw [inner_smul_left]
    change star (star (a n))*inner ℂ (Rvector z (j+1) g n) f=_
    rw [star_star,Rvector_evaluates]
  have normB : G*‖v‖^2≤B*energy S a := by
    by_cases hv : v=0
    · simpa [hv] using mul_nonneg bp (energy_nonneg S a)
    · let R := fun n => frameR z (NeZero.pos z) (j+1) v g n
      have ce : ‖F v‖^2≤energy S a*(∑ n∈S,‖R n‖^2) := by
        have n1 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S (fun n => a n*R n)) 2
        simp only [norm_mul] at n1
        exact n1.trans (Finset.sum_mul_sq_le_sq_mul_sq S (fun n => ‖a n‖) (fun n => ‖R n‖))
      have normE : ‖F v‖=‖v‖^2 := by
        rw [←eval,inner_self_eq_norm_sq_to_K,←Complex.ofReal_pow,Complex.norm_real,
          Real.norm_of_nonneg (sq_nonneg _)]
      have P := mul_le_mul_of_nonneg_left ce gp
      have Q := mul_le_mul_of_nonneg_left (restriction z j one hL S band v) (energy_nonneg S a)
      rw [normE] at P
      apply le_of_mul_le_mul_right _ (sq_pos_of_pos (norm_pos_iff.mpr hv))
      nlinarith only [P,Q]
  have hB := basis.orthonormal.sum_inner_products_le (s:=Finset.univ) v
  apply (mul_le_mul_of_nonneg_left _ gp).trans normB
  apply le_trans _ hB
  apply Finset.sum_le_sum
  intro i _
  exact le_of_eq (congrArg (fun x : ℝ => x^2)
    ((congrArg norm (eval (basis i)).symm).trans (norm_inner_symm (𝕜:=ℂ) _ _)))

/-- j indexes the even weight k=2j+2; its height is exactly k−1. -/
def weights (K : ℝ) : Finset ℕ :=
  (Finset.range ⌊K⌋₊).filter (fun j => (order j:ℝ)≤K)

theorem mem_weights {j : ℕ} {K : ℝ} : j∈weights K ↔ (order j:ℝ)≤K := by
  refine ⟨fun hj => (Finset.mem_filter.mp hj).2,fun hj => Finset.mem_filter.mpr ⟨?_,hj⟩⟩
  apply Finset.mem_range.mpr
  have kn : order j≤⌊K⌋₊ := Nat.le_floor hj
  dsimp [order] at kn
  omega

private def C₀ : ℝ := (2+32*Real.pi/Real.log (3/2))/Real.pi
private theorem cpos : 0<C₀ := by
  have := Real.log_pos (by norm_num : (1:ℝ)<3/2)
  dsimp [C₀]; positivity

private theorem price (z : ℕ) [NeZero z] {j : ℕ} {K L : ℝ} (sK : (order j:ℝ)≤K)
    (hK : 0≤K) (hL : 0≤L) : fixedBill z j L≤C₀*(K+L/(z:ℝ)) := by
  let l := L/(z:ℝ)
  let c := 32*Real.pi/Real.log (3/2)
  have lp : 0≤l := div_nonneg hL (Nat.cast_nonneg _)
  have cp : 0≤c := div_nonneg (by positivity) (Real.log_pos (by norm_num : (1:ℝ)<3/2)).le
  have E : fixedBill z j L=((order j:ℝ)*2+c*l)/Real.pi := by dsimp [fixedBill,c,l];ring
  rw [E,show C₀=(2+c)/Real.pi from rfl]
  rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right Real.pi_pos]
  nlinarith only [sK,lp,mul_nonneg cp hK]

/-- Exact original cost, uniformly in all parameters and arbitrarily high K.
The supported ranges are separate ways to pay the single fixed-weight
length cost when all weights are added: L/z≤K, K≤L^ε, or K≤2. -/
theorem manuscript_holomorphic (ε : ℝ) (he : 0<ε) : ∃ C : ℝ,0<C ∧
    ∀ (z : ℕ) [NeZero z] (one : Bool) {K L : ℝ},1≤K → 1/2≤L →
    (L/(z:ℝ)≤K ∨ K≤L^ε ∨ K≤2) →
    ∀ (S : Finset ℕ) (a : ℕ→ℂ),Dyadic L S → ∀ (bases : ∀ j,WeightBasis z j),
      (∑ j∈weights K,shell z j one S a (bases j)) ≤ C*(K^2+L^(1+ε)/(z:ℝ))*energy S a := by
  refine ⟨4*C₀,mul_pos (by norm_num) cpos,?_⟩
  intro z inst one K L hK lh regime S a band bases
  have lp : 0<L := by linarith
  have kp : 0<K := zero_lt_one.trans_le hK
  have zp : 0<(z:ℝ) := by exact_mod_cast NeZero.pos z
  have z1 : (1:ℝ)≤z := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos z)
  let l := L/(z:ℝ)
  let b := L^(1+ε)/(z:ℝ)
  let e := energy S a
  have en : 0≤e := energy_nonneg S a
  have bn : 0≤b := div_nonneg (Real.rpow_nonneg lp.le _) zp.le
  have ln : 0≤l := div_nonneg lp.le zp.le
  have gm : K*l≤3*(K^2+b) := by
    rcases regime with s|s|s
    · nlinarith only [mul_le_mul_of_nonneg_left s kp.le,bn,sq_nonneg K]
    · have eL : L^ε*l=b := by dsimp [b,l];rw [Real.rpow_add lp,Real.rpow_one];ring
      nlinarith only [mul_le_mul_of_nonneg_right s ln,eL,bn,sq_nonneg K]
    · by_cases u : 1≤L
      · have p : l≤b := div_le_div_of_nonneg_right
          (Real.self_le_rpow_of_one_le u (by linarith : 1≤1+ε)) zp.le
        nlinarith only [mul_le_mul_of_nonneg_right s ln,p,bn,sq_nonneg K]
      · have p : l≤1 := (div_le_one zp).mpr ((le_of_not_ge u).trans z1)
        nlinarith only [mul_le_mul_of_nonneg_left p kp.le,hK,sq_nonneg (K-1),bn]
  have count : ((weights K).card:ℝ)≤K := by
    apply le_trans _ (Nat.floor_le kp.le)
    exact_mod_cast (show (weights K).card≤⌊K⌋₊ by
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _))
  have B : 0≤C₀*(K+l)*e := mul_nonneg (mul_nonneg cpos.le (add_nonneg kp.le ln)) en
  calc
    _ ≤ ∑ _j∈weights K,C₀*(K+l)*e := Finset.sum_le_sum (fun j hj =>
      (shell_bound z j one lp S a band (bases j)).trans
        (mul_le_mul_of_nonneg_right (price z (mem_weights.mp hj) kp.le lp.le) en))
    _ = ((weights K).card:ℝ)*(C₀*(K+l)*e) := by simp [nsmul_eq_mul]
    _ ≤ K*(C₀*(K+l)*e) := mul_le_mul_of_nonneg_right count B
    _ = C₀*(K^2+K*l)*e := by ring
    _ ≤ C₀*(4*(K^2+b))*e := by
      apply mul_le_mul_of_nonneg_right _ en
      apply mul_le_mul_of_nonneg_left _ cpos.le
      nlinarith only [gm,bn]
    _ = _ := by dsimp [b,e]; ring

/-- The initial cumulative interval uses one constant for the three
original measures. Opposite signs in the Maass coefficients are allowed;
the holomorphic sum is the original positive-frequency branch. -/
theorem manuscript_base_three (ε : ℝ) (he : 0<ε) : ∃ C : ℝ,0<C ∧
    ∀ (z : ℕ) [NeZero z] (one neg : Bool) {K L : ℝ},1≤K → K≤2 → 1/2≤L →
    ∀ (S : Finset ℕ) (a : ℕ→ℂ),Dyadic L S → ∀ (bases : ∀ j,WeightBasis z j),
      let B := C*(K^2+L^(1+ε)/(z:ℝ))*energy S a
      Summable (baseTerm z one neg K S a) ∧ (∑' i,baseTerm z one neg K S a i)≤B ∧
      IntegrableOn (lineTerm z one neg S a) (Icc (-K) K) ∧ (∫ t in Icc (-K) K,lineTerm z one neg S a t)≤B ∧
      (∑ j∈weights K,shell z j one S a (bases j))≤B := by
  obtain ⟨C,hC,A⟩ := manuscript_base ε he
  obtain ⟨D,hD,H⟩ := manuscript_holomorphic ε he
  refine ⟨max C D,hC.trans_le (le_max_left _ _),?_⟩
  intro z _ one neg K L k₁ k₂ l₁ S a span bases
  obtain ⟨sm,ds,im,cs⟩ := A z one neg k₁ k₂ l₁ S a span
  have hs := H z one k₁ l₁ (Or.inr (Or.inr k₂)) S a span bases
  have lp : 0≤L := by linarith
  have p : 0≤K^2+L^(1+ε)/(z:ℝ) := by positivity
  have lift (c : ℝ) (q : c≤max C D) : c*(K^2+L^(1+ε)/(z:ℝ))*energy S a≤
      max C D*(K^2+L^(1+ε)/(z:ℝ))*energy S a :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right q p) (energy_nonneg S a)
  exact ⟨sm,ds.trans (lift C (le_max_left _ _)),im,cs.trans (lift C (le_max_left _ _)),
    hs.trans (lift D (le_max_right _ _))⟩

end ImbalancedChen.Part3.OriginalRegularHolomorphicCumulative20261113
end
