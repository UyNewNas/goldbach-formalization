import ImbalancedChen.P4BOriginalRankTwoPrimeMesh
import ImbalancedChen.P2GammaPrimeLocalConductorSaving
import ImbalancedChen.P2GammaRetainedActualNorms

/-! The existing full prime-local conductor theorem for the two actual
complementary rows: frozen physical values and nonnegative variations. -/
namespace ImbalancedChen.P4BOriginalRankTwoSampleConductor
noncomputable section
open Classical Filter Set MeasureTheory
open scoped BigOperators
open P4BOriginalRankTwoPrimeMesh (primes)
open P4BOriginalRankTwoPositiveRestoration (discrepancy separated)
open P4BOriginalPairFibreDictionary (kernel)
open P2GammaVariablePrimeProfile P2GammaPrimeTargetDeletion P2GammaPrimeCharacterSW
open P2GammaSmallConductorIntervalBridge P2GammaConvolutionLargeConductor
open P2GammaRetainedActualNorms (paddedRow_energy)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev head := targetDeleted 1 (profilePrimeCoefficient (fun _ => (1:ℂ)))

theorem head_value (p : ℕ) : head p=if p.Prime then 1 else 0 := by
  by_cases hp : p.Prime <;> simp [head,targetDeleted,profilePrimeCoefficient,primeSWBeta,hp]

theorem rectangle_eq (l h N d : ℕ) (T : Finset ℕ) (g : ℕ → ℝ) :
    naturalRectangleDiscrepancy (primeSWInterval (l:ℝ) (h:ℝ)) T head (fun t => (g t:ℂ)) N d=
      ((∑ p∈primes l h,∑ t∈T,g t*kernel N d (p*t):ℝ):ℂ) := by
  simp only [naturalRectangleDiscrepancy,primeSWInterval,Nat.floor_natCast,primes,Finset.sum_filter,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · simp only [head_value,if_pos hp,one_mul,Complex.ofReal_sum,Complex.ofReal_mul,
      P2OriginalGammaUpperLowRankConsumer.gammaKernel,kernel]
  · simp [head_value,hp]

private theorem costs (T : Finset ℕ) (g : ℕ → ℂ) (V : ℕ)
    (hT : T⊆Finset.Icc 1 (2*V)) (hg : ∀ t∈T,‖g t‖≤5) :
    rowMass T g≤10*(V:ℝ) ∧ rowEnergy (paddedRow T g) 0 (2*V)≤50*(V:ℝ) := by
  have hh : T.card≤2*V := by simpa using Finset.card_le_card hT
  have hcard : (T.card:ℝ)≤2*(V:ℝ) := by exact_mod_cast hh
  constructor
  · calc
      _ ≤ ∑ _t∈T,(5:ℝ) := Finset.sum_le_sum hg
      _ = (T.card:ℝ)*5 := by simp
      _ ≤ _ := by linarith
  · rw [paddedRow_energy _ _ _ hT]
    calc
      _ ≤ ∑ _t∈T,(5:ℝ)^2 := Finset.sum_le_sum (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hg t ht) 2)
      _ = (T.card:ℝ)*25 := by norm_num [nsmul_eq_mul]
      _ ≤ _ := by linarith

/-- One threshold precedes endpoints, the actual signed weights, arbitrary
bounded companion weights, all inverse targets, and the complete moduli.
There is no lower bound on the clipped head interval's length. -/
theorem exists_bound (D : ℕ) : ∃ K : ℝ,0<K ∧ ∃ x0 : ℝ,1<x0 ∧
    ∀ N P V l h : ℕ,∀ (S T : Finset ℕ) (c g : ℕ → ℝ),
      let x := (P:ℝ)*(V:ℝ)
      x0≤x → x^(1/10:ℝ)≤P → x^(1/10:ℝ)≤V → P≤l → l≤h → h≤2*P →
      T⊆Finset.Icc 1 (2*V) → (∀ t∈T,|g t|≤5) →
      (∀ d∈S,0<d ∧ (d:ℝ)≤x^(9/20:ℝ) ∧ N.Coprime d ∧ |c d|≤1) →
      |separated N S c (primes l h) T g|≤K*x/(Real.log x)^D := by
  obtain ⟨K,hK,x0,hx0,H⟩ := P2GammaPrimeLocalConductorSaving.exists_actual_prime_local_conductor_saving
    (D:ℝ) 0 0 (1/10) (1/20) 0 1 0 2 8 2 10 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨K,hK,x0,hx0,?_⟩
  intro N P V l h S T c g
  dsimp only
  intro hx hP hV hl hlh hhi hT hg hS
  let x := (P:ℝ)*(V:ℝ)
  let Q := Nat.floor (x^(9/20:ℝ))
  let I := primeSWInterval (l:ℝ) (h:ℝ)
  let beta := fun t => (g t:ℂ)
  have hI : I⊆Finset.Icc 1 (2*P) := by
    intro p hp
    simp only [I,primeSWInterval,Nat.floor_natCast,Finset.mem_Ioc] at hp
    exact Finset.mem_Icc.mpr ⟨by omega,hp.2.trans hhi⟩
  have hcard : I.card≤2*P := by simpa using Finset.card_le_card hI
  have hcardR : (I.card:ℝ)≤2*(P:ℝ) := by exact_mod_cast hcard
  have hhead : rowEnergy (paddedRow I head) 0 (2*P)≤2*(P:ℝ) := by
    rw [paddedRow_energy _ _ _ hI]
    calc
      _ ≤ ∑ _p∈I,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        by_cases hp : p.Prime <;> simp [head_value,hp]
      _ ≤ _ := by simpa using hcardR
  obtain ⟨hlone,hlen⟩ := costs T beta V hT (fun t ht => by
    simpa only [beta,Complex.norm_real,Real.norm_eq_abs] using hg t ht)
  have hq : (Q:ℝ)≤x^(1/2-1/20:ℝ) := by
    rw [show (1/2-1/20:ℝ)=9/20 by norm_num]
    exact Nat.floor_le (Real.rpow_nonneg (by dsimp [x]; positivity) _)
  have Hrect := H x (P:ℝ) (V:ℝ) (l:ℝ) (h:ℝ) hx rfl hP hV (by exact_mod_cast hl)
    (by exact_mod_cast hlh) (by exact_mod_cast hhi) (fun _ => (1:ℂ)) (fun _ _ => differentiableAt_const _)
    (by simp) (by simp [profileAbelNorm]) (by simp) 1 (by norm_num) (by simp)
    (2*P) (2*V) Q T beta hI hT (fun d => ((N:ZMod d)⁻¹))
    (by simpa [head] using hhead.trans (show 2*(P:ℝ)≤2^2*(P:ℝ) by linarith [Nat.cast_nonneg P]))
    (by simpa using hlen.trans (show 50*(V:ℝ)≤8^2*(V:ℝ) by linarith [Nat.cast_nonneg V]))
    (by simpa using hlone) (by norm_num <;> linarith [Nat.cast_nonneg P])
    (by norm_num <;> linarith [Nat.cast_nonneg V]) hq
  have hsub : S⊆(Finset.Icc 1 Q).filter (fun d => N.Coprime d) := by
    intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hS d hd).1,Nat.le_floor (hS d hd).2.1⟩,
      (hS d hd).2.2.1⟩
  have hr := natural_rectangle_norm_sum_le_character_sum I T head beta (2*P) (2*V) N Q hI hT
  calc
    _ ≤ ∑ d∈S,|c d*(∑ p∈primes l h,∑ t∈T,g t*kernel N d (p*t))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d∈S,‖naturalRectangleDiscrepancy I T head beta N d‖ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [rectangle_eq,Complex.norm_real,Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul_of_nonneg_right (hS d hd).2.2.2 (abs_nonneg _)).trans_eq (one_mul _)
    _ ≤ ∑ d∈(Finset.Icc 1 Q).filter (fun d => N.Coprime d),
        ‖naturalRectangleDiscrepancy I T head beta N d‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ ≤ _ := hr.trans (by simpa only [Real.rpow_natCast] using Hrect)

end
end ImbalancedChen.P4BOriginalRankTwoSampleConductor
