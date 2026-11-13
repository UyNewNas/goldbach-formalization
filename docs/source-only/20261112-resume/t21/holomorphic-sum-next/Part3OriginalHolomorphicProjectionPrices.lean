import ImbalancedChen.Part3OriginalPositivePeterssonTrace
import ImbalancedChen.Part3ActualPositiveHolomorphicDiagonal
import ImbalancedChen.Part3OriginalCrossCuspWeightTwoTail
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Joint absolute convergence in the actual positive moduli and all even weights.
The first power of the Bessel argument is kept at every odd order, including one. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicProjectionPrices20261112
open Complex
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalNonzeroCuspOneSource20261102 (cuspOneMatrixSum)
open OriginalPeterssonLipschitz20261112 (argument)
open OriginalPeterssonNormalizedOrbits20261112 (modulus modulus_pos)
open ActualPositiveHolomorphicWeights20261112

def qMark (N m h : ℕ) (d : ℕ+) : ℝ :=
  argument (Real.sqrt m) (Real.sqrt h) (modulus N d)

def arithmetic (N m h : ℕ) (d : ℕ+) : ℂ :=
  if good : N.Coprime (d:ℕ) then cuspOneMatrixSum N d good m h/(modulus N d:ℂ) else 0

def oddTerm (Φ : ℝ→ℂ) (j : ℕ) (q : ℝ) : ℂ :=
  2*((2*j+1:ℕ):ℂ)*moment (2*j+1) Φ*intJ (2*j+1) q

def joint (N m h : ℕ) (Φ : ℝ→ℂ) (p : ℕ+ × ℕ) : ℂ :=
  arithmetic N m h p.1*oddTerm Φ p.2 (qMark N m h p.1)

theorem weighted_moments (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun j : ℕ => ((2*j+1:ℕ):ℝ)*‖moment (2*j+1) (spectralTest ell Y)‖) := by
  obtain ⟨K,hK,h⟩ := moment_factorial ell hY
  let x := 8*Y
  have he := (Real.summable_pow_div_factorial x).comp_injective
    (show Function.Injective (fun j : ℕ => 2*j) from fun a b hab => by omega)
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ (he.mul_left (K*x))
  intro j
  calc
    _ ≤ ((2*j+1:ℕ):ℝ)*(K*x^(2*j+1)/((2*j+1).factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left (h _) (by positivity)
    _ = _ := by
      dsimp only [Function.comp_apply]
      rw [Nat.factorial_succ,pow_succ]
      push_cast
      field_simp [(by positivity : (2*(j:ℝ)+1)≠0),
        (by exact_mod_cast (Nat.factorial_ne_zero (2*j)) : ((2*j).factorial:ℝ)≠0)]
      <;> ring

private theorem expMass_mono {a b : ℝ} (ha : 0≤a) (hab : a≤b) : expMass a≤expMass b := by
  have S (x : ℝ) : Summable (fun k : ℕ => (x/2)^(2*k)/(k.factorial:ℝ)) := by
    simpa only [pow_mul] using Real.summable_pow_div_factorial ((x/2)^2)
  exact (S a).tsum_le_tsum (fun k => by gcongr) (S b)

/-- The constant is independent of the denominator and the odd order. -/
theorem odd_bessel_uniform {A : ℝ} (hA : 0≤A) :
    ∃ K : ℝ, 0≤K ∧ ∀ (d : ℕ+) (j : ℕ), ‖intJ (2*j+1) (A/(d:ℝ))‖ ≤ K/(d:ℝ) := by
  let b := fun n : ℕ => (A/2)^n/(n.factorial:ℝ)
  have sb : Summable b := Real.summable_pow_div_factorial _
  have hb (n : ℕ) : 0≤b n := by dsimp [b]; positivity
  refine ⟨(∑' n,b n)*expMass A,mul_nonneg (tsum_nonneg hb) (expMass_nonneg _),?_⟩
  intro d j
  have hd : 1≤(d:ℝ) := by exact_mod_cast d.2
  have hd0 : 0<(d:ℝ) := by linarith
  have hsmall : A/(d:ℝ)≤A := div_le_self hA hd
  let n := 2*j+1
  have hp : (d:ℝ)≤(d:ℝ)^n := by
    change _≤(d:ℝ)^(2*j+1)
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hd (n:=2*j)) hd0.le
  have hs : ((A/(d:ℝ))/2)^n/(n.factorial:ℝ)≤b n/(d:ℝ) := by
    rw [show A/(d:ℝ)/2=(A/2)/(d:ℝ) by ring,div_pow]
    calc
      _ = b n/(d:ℝ)^n := by dsimp [b];ring
      _ ≤ _ := div_le_div_of_nonneg_left (hb n) hd0 hp
  calc
    _ ≤ ((A/(d:ℝ)/2)^n/(n.factorial:ℝ))*expMass (A/d) :=
      intJ_bound n (by positivity) le_rfl
    _ ≤ (b n/(d:ℝ))*expMass A := mul_le_mul hs
      (expMass_mono (by positivity) hsmall) (expMass_nonneg _) (by positivity)
    _ ≤ ((∑' k,b k)/(d:ℝ))*expMass A := by
      gcongr
      exact sb.le_tsum n (fun i _ => hb i)
    _ = _ := by ring

theorem joint_absolute (N m h : ℕ) [NeZero N] (hm : 0<m)
    (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun p : ℕ+ × ℕ => ‖joint N m h (spectralTest ell Y) p‖) := by
  let Φ := spectralTest ell Y
  let A := 4*Real.pi*Real.sqrt m*Real.sqrt h/Real.sqrt N
  have sN : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos _))
  obtain ⟨K,hK,hJ⟩ := odd_bessel_uniform (show 0≤A by dsimp [A]; positivity)
  let b := fun d : ℕ+ => FixedMarkTail.price m 0 d
  let c := fun j : ℕ => ((2*j+1:ℕ):ℝ)*‖moment (2*j+1) Φ‖
  let T := 2*K/Real.sqrt N
  have sb : Summable b := (FixedMarkTail.summable_majorant_price
    (m:=(m:ℤ)) (by exact_mod_cast hm.ne') (δ:=0) (by norm_num)).comp_injective Subtype.val_injective
  have sc : Summable c := weighted_moments ell hY
  have b0 (d) : 0≤b d := FixedMarkTail.price_nonneg _ _ _
  have c0 (j) : 0≤c j := by dsimp [c]; positivity
  have T0 : 0≤T := by dsimp [T]; positivity
  have S : Summable (fun p : ℕ+ × ℕ => (T*b p.1)*c p.2) := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (mul_nonneg T0 (b0 p.1)) (c0 p.2))).mpr
    exact ⟨fun d => sc.mul_left _, by simpa only [tsum_mul_left] using (sb.mul_left T).mul_right (∑' j,c j)⟩
  apply S.of_nonneg_of_le (fun _ => norm_nonneg _)
  rintro ⟨d,j⟩
  have hd : 0<(d:ℝ) := by exact_mod_cast d.2
  have bval : b d = FixedMarkTail.majorant m d/(d:ℝ)^2 := by
    simp [b,FixedMarkTail.price,d.2.ne',Real.rpow_neg hd.le,Real.rpow_two,div_eq_mul_inv]
  by_cases good : N.Coprime (d:ℕ)
  · have qval : qMark N m h d=A/(d:ℝ) := by
      dsimp [qMark,argument,modulus,A];ring
    rw [joint,arithmetic,dif_pos good,oddTerm,norm_mul,norm_mul,norm_mul,norm_mul,
      norm_div,Complex.norm_real,Real.norm_of_nonneg (modulus_pos N d).le,
      Complex.norm_ofNat,Complex.norm_natCast,qval]
    calc
      _ ≤ (FixedMarkTail.majorant m d/modulus N d)*
          (2*((2*j+1:ℕ):ℝ)*‖moment (2*j+1) Φ‖*(K/(d:ℝ))) := by
        apply mul_le_mul (div_le_div_of_nonneg_right
          (FixedMarkTail.cusp_one_le N d (NeZero.pos N) good m h) (modulus_pos N d).le)
          (mul_le_mul_of_nonneg_left (hJ d j) (by positivity)) (by positivity)
          (div_nonneg (FixedMarkTail.majorant_nonneg _ _) (modulus_pos N d).le)
      _ = _ := by rw [bval];dsimp [T,c,modulus];ring
  · simp only [joint,arithmetic,dif_neg good,zero_mul,norm_zero]
    exact mul_nonneg (mul_nonneg T0 (b0 d)) (c0 j)

end ImbalancedChen.Part3.OriginalHolomorphicProjectionPrices20261112
end
