import ImbalancedChen.Part3OriginalMellinPrefixVariation
import ImbalancedChen.Part3OriginalInverseShortMeanInitial

/-! Restore both Mellin factors on the actual common additive phases and
physical Kloosterman sums. Both Abel coefficients are outside the modulus sum. -/
namespace ImbalancedChen.Part3.OriginalTwistedInitialMean20261113
noncomputable section
open Finset
open scoped BigOperators
open OriginalSwitchedMellinRows20261113 OriginalMellinPrefixVariation20261113
open OriginalInverseShortMeanInitial20261113 OriginalSmoothPoissonTail ActualIntervalGeometricSumSourceOnly

def kernel (k : ℕ+) (ω : ℝ) (m n : ℕ) : ℂ :=
  phaseAt ω m*phaseAt (-ω) n*kloosterman k.val (m:ℤ) (n:ℤ)

def twistedSum (k : ℕ+) (a b c d : ℕ) (ω s t : ℝ) : ℂ :=
  ∑ m ∈ Ico a b, ∑ n ∈ Ico c d, wave (m:ℝ) s*wave (n:ℝ) t*kernel k ω m n

private theorem expanded (k : ℕ+) (a b c d : ℕ) (ω s t : ℝ) :
    twistedSum k a b c d ω s t =
      ∑ i ∈ Icc a b, ∑ j ∈ Icc c d, (coeff s b i*coeff t d j)*
        (∑ m ∈ Ico a (min b (i+1)), ∑ n ∈ Ico c (min d (j+1)), kernel k ω m n) := by
  classical
  let u (i) := Ico a (min b (i+1))
  let v (j) := Ico c (min d (j+1))
  have row (m : ℕ) := abel (kernel k ω m) t c d
  have H (i) : (∑ m ∈ u i, ∑ n ∈ Ico c d, wave (n:ℝ) t*kernel k ω m n) =
      ∑ j ∈ Icc c d, coeff t d j*∑ m ∈ u i, ∑ n ∈ v j, kernel k ω m n := by
    simp_rw [row]
    rw [sum_comm (s := u i) (t := Icc c d)]
    exact sum_congr rfl (fun j _ => (mul_sum _ _ _).symm)
  unfold twistedSum
  have factor (m : ℕ) :
      (∑ n ∈ Ico c d, wave (m:ℝ) s*wave (n:ℝ) t*kernel k ω m n) =
        wave (m:ℝ) s*∑ n ∈ Ico c d, wave (n:ℝ) t*kernel k ω m n := by
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ => mul_assoc _ _ _)
  simp_rw [factor]
  rw [abel _ s a b]
  apply sum_congr rfl
  intro i hi
  change coeff s b i*(∑ m ∈ u i, ∑ n ∈ Ico c d, wave (n:ℝ) t*kernel k ω m n)=_
  rw [H,mul_sum]
  exact sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)

/-- The two independent Mellin frequencies cost (1+|s|)(1+|t|).
In (4.30) one takes s=t equal to the common half-frequency. -/
theorem twisted_initial_mean {ε : ℝ} (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (L : Finset ℕ+) (X M N : ℕ), 1≤X → 1≤M → 1≤N →
      (∀ k ∈ L, k.val≤X) → ∀ a b c d : ℕ,
      0<a → a≤b → b≤2*a → b-a≤M → 0<c → c≤d → d≤2*c → d-c≤N →
      ∀ ω s t : ℝ, (∑ k ∈ L, ‖twistedSum k a b c d ω s t‖) ≤
        C*((X:ℝ)*M*N)^ε*(X:ℝ)*((X:ℝ)+(M:ℝ)*N)*(1+|s|)*(1+|t|) := by
  classical
  obtain ⟨C,hC,bound⟩ := initial_opened_mean he
  refine ⟨C,hC,?_⟩
  intro L X M N x m n cap a b c d ha hab bcap hm hc hcd dcap hn ω s t
  let I := Icc a b
  let J := Icc c d
  let B := C*((X:ℝ)*M*N)^ε*(X:ℝ)*((X:ℝ)+(M:ℝ)*N)
  let P (k : ℕ+) (i j : ℕ) := ∑ l ∈ Ico a (min b (i+1)), ∑ r ∈ Ico c (min d (j+1)), kernel k ω l r
  let A (i j : ℕ) := ‖coeff s b i‖*‖coeff t d j‖
  have one (k) : ‖twistedSum k a b c d ω s t‖ ≤ ∑ i ∈ I, ∑ j ∈ J, A i j*‖P k i j‖ := by
    rw [expanded]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i hi
    simpa only [A,P,norm_mul] using (norm_sum_le J
      (fun j => (coeff s b i*coeff t d j)*P k i j))
  have prefix (i) (hi : i∈I) (j) (hj : j∈J) : (∑ k ∈ L, ‖P k i j‖)≤B := by
    have iv := mem_Icc.mp hi
    have jv := mem_Icc.mp hj
    exact bound L X M N x m n cap a (min b (i+1)) c (min d (j+1))
      (le_min hab (by omega)) (le_min hcd (by omega))
      (by omega) (by omega) ω
  have exchange :
      (∑ k ∈ L, ∑ i ∈ I, ∑ j ∈ J, A i j*‖P k i j‖) =
      ∑ i ∈ I, ∑ j ∈ J, A i j*∑ k ∈ L, ‖P k i j‖ := by
    rw [sum_comm (s := L) (t := I)]
    apply sum_congr rfl
    intro i hi
    rw [sum_comm (s := L) (t := J)]
    exact sum_congr rfl (fun j _ => (mul_sum _ _ _).symm)
  have total : (∑ i ∈ I, ∑ j ∈ J, A i j*B) =
      ((∑ i ∈ I, ‖coeff s b i‖)*(∑ j ∈ J, ‖coeff t d j‖))*B := by
    rw [sum_mul_sum,sum_mul]
    exact sum_congr rfl (fun i _ => (sum_mul _ _ _).symm)
  change (∑ k ∈ L, ‖twistedSum k a b c d ω s t‖)≤B*(1+|s|)*(1+|t|)
  calc
    _ ≤ _ := sum_le_sum (fun k (_ : k∈L) => one k)
    _ = _ := exchange
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, A i j*B := sum_le_sum (fun i hi => sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (prefix i hi j hj) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))
    _ = _ := total
    _ ≤ ((1+|s|)*(1+|t|))*B := mul_le_mul_of_nonneg_right (mul_le_mul
      (variation s ha hab bcap) (variation t hc hcd dcap) (sum_nonneg (fun _ _ => norm_nonneg _))
      (by positivity)) (by dsimp [B]; positivity)
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalTwistedInitialMean20261113
