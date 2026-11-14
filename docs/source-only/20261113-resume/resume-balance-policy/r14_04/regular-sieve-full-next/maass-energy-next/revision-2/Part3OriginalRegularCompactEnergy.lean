import ImbalancedChen.Part3OriginalRegularCompactGram

/-! Uniform bound for the limit of the actual Gaussian L² energies,
with a single diagonal and the complete arbitrary-sequence off-diagonal. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCompactEnergy20261113
open Finset Real Complex Set Filter MeasureTheory
open scoped Topology ComplexConjugate MatrixGroups
open OriginalRegularCutoffModuli20261113 (series compact_average_limit weighted_integrable)
open OriginalRegularCutoffDiagonal20261113 (height height_limit)
open OriginalRegularCutoffPlane20261113 (compact)
open OriginalRegularPreKuznetsovGaussian20261113 (weight)
open OriginalRegularPreKuznetsovAverage20261113 (gaussianOrbit weight_integrable)
open OriginalRegularPreKuznetsovFourier20261113 (full_gaussian_diagonal)
open OriginalRegularCompactGram20261113 (mark vector gram full_rows)
open OriginalSameInfinityScalarGeometry20261113 (term)
open OriginalHolomorphicInfinityGram20261113 (packet)
open OriginalRegularGaussianOffDiagonal20261113 (entry cost gaussian_off_diagonal)
open OriginalAllParameterKloosterman20261113 (dyadEnergy)
open OriginalHolomorphicShortOscillation20261113 (rowProduct)

private def tail (q : ℕ+) (M : ℕ) (a : ℕ→ℂ) (K : ℝ) :=
  packet M a (fun m n => ∑' c,term (gaussianOrbit K) q (mark m) (mark n) c)

def limitEnergy (q : ℕ+) (M : ℕ) (a : ℕ→ℂ) (K : ℝ) :=
  (π/4)*(sqrt π*K^3/2)*dyadEnergy M a+(tail q M a K).re

private def marked (q : ℕ+) (M : ℕ) (a : ℕ→ℂ) (K : ℝ) (j : ℕ) (r : ℝ) :=
  ∑ i∈range (M+1),∑ l∈range (M+1),conj (a (M+i))*a (M+l)*
    ((weight K r:ℂ)*series q (mark (M+i)) (mark (M+l)) (some j) r)

private theorem marked_integral {K : ℝ} (hp : 0<K) (q : ℕ+) (M : ℕ) (a : ℕ→ℂ) (j : ℕ) :
    Integrable (marked q M a K j) ∧
    (∫ r : ℝ,marked q M a K j r)=packet M a (fun m n =>
      ∫ r : ℝ,(weight K r:ℂ)*series q (mark m) (mark n) (some j) r) := by
  have h (i l : ℕ) := (weighted_integrable hp q (mark (M+i)) (mark (M+l)) (some j)).const_mul
    (conj (a (M+i))*a (M+l))
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => h i l)),?_⟩
  rw [marked,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => h i l))]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun l _ => h i l)]
  exact sum_congr rfl (fun l _ => integral_const_mul _ _)

private theorem marked_limit {K : ℝ} (hp : 0<K) (q : ℕ+) (M : ℕ) (a : ℕ→ℂ) :
    Tendsto (fun j : ℕ => ∫ r : ℝ,marked q M a K j r) atTop (𝓝 (tail q M a K)) := by
  simp_rw [(marked_integral hp q M a _).2]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro l _
  exact (compact_average_limit hp q (mark (M+i)) (mark (M+l))).const_mul _

def mass (q : ℕ+) (M : ℕ) (a : ℕ→ℂ) (K : ℝ) (j : ℕ) (r : ℝ) :=
  weight K r*‖vector q M a (compact r j)‖^2

private theorem split_mass {M : ℕ} (hM : 0<M) (q : ℕ+) (a : ℕ→ℂ) (K : ℝ) (j : ℕ) (r : ℝ) :
    mass q M a K j r=weight K r*(height j*dyadEnergy M a)+(marked q M a K j r).re := by
  have fac : marked q M a K j r=(weight K r:ℂ)*packet M a (fun m n => series q (mark m) (mark n) (some j) r) := by
    simp only [marked,packet,Finset.mul_sum]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun l _ => by ring))
  rw [mass,gram q hM a j r,fac,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem energy_limit {K : ℝ} (hp : 0<K) (q : ℕ+) {M : ℕ} (hM : 0<M) (a : ℕ→ℂ) :
    (∀ j,Integrable (mass q M a K j)) ∧
    Tendsto (fun j : ℕ => ∫ r : ℝ,mass q M a K j r) atTop (𝓝 (limitEnergy q M a K)) := by
  let T := fun j => marked q M a K j
  have si (j : ℕ) := (marked_integral hp q M a j).1
  have di (j : ℕ) := (weight_integrable hp).mul_const (height j*dyadEnergy M a)
  have E (j : ℕ) : mass q M a K j=fun r => weight K r*(height j*dyadEnergy M a)+(T j r).re :=
    funext (split_mass hM q a K j)
  refine ⟨fun j => by rw [E j]; exact (di j).add (si j).re,?_⟩
  have diE (j : ℕ) : (∫ r : ℝ,mass q M a K j r)=
      (sqrt π*K^3/2)*(height j*dyadEnergy M a)+(∫ r : ℝ,T j r).re := by
    rw [E,integral_add (di j) (si j).re,integral_mul_const,full_gaussian_diagonal hp,integral_re (si j)]
  simp_rw [diE]
  have h := ((height_limit.mul_const (dyadEnergy M a)).const_mul (sqrt π*K^3/2)).add
    (Complex.continuous_re.continuousAt.tendsto.comp (marked_limit hp q M a))
  convert h using 1 <;> dsimp only [limitEnergy] <;> ring

theorem energy_bound {e K : ℝ} (he : 0<e) (hK : 2≤K) (q : ℕ+) {M : ℕ} (hM : 0<M) (a : ℕ→ℂ) :
    limitEnergy q M a K≤
      ((π*sqrt π/8)*K^3+cost e*K*((M:ℝ)^(1+e)/q.val))*dyadEnergy M a := by
  have hp : 0<K := by linarith only [hK]
  have H := full_rows hp q hM a
  have C := gaussian_off_diagonal he M q.val hM q.property hK (fun n => star (a n)) a
  have E : rowProduct M (fun n => star (a n)) a=dyadEnergy M a := by
    have a0 : 0≤dyadEnergy M a := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have id : dyadEnergy M (fun n => star (a n))=dyadEnergy M a := by simp [dyadEnergy]
    rw [rowProduct,id,←sq,sq_sqrt a0]
  obtain ⟨summ,cap⟩ := C
  rw [E] at cap
  have w : ‖tail q M a K‖≤∑' l,‖entry M q.val K (fun n => star (a n)) a l‖ := by
    rw [show tail q M a K=∑' l,entry M q.val K (fun n => star (a n)) a l from H.tsum_eq.symm]
    exact norm_tsum_le_tsum_norm summ
  have b := ((Complex.re_le_norm (tail q M a K)).trans w).trans cap
  dsimp only [limitEnergy]
  nlinarith only [b]

end ImbalancedChen.Part3.OriginalRegularCompactEnergy20261113
end

