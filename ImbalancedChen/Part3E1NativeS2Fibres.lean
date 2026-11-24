import ImbalancedChen.Part3E1PhysicalTail
import ImbalancedChen.Part3E1ProfileS2Progression

/-!
# Tagged carrier for the restored physical S2 block

The archived product order carries one `q`, one `d` and two independent
rough/alpha pairs. The sample profile is an explicit argument.
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Finset
open scoped BigOperators FourierTransform SchwartzMap

/-- The tagged carrier of a restored S2 block over the ordered rough/alpha pairs. -/
def restoredS2FibreCarrier (a : ℤ) (Q D R N : Finset ℕ) :
    Finset ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :=
  (primitive a Q ×ˢ D) ×ˢ ((R ×ˢ N) ×ˢ (R ×ˢ N))

/-- Exact sum reindexing, keeping the two rough labels and two alpha labels independent. -/
theorem sum_restoredS2FibreCarrier {M : Type*} [AddCommMonoid M]
    (a : ℤ) (Q D R N : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → M) :
    (∑ v ∈ restoredS2FibreCarrier a Q D R N,
      f v.1.1 v.1.2 v.2.1.1 v.2.2.1 v.2.1.2 v.2.2.2) =
    ∑ d ∈ D, ∑ q ∈ primitive a Q, ∑ n ∈ N, ∑ s ∈ R, ∑ n' ∈ N, ∑ r ∈ R,
      f q d r s n n' := by
  simp only [restoredS2FibreCarrier, sum_product]
  rw [sum_comm (s := primitive a Q) (t := D)]
  refine sum_congr rfl fun d _ => sum_congr rfl fun q _ => ?_
  rw [sum_comm (s := R) (t := N)]
  refine sum_congr rfl fun n _ => ?_
  rw [sum_comm (s := R) (t := R)]
  refine sum_congr rfl fun s _ => ?_
  exact sum_comm

/-- The restored physical fibre with arbitrary m profile over the original
finite carrier. Its outer coefficient keeps the original real q weight. -/
def restoredS2ProfileFibre (ψ : 𝓢(ℝ, ℂ)) (a : ℤ) (V : ℝ)
    (qWeight : ℕ → ℝ) (lambdaTrim : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ)
    (q d r s n n' : ℕ) : ℂ :=
  if n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) then
    ((qWeight q : ℂ) * lambdaTrim d r * star (lambdaTrim d s) * alpha n * star (alpha n')) *
      physicalProfileS2Progression ψ V a (q * d * r) n /
      ((q * d * s).totient : ℂ)
  else 0

/-- Reindex the current physical block on the original tagged carrier. -/
theorem physicalSameCutoffS2Block_eq_restoredS2FibreCarrier
    (Q D R N : Finset ℕ) (a : ℤ) (V : ℝ) (qWeight : ℕ → ℝ)
    (lambdaTrim : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ) :
    (∑ d ∈ D, physicalSameCutoffS2FixedD Q R N d a V qWeight (lambdaTrim d) alpha) =
    ∑ v ∈ restoredS2FibreCarrier a Q D R N,
      restoredS2ProfileFibre GevreyCutoff.cutoffSchwartz a V qWeight lambdaTrim alpha
        v.1.1 v.1.2 v.2.1.1 v.2.2.1 v.2.1.2 v.2.2.2 := by
  rw [sum_restoredS2FibreCarrier]
  rfl

/-- Reindex the corresponding zero Fourier block on the same tagged carrier. -/
theorem physicalSameCutoffS2ZeroBlock_eq_restoredS2FibreCarrier
    (Q D R N : Finset ℕ) (a : ℤ) (V : ℝ) (qWeight : ℕ → ℝ)
    (lambdaTrim : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ) :
    let term (q d r s n n' : ℕ) :=
      if n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) then
        ((qWeight q : ℂ) * lambdaTrim d r * star (lambdaTrim d s) * alpha n * star (alpha n')) *
          sameCutoffS2ZeroMode V (q * d * r) / ((q * d * s).totient : ℂ)
      else 0
    (∑ d ∈ D, physicalSameCutoffS2ZeroFixedD Q R N d a V qWeight (lambdaTrim d) alpha) =
    ∑ v ∈ restoredS2FibreCarrier a Q D R N,
      term v.1.1 v.1.2 v.2.1.1 v.2.2.1 v.2.1.2 v.2.2.2 := by
  intro term
  exact (sum_restoredS2FibreCarrier a Q D R N term).symm

/-- Exact same-profile S2 Poisson splitting on the original tagged carrier.
The common coefficient applies to both independent primitive gates. -/
theorem restoredS2ProfileBlock_eq_zero_add_nonzero
    (ψ : 𝓢(ℝ, ℂ))
    (hψ : ∀ ⦃x : ℝ⦄, ψ x ≠ 0 → x ∈ Set.Icc (1 / 2 : ℝ) (5 / 2))
    (Q D R N : Finset ℕ) (a : ℤ) {V : ℝ} (hV : 0 < V)
    (qWeight : ℕ → ℝ) (lambdaTrim : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ)
    (hQ : ∀ q ∈ Q, 0 < q) (hD : ∀ d ∈ D, 0 < d) (hR : ∀ r ∈ R, 0 < r) :
    let carrier := restoredS2FibreCarrier a Q D R N
    let coefficient (q d r s n n' : ℕ) :=
      if n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) then
        ((qWeight q : ℂ) * lambdaTrim d r * star (lambdaTrim d s) * alpha n * star (alpha n')) /
          ((q * d * s).totient : ℂ)
      else 0
    (∑ v ∈ carrier, restoredS2ProfileFibre ψ a V qWeight lambdaTrim alpha
      v.1.1 v.1.2 v.2.1.1 v.2.2.1 v.2.1.2 v.2.2.2) =
    (∑ v ∈ carrier, coefficient v.1.1 v.1.2 v.2.1.1 v.2.2.1 v.2.1.2 v.2.2.2 *
      profileS2ZeroMode ψ V (v.1.1 * v.1.2 * v.2.1.1)) +
    (∑ v ∈ carrier, coefficient v.1.1 v.1.2 v.2.1.1 v.2.2.1 v.2.1.2 v.2.2.2 *
      ∑' h : ℤ, retainedS2Mode (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) V a
        (v.1.1 * v.1.2 * v.2.1.1) v.2.1.2 h) := by
  dsimp only
  rw [← sum_add_distrib]
  refine sum_congr rfl fun v hv => ?_
  rcases v with ⟨⟨q, d⟩, ⟨r, n⟩, ⟨s, n'⟩⟩
  obtain ⟨hqd, hrough⟩ := mem_product.mp hv
  obtain ⟨hq, hd⟩ := mem_product.mp hqd
  have hr := (mem_product.mp (mem_product.mp hrough).1).1
  have hm := Nat.mul_pos (Nat.mul_pos (hQ q (mem_filter.mp hq).1) (hD d hd)) (hR r hr)
  by_cases hunit : n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s)
  · simp only [restoredS2ProfileFibre, if_pos hunit]
    rw [physicalProfileS2Progression_eq_zero_add_nonzero ψ hψ hV a hm hunit.1]
    ring
  · simp [restoredS2ProfileFibre, hunit]

end

end ImbalancedChen.Part3.E1Finite
