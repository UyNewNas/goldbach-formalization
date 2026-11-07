import ImbalancedChen.Part3RoughAPPrincipalCancellation
import ImbalancedChen.Part3RoughSlotPerronTruncation

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- The finite nonprincipal average costs at most one. The analytic
-- input is a bound on each actual character twist, not an AP estimate.
-- The final dictionary binds those twists to the genuine rough Perron
-- coefficients, including their deliberately zero n=0 coefficient.

namespace ImbalancedChen.Part3.RoughAPTwistAverage20261027
noncomputable section
open Classical Finset Set
open scoped BigOperators
open RoughAPPrincipalCancellation20261027
open RoughSlotSmoothedPerron20261026b RoughSlotPerronTruncation20261026b
open RoughSlotMellinSeries20261026b PrimeMellinProfileVariation20261026b

private theorem character_card {q : ℕ} (hq : 0 < q) :
    Fintype.card (DirichletCharacter ℂ q) = q.totient := by
  let : NeZero q := ⟨hq.ne'⟩
  have hexp : Monoid.exponent (ZMod q)ˣ ≠ 0 := Monoid.exponent_ne_zero.mpr
    (Monoid.ExponentExists.of_finite (G := (ZMod q)ˣ))
  let : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) := by
    let : NeZero (Monoid.exponent (ZMod q)ˣ) := ⟨hexp⟩
    refine { prim := ?_, cyc := ?_ }
    · exact ⟨Complex.exp (2 * Real.pi * Complex.I /
        (Monoid.exponent (ZMod q)ˣ : ℂ)),
        Complex.isPrimitiveRoot_exp (Monoid.exponent (ZMod q)ˣ) hexp⟩
    · infer_instance
  simpa only [Nat.card_eq_fintype_card] using
    (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q)

-- This is purely a finite averaging inequality. In a uniform SW consumer,
-- E must first be supplied uniformly for the actual nonprincipal twists.
theorem auxiliarySWError_norm_le_of_twist_le (S : Finset ℕ) (α : ℕ → ℂ) (k : ℕ)
    {q b : ℕ} (hq : 0 < q) (hb : b.Coprime q) {E : ℝ} (hE : 0 ≤ E)
    (hTwist : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖twist S α k χ‖ ≤ E) :
    ‖auxiliarySWError S α k q b‖ ≤ E := by
  let T : Finset (DirichletCharacter ℂ q) := Finset.univ.erase 1
  have hcNat : T.card ≤ q.totient := by
    calc
      _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card :=
        Finset.card_le_card (Finset.erase_subset _ _)
      _ = _ := by simpa only [Finset.card_univ] using character_card hq
  have hc : (T.card : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast hcNat
  have hsum : (∑ χ ∈ T, ‖twist S α k χ‖) ≤ (q.totient : ℝ)*E := by
    calc
      _ ≤ ∑ _χ ∈ T, E := by
        apply sum_le_sum
        intro χ hχ
        exact hTwist χ (Finset.mem_erase.mp hχ).1
      _ = (T.card : ℝ)*E := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hE
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  refine (auxiliarySWError_norm_le_nonprincipal S α k hq hb).trans ?_
  apply (div_le_iff₀ hphi).mpr
  simpa only [mul_comm] using hsum

def actualBaseCoefficient (useMu : Bool) (z τ U : ℝ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n=0 then 0 else
    roughCoefficient useMu z (fun m => phase τ ((m : ℝ)/U) * w m) n

-- This equality has no support, differentiability, or SW premise. A
-- weight and carrier are fixed before the character is introduced.
theorem actual_twist_eq_finite (S : Finset ℕ) (useMu : Bool)
    (z τ U : ℝ) (w : ℕ → ℂ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    twist S (actualBaseCoefficient useMu z τ U w) 1 χ =
      ∑ n ∈ S, coefficient useMu χ z τ U n * w n := by
  unfold twist
  apply sum_congr rfl
  intro n _
  simp only [Nat.coprime_one_right_eq_true, if_true]
  by_cases hn : n=0
  · simp only [actualBaseCoefficient, hn, if_true, coefficient_zero, zero_mul]
  · cases useMu <;>
      simp only [actualBaseCoefficient, hn, if_false, roughCoefficient,
        coefficient, Bool.false_eq_true, if_true, roughOneMellin, roughMoebiusMellin] <;>
      ring

-- The existing genuine finite-support identity identifies the precise
-- finite twist consumed by Perron with the actual smoothed rough sum.
theorem smooth_twist_eq_roughSmoothedSum (useMu : Bool)
    (z τ U : ℝ) {ν : ℝ → ℝ} (hsupp : Function.support ν ⊆ Icc (1/2) 2)
    {ε X : ℝ} (hε : 0<ε) (hε1 : ε<1) (hX : 0<X)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    twist (smoothCarrier ν ε X)
      (actualBaseCoefficient useMu z τ U (fun n => (Smooth1 ν ε ((n : ℝ)/X) : ℂ)))
      1 χ = roughSmoothedSum useMu χ z τ U ν ε X := by
  rw [actual_twist_eq_finite]
  exact (roughSmoothedSum_eq_finite useMu χ z τ U hsupp hε hε1 hX).symm

end
end ImbalancedChen.Part3.RoughAPTwistAverage20261027
