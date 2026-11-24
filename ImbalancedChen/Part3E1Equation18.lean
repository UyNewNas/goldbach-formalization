import ImbalancedChen.Part3E1CompletedAggregate
import ImbalancedChen.Part3E1FiniteCauchy

/-!
# The original E1 sum and equation (18)

The residue remains an arbitrary signed integer, with only the factorwise
primitive gates. The exterior scale, both frequency signs, and the
original inverse totient inside the unrestricted second slot are retained.
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Finset
open scoped BigOperators SchwartzMap FourierTransform

/-- Equation (18) for the natural dyadic carriers and a fixed smooth
Fourier profile, uniformly in both bounded coefficient sequences. -/
theorem exists_source_dyadic_equation18 {κ ε Ccut : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hCcut : 0 ≤ Ccut) (ψ : 𝓢(ℝ, ℂ)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (X M : ℝ) (Q R N H : ℕ), 1 ≤ X → 0 < M → 0 < Q → 0 < R → 0 < N →
        X = M * (N : ℝ) →
        8 * (Q : ℝ) * (R : ℝ)^2 ≤ X ^ κ → 4 * (H : ℝ) * (R : ℝ) ≤ X ^ κ →
        (H : ℝ) ≤ (Ccut * (Real.log X)^5) * ((Q : ℝ) * (R : ℝ) / M) →
        ∀ (a : ℤ) (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ),
          (∀ q ∈ Icc Q (2 * Q), ∀ r ∈ Icc R (2 * R), ‖lambda q r‖ ≤ 1) →
          (∀ n ∈ Icc N (2 * N), ‖alpha n‖ ≤ 1) →
          ‖source (Icc Q (2 * Q)) (Icc R (2 * R)) (Icc N (2 * N))
            (e1NonzeroFrequencies H) a M (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) lambda alpha‖ ^ 2 ≤
            A * X ^ ε * ((N : ℝ)^4 / (Q : ℝ)^2) *
              ((N : ℝ) * Q / X + (N : ℝ) * (Q : ℝ) ^ (5/2 : ℝ) * (R : ℝ)^3 / X^2 +
                (N : ℝ)^2 * Q * R / X^2) := by
  let w := CommonSmoothCutoff.dyadicCutoffSchwartz
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨P, hP, hPdecay⟩ := CommonSmoothCutoff.schwartz_norm_le_rapidDecay (𝓕 ψ) 0
  have hψ (x : ℝ) : ‖(𝓕 ψ) x‖ ≤ P := by simpa only [pow_zero, div_one] using hPdecay x
  obtain ⟨C, hC, hdecay⟩ := CommonSmoothCutoff.schwartz_norm_le_rapidDecay (𝓕 w) 2
  obtain ⟨D, hD, hphi⟩ := exists_e1ReciprocalTotient_rpow hκ hδ
  obtain ⟨K, hK, hmass⟩ := exists_e1CompletedCauchyMass_rpow (B := 4) hκ hδ
    (by norm_num) hC.le
  refine ⟨(8 * D)^2 * P^2 * K * (1 + Ccut * (40 / ε)^5)^2, by positivity, ?_⟩
  intro X M Q R N H hX hM hQ hR hN hscale hQR hHR hcut a lambda alpha hlambda halpha
  let S := Icc 0 (3 * N)
  let L := Ccut * (Real.log X)^5
  obtain ⟨hNS, hw, hmaj, hneg, hsupp, hmassW⟩ := e1_fixedMajorant N hN
  have hQ' : 0 < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hR' : 0 < (R : ℝ) := Nat.cast_pos.mpr hR
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact mul_nonneg hCcut (pow_nonneg (Real.log_nonneg hX) _)
  have hphiEnvelope : 4 * (Q : ℝ) * R ≤ X ^ κ := by
    refine le_trans ?_ hQR
    nlinarith only [mul_nonneg hQ'.le (show 0 ≤ (R : ℝ) ^ 2 - R by nlinarith [sq_nonneg ((R : ℝ) - 1)])]
  have hREnvelope : 2 * (R : ℝ) ≤ X ^ κ := by
    refine le_trans ?_ hphiEnvelope
    nlinarith only [mul_nonneg (sub_nonneg.mpr hQ1) hR'.le, hR'.le]
  have htot := hphi X hX Q R hQ hR hphiEnvelope
  have hT2 := hmass X hX Q R H hQ hR hQR hREnvelope hHR a N hN' w S hneg hsupp hdecay hmassW
  have hwComplex (n : ℕ) : ((w ((n : ℝ) / N)).re : ℂ) = w ((n : ℝ) / N) := by
    dsimp only [w]
    simp only [CommonSmoothCutoff.dyadicCutoffSchwartz_apply, Complex.ofReal_re]
  let v (n : ℕ) : ℝ := (w ((n : ℝ) / (N : ℝ))).re
  have hterm (q r r' : ℕ) (h h' : ℤ) (hm : 0 < q * r * r') :
      completedTerm S v q r r' a h h' = e1CompletedSmoothTerm q r r' h h' a N w S := by
    let _ : NeZero (q * r * r') := ⟨hm.ne'⟩
    rw [e1CompletedSmoothTerm, dif_pos hm]
    unfold completedTerm smoothReciprocalSum
    exact sum_congr rfl (fun n _ => by
      rw [completedPhase_eq_reciprocalPhase, show (v n : ℂ) = w ((n : ℝ) / N) from hwComplex n])
  have hmassEq : completedMass (Icc Q (2 * Q)) (Icc R (2 * R)) S (e1NonzeroFrequencies H) a v =
      e1CompletedCauchyMass Q R H a N w S := by
    simp only [completedMass, primitive_eq_filter, e1CompletedCauchyMass]
    refine sum_congr rfl (fun q hq => sum_congr rfl (fun r hr => sum_congr rfl (fun r' hr' =>
      sum_congr rfl (fun h _ => sum_congr rfl (fun h' _ => ?_)))))
    have hm : 0 < q * r * r' := Nat.mul_pos (Nat.mul_pos
      (hQ.trans_le (mem_Icc.mp (mem_filter.mp hq).1).1)
      (hR.trans_le (mem_Icc.mp (mem_filter.mp hr).1).1))
      (hR.trans_le (mem_Icc.mp (mem_filter.mp hr').1).1)
    rw [hterm q r r' h h' hm]
  have hsource := source_norm_sq_le_completedMass Q R N hQ hR hN S (e1NonzeroFrequencies H)
    a M (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) lambda alpha v (D * X ^ (ε/4)) P (by positivity) hP.le hNS hw hmaj
    (fun q hq r hr => hlambda q (mem_filter.mp hq).1 r (mem_filter.mp hr).1) halpha hψ
    (fun q hq s hs => by
      rw [← one_div]
      exact htot q (mem_filter.mp hq).1 s (mem_filter.mp hs).1)
  rw [hmassEq] at hsource
  let E := (N : ℝ) * Q * R * H + (Q : ℝ) * Real.sqrt Q * (R : ℝ)^3 * (H : ℝ)^2 +
    (N : ℝ) * R * (H : ℝ)^2
  calc
    _ ≤ 64 * (D * X ^ (ε/4))^2 * P^2 * (N : ℝ)^3 / ((Q : ℝ)^3 * (R : ℝ)^2) *
        e1CompletedCauchyMass Q R H a N w S := hsource
    _ ≤ 64 * (D * X ^ (ε/4))^2 * P^2 * (N : ℝ)^3 / ((Q : ℝ)^3 * (R : ℝ)^2) *
        (K * X ^ (ε/4) * E) := mul_le_mul_of_nonneg_left hT2 (by positivity)
    _ = (8 * D * X ^ (ε/4))^2 * P^2 * (K * X ^ (ε/4)) *
        ((N : ℝ)^3 / ((Q : ℝ)^3 * (R : ℝ)^2) * E) := by ring
    _ ≤ _ := e1_scale_budget_le hN' hQ' hR' hM (Nat.cast_nonneg H)
      hL hX hε hK.le hCcut hscale hcut le_rfl

end

end ImbalancedChen.Part3.E1Finite
