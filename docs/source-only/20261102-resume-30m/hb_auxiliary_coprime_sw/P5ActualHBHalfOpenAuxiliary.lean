import ImbalancedChen.P5ActualHBAuxiliaryPrefixes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Endpoint identities for every auxiliary k.  Native HB (u,v] is retained;
if a caller asks for [u,v), both endpoint integers are explicitly present.
-/
namespace ImbalancedChen.P5Z.ActualHBHalfOpenAuxiliary
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open OriginalBetaPrimeSource OriginalBetaPrimeHalfOpenSW
open ActualRoughHeathBrownWords ActualHBAuxiliaryPrefixes

theorem auxiliary_halfOpen_eq (S : Finset ℕ) (c : ℕ → ℂ)
    {u v : ℝ} (huv : u < v) (k q b : ℕ) :
    auxiliarySWError (S.filter (fun n => u ≤ (n : ℝ) ∧ (n : ℝ) < v)) c k q b =
      auxiliarySWError (S.filter (fun n => u < (n : ℝ) ∧ (n : ℝ) ≤ v)) c k q b +
        (∑ n ∈ S, if (n : ℝ) = u then coprimeMask c k n*exactKernel q b n else 0) -
        (∑ n ∈ S, if (n : ℝ) = v then coprimeMask c k n*exactKernel q b n else 0) := by
  rw [auxiliary_eq_mask (S.filter (fun n => u ≤ (n : ℝ) ∧ (n : ℝ) < v)) c k q b,
    auxiliary_eq_mask (S.filter (fun n => u < (n : ℝ) ∧ (n : ℝ) ≤ v)) c k q b]
  simp only [error_eq_kernel,Finset.sum_filter,
    ← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h1 : (n : ℝ) = u
  · have h2 : (n : ℝ) ≠ v := by linarith
    simp [h1,h2,huv,huv.le]
  · by_cases h2 : (n : ℝ) = v
    · simp [h1,h2,huv,huv.le]
    · have hs : (u ≤ (n : ℝ) ∧ (n : ℝ) < v) ↔
          (u < (n : ℝ) ∧ (n : ℝ) ≤ v) := by
        constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
      simp only [h1,h2,if_false,hs,add_zero,sub_zero]

theorem actual_auxiliary_halfOpen_norm_le (z y : ℝ) (role : Role)
    (S : Finset ℕ) (H k q b : ℕ) (hS : S ⊆ Finset.Ioc 0 H)
    {u v : ℝ} (huv : u < v) (hq : 0 < q) :
    ‖auxiliarySWError (S.filter (fun n => u ≤ (n : ℝ) ∧ (n : ℝ) < v))
      (actual z y role) k q b‖ ≤
      ‖auxiliarySWError (S.filter (fun n => u < (n : ℝ) ∧ (n : ℝ) ≤ v))
        (actual z y role) k q b‖ + 4*roleAmplitude role H := by
  have hnorm (n : ℕ) (hn : n ∈ S) :
      ‖coprimeMask (actual z y role) k n‖ ≤ roleAmplitude role H := by
    by_cases hc : n.Coprime k
    · simpa only [coprimeMask,if_pos hc] using
        actual_norm_le_roleAmplitude z y role
          (Finset.mem_Ioc.mp (hS hn)).1 (Finset.mem_Ioc.mp (hS hn)).2
    · simpa only [coprimeMask,if_neg hc,norm_zero] using roleAmplitude_nonneg role H
  have hu := endpoint_mass_norm_le S (coprimeMask (actual z y role) k) u
    (roleAmplitude role H) (roleAmplitude_nonneg role H) (fun n hn he => hnorm n hn) hq
  have hv := endpoint_mass_norm_le S (coprimeMask (actual z y role) k) v
    (roleAmplitude role H) (roleAmplitude_nonneg role H) (fun n hn he => hnorm n hn) hq
  rw [auxiliary_halfOpen_eq S (actual z y role) huv k q b]
  exact (norm_sub_le _ _).trans
    ((add_le_add (norm_add_le _ _) le_rfl).trans (by linarith))

end
end ImbalancedChen.P5Z.ActualHBHalfOpenAuxiliary
