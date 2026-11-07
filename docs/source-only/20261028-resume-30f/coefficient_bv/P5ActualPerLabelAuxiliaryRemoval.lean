import ImbalancedChen.P5ActualInnerPerLabelGamma
import ImbalancedChen.Part3RoughAuxiliarySW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual ORIGINAL label-normalized mesh gamma supplies the genuine rough
auxiliary-coprimality removal bound with the SAME primitive coprime mean.
All support, one-bound and rough-factor inputs are derived from the actual
fixed prime-label word. This is NOT the remaining k=1 Siegel--Walfisz
estimate, and no desired SW hypothesis is introduced to replace it.
Small beta is absent here: it is small, so the attached gamma3 is not
falsely declared a rough coefficient.
-/

namespace ImbalancedChen.P5Z.ActualPerLabelAuxiliaryRemoval
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open All16FineMeshGateScalar ActualInnerPerLabelGamma

def endpointProduct (N m : ℕ) (word : List (Fin (m + 1))) : ℕ :=
  (word.map (meshUpper N m)).prod

/-- Every occupied group product is positive and below its literal
computed endpoint product, independently of discrepancies or residues. -/
theorem actual_mesh_group_interval (N cap m : ℕ) (w Z : ℝ)
    (word : List (Fin (m + 1))) :
    ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z word ⊆
      Finset.Ioc 0 (endpointProduct N m word) := by
  intro d hd
  have hrough := ActualInnerMeshSeparatedGamma.groupSupport_rough w Z word hd
  obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hd
  apply Finset.mem_Ioc.mpr
  refine ⟨Nat.pos_of_ne_zero hrough.1, ?_⟩
  exact actualPrimeSlotBox_prod_le_upper (meshPrimeAlphabet N cap w Z m) (meshUpper N m)
    word (fun _ _ _ hp => mesh_prime_le_upper hp) ps hps

/-- Concrete finite auxiliary-k removal for an ACTUAL original per-label
gamma. The divisor order is one, every positive q,k and primitive residue
test retain their exact common source. No analytic SW estimate is assumed. -/
theorem actual_mesh_gamma_auxiliary_removal {N cap m : ℕ} (hN : 1 < N)
    (w Z : ℝ) (hw : 0 < w) (word : List (Fin (m + 1))) (hnd : word.Nodup)
    (k q b : ℕ) (hk : 0 < k) (hq : 0 < q) :
    ‖Part3.auxiliarySWError (ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z word)
        (fun d => (meshGamma N cap m w Z word d : ℂ)) k q b -
      Part3.auxiliarySWError (ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z word)
        (fun d => (meshGamma N cap m w Z word d : ℂ)) 1 q b‖ ≤
      4 * (k.divisors.card : ℝ) * (endpointProduct N m word : ℝ) / w := by
  have hnorm : ∀ d ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z word,
      ‖(meshGamma N cap m w Z word d : ℂ)‖ ≤ 1 := by
    intro d hd
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      meshGamma_abs_le_one hN w Z word hnd d
  have hrough : ∀ d ∈ ActualInnerMeshSeparatedGamma.groupSupport N cap m w Z word,
      (meshGamma N cap m w Z word d : ℂ) ≠ 0 →
        ∀ p : ℕ, p.Prime → p ∣ d → w / 2 < (p : ℝ) := by
    intro d hd hnonzero p hp hpd
    have hr := ActualInnerMeshSeparatedGamma.groupSupport_rough w Z word hd
    have hpw := hr.2 p (hp.mem_primeFactors hpd hr.1)
    linarith
  calc
    _ ≤ 2 * (k.divisors.card : ℝ) * (endpointProduct N m word : ℝ) / (w / 2) :=
      Part3.auxiliarySWError_sub_one_norm_le _ _ (endpointProduct N m word) k q b (w / 2)
        (actual_mesh_group_interval N cap m w Z word) (by positivity) hk hq hnorm hrough
    _ = _ := by
      field_simp [hw.ne'] <;> ring

end
end ImbalancedChen.P5Z.ActualPerLabelAuxiliaryRemoval
