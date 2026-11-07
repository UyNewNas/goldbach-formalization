import ImbalancedChen.P2EnhancedShortWordUnitBound

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual arithmetic unit payment for all 18 original Gamma9--19 occurrences.
Gamma20/21 remain the independent P five/six-prime unit suppliers.
-/
namespace ImbalancedChen.P2EnhancedShortWordUnitTheta
noncomputable section
open Real Finset Wu2008DoubleSieve
open P2EnhancedSwitchedUnsiftedSource P2EnhancedSwitchedTrueNormalization
open P2EnhancedNonunitWordMass (rawScale)
open P2EnhancedShortWordUnitBound
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open scoped Classical BigOperators

def convertedUnit (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (cs : List ℕ) : ℝ :=
  ∑ d ∈ D, sigma d*thetaConversion N d*unitWordMass N Q d cs

def originalShortUnits (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ j : Fin 11, ((secondFunctionalMotherGammaWords (9+j.val)).map
    (convertedUnit N Q D sigma)).sum

/-- A single threshold pays EVERY short word before Q and the marks.
Zero support and zero total Theta require no cancellation. -/
theorem short_word_theta_upper {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      ∀ cs : List ℕ, cs.length ≤ 4 →
        convertedUnit N Q D sigma cs ≤ epsilon*Theta N Q D sigma := by
  obtain ⟨T,hT,h⟩ := actual_short_unit_upper heta he
  refine ⟨T,hT,?_⟩
  intro N hN Q D sigma hd hsigma hscale ha cs hn
  have hN4 := hT.trans hN
  have hN0 : 0 < N := by omega
  have hR (d : ℕ) (hm : d ∈ D) : 1 < Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le (hscale d hm)
  have hp (d : ℕ) (hm : d ∈ D) :
      sigma d*thetaConversion N d*unitWordMass N Q d cs ≤
        epsilon*(sigma d*thetaAtom N Q d) := by
    have hw := mul_nonneg (hsigma d hm)
      (P2EnhancedUnitSourceMass.thetaConversion_nonneg hN4 (hd d hm) (hR d hm))
    have hconvert := rawMainAtom_to_thetaAtom hN0 (hd d hm) Q (hR d hm) (fun _ => 1)
    simp only [rawMainAtom,mul_one] at hconvert
    calc
      _ ≤ sigma d*thetaConversion N d*(epsilon*rawScale N Q d) :=
        mul_le_mul_of_nonneg_left (h N hN Q d (hd d hm) (hscale d hm)
          (ha d hm) cs hn) hw
      _ = epsilon*(sigma d*(thetaConversion N d*rawScale N Q d)) := by ring
      _ = _ := by rw [rawScale,hconvert]
  have hs := sum_le_sum (s := D) hp
  simpa only [convertedUnit, ← mul_sum, ← Theta_eq_sum_atoms] using hs

/-- Both repeated 112 and 122 occurrences are charged twice; 18 atoms
receive epsilon/18, hence one epsilon times the unchanged original Theta. -/
theorem original_Gamma9_to_19_unit_theta_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      originalShortUnits N Q D sigma ≤ epsilon*Theta N Q D sigma := by
  obtain ⟨T,hT,h⟩ := short_word_theta_upper heta (show 0 < epsilon/18 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN Q D sigma hd hsigma hscale ha
  let F := convertedUnit N Q D sigma
  let E := (epsilon/18)*Theta N Q D sigma
  have hword (j : Fin 11) (cs : List ℕ)
      (hc : cs ∈ secondFunctionalMotherGammaWords (9+j.val)) : F cs ≤ E :=
    h N hN Q D sigma hd hsigma hscale ha cs (original_short_arity j hc)
  have hlist (ws : List (List ℕ)) : (∀ cs ∈ ws, F cs ≤ E) →
      (ws.map F).sum ≤ (ws.length : ℝ)*E := by
    induction ws with
    | nil => intro _; simp
    | cons w ws ih =>
      intro hw
      have hw0 := hw w (by simp)
      have ht := ih (fun v hv => hw v (by simp [hv]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith
  have hs := sum_le_sum (s := (univ : Finset (Fin 11))) (fun j _ =>
    hlist (secondFunctionalMotherGammaWords (9+j.val)) (hword j))
  have hcount : (∑ j : Fin 11, ((secondFunctionalMotherGammaWords (9+j.val)).length : ℝ)) = 18 := by
    norm_num [Fin.sum_univ_succ,secondFunctionalMotherGammaWords]
  rw [← sum_mul,hcount] at hs
  change originalShortUnits N Q D sigma ≤ 18*E at hs
  have heq : 18*E = epsilon*Theta N Q D sigma := by dsimp [E]; ring
  rwa [heq] at hs

end
end ImbalancedChen.P2EnhancedShortWordUnitTheta
