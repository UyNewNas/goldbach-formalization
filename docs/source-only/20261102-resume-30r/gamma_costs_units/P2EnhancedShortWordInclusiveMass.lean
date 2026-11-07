import ImbalancedChen.P2EnhancedShortWordUnitTheta

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Rejoin the actual paid short-word unit atoms to Q's existing ordinary
nonunit integrals. No quadrature or repeat/center proof is reconstructed.
The original reduced/grouped cap dictionary remains a separate obligation.
-/
namespace ImbalancedChen.P2EnhancedShortWordInclusiveMass
noncomputable section
open Real Finset Wu2008DoubleSieve
open P2EnhancedSwitchedTrueNormalization
open P2EnhancedNonunitLabelGeometry P2EnhancedNonunitWordMass
open P2EnhancedNonunitMarkedMass
open P2EnhancedShortWordUnitTheta
open P2OriginalChildPhysicalNormalization (Theta_eq_sum_atoms)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open scoped Classical BigOperators

def convertedOrdinary (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (cs : List ℕ) : ℝ :=
  ∑ d ∈ D, sigma d*thetaConversion N d*
    P2EnhancedReceiverRoughPurification.ordinaryWordMass N Q d cs

def originalShortOrdinary (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ j : Fin 11, ((secondFunctionalMotherGammaWords (9+j.val)).map
    (convertedOrdinary N Q D sigma)).sum

def originalShortIntegrals (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ j : Fin 11, ((secondFunctionalMotherGammaWords (9+j.val)).map
    (fun cs => thetaPayload N Q D sigma (nonunitIntegral cs))).sum

theorem convertedOrdinary_eq_unit_add_nonunit (N : ℕ) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) (hd : ∀ d ∈ D, 0 < d) (cs : List ℕ) :
    convertedOrdinary N Q D sigma cs =
      convertedUnit N Q D sigma cs + convertedWord N Q D sigma cs := by
  unfold convertedOrdinary convertedUnit convertedWord
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hm
  rw [ordinary_word_unit_nonunit (hd d hm)]
  ring

theorem originalShortOrdinary_eq (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hd : ∀ d ∈ D, 0 < d) :
    originalShortOrdinary N Q D sigma = originalShortUnits N Q D sigma +
      ∑ j : Fin 11, ((secondFunctionalMotherGammaWords (9+j.val)).map
        (convertedWord N Q D sigma)).sum := by
  unfold originalShortOrdinary originalShortUnits
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  have hlist (ws : List (List ℕ)) :
      (ws.map (convertedOrdinary N Q D sigma)).sum =
        (ws.map (convertedUnit N Q D sigma)).sum +
          (ws.map (convertedWord N Q D sigma)).sum := by
    induction ws with
    | nil => simp
    | cons cs ws ih =>
      simp only [List.map_cons,List.sum_cons,convertedOrdinary_eq_unit_add_nonunit N Q D sigma hd,ih]
      ring
  exact hlist _

/-- Inclusive ordinary raw masses now reach Q's literal nonunit word
integrals with one error budget. Every original short-word unit is paid.
The thresholds precede Q, d, marks and all 18 list occurrences. -/
theorem original_Gamma9_to_19_inclusive_theta_upper {eta epsilon : ℝ}
    (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      originalShortOrdinary N Q D sigma ≤ originalShortIntegrals N Q D sigma +
        epsilon*Theta N Q D sigma := by
  obtain ⟨Tu,hTu,hu⟩ := original_Gamma9_to_19_unit_theta_payment heta (half_pos he)
  obtain ⟨Tn,_,hn⟩ := all_original_word_theta_upper heta
    (show 0 < (5/9 : ℝ)*epsilon by positivity)
  refine ⟨max Tu Tn,hTu.trans (le_max_left _ _),?_⟩
  intro N hN Q D sigma hd hsigma hscale ha
  have hNu : Tu ≤ N := (le_max_left _ _).trans hN
  have hNn : Tn ≤ N := (le_max_right _ _).trans hN
  have hunit := hu N hNu Q D sigma hd hsigma hscale ha
  let F := convertedWord N Q D sigma
  let I := fun cs => thetaPayload N Q D sigma (nonunitIntegral cs)
  let E := (epsilon/36)*Theta N Q D sigma
  have hword (j : Fin 11) (cs : List ℕ)
      (hc : cs ∈ secondFunctionalMotherGammaWords (9+j.val)) : F cs ≤ I cs+E := by
    have hh := hn N hNn Q D sigma hd hsigma hscale ha
      (⟨j.val, by omega⟩ : Fin 13) cs hc
    convert hh using 1 <;> dsimp [F,I,E] <;> ring
  have hlist (ws : List (List ℕ)) : (∀ cs ∈ ws, F cs ≤ I cs+E) →
      (ws.map F).sum ≤ (ws.map I).sum+(ws.length : ℝ)*E := by
    induction ws with
    | nil => intro _; simp
    | cons cs ws ih =>
      intro hw
      have h0 := hw cs (by simp)
      have ht := ih (fun v hv => hw v (by simp [hv]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith
  have hs := sum_le_sum (s := (univ : Finset (Fin 11))) (fun j _ =>
    hlist (secondFunctionalMotherGammaWords (9+j.val)) (hword j))
  have hcount : (∑ j : Fin 11, ((secondFunctionalMotherGammaWords (9+j.val)).length : ℝ)) = 18 := by
    norm_num [Fin.sum_univ_succ,secondFunctionalMotherGammaWords]
  rw [sum_add_distrib,← sum_mul,hcount] at hs
  have hpay : 18*E = (epsilon/2)*Theta N Q D sigma := by dsimp [E]; ring
  rw [hpay] at hs
  rw [originalShortOrdinary_eq N Q D sigma hd]
  change originalShortUnits N Q D sigma + (∑ j : Fin 11,
    ((secondFunctionalMotherGammaWords (9+j.val)).map F).sum) ≤
      originalShortIntegrals N Q D sigma+epsilon*Theta N Q D sigma
  change (∑ j : Fin 11, ((secondFunctionalMotherGammaWords (9+j.val)).map F).sum) ≤
    originalShortIntegrals N Q D sigma+(epsilon/2)*Theta N Q D sigma at hs
  linarith

end
end ImbalancedChen.P2EnhancedShortWordInclusiveMass
