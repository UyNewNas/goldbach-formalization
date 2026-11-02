import ImbalancedChen.P2EnhancedNonunitWordMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Positive marked lifting of the proved ordinary rough nonunit supplier.
This is a converted arithmetic raw mass. It is NOT a same-rho density
identity, a positive-product estimate, or a K/4 count licence.
-/

namespace ImbalancedChen.P2EnhancedNonunitMarkedMass
noncomputable section
open Real Finset Set Wu2008DoubleSieve
open P2EnhancedSwitchedUnsiftedSource P2EnhancedSwitchedTrueNormalization
open P2EnhancedNonunitPhysicalQuadrature P2EnhancedNonunitLabelGeometry
open P2EnhancedNonunitWordMass
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open scoped Classical BigOperators

def penultimate (c : ℕ) (cs : List ℕ) : Fin (c::cs).length :=
  ⟨(c::cs).length-2, by simp only [List.length_cons]; omega⟩

def nonunitIntegral (w : List ℕ) (alpha : ℝ) : ℝ :=
  match w with
  | [] => 0
  | c::cs => wordIntegral c cs (penultimate c cs) alpha

theorem selected_penultimate (N d : ℕ) (Q : ℝ) (c : ℕ) (cs : List ℕ) :
    selectedWord N Q d (c::cs) (penultimate c cs) = ordinaryNonunitWord N Q d (c::cs) := by
  unfold selectedWord ordinaryNonunitWord
  apply sum_congr rfl
  intro l hl
  rw [(label_data hl).1]
  rfl

theorem original_word_upper (w : List ℕ) (hw : w ≠ [])
    {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      0 < d → (N : ℝ)^eta ≤ Q/d → 2 ≤ trueAlpha N Q d →
      ordinaryNonunitWord N Q d w ≤
        rawScale N Q d * (nonunitIntegral w (trueAlpha N Q d) + epsilon) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons c cs =>
    obtain ⟨T, hT, h⟩ := actual_selected_word_upper c cs (penultimate c cs) heta he
    refine ⟨T, hT, ?_⟩
    intro N hN Q d hd hscale ha
    simpa only [selected_penultimate, nonunitIntegral] using h N hN Q d hd hscale ha

def convertedWord (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (w : List ℕ) : ℝ :=
  ∑ d ∈ D, sigma d * thetaConversion N d * ordinaryNonunitWord N Q d w

/-- The source threshold precedes every finite marked family. Original
sigma and d-dependent alpha are retained; total Theta may be zero. -/
theorem original_word_theta_upper (w : List ℕ) (hw : w ≠ [])
    {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      convertedWord N Q D sigma w ≤ thetaPayload N Q D sigma (nonunitIntegral w) +
        epsilon * Theta N Q D sigma := by
  obtain ⟨T, hT, h⟩ := original_word_upper w hw heta he
  refine ⟨T, hT, ?_⟩
  intro N hN Q D sigma hd hsigma hscale ha
  have hN4 := hT.trans hN
  have hR (d : ℕ) (hm : d ∈ D) : 1 < Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le (hscale d hm)
  have hp (d : ℕ) (hm : d ∈ D) :
      sigma d * thetaConversion N d * ordinaryNonunitWord N Q d w ≤
        sigma d * thetaAtom N Q d * (nonunitIntegral w (trueAlpha N Q d) + epsilon) := by
    have hweight := mul_nonneg (hsigma d hm)
      (P2EnhancedUnitSourceMass.thetaConversion_nonneg hN4 (hd d hm) (hR d hm))
    have hsource := h N hN Q d (hd d hm) (hscale d hm) (ha d hm)
    calc
      _ ≤ sigma d * thetaConversion N d *
          rawMainAtom N Q d (fun alpha => nonunitIntegral w alpha + epsilon) := by
        simpa only [rawMainAtom, rawScale] using mul_le_mul_of_nonneg_left hsource hweight
      _ = sigma d * (thetaConversion N d *
          rawMainAtom N Q d (fun alpha => nonunitIntegral w alpha + epsilon)) := by ring
      _ = _ := by rw [rawMainAtom_to_thetaAtom (by omega : 0 < N) (hd d hm) Q (hR d hm)]; ring
  have hs := sum_le_sum (s := D) hp
  simpa only [convertedWord, thetaPayload, mul_add, sum_add_distrib,
    ← sum_mul, ← Theta_eq_sum_atoms, mul_comm (Theta N Q D sigma) epsilon] using hs

/-- The finite set is used only for choosing a common threshold.
Arithmetic and integral aggregation below still use the literal lists. -/
def thresholdWords : Finset (List ℕ) :=
  univ.biUnion (fun j : Fin 13 => (secondFunctionalMotherGammaWords (9+j.val)).toFinset)

theorem occurrence_mem_threshold {j : Fin 13} {w : List ℕ}
    (hw : w ∈ secondFunctionalMotherGammaWords (9+j.val)) : w ∈ thresholdWords := by
  exact mem_biUnion.mpr ⟨j, mem_univ _, List.mem_toFinset.mpr hw⟩

theorem threshold_word_nonempty {w : List ℕ} (hw : w ∈ thresholdWords) : w ≠ [] := by
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp hw
  have hlist := List.mem_toFinset.mp hj
  intro he
  subst w
  fin_cases j <;> simp [secondFunctionalMotherGammaWords] at hlist

/-- All 20 occurrences share one tolerance and one pre-N threshold;
repeated 112 and 122 occurrences are never deduplicated in a source sum. -/
theorem all_original_word_theta_upper {eta epsilon : ℝ}
    (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      ∀ j : Fin 13, ∀ w ∈ secondFunctionalMotherGammaWords (9+j.val),
        convertedWord N Q D sigma w ≤ thetaPayload N Q D sigma (nonunitIntegral w) +
          (epsilon/20) * Theta N Q D sigma := by
  have he20 : 0 < epsilon/20 := by positivity
  have hall (w : thresholdWords) := original_word_theta_upper w.val
    (threshold_word_nonempty w.property) heta he20
  choose T hT hupper using hall
  let T0 := max 4 (univ.sup T)
  refine ⟨T0, le_max_left _ _, ?_⟩
  intro N hN Q D sigma hd hsigma hscale ha j w hw
  let w' : thresholdWords := ⟨w, occurrence_mem_threshold hw⟩
  have hsmall : T w' ≤ T0 :=
    (le_sup (mem_univ w')).trans (le_max_right _ _)
  exact hupper w' N (hsmall.trans hN) Q D sigma hd hsigma hscale ha

def convertedOriginalSwitches (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ j : Fin 13, ((secondFunctionalMotherGammaWords (9+j.val)).map
    (convertedWord N Q D sigma)).sum

def originalIntegralSwitches (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ j : Fin 13, ((secondFunctionalMotherGammaWords (9+j.val)).map
    (fun w => thetaPayload N Q D sigma (nonunitIntegral w))).sum

/-- The final error is epsilon times the original Theta, not 13 epsilon
or 20 epsilon. The literal Gamma-word lists retain repeated occurrences. -/
theorem original_Gamma9_to_21_theta_upper {eta epsilon : ℝ}
    (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      convertedOriginalSwitches N Q D sigma ≤ originalIntegralSwitches N Q D sigma +
        epsilon * Theta N Q D sigma := by
  obtain ⟨T, hT, h⟩ := all_original_word_theta_upper heta he
  refine ⟨T, hT, ?_⟩
  intro N hN Q D sigma hd hsigma hscale ha
  have hwords := h N hN Q D sigma hd hsigma hscale ha
  let F := convertedWord N Q D sigma
  let I := fun w => thetaPayload N Q D sigma (nonunitIntegral w)
  let E := (epsilon/20)*Theta N Q D sigma
  have hlist (ws : List (List ℕ)) : (∀ w ∈ ws, F w ≤ I w + E) →
      (ws.map F).sum ≤ (ws.map I).sum + (ws.length : ℝ)*E := by
    induction ws with
    | nil => intro _; simp
    | cons w ws ih =>
      intro hw
      have hw0 := hw w (by simp)
      have htail := ih (fun v hv => hw v (by simp [hv]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
  have hs := sum_le_sum (s := (univ : Finset (Fin 13))) (fun j _ =>
    hlist (secondFunctionalMotherGammaWords (9+j.val)) (hwords j))
  have hcount : (∑ j : Fin 13, ((secondFunctionalMotherGammaWords (9+j.val)).length : ℝ)) = 20 := by
    norm_num [Fin.sum_univ_succ, secondFunctionalMotherGammaWords]
  rw [sum_add_distrib, ← sum_mul, hcount] at hs
  change convertedOriginalSwitches N Q D sigma ≤ originalIntegralSwitches N Q D sigma + 20*E at hs
  have heq : 20*E = epsilon*Theta N Q D sigma := by dsimp [E]; ring
  rwa [heq] at hs

end
end ImbalancedChen.P2EnhancedNonunitMarkedMass
