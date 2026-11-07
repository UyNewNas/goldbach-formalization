import ImbalancedChen.P2CausalMarkedThetaSupply
import ImbalancedChen.Part5OriginalH430NativeQueryPaths

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original component LIST is evaluated on the actual generated prime
carriers. The fixed W2 entries retain distinct argument tags even though
their integer prefix is unchanged. The finite Q10 count theorem is then
instantiated at every product in the generated marked support. None of
this identifies the immutable arithmetic iterate with a saved H/h table.
-/

namespace ImbalancedChen.P2CausalBankOccurrenceBinding
noncomputable section
open Finset Wu2008DoubleSieve
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2EnhancedLowerPhysicalTransition P5OriginalActionMassBound
open Part5OriginalH430NativeQueryPaths
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2OriginalW2CountTupleReindex P2OriginalW2MotherOccurrenceReindex
open P2OriginalW2ComplementAction P2FrozenReceiverCountActions
open P2OriginalHalfOpenProfileCarrier P2OriginalBankChildPrimeMass
open P2AllW1SameQRawCountInduction
open P2OriginalLiteralW1OldProfile P2OriginalProfileThetaNormalization
open P2OriginalChildPhysicalNormalization P2OriginalBankOldProfilePassage
open scoped Classical BigOperators

def parentTest (m : Mark) (N : ℕ) (nu : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ t ∈ m.source N nu, m.weight*G (Part3.labelledProduct t)

def singleTest (m : Mark) (N : ℕ) (nu : ℝ) (rule : SingleRule) (G : ℕ → ℝ) : ℝ :=
  ∑ old ∈ m.source N nu,
    ∑ t ∈ singleFamily rule N ((N : ℝ)^nu) old (m.history.ceiling m.ceiling old),
      m.weight*G (Part3.labelledProduct t)

def pairTest (m : Mark) (N : ℕ) (nu : ℝ) (bank : Fin 36) (piece : Fin 4)
    (G : ℕ → ℝ) : ℝ :=
  ∑ old ∈ m.source N nu,
    ∑ t ∈ pairFamily bank piece N ((N : ℝ)^nu) old (m.history.ceiling m.ceiling old),
      m.weight*G (Part3.labelledProduct t)

/-- G is indexed by the entire component, so fixed s0/phi1 queries and
the three singleton/four pair positions cannot be accidentally merged. -/
def componentTest (m : Mark) (N : ℕ) (nu : ℝ) (G : StepShape → ℕ → ℝ)
    (shape : StepShape) : ℝ :=
  match shape with
  | .w1Singleton i j => singleTest m N nu (.w1 i j) (G shape)
  | .w2Singleton bank piece => singleTest m N nu (.w2 bank piece) (G shape)
  | .w2Pair bank piece => pairTest m N nu bank piece (G shape)
  | _ => parentTest m N nu (G shape)

/-- Direct instance of the original two-entry W1 list. The /2 is used
once here; raw childTest carries only the incoming history scalar. -/
theorem W1_actual_occurrences (m : Mark) (N : ℕ) (nu : ℝ)
    (i : Fin 7) (j : Fin 10) (G : StepShape → ℕ → ℝ) :
    componentSum (.inl (i,j)) (componentTest m N nu G) =
      parentTest m N nu (G (.w1Fixed i j)) +
      singleTest m N nu (.w1 i j) (G (.w1Singleton i j))/2 := by
  exact W1_components_exact i j (componentTest m N nu G)

/-- Direct instance of the nine-entry W2 list. In particular 4H(s0),
H(phi1), all three singleton slots and all four pair slots survive. -/
theorem W2_actual_occurrences (m : Mark) (N : ℕ) (nu : ℝ)
    (bank : Fin 36) (G : StepShape → ℕ → ℝ) :
    componentSum (.inr bank) (componentTest m N nu G) =
      (4*parentTest m N nu (G (.w2Fixed bank true)) +
        parentTest m N nu (G (.w2Fixed bank false)) +
        (∑ piece : Fin 3, singleTest m N nu (.w2 bank piece) (G (.w2Singleton bank piece))) +
        (∑ piece : Fin 4, pairTest m N nu bank piece (G (.w2Pair bank piece))))/5 := by
  exact W2_components_exact bank (componentTest m N nu G)

theorem actual_sameQ {N d : ℕ} (hN : 1 < N) (hd : 0 < d) (nu : ℝ) :
    (N : ℝ)^nu = (d : ℝ)*(N : ℝ)^(residualExponent N d nu) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have he : (N : ℝ)^(residualExponent N d nu) = (N : ℝ)^nu/d := by
    apply Real.log_injOn_pos (Real.rpow_pos_of_pos hN0 _)
      (div_pos (Real.rpow_pos_of_pos hN0 _) hd0)
    rw [Real.log_rpow hN0,residual_log hN hd]
    ring
  rw [he]
  field_simp [hd0.ne']

/-- The existing W1 half-open d*N-mask profile theorem is applied to
this actual source, separately from the open child constructor. This
retains its already-paid prefix/endpoint correction and same-Q atom.
It is a mass/profile passage, not a licence for the old H/h arrays. -/
theorem actual_source_W1_profile {eta epsilon : ℝ} (he : 0 < eta)
    (heps : 0 < epsilon) (horizon : ℕ) (oldH oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark),
      (∀ i ∈ A, (marks i).BoxRows nu eta horizon) →
      ∀ i : Fin 7, ∀ j : Fin 10,
      let D := sourceSupport A marks N nu
      let sigma := sourceSigma A marks N nu
      |(∑ d ∈ D, sigma d*literalW1ThetaOldProfile N ((N : ℝ)^nu) d i j oldH oldh) -
        Theta N ((N : ℝ)^nu) D sigma*W1OldIntegral i j oldH oldh| ≤
        epsilon*Theta N ((N : ℝ)^nu) D sigma := by
  have hfloor := floorAt_pos he horizon
  obtain ⟨T0,hprofile⟩ := all70_literal_sameQ_Theta_profile_passage
    hfloor (le_max_right (1 : ℝ) (floorAt eta horizon)) heps oldH oldh
  refine ⟨max 4 T0,le_max_left _ _,?_⟩
  intro N hN nu hnu I A marks hm i j
  have hN1 : 1 < N := by omega
  have hs := source_support_data hN1 he A marks hm
  have hres (d : ℕ) (hd : d ∈ sourceSupport A marks N nu) :
      residualExponent N d nu ∈ Set.Icc (floorAt eta horizon) (max 1 (floorAt eta horizon)) := by
    obtain ⟨a,ha,hd'⟩ := mem_biUnion.mp hd
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hd'
    have hf := facts_trueAlpha hN1 hfloor ((marks a).source_facts hN1 he (hm a ha) ht)
    have hd1 : (1 : ℝ) ≤ Part3.labelledProduct t := by exact_mod_cast hf.1
    have hb : 0 ≤ prefixExponent N (Part3.labelledProduct t) :=
      div_nonneg (Real.log_nonneg hd1) (Real.log_pos (by exact_mod_cast hN1)).le
    refine ⟨by linarith only [hf.2.1,hfloor],?_⟩
    have hu : residualExponent N (Part3.labelledProduct t) nu ≤ 1 := by
      unfold residualExponent
      linarith only [hnu,hb]
    exact hu.trans (le_max_left _ _)
  have ha (d : ℕ) (hd : d ∈ sourceSupport A marks N nu) :
      2 ≤ P2OriginalChildPhysicalNormalization.alpha
        (Real.log (d : ℝ)/Real.log (N : ℝ)) (residualExponent N d nu) := by
    have h := (hs hd).2.2.2
    rw [trueAlpha_eq hN1 (hs hd).1 nu] at h
    exact h
  have h := hprofile N ((le_max_right _ _).trans hN) ((N : ℝ)^nu)
    (sourceSupport A marks N nu) (fun d => residualExponent N d nu) (fun d => d)
    (sourceSigma A marks N nu) hres (fun d hd => (hs hd).1)
    (fun d hd => actual_sameQ hN1 (hs hd).1 nu)
    (fun d _ => sourceSigma_nonneg A marks N nu (fun a ha => (hm a ha).2.2.2.2) d)
    ha i j
  simpa only [Theta_eq_sum_atoms] using h

/-- Q10's full finite W2 theorem at an actual generated source product.
The N-window mother is kept, including rejected pairs and collisions in
countRemainder. It is not replaced by the collision-free history child.
This is reuse of Q10, not a new analytic old-generation count licence. -/
theorem actual_source_W2_tuple_upper {I : Type*} {N horizon : ℕ}
    (hN : 1 < N) {nu eta : ℝ} (he : 0 < eta)
    (A : Finset I) (marks : I → Mark) (hm : ∀ i ∈ A, (marks i).BoxRows nu eta horizon)
    {d : ℕ} (hd : d ∈ sourceSupport A marks N nu)
    (bank : List P2ActualMarkedCountState.Query) (rounds : ℕ) (j : Fin 36) :
    let Q := (N : ℝ)^nu
    let L := residualExponent N d nu
    let old := P2AllW2ImmutableCountRecursion.iterate N Q
      (P5OriginalU5FrozenSource.receiver N) bank rounds
    (frozenCount N d (P5OriginalU5FrozenSource.receiver N)
      (cutoff Q d (originalW2At j).s) : ℝ) ≤
      (4*old.upper d (cutoff Q d (originalW2At j).s0) +
        old.upper d (cutoff Q d (originalW2At j).phi1) +
        (∑ k : Fin 4,
          ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
            if normalizedLog N L p ∈ pairHalf (originalW2At j) k then
              old.upper (d*p 0*p 1)
                (occurrenceCutoff Q d (originalW2At j) k (p 0) (p 1)) else 0) +
        countRemainder N Q old d (originalW2At j))/5 + W2Charge N Q d j/5 := by
  obtain ⟨i,hi,hdi⟩ := mem_biUnion.mp hd
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hdi
  have hf := (marks i).source_facts hN he (hm i hi) ht
  have hpos := floorAt_pos he horizon
  have h := facts_trueAlpha hN hpos hf
  have hL : 0 < residualExponent N (Part3.labelledProduct t) nu := by
    linarith only [h.2.1,hpos]
  exact iterate_original_W2_count_tuple_upper hN h.1 hL
    (actual_sameQ hN h.1 nu) bank rounds j

end
end ImbalancedChen.P2CausalBankOccurrenceBinding
