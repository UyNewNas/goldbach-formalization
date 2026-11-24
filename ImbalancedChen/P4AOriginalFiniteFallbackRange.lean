import ImbalancedChen.P4AOriginalFiniteFallbackPolicy

namespace ImbalancedChen.P4AOriginalFiniteFallbackRange
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackPolicy
open P4AOriginalFiniteFallbackBank (Bank read read_some_iff)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AFull87UnionCompilerPayment (top)
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport

def Bounded (B : Bank) : Prop :=
  (∀ t c,read B.mesh B.second t=some c → (c:ℝ)≤top) ∧
    (∀ t c,read B.mesh B.third t=some c → (c:ℝ)≤top)

theorem of_licensed {B : Bank}
    (h2 : ∀ t c,read B.mesh B.second t=some c → (c:ℝ)<VariableEnvelope.v (t 1))
    (h3 : ∀ t c,read B.mesh B.third t=some c → (c:ℝ)<VariableEnvelope.v (t 1+t 2)) :
    Bounded B := by
  have hh : VariableEnvelope.cap≤top := by norm_num [VariableEnvelope.cap,top]
  exact ⟨fun t c h => (h2 t c h).le.trans ((VariableEnvelope.v_le_cap _).trans hh),
    fun t c h => (h3 t c h).le.trans ((VariableEnvelope.v_le_cap _).trans hh)⟩

theorem chosen_le (o : Option ℚ) {x : ℝ} (hx : x≤top) (ho : ∀ c,o=some c → (c:ℝ)≤top) :
    choose o x≤top := by
  cases o with
  | none => exact hx
  | some c => exact ho c rfl

theorem upper_guard {B : Bank} (hB : Bounded B) (d : OriginalData) (he : 0≤d.e)
    (w : ℝ) (N : ℕ) (hN : (1:ℝ)≤N) (p : List ℕ) (h : upper B d w N false p=true) :
    ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) p := by
  rw [upper] at h
  split at h
  · have hp : ordinaryRosserPrefixAdmissible false ((N:ℝ)^HistoricalThirdCoarse.initial (d.e:ℝ)) p ∧
      (p.length=1 → HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m N p) := by
      simpa [HistoricalThirdCoarse.initialPolicy,oddFirstExitPolicy] using h
    exact ordinaryRosserPrefixAdmissible_mono false p (Real.rpow_le_rpow_of_exponent_le hN
      (P5Z.ActualCommonRefinedRange.initial_le_theta _ he)) hp.1
  · have h2 : secondLevel B d w N p≤top :=
      chosen_le _ (P4AOrderedThirdGlobalRange.seed_le d he w N p) (hB.1 _)
    have h3 : level B d w N p≤top := by
      unfold level
      split
      · exact h2
      · exact chosen_le _ h2 (hB.2 _)
    exact ordinaryRosserPrefixAdmissible_mono false p (Real.rpow_le_rpow_of_exponent_le hN h3)
      (by simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using h)

theorem raw_guard (B : Bank) (hB : Bounded B) (delta : ℝ) (hd : 0<delta) (n : ℕ)
    (d : OriginalData) (he : 0≤d.e) (w : ℝ) (N : ℕ) (hN : (1:ℝ)≤N) (p : List ℕ)
    (h : F B delta n d w N p=true) : ordinaryRosserPrefixAdmissible false ((N:ℝ)^top) p := by
  by_cases hh : high N p
  · exact upper_guard hB d he w N hN p (by simpa [F,policy,dispatch,hh] using h)
  · exact P4AOrderedThirdGlobalRange.raw_guard delta hd n d he w N hN p
      (by simpa [F,policy,dispatch,hh] using h)

theorem raw_range (B : Bank) (hB : Bounded B) (delta : ℝ) (hd : 0<delta) (n : ℕ)
    (d : OriginalData) (he : 0≤d.e) (w : ℝ) (N cap : ℕ) (hN : 2≤N) (omega z : ℝ) (hw : 0<omega)
    {x : ℕ} (hm : x∈rawSupport (F B delta n d w N) N cap ((N:ℝ)^omega) z) :
    x.primeFactorsList.length<J0 omega ∧ (x:ℝ)<(N:ℝ)^top := by
  let f := F B delta n d w N
  have eqv : P4AFiniteCapTaggedConstructor.keep (fun _ : Fin 1 => top) (fun _ => 0) f N=f := by
    funext p
    by_cases h : f p=true
    · have hp := raw_guard B hB delta hd n d he w N (by exact_mod_cast (show 1≤N by omega)) p h
      simpa [P4AFiniteCapTaggedConstructor.keep,P4AFiniteCapTaggedConstructor.boundedCap,top,h] using hp
    · cases hh : f p <;> simp [P4AFiniteCapTaggedConstructor.keep,hh] at h ⊢
  change x∈rawSupport f N cap ((N:ℝ)^omega) z at hm
  rw [←eqv] at hm
  exact ⟨P4AFiniteCapTaggedConstructor.raw_rank_lt _ _ _ omega hw N cap hN z hm,
    P4AFiniteCapTaggedConstructor.raw_support_lt _ _ _ N cap hN _ z hm⟩

end
end ImbalancedChen.P4AOriginalFiniteFallbackRange
