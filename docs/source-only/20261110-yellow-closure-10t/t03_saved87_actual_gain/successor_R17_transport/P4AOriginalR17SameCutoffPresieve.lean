import ImbalancedChen.P4AOriginalR17Full87SavedEndpoint

/-! The single positive presieve and the runtime ordered-third policy use
the same exponent omega = nu * beta². Beta is chosen below the already
fixed positive historical cutoff before the arithmetic target. -/
namespace ImbalancedChen.P4AOriginalR17SameCutoffPresieve
noncomputable section
open scoped Classical BigOperators
open P4AOriginalR17EighthParent (orderedSixth orderedEighth)
open P4AOriginalR17Full87SavedEndpoint (Ordinary original_ordinary_source original_ordinary_saved)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87Saved86 (savedGain)
open P4AOriginalVariableFifthPhysicalLedger (raw physical)
open P5OriginalCommonPositivePresieve (normalize)

def SameCutoff (gain nu eps : ℝ) : Prop :=
  ∃ r0 : ℕ, ∀ r : ℕ, r0≤r → ∃ n0 : ℕ, ∀ n : ℕ, n0≤n →
  ∃ e0 : ℝ, 0<e0 ∧ ∀ e : ℚ, 0<e → (e:ℝ)<e0 →
  ∃ q0 : ℕ, 0<q0 ∧ ∀ q : ℕ, q0≤q → ∀ a : ℝ, 0<a → a≤1/100 →
  ∀ betaMax : ℝ, 0<betaMax →
  ∃ beta : ℝ, 0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ nu*beta^2<a ∧ beta^2≤(19/96:ℝ)/nu ∧
  ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N → Even N →
  ∀ cap : ℕ, (N:ℝ)^(19/96:ℝ)≤cap →
    let omega := nu*beta^2
    let w := (N:ℝ)^omega
    let z := (N:ℝ)^(19/96:ℝ)
    let L := (N:ℝ)^(nu*beta)
    1<w ∧ w≤z ∧ normalize N (physical (orderedEighth r n e q a omega N) N cap w z L) <
      normalize N (raw (orderedSixth n e q a omega N) N cap 0 z)-gain+eps

private theorem project (gain nu eps : ℝ) (hnu : 0<nu) (heps : 0<eps)
    (hOrd : Ordinary gain (eps/2)) : SameCutoff gain nu eps := by
  have hnr : nu*((19/96:ℝ)/nu)=(19/96:ℝ) := by field_simp [hnu.ne'] <;> ring
  obtain ⟨r0,hr⟩ := hOrd
  refine ⟨r0,?_⟩
  intro r hrr
  obtain ⟨n0,hn⟩ := hr r hrr
  refine ⟨n0,?_⟩
  intro n hnn
  obtain ⟨e0,he0,he⟩ := hn n hnn
  refine ⟨e0,he0,?_⟩
  intro e hep hee
  obtain ⟨q0,hq0,hq⟩ := he e hep hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq a ha ha1 betaMax hmax
  obtain ⟨Na,hNa,hold⟩ := hq q hqq a ha1
  obtain ⟨beta,hb,hb8,hbm,hbr,Nb,_,hbeta⟩ := exists_actualSmallRoughRho_density_le_full_reserve
    nu ((19/96:ℝ)/nu) (eps/2) (min betaMax (a/nu)) hnu (div_pos (by norm_num) hnu)
    (half_pos heps) (lt_min hmax (div_pos ha hnu))
  have hb1 : beta<1 := hb8.trans (by norm_num)
  have hsq : beta^2<beta := by nlinarith only [mul_pos hb (sub_pos.mpr hb1)]
  have hba : beta<a/nu := hbm.trans_le (min_le_right _ _)
  have hw : nu*beta^2<a := by
    rw [mul_comm]
    exact (lt_div_iff₀ hnu).mp (hsq.trans hba)
  refine ⟨beta,hb,hb8,hbm.trans_le (min_le_left _ _),hw,hbr,
    max Na Nb,hNa.trans (le_max_left _ _),?_⟩
  intro N hN hEven cap hcap
  have h2 : 2≤N := hNa.trans ((le_max_left _ _).trans hN)
  have hNr : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hz := Real.rpow_le_rpow_of_exponent_le hNr.le
    (show VariableEnvelope.mu≤(19/96:ℝ) by norm_num [VariableEnvelope.mu])
  have hraw := hold N ((le_max_left _ _).trans hN) hEven (nu*beta^2) hw.le cap _ hz hcap
  rw [P5OriginalCommonPositivePresieve.normalize_sub] at hraw
  let S := orderedEighth r n e q a (nu*beta^2) (N:ℝ)
  have hres := hbeta N ((le_max_right _ _).trans hN) hEven cap
    (by simpa only [hnr] using hcap) (S false)
  dsimp only at hres
  simp only [hnr] at hres
  change physical S N cap ((N:ℝ)^(nu*beta^2)) ((N:ℝ)^(19/96:ℝ)) ((N:ℝ)^(nu*beta)) ≤
    raw S N cap 0 ((N:ℝ)^(19/96:ℝ))+(eps/2)*singularSeries N/Real.log (N:ℝ) at hres
  have hnorm := P5OriginalCommonPositivePresieve.normalize_mono N h2 hres
  rw [P5OriginalCommonPositivePresieve.normalize_add,
    P5OriginalCommonPositivePresieve.normalize_reserve N h2] at hnorm
  refine ⟨Real.one_lt_rpow hNr (mul_pos hnu (sq_pos_of_pos hb)),?_,?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hNr.le
    simpa only [hnr] using mul_le_mul_of_nonneg_left hbr hnu.le
  · dsimp only [S] at hnorm
    linarith only [hnorm,hraw]

theorem original_source (nu eps : ℝ) (hnu : 0<nu) (heps : 0<eps) :
    SameCutoff (∑ c : Cell,cellIntegral c) nu eps :=
  project _ _ _ hnu heps (original_ordinary_source (eps/2) (half_pos heps))

theorem original_saved (nu eps : ℝ) (hnu : 0<nu) (heps : 0<eps) :
    SameCutoff (savedGain:ℝ) nu eps :=
  project _ _ _ hnu heps (original_ordinary_saved (eps/2) (half_pos heps))

end
end ImbalancedChen.P4AOriginalR17SameCutoffPresieve
