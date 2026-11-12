import ImbalancedChen.Part5OriginalH430ClassicalSmoothWordGates

/-! The literal physical test for every fixed gate, including all three
nested colour decisions and the closed penultimate comparison. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothWordPhysical
noncomputable section
open Finset Real Wu2008DoubleSieve
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)
open Part5UpperTables.OriginalU34 (clampStart)
open Part5OriginalH430ClassicalFixedClampPrimeGeometry (affine_colour_wall)
open Part5OriginalH430ClassicalSmoothWordGates
open scoped Classical BigOperators

def logPoint {s r : ℕ} (N p : ℕ) (qs : Fin s → ℕ) (rs : Fin r → ℕ) : Point s r :=
  (log (p:ℝ)/log (N:ℝ),fun i => log (qs i:ℝ)/log (N:ℝ),fun j => log (rs j:ℝ)/log (N:ℝ))

def raw {s r : ℕ} (N p : ℕ) (R : ℝ) (qs : Fin s → ℕ) (rs : Fin r → ℕ) : Gate s r → Prop
  | .outerLo => (N:ℝ)^clampStart≤(p:ℝ)
  | .outerHi => (p:ℝ)<(N:ℝ)^(1/3:ℝ)
  | .primeLo i => R^a0≤(qs i:ℝ)
  | .primeHi i => (qs i:ℝ)<R^b
  | .colourLo i j => R^(colourPower j)≤(qs i:ℝ)
  | .colourHi i j => (qs i:ℝ)<R^(colourPower j)
  | .primeOrder i j => qs i<qs j
  | .tailOrder i j => rs i≤rs j
  | .penultimate i j => qs i≤rs j

theorem raw_iff_passed {s r N p : ℕ} {qs : Fin s → ℕ} {rs : Fin r → ℕ}
    (hN : 1<N) (hp : 0<p) (hq : ∀i,0<qs i) (hr : ∀j,0<rs j) (ν : ℝ) (g : Gate s r) :
    raw N p ((N:ℝ)^ν/(p:ℝ)) qs rs g ↔ passed ν (logPoint N p qs rs) g := by
  let R := (N:ℝ)^ν/(p:ℝ)
  let t := logPoint N p qs rs
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have hL := log_pos hNr
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hout (v : ℝ) : (N:ℝ)^v≤(p:ℝ) ↔ v≤t.1 := by
    change _ ↔ v≤log (p:ℝ)/log (N:ℝ)
    rw [←log_le_log_iff (rpow_pos_of_pos h0 _) hp',log_rpow h0,le_div_iff₀ hL]
  have hout' (v : ℝ) : (p:ℝ)<(N:ℝ)^v ↔ t.1<v := by
    simpa only [not_le] using not_congr (hout v)
  have hpow (i : Fin s) (v : ℝ) : R^v≤(qs i:ℝ) ↔ 0≤powerMargin ν v t.1 (t.2.1 i) := by
    simpa only [powerMargin,sub_nonneg,logPoint,t,R] using (affine_colour_wall hN hp (hq i) ν v)
  have hpow' (i : Fin s) (v : ℝ) : (qs i:ℝ)<R^v ↔ 0< -powerMargin ν v t.1 (t.2.1 i) := by
    simpa only [not_le,neg_pos] using not_congr (hpow i v)
  have hcmp {u v : ℕ} (hu : 0<u) (hv : 0<v) :
      u≤v ↔ log (u:ℝ)/log (N:ℝ)≤log (v:ℝ)/log (N:ℝ) := by
    rw [div_le_div_iff_of_pos_right hL,log_le_log_iff (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hv)]
    exact Nat.cast_le.symm
  have hlt {u v : ℕ} (hu : 0<u) (hv : 0<v) :
      u<v ↔ log (u:ℝ)/log (N:ℝ)<log (v:ℝ)/log (N:ℝ) := by
    simpa only [not_le] using not_congr (hcmp hv hu)
  cases g with
  | outerLo => simpa only [raw,passed,openFace,margin,Bool.false_eq_true,if_false,sub_nonneg,t] using hout clampStart
  | outerHi => simpa only [raw,passed,openFace,margin,if_true,sub_pos,t] using hout' (1/3)
  | primeLo i => exact hpow i a0
  | primeHi i => exact hpow' i b
  | colourLo i j => exact hpow i (colourPower j)
  | colourHi i j => exact hpow' i (colourPower j)
  | primeOrder i j => simpa only [raw,passed,openFace,margin,if_true,sub_pos,logPoint] using hlt (hq i) (hq j)
  | tailOrder i j => simpa only [raw,passed,openFace,margin,Bool.false_eq_true,if_false,sub_nonneg,logPoint] using hcmp (hr i) (hr j)
  | penultimate i j => simpa only [raw,passed,openFace,margin,Bool.false_eq_true,if_false,sub_nonneg,logPoint] using hcmp (hq i) (hr j)

theorem literal_colours (R : ℝ) (q c : ℕ) (hc : c≤3) :
    secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) q=c ↔
      (∀ j : Fin 3,j.val<c → R^(colourPower j)≤(q:ℝ)) ∧
      (∀ j : Fin 3,j.val=c → (q:ℝ)<R^(colourPower j)) := by
  interval_cases c <;> unfold secondFunctionalMotherColour <;> split_ifs <;>
    simp_all [Fin.forall_fin_succ,colourPower,not_lt,not_le] <;> first | omega | aesop

/-- The right hand side is the raw prime-power program used in the original
sharp definition. The word C can be either of two equal marked occurrences. -/
theorem original_raw_program {s r N p : ℕ} {qs : Fin s → ℕ} {rs : Fin r → ℕ}
    (C : Fin s → ℕ) (hC : ∀i,C i≤3) (R : ℝ) :
    (∀ g∈program r C,raw N p R qs rs g) ↔
      ((N:ℝ)^clampStart≤(p:ℝ) ∧ (p:ℝ)<(N:ℝ)^(1/3:ℝ)) ∧
      (∀ i,R^a0≤(qs i:ℝ) ∧ (qs i:ℝ)<R^b) ∧
      (∀ i,secondFunctionalMotherColour (R^a1) (R^a2) (R^a3) (qs i)=C i) ∧
      (∀ i j,i<j → qs i<qs j) ∧ (∀ i j,i<j → rs i≤rs j) ∧
      (∀ i j,i.val=s-2 → qs i≤rs j) := by
  constructor
  · intro H
    have h (g : Gate s r) (hg : active C g) := H g (mem_program.mpr hg)
    refine ⟨⟨h .outerLo trivial,h .outerHi trivial⟩,fun i => ⟨h (.primeLo i) trivial,
      h (.primeHi i) trivial⟩,fun i => ?_,fun i j hij => h (.primeOrder i j) hij,
      fun i j hij => h (.tailOrder i j) hij,fun i j hij => h (.penultimate i j) hij⟩
    exact (literal_colours R (qs i) (C i) (hC i)).mpr ⟨fun j hj => h (.colourLo i j) hj,
      fun j hj => h (.colourHi i j) hj⟩
  · rintro ⟨hP,hQ,hC',hQord,hRord,hpen⟩ g hg
    have h := mem_program.mp hg
    cases g with
    | outerLo => exact hP.1
    | outerHi => exact hP.2
    | primeLo i => exact (hQ i).1
    | primeHi i => exact (hQ i).2
    | colourLo i j => exact ((literal_colours R (qs i) (C i) (hC i)).mp (hC' i)).1 j h
    | colourHi i j => exact ((literal_colours R (qs i) (C i) (hC i)).mp (hC' i)).2 j h
    | primeOrder i j => exact hQord i j h
    | tailOrder i j => exact hRord i j h
    | penultimate i j => exact hpen i j h

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothWordPhysical

