import ImbalancedChen.P2EnhancedSeedActualFeedbackAssembly

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Same-Q geometry for ALL seven literal positive second-seed terms.
These are exact residual-exponent, comparison-cutoff, ordering and square
identities. Analytic distribution, moving-residue and enhanced count
licences remain separate obligations. No new value of lambda is asserted.
-/

namespace ImbalancedChen.P2EnhancedSeedSameQFeedbackGeometry
noncomputable section
open Set Classical
open P2EnhancedSeedSingletonPrimitive
open P2EnhancedSeedActualFeedbackAssembly (supportedPair)
open P5OriginalActionMassBound (Point W2SingletonDomain)
open P5OriginalFeedbackDomains

/-- Both fixed-profile pair terms and both moving-profile pair terms
use their ACTUAL upper arguments. Support at S gives admission below the
new smallest prime. The two square tests are at the original total level. -/
theorem all_four_pair_sameQ {nu T L chi alpha : ℝ}
    (hlevel : nu=T+L) (hL : 0<L) (hchi : L/S<chi) (ha : 2≤alpha)
    (j : Fin 4) {x : Point} (hx : x ∈ supportedPair j) :
    nu=(T+L*x 1+L*x 0)+L*(1-x 0-x 1) ∧
    0<L*(1-x 0-x 1) ∧
    (L*(1-x 0-x 1))/S≤L*x 0 ∧
    L*x 0<L*x 1 ∧ L*x 1<L/S ∧ L/S<chi ∧
    T+2*(L*x 1)<nu ∧ T+L*x 1+2*(L*x 0)<nu ∧
    alpha≤pairChildAlpha alpha x ∧ 1<pairProfile parameters j x := by
  have hD := hx.1
  have hs : pairProfile parameters j x≤S := hx.2
  have hg := W2PairDomain_geometry parameters_geometry j hD
  obtain ⟨hu,huv,hv,hgate⟩ := W2PairDomain_gates parameters_geometry j hD
  norm_num [P5OriginalActionMassBound.a0,parameters] at hu
  have hres : 0<1-x 0-x 1 := lt_of_lt_of_le (by norm_num) hg.2
  have hcut : (1-x 0-x 1)/S≤x 0 := by
    have hS : 0<S := by norm_num [S]
    fin_cases j
    · change s0*(1-x 0-x 1)≤S at hs
      have hh : (1-x 0-x 1)/S≤a0 := by
        dsimp [s0,S,a0] at *
        linarith only [hs]
      exact hh.trans hu.le
    · change s0*(1-x 0-x 1)≤S at hs
      have hh : (1-x 0-x 1)/S≤a0 := by
        dsimp [s0,S,a0] at *
        linarith only [hs]
      exact hh.trans hu.le
    · change (1-x 0-x 1)/x 0≤S at hs
      have hu0 : 0<x 0 := lt_of_lt_of_le (by norm_num) (hg.1.1 0)
      apply (div_le_iff₀ hS).mpr
      simpa only [mul_comm] using (div_le_iff₀ hu0).mp hs
    · change (1-x 0-x 1)/x 0≤S at hs
      have hu0 : 0<x 0 := lt_of_lt_of_le (by norm_num) (hg.1.1 0)
      apply (div_le_iff₀ hS).mpr
      simpa only [mul_comm] using (div_le_iff₀ hu0).mp hs
  have hvS : x 1<1/S := by
    have hv3 : x 1<(25/61 : ℝ) := by
      fin_cases j
      · have h := hD.2.2.1
        norm_num [P5OriginalActionMassBound.a2,parameters] at h
        linarith only [h]
      · have h := hD.2.2.2
        norm_num [P5OriginalActionMassBound.a3,parameters] at h
        exact h
      · have h := hD.2.2
        norm_num [P5OriginalActionMassBound.a1,parameters] at h
        linarith only [h]
      · have h := hD.2.2.2
        norm_num [P5OriginalActionMassBound.a2,parameters] at h
        linarith only [h]
    norm_num [S]
    linarith only [hv3]
  have hscaled := mul_le_mul_of_nonneg_left hcut hL.le
  have hvscaled := mul_lt_mul_of_pos_left hvS hL
  have hsquare1 := mul_lt_mul_of_pos_left hv hL
  have hsquare2 := mul_lt_mul_of_pos_left hgate hL
  refine ⟨?_,mul_pos hL hres,?_,mul_lt_mul_of_pos_left huv hL,?_,hchi,?_,?_,
    pairChildAlpha_ge_parent parameters_geometry j ha hD,
    (W2PairDomain_profile_bounds parameters_geometry j hD).1⟩
  · rw [hlevel]; ring
  · convert hscaled using 1 <;> ring
  · convert hvscaled using 1 <;> ring
  · rw [hlevel]; nlinarith only [hsquare1]
  · rw [hlevel]; nlinarith only [hsquare2]

/-- Every old specified slot above the common ceiling precedes BOTH new
pair slots. This retains old selected slots and any old third-slot cap. -/
theorem pair_slots_below_old_prefix {n : ℕ} (old : Fin n → ℝ)
    {nu T L chi alpha : ℝ} (hlevel : nu=T+L) (hL : 0<L)
    (hchi : L/S<chi) (ha : 2≤alpha) (hold : ∀ i,chi≤old i)
    (j : Fin 4) {x : Point} (hx : x ∈ supportedPair j) :
    ∀ i,L*x 0<old i ∧ L*x 1<old i := by
  have h := all_four_pair_sameQ hlevel hL hchi ha j hx
  intro i
  have hv := (h.2.2.2.2.1.trans hchi).trans_le (hold i)
  exact ⟨h.2.2.2.1.trans hv,hv⟩

/-- The singleton's own physical cutoff suffices. Its Buchstab child
keeps every argument v in [rho-1,S], including 1≤v<2. No lower-parent
admission at S has been added. The same total exponent nu is retained. -/
theorem all_three_singleton_nested_sameQ {nu T L chi alpha : ℝ}
    (hlevel : nu=T+L) (hL : 0<L) (hchi : L/S<chi) (ha : 2≤alpha)
    (j : Fin 3) {u v : ℝ} (hu : u ∈ W2SingletonDomain parameters j)
    (hv : v ∈ Icc (profile u-1) S) :
    let q := (L*(1-u))/(v+1)
    let R := (L*(1-u))*v/(v+1)
    nu=(T+L*u+q)+R ∧ 1≤v ∧ 0<R ∧ R/S≤q ∧
    q≤L*a0 ∧ L*a0<L*u ∧ L*u<L/S ∧ L/S<chi ∧
    T+2*(L*u)<nu ∧ T+L*u+2*q≤nu ∧
    alpha≤singletonChildAlpha alpha u ∧
    singletonChildAlpha alpha u≤singletonChildAlpha alpha u+
      (singletonChildAlpha alpha u-1)/v := by
  have hinherit := P2EnhancedSeedInheritedCellBounds.three_singleton_nested_cutoff
    hL hchi ha j hu hv
  have hu' := hu
  rw [original_singleton_domain] at hu'
  have huHi : u<(5/11 : ℝ) := hu'.2.trans_le (literal_bounds j).2.2.2.1
  have hp := profile_gt_two huHi.le
  have hv1 : 1≤v := by linarith only [hv.1,hp]
  have hd : 0<v+1 := by linarith only [hv1]
  have hRpos : 0<(L*(1-u))*v/(v+1) :=
    div_pos (mul_pos hinherit.1 (by linarith only [hv1])) hd
  dsimp only
  refine ⟨?_,hv1,hRpos,hinherit.2.1,hinherit.2.2.1,hinherit.2.2.2.1,
    hinherit.2.2.2.2.1,hinherit.2.2.2.2.2.1,?_,?_,
    hinherit.2.2.2.2.2.2.2.2.1,hinherit.2.2.2.2.2.2.2.2.2⟩
  · rw [hlevel]
    field_simp [hd.ne']
    <;> ring
  · rw [hlevel]
    nlinarith only [mul_pos hL (show 0<1-2*u by linarith only [huHi])]
  · rw [hlevel]
    linarith only [hinherit.2.2.2.2.2.2.1]

/-- Removing any fixed selected old subproduct subtracts the SAME
exponent A from the level and its complete-prefix square inequalities. -/
theorem pair_selected_remaining_sameQ {nu T L chi alpha A : ℝ}
    (hlevel : nu=T+L) (hL : 0<L) (hchi : L/S<chi) (ha : 2≤alpha)
    (j : Fin 4) {x : Point} (hx : x ∈ supportedPair j) :
    (T-A)+2*(L*x 1)<nu-A ∧
    (T-A)+L*x 1+2*(L*x 0)<nu-A ∧
    nu-A=((T-A)+L*x 1+L*x 0)+L*(1-x 0-x 1) := by
  have h := all_four_pair_sameQ hlevel hL hchi ha j hx
  constructor
  · linarith only [h.2.2.2.2.2.2.1]
  constructor
  · linarith only [h.2.2.2.2.2.2.2.1]
  · linarith only [h.1]

end
end ImbalancedChen.P2EnhancedSeedSameQFeedbackGeometry
