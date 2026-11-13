import ImbalancedChen.Part3OriginalSwitchedHolExchange

/-! The original smooth bump and its reflected product on the full
positive same-infinity trace, before taking the exceptional projection. -/
namespace ImbalancedChen.Part3.OriginalSwitchedPrescribedTrace20261113
noncomputable section
open Set Finset Complex
open scoped BigOperators
open OriginalSameInfinityPeriodTrace20261113 (same_infinity_period_trace)
open OriginalSameInfinityWeightedHol20261113 (holSum)
open OriginalSwitchedMaassExchange20261113 (mass maass_exchange)
open OriginalSwitchedHolExchange20261113 (hol_exchange)
open OriginalSwitchedCutoffFamily20261113 (profile support)
open OriginalSwitchedCutoffModes20261113 (mode coefficient prescribed_modes)
open OriginalSameInfinityScalarGeometry20261113 (term)
open OriginalInfinitySwitchedGeometry20261113 (argument)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalFullModulusTestJets20261102 (spectralTest_tsupport_strict)

private theorem finite_window (m n : ℕ+) (s : Bool) (L Y : ℝ) (yp : 0<Y) :
    ∃ S : Finset ℕ+,∀ k∉S,
      (∀ j : ℤ,spectralTest (mode j) Y⁻¹ (argument m n k)=0) ∧
        profile s L (Y*argument m n k)=0 := by
  let A := 4*Real.pi*Real.sqrt ((m.val:ℝ)*(n.val:ℝ))
  let δ := Y⁻¹/16
  have dp : 0<δ := by dsimp [δ];positivity
  obtain ⟨T,t⟩ := exists_nat_gt (A/δ)
  let S := Finset.Icc (1:ℕ+) (⟨T+1,Nat.succ_pos _⟩:ℕ+)
  refine ⟨S,fun k hk => ?_⟩
  have gt : T<k.val := by
    by_contra! h
    exact hk (Finset.mem_Icc.mpr ⟨k.property,h.trans (Nat.le_succ _)⟩)
  have less : argument m n k<δ := by
    have bo := (div_lt_iff₀ dp).mp (t.trans (by exact_mod_cast gt : (T:ℝ)<k.val))
    exact (div_lt_iff₀ (by exact_mod_cast k.property : (0:ℝ)<k.val)).mpr (by
      simpa only [mul_comm δ (k.val:ℝ)] using bo)
  constructor
  · intro j
    by_contra nz
    exact (not_lt_of_ge less.le) (spectralTest_tsupport_strict (mode j) (inv_pos.mpr yp) (subset_tsupport _ nz)).1
  · by_contra nz
    have H := (support s L (subset_tsupport _ nz)).1
    have p := mul_lt_mul_of_pos_left less yp
    rw [show Y*δ=1/16 by dsimp [δ];field_simp [yp.ne']] at p
    linarith only [H,p]

private theorem geom_exchange (q m n : ℕ+) (s : Bool) (L Y : ℝ) (yp : 0<Y) :
    let f := fun x => profile s L (Y*x)
    Summable (fun k : ℕ+ => ‖term f q m n k‖) ∧
    HasSum (fun j : ℤ => coefficient s L j*∑' k : ℕ+,term (spectralTest (mode j) Y⁻¹) q m n k)
      (∑' k : ℕ+,term f q m n k) := by
  let f := fun x => profile s L (Y*x)
  let Φ := fun j : ℤ => spectralTest (mode j) Y⁻¹
  obtain ⟨S,h⟩ := finite_window m n s L Y yp
  have outside (k : ℕ+) (hk : k∉S) : term f q m n k=0 := by simp [term,f,(h k hk).2]
  have oj (j : ℤ) (k : ℕ+) (hk : k∉S) : term (Φ j) q m n k=0 := by simp [term,Φ,(h k hk).1 j]
  refine ⟨summable_of_hasFiniteSupport (S.finite_toSet.subset (fun k nz => by
    by_contra hk;exact nz (by rw [outside k hk,norm_zero]))),?_⟩
  have H (k : ℕ+) : HasSum (fun j => coefficient s L j*term (Φ j) q m n k) (term f q m n k) := by
    by_cases good : q.val∣k.val
    · simp only [term,if_pos good]
      exact ((prescribed_modes s L Y _ yp).mul_left _).congr_fun (fun j => by dsimp only [f,Φ];ring)
    · simp [term,good]
  have bars (j : ℤ) : (∑' k : ℕ+,term (Φ j) q m n k)=∑ k ∈ S,term (Φ j) q m n k := tsum_eq_sum (oj j)
  rw [tsum_eq_sum outside]
  apply (hasSum_sum (s:=S) (fun k _ => H k)).congr_fun
  intro j
  rw [bars,Finset.mul_sum]

/-- All positive test parameters and both positive Fourier marks at
their actual level. When s=true, L may subsequently be chosen afresh
for each m,n,d in the return trace. -/
theorem same_infinity_cutoff_trace (q m n : ℕ+) (s : Bool) (L Y : ℝ) (yp : 0<Y) :
    let f := fun x => profile s L (Y*x)
    Summable (fun k : ℕ+ => ‖term f q m n k‖) ∧
    (∑' k : ℕ+,term f q m n k)=mass q m n f+holSum q m n f := by
  obtain ⟨S,G⟩ := geom_exchange q m n s L Y yp
  have H := (maass_exchange q m n s L Y yp).add (hol_exchange q m n s L Y yp)
  refine ⟨S,G.unique (H.congr_fun ?_)⟩
  intro j
  rw [(same_infinity_period_trace q m n (mode j) (inv_pos.mpr yp)).2,mul_add] <;> rfl

end
end ImbalancedChen.Part3.OriginalSwitchedPrescribedTrace20261113
