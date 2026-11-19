import ImbalancedChen.P4AOriginalFiniteFallbackPolicy

namespace ImbalancedChen.P4AOriginalFiniteFallbackProjection
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackPolicy (F policy_cut)
open P4AUpperTaggedParityCompiler
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)

theorem selection_cut (T : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    {w : ℝ} (hw : 0≤w) (xs pre : List ℕ) (pos : Bool)
    (hxs : ∀ x∈xs,(N:ℝ)^w≤(x:ℝ)) (hpre : ∀ x∈pre,(N:ℝ)^w≤(x:ℝ)) :
    FirstExitValidSelection (oddFirstExitPolicy (F T delta n d w N)) pre pos xs ↔
      FirstExitValidSelection (oddFirstExitPolicy (F T delta n d 0 N)) pre pos xs := by
  induction xs generalizing pre pos with
  | nil => rfl
  | cons x xs ih =>
    have hp (y : ℕ) (hy : y∈x::pre) : (N:ℝ)^w≤(y:ℝ) := by
      rcases List.mem_cons.mp hy with rfl|hy
      · exact hxs _ List.mem_cons_self
      · exact hpre y hy
    simp only [FirstExitValidSelection,oddFirstExitPolicy,policy_cut T delta n d hN hw (x::pre) hp]
    exact and_congr_right (fun _ => ih _ _ (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hp)

theorem support_cut (T : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    (cap : ℕ) {w : ℝ} (hw : 0≤w) (z : ℝ) :
    rawSupport (F T delta n d w N) N cap ((N:ℝ)^w) z=rawSupport (F T delta n d 0 N) N cap ((N:ℝ)^w) z := by
  ext x
  rw [raw_support_iff_canonical_validSelection,raw_support_iff_canonical_validSelection]
  apply and_congr_right
  intro hx
  have hs := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap _ z hx).1
  exact selection_cut T delta n d hN hw _ [] true
    (fun p hp => mem_roughPrimeUniverse_lower (hs.subset hp)) (by simp)

theorem rough_equal (T : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    (cap : ℕ) {w : ℝ} (hw : 0≤w) (z tau L : ℝ) (tag : ℕ → List Bool) :
    let B := (N:ℝ)^w
    let Fw := F T delta n d w N
    let F0 := F T delta n d 0 N
    P4AUpperTaggedBetaAttachment.rho Fw tag N cap B z tau L=P4AUpperTaggedBetaAttachment.rho F0 tag N cap B z tau L ∧
    changedMass Fw tag N cap B z tau=changedMass F0 tag N cap B z tau ∧
    P4AFiniteCapTaggedConstructor.compilerExpense Fw tag N cap B z tau L=
      P4AFiniteCapTaggedConstructor.compilerExpense F0 tag N cap B z tau L ∧
    p4aReserveRawDensity Fw N cap B z=p4aReserveRawDensity F0 N cap B z := by
  let Fw := F T delta n d w N
  let F0 := F T delta n d 0 N
  let B := (N:ℝ)^w
  have hs : rawSupport Fw N cap B z=rawSupport F0 N cap B z := support_cut T delta n d hN cap hw z
  have hr : raw Fw N cap B z=raw F0 N cap B z := by funext x; rw [raw_value,raw_value,hs]
  have hc : coefficient Fw tag N cap B z tau=coefficient F0 tag N cap B z tau := by
    funext x; simp only [coefficient,inner,outer,hs]
  have hb : P4AUpperTaggedBetaAttachment.rho Fw tag N cap B z tau L=
      P4AUpperTaggedBetaAttachment.rho F0 tag N cap B z tau L := by simp only [P4AUpperTaggedBetaAttachment.rho,hc]
  have hM : changedMass Fw tag N cap B z tau=changedMass F0 tag N cap B z tau := by
    simp only [changedMass,changed,outer,inner,hs]
  change fixedRoughSupport Fw N cap B z=fixedRoughSupport F0 N cap B z at hs
  change fixedRoughCoefficient Fw N cap B z=fixedRoughCoefficient F0 N cap B z at hr
  have hD : p4aReserveRawDensity Fw N cap B z=p4aReserveRawDensity F0 N cap B z := by
    simp only [p4aReserveRawDensity,hs,hr]
  have hP : p4aReservePhysicalDensity Fw N cap B z L=p4aReservePhysicalDensity F0 N cap B z L := by
    simp only [p4aReservePhysicalDensity,actualSmallRoughModuli,actualSmallRoughRho,hs,hr]
  exact ⟨hb,hM,by simp only [P4AFiniteCapTaggedConstructor.compilerExpense,hP,hD,hb],hD⟩

/-- Full small-inclusive roots have different true continuations. Only
their already projected combinations are transported across the runtime cut. -/
theorem projected_cut (T : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    (cap : ℕ) {w : ℝ} (hw : 0≤w) (z : ℝ) (hz : (N:ℝ)^w≤z) :
    let Fw := F T delta n d w N
    let F0 := F T delta n d 0 N
    p4aReserveRawDensity Fw N cap 0 z-p4aActualPresieveCorrection Fw N cap ((N:ℝ)^w) z=
    p4aReserveRawDensity F0 N cap 0 z-p4aActualPresieveCorrection F0 N cap ((N:ℝ)^w) z := by
  dsimp only
  rw [p4a_fullRaw_eq_euler_presieved_add_correction _ _ _ _ _ hz,
    p4a_fullRaw_eq_euler_presieved_add_correction (F T delta n d 0 N) _ _ _ _ hz,
    (rough_equal T delta n d hN cap hw z 1 1 (fun _ => [])).2.2.2]
  ring

end
end ImbalancedChen.P4AOriginalFiniteFallbackProjection
