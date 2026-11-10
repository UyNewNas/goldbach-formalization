import ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient
import ImbalancedChen.P4AFull87PhysicalReserveFromRate

namespace ImbalancedChen.P4AOrderedThirdRoughCutTransport
noncomputable section
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy (Root current policy)
open P4AOriginalOrderedThirdTable (rawExponent)
open P4AUpperTaggedParityCompiler
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)
open scoped Classical BigOperators

abbrev F (delta : ℝ) (n : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) := policy delta n d w N false

theorem active_iff_length {N w : ℝ} {pre : List ℕ} (hp : ∀ p∈pre,N^w≤(p:ℝ)) :
    HistoricalThirdCoarse.active w N pre ↔ pre.length=3 := by
  exact ⟨And.left,fun h => ⟨h,hp _ (primeHistoryTuple_mem h 2)⟩⟩

theorem root_cut {N w : ℝ} (hN : 1≤N) (hw : 0≤w) (d : OriginalData) (pre : List ℕ)
    (hp : ∀ p∈pre,N^w≤(p:ℝ)) : current d w N pre=current d 0 N pre := by
  let a := rosserAncestor 3 pre
  have ha (p : ℕ) (h : p∈a) := hp p ((List.drop_sublist _ _).subset h)
  have ha0 (p : ℕ) (h : p∈a) : N^(0:ℝ)≤(p:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hN hw).trans (ha p h)
  have h := (active_iff_length ha).trans (active_iff_length ha0).symm
  simp only [current,rawExponent,show HistoricalThirdCoarse.active w N (rosserAncestor 3 pre) ↔
    HistoricalThirdCoarse.active 0 N (rosserAncestor 3 pre) from h]

theorem policy_cut (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    {w : ℝ} (hw : 0≤w) (p : List ℕ) (hp : ∀ x∈p,(N:ℝ)^w≤(x:ℝ)) :
    F delta n d w N p=F delta n d 0 N p := by
  simp only [F,policy,root_cut (by exact_mod_cast hN) hw d p hp]

theorem selection_cut (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    {w : ℝ} (hw : 0≤w) (xs pre : List ℕ) (pos : Bool)
    (hxs : ∀ x∈xs,(N:ℝ)^w≤(x:ℝ)) (hpre : ∀ x∈pre,(N:ℝ)^w≤(x:ℝ)) :
    FirstExitValidSelection (oddFirstExitPolicy (F delta n d w N)) pre pos xs ↔
      FirstExitValidSelection (oddFirstExitPolicy (F delta n d 0 N)) pre pos xs := by
  induction xs generalizing pre pos with
  | nil => rfl
  | cons x xs ih =>
    have hp (y : ℕ) (hy : y∈x::pre) : (N:ℝ)^w≤(y:ℝ) := by
      rcases List.mem_cons.mp hy with rfl|hy
      · exact hxs _ List.mem_cons_self
      · exact hpre y hy
    simp only [FirstExitValidSelection,oddFirstExitPolicy,policy_cut delta n d hN hw (x::pre) hp]
    exact and_congr_right (fun _ => ih _ _ (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hp)

theorem support_cut (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    (cap : ℕ) {w : ℝ} (hw : 0≤w) (z : ℝ) :
    rawSupport (F delta n d w N) N cap ((N:ℝ)^w) z=rawSupport (F delta n d 0 N) N cap ((N:ℝ)^w) z := by
  ext x
  rw [raw_support_iff_canonical_validSelection,raw_support_iff_canonical_validSelection]
  apply and_congr_right
  intro hx
  have hs := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap _ z hx).1
  exact selection_cut delta n d hN hw _ [] true
    (fun p hp => mem_roughPrimeUniverse_lower (hs.subset hp)) (by simp)

theorem rough_equal (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    (cap : ℕ) {w : ℝ} (hw : 0≤w) (z tau L : ℝ) (tag : ℕ → List Bool) :
    let B := (N:ℝ)^w
    let Fw := F delta n d w N
    let F0 := F delta n d 0 N
    P4AUpperTaggedBetaAttachment.rho Fw tag N cap B z tau L=P4AUpperTaggedBetaAttachment.rho F0 tag N cap B z tau L ∧
    changedMass Fw tag N cap B z tau=changedMass F0 tag N cap B z tau ∧
    P4AFiniteCapTaggedConstructor.compilerExpense Fw tag N cap B z tau L=
      P4AFiniteCapTaggedConstructor.compilerExpense F0 tag N cap B z tau L ∧
    p4aReserveRawDensity Fw N cap B z=p4aReserveRawDensity F0 N cap B z := by
  let Fw := F delta n d w N
  let F0 := F delta n d 0 N
  let B := (N:ℝ)^w
  have hs : rawSupport Fw N cap B z=rawSupport F0 N cap B z := support_cut delta n d hN cap hw z
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
theorem projected_cut (delta : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1≤N)
    (cap : ℕ) {w : ℝ} (hw : 0≤w) (z : ℝ) (hz : (N:ℝ)^w≤z) :
    let Fw := F delta n d w N
    let F0 := F delta n d 0 N
    p4aReserveRawDensity Fw N cap 0 z-p4aActualPresieveCorrection Fw N cap ((N:ℝ)^w) z=
    p4aReserveRawDensity F0 N cap 0 z-p4aActualPresieveCorrection F0 N cap ((N:ℝ)^w) z := by
  dsimp only
  rw [p4a_fullRaw_eq_euler_presieved_add_correction _ _ _ _ _ hz,
    p4a_fullRaw_eq_euler_presieved_add_correction (F delta n d 0 N) _ _ _ _ hz,
    (rough_equal delta n d hN cap hw z 1 1 (fun _ => [])).2.2.2]
  ring

end
end ImbalancedChen.P4AOrderedThirdRoughCutTransport

