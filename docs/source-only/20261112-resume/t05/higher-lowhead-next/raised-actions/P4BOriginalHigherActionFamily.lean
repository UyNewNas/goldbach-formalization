import ImbalancedChen.P4BOriginalHigherLowAdmissible

namespace ImbalancedChen.P4BOriginalHigherActionFamily
noncomputable section
open scoped BigOperators
open Classical Filter
open P4BOriginalCollisionWords (Params)
open P4BOriginalHigherActionGroups (rule split)
open P4BOriginalHigherActionKeys (localE)
open P4BOriginalHigherLowRepresentative (d t)
open P4BOriginalHigherLowTensor (restore)
open P4BOriginalMediumAtomFamily (Index)
open P4BOriginalMediumPhysicalAtomSum (onWord)
open P4BOriginalMediumSignedFibre (scalar originalMode)
open P4BOriginalHighRankComplementBlocks (fibre cap)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalHighRankMotherMass (totalMass)
open P4BOriginalHighRankScheduledCount (outerWidth)
open P4BOuterRampRoughness (baseline)
open P5Z.HBRightClosedDyadicRoles (Block owner bank)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open PrimeProducts.MellinInsertion20261028 (exactDiscrepancy)
open P4AHeldTaggedCompilerSupport (J0)

variable {o : ℕ} {z k0 : ℝ} (I : Index o z k0)
abbrev groups := P4BOriginalHigherLowNativeAtoms.ByRule.groups rule I
abbrev firstSet := P4BOriginalHigherLowNativeAtoms.ByRule.firstSet rule I
abbrev secondSet := P4BOriginalHigherLowNativeAtoms.ByRule.secondSet rule I
abbrev thirdSet := P4BOriginalHigherLowNativeAtoms.ByRule.thirdSet rule I
abbrev atom := P4BOriginalHigherLowNativeAtoms.ByRule.atom rule I
abbrev errors := P4BOriginalHigherLowNativeAtoms.ByRule.errors rule I
abbrev pieces := P4BOriginalHigherLowRestoration.ByRule.pieces rule I

/-- The coarse fourth-row gap, the buffered fifth bank, the sixth grid
and the eighth trim are all fixed before the single fine PP choice. -/
theorem pre_target (e : ℚ) (he : 0<e) (r n : ℕ) {extra : ℝ} (h : 0<extra) :
    ∃ z : ℝ,0<z ∧ z≤extra ∧ z≤1/20000 ∧ z≤P4BOriginalHigherActionMargins.reserve e r n/4/512 := by
  let G := P4BOriginalHigherActionMargins.reserve e r n
  have hG : 0<G := (P4BOriginalHigherActionMargins.reserve_bounds he r n).1
  exact ⟨min (min extra (1/20000)) (G/4/512),lt_min (lt_min h (by norm_num)) (by positivity),
    (min_le_left _ _).trans (min_le_left _ _),(min_le_left _ _).trans (min_le_right _ _),min_le_right _ _⟩

theorem original_fibre (K : ℕ) (hN : 1<I.P.N) (hU : 1<I.U) :
    exactDiscrepancy (fibre I.bs I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
      completeProduct I.P.N (originalMode I K)=
      (scalar I:ℂ)*∑ j∈I.P.words.attach,let A := onWord I j
        (restore I.P j.val (groups A):ℂ)*errors A K :=
  P4BOriginalHigherLowNativeAtoms.ByRule.original_fibre rule I K hN hU

theorem uniform_auxiliary (K order : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    Part3.UniformAuxiliarySW
      (fun p : Index order zeta kap0 × Block × Block × Block => atom p.1 K p.2.1 p.2.2.1 p.2.2.2) 1 :=
  P4BOriginalHigherLowNativeAtoms.ByRule.uniform_auxiliary rule K order hz hz1 hk hkz ht ht1

/-- Complete original low-first medium family above rough rank three.
The dyadic gamma blocks are exactly the occupied images of the new split. -/
theorem eventually_all_low (K order : ℕ) {z k k0 : ℝ}
    (hz : 0<z) (hz' : z≤1/20000) (hk : 0<k) (hk' : k≤z/200000)
    (hk0 : k0<k/(4*(1+k))) (hk1 : k0<1) :
    ∀ᶠ N : ℕ in atTop,∀ (I : Index order z k0),I.P.N=N → I.eta=z →
      0<I.P.e → (I.P.e:ℝ)≤1/2048 → z≤localE I.P/512 →
      logPrimeMeshStep 0 (19/96) (d I.P).m≤(I.P.e:ℝ)/20 →
      0<I.P.omega → I.P.T*((J0 I.P.omega:ℝ)+1)≤z → 0≤I.P.ell → 2*I.P.ell≤z/16 →
      4≤I.J.length ∧ t I.P I.J 0≤VariableEnvelope.mu →
      ∀ D∈(firstSet I).image owner,∀ E∈(secondSet I).image owner,∀ G∈(thirdSet I).image owner,
      Part3.MediumAdmissible 12 (z/2000) k (1/Real.exp 1) (atom I K D E G) :=
  P4BOriginalHigherLowAdmissible.Mode.eventually_words true K order hz hz' hk hk' hk0 hk1

theorem restoration (omega T : ℝ) (ho : 0<omega) :
    ∃ C : ℝ,0≤C ∧ ∀ {b kap : ℝ},0<b → b≤1 → 0<kap → 19/96<baseline b kap →
    ∀ᶠ N : ℕ in atTop,∀ (order : ℕ) (zeta kap0 : ℝ) (I : Index order zeta kap0),
    I.P.N=N → I.P.omega=omega → I.P.T=T → 0≤I.P.e → I.P.ell≤1 →
    ((bank (cap N)).card:ℝ)*totalMass b kap (outerWidth N) N kap0*scalar I*
      (∑ j∈I.P.words.attach,let A := onWord I j
        |restore I.P j.val (groups A)|*(pieces A:ℝ))≤C*(Real.log (N:ℝ))^54 :=
  P4BOriginalHigherLowRestoration.ByRule.scheduled rule omega T ho

theorem off_low (P : Params) (x U eta : ℝ) (J : List ℕ)
    (h : J.length<4 ∨ VariableEnvelope.mu<t P J 0) :
    split P x U eta J=P4BOriginalCollisionThirdFactor.splitAt P x U eta J := by
  have off : ¬P4BOriginalHigherActionKeys.needsAction P J := by
    intro h'; rcases h with hs|hm
    · exact (not_lt_of_ge h'.1) hs
    · exact (not_lt_of_ge h'.2.1) hm
  have off' : ¬P4BOriginalHigherLowBins.useRoot P J := by
    intro h'; rcases h with hs|hm
    · exact (not_lt_of_ge h'.1) hs
    · exact (not_lt_of_ge h'.2.1) hm
  rw [split,dif_neg off]
  exact P4BOriginalHigherLowBins.off_root P x U eta off'

end
end ImbalancedChen.P4BOriginalHigherActionFamily
