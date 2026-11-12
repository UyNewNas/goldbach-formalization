import ImbalancedChen.P4AFinitePPLowActualRoot

namespace ImbalancedChen.P4AFinitePPLastOddSupport
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteFallbackPrograms (code)
open P4AOrderedThirdRectangleRate (position)
open P4AUpperTaggedParityCompiler P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AUpperTaggedFirstPrefixDisagreement (polarityAfter)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AFull87ActualAffineDeletion (coords)
open P4AFull87OrdinaryAdmissionDeletion (reversed_prefix)
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)

def tested (p : List ℕ) := if evenListLength p then p.tail else p

theorem tested_spec {p : List ℕ} (hp : p≠[]) :
    evenListLength (tested p)=false ∧ tested p≠[] ∧
      (p=tested p ∨ ∃ q,p=q::tested p) := by
  cases p with
  | nil => contradiction
  | cons q xs =>
    cases h : evenListLength xs
    · have he : xs≠[] := by rintro rfl; simp [evenListLength] at h
      simp [tested,evenListLength,h,he]
    · simp [tested,evenListLength,h]

private theorem parity (p : Bool) (xs : List ℕ) :
    polarityAfter p xs.length = if evenListLength xs then p else !p := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,polarityAfter,ih,evenListLength]
    cases evenListLength xs <;> cases p <;> rfl

def exponent (B : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) (N u : ℕ) :=
  (code B delta n d (position (tested u.primeFactorsList).length)).eval
    (coords N _ u.primeFactorsList.reverse)

/-- At even length the last prime extends the previous retained odd test.
In particular the complete ordinary cube system has a single cap on the
physical word, even when earlier actions used different levels. -/
theorem full (B : Bank) (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData)
    {N cap u : ℕ} (hN : 1<N) {w v : ℝ} (hw : 0≤w)
    (hu : u∈rawSupport (F B delta n d w N) N cap ((N:ℝ)^w) ((N:ℝ)^v))
    (hne : u.primeFactorsList≠[]) :
    ordinaryRosserPrefixAdmissible false ((N:ℝ)^exponent B delta n d N u) u.primeFactorsList ∧
    actualDwellSupport ((N:ℝ)^exponent B delta n d N u) u.primeFactorsList.reverse := by
  let p := tested u.primeFactorsList
  let M := exponent B delta n d N u
  obtain ⟨hp,hpne,hcases⟩ := tested_spec hne
  have hlen : p.length≤u.primeFactorsList.length := by
    rcases hcases with h|⟨q,h⟩
    · exact (congrArg List.length h).ge
    · change u.primeFactorsList=q::p at h
      rw [h]; simp
  have hpos : 0<p.length := List.length_pos_iff.mpr hpne
  have hanc : rosserAncestor p.length u.primeFactorsList=p := by
    rcases hcases with h|⟨q,h⟩
    · change u.primeFactorsList=p at h
      calc
        rosserAncestor p.length u.primeFactorsList = rosserAncestor p.length p := congrArg _ h
        _ = p := by simp [rosserAncestor]
    · change u.primeFactorsList=q::p at h
      calc
        rosserAncestor p.length u.primeFactorsList = rosserAncestor p.length (q::p) := congrArg _ h
        _ = p := by simp [rosserAncestor]
  have ho : polarityAfter true p.length=false := by rw [parity]; simp [p,hp]
  have hU := (raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hu |>.1
  have hc := P4AOriginalFiniteFallbackAtoms.retained_strict_cubes B delta hd n d hN hw hu
    (p.length-1) (by omega) (by rwa [Nat.sub_add_cancel hpos])
  rw [Nat.sub_add_cancel hpos] at hc
  have hodd : ordinaryRosserPrefixAdmissible false ((N:ℝ)^M) p := by
    rw [←hanc,←reversed_prefix u p.length hlen]
    exact (P5Z.PresievedRoughSlotAffineGates.original_upper_prefix_iff_log hN _ _
      (canonicalPrefix_pos hU hlen) (canonicalPrefix_strictAnti hU hlen)).mpr hc
  have hsub := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap _ _ hU).1
  have hsort := (roughPrimeUniverse_pairwise_gt _ _ _ _).sublist hsub
  have hsort' : u.primeFactorsList.Pairwise (·<·) := by simpa only [List.pairwise_reverse] using hsort
  have htotal : ordinaryRosserPrefixAdmissible false ((N:ℝ)^M) u.primeFactorsList := by
    rcases hcases with h|⟨q,h⟩
    · exact (congrArg (ordinaryRosserPrefixAdmissible false ((N:ℝ)^M)) h).mpr hodd
    · change u.primeFactorsList=q::p at h
      have hq : q.Prime := Nat.prime_of_mem_primeFactorsList (show q∈u.primeFactorsList by rw [h]; simp)
      have H := ordinaryParityRosserPolicy_eq_full_on_valid_prefix false ((N:ℝ)^M) p false q hodd hp.symm hq
        (by simp) (h ▸ hsort')
      have HH : ordinaryRosserPrefixAdmissible false ((N:ℝ)^M) (q::p) := by
        apply of_decide_eq_true
        simpa [ordinaryRosserRetainedPolicy] using H.symm
      exact (congrArg (ordinaryRosserPrefixAdmissible false ((N:ℝ)^M)) h).mpr HH
  refine ⟨htotal,Part3.ActualCompactAllRankSupport.upper_set_dwell_support _
    (fun q hq => mem_roughPrimeUniverse_prime (hsub.subset hq)) hsort ?_⟩
  simpa only [Bool.false_eq_true,if_false,List.toFinset_reverse] using htotal.2

end
end ImbalancedChen.P4AFinitePPLastOddSupport
