import ImbalancedChen.OriginalFourthActualAtomEndpointSupport

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

A genuinely finite, fixed-before-N family of constant analytic caps now
covers the actual original fourth source. Labels record the literal
third-seed/activation branch, every closed row-box wall sign, and a small
half-open refinement box. No reference corner, seed equality, endpoint
size, rank ceiling or endpoint support is supplied by the consumer.

The policy and physical cap remain the actual pointwise original maximum.
The constant cap is solely an analytic endpoint cover, with a remaining
positive original buffer. Equality faces and all fallback branches are
retained; this is not an external distribution or archive certificate.
-/

namespace ImbalancedChen.OriginalFourthFiniteAtomEndpointRealization20261026b

noncomputable section
open Filter Topology Set
open scoped Classical
open HistoricalThirdCoarse VariableEnvelope P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthFullSourceActivation
open P1OriginalVariableFourthEligibilityPartition
open OriginalFourthOwnedEndpointBuffer20261026b
open OriginalFourthCanonicalIntegerEndpoints20261026b
open OriginalFourthFrozenAtomCap20261026b
open OriginalFourthActualAtomEndpointSupport20261026b

abbrev CoverLabel (records : List FourthWireRow) (m k : ℕ) :=
  Label m × Pattern (fourthFamily records) × (Fin 4 → Fin (k + 1))

def coverRegion (records : List FourthWireRow) (m k : ℕ) (omega : ℝ)
    (l : CoverLabel records m k) : Set Point :=
  meshBranch m omega l.1 ∩
    (wallAtom (fourthFamily records) l.2.1 ∩
      logPrimeMeshCell 0 (19 / 96 : ℝ) k l.2.2)

def coverCap (records : List FourthWireRow) (e chi : ℝ) (m k : ℕ)
    (licensed : ProducerRow → Prop) (delta : ℝ) (l : CoverLabel records m k) : ℝ :=
  frozenAtomCap e (branchSeed e chi m l.1) (fourthFamily records) licensed l.2.1
    (logPrimeMeshLo 0 (19 / 96 : ℝ) k l.2.2) delta

/-- The label is uniquely constructed from ordinary half-open mesh and
strict/weak wall ownership. No selected winning row is an input. -/
theorem finite_cover_unique (records : List FourthWireRow) (m k : ℕ) (omega : ℝ)
    {t : Point}
    (ht : t ∈ logPrimeBox (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))) :
    ∃! l : CoverLabel records m k, t ∈ coverRegion records m k omega l := by
  obtain ⟨branch, hb⟩ := exists_meshBranch m omega ht
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96 : ℝ) k ht
  let s := actualPattern (fourthFamily records) t
  refine ⟨(branch, s, j), ⟨hb, mem_actual_wallAtom _ _, hj⟩, ?_⟩
  intro l hl
  have hbranch := meshBranch_unique m omega hl.1 hb
  have hwalls := wallAtom_unique hl.2.1 (mem_actual_wallAtom (fourthFamily records) t)
  have hmesh := logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hl.2.2 hj
  exact Prod.ext hbranch (Prod.ext hwalls hmesh)

private theorem refinement_corner_close (k : ℕ) (delta : ℝ)
    (hk : logPrimeMeshStep 0 (19 / 96 : ℝ) k ≤ delta)
    {j : Fin 4 → Fin (k + 1)} {t : Point}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96 : ℝ) k j) :
    ∀ i, |t i - logPrimeMeshLo 0 (19 / 96 : ℝ) k j i| ≤ delta := by
  intro i
  have hi := mem_logPrimeMeshCell.mp ht i
  rw [logPrimeMeshHi_eq_lo_add_step] at hi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega : ℝ)
  (licensed : ProducerRow → Prop)

/-- The finite cover really contains the original ancestor of each
physical state, with the actual target exclusion and rough carrier intact. -/
theorem actual_ancestor_in_cover_box (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (hz : z ≤ (N : ℝ) ^ (19 / 96 : ℝ))
    (weight : ℕ → ℝ) (rank : ℕ) (hrank : 4 ≤ rank)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 state.selectedPrefix) ∈
      logPrimeBox (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
  have hlen := firstExitDepthFrontier_selected_length rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight [] (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight (roughPrimeUniverse N cap w z) state hstate
  apply mem_logPrimeBox.mpr
  intro i
  have hmem := hsub.subset
    (List.mem_reverse.mpr (primeHistoryTuple_mem hlen (i.castLE hrank)))
  have hcoord := primeCoordinate_mem hN (mem_roughPrimeUniverse_prime hmem).pos
    ((mem_roughPrimeUniverse_upper hmem).trans_le hz)
  change 0 ≤ Real.log (primeHistoryTuple 4 (rosserAncestor 4 state.selectedPrefix) i : ℝ) /
      Real.log (N : ℝ) ∧
    Real.log (primeHistoryTuple 4 (rosserAncestor 4 state.selectedPrefix) i : ℝ) /
      Real.log (N : ℝ) < 19 / 96
  rw [primeHistoryTuple_ancestor hlen hrank i]
  exact hcoord

/-- All cap labels, widths, refinement boxes and natural endpoint maps
are fixed before N. Every later actual descendant constructs its own
unique region label and receives full endpoint support at that label's
constant analytic cap. The original variable policy is unchanged. -/
theorem exists_finite_actual_atom_endpoint_realization (he : 0 < e)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ e / 24 ∧ ∃ k n : ℕ,
      ∀ᶠ N : ℕ in atTop, ∀ (cap : ℕ) (w z : ℝ),
        (N : ℝ) ^ rho ≤ w → z ≤ (N : ℝ) ^ (19 / 96 : ℝ) →
        ∀ (weight : ℕ → ℝ) (rank : ℕ), 4 ≤ rank → ∀ state : FirstExitDepthState ℕ,
          state ∈ firstExitDepthFrontier rank
            (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
            weight [] true 1 (roughPrimeUniverse N cap w z) →
          ∃ l : CoverLabel records m k,
            primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 state.selectedPrefix) ∈
              coverRegion records m k omega l ∧
            (∀ p ∈ state.selectedPrefix.reverse, p ≤ integerUpper n N p) ∧
            actualDwellSupport
              ((N : ℝ) ^ coverCap records e chi m k licensed delta l)
              (state.selectedPrefix.reverse.map (integerUpper n N)) ∧
            ownedExponent records e chi m omega (N : ℝ) licensed state.selectedPrefix + e / 2 ≤
              coverCap records e chi m k licensed delta l ∧
            coverCap records e chi m k licensed delta l ≤
              ownedExponent records e chi m omega (N : ℝ) licensed state.selectedPrefix + e := by
  let R := actualRoughVectorRankBound rho
  let tau : ℝ := e / (2 * ((R : ℝ) + 1))
  let delta : ℝ := e / 48
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hsmall : delta ≤ e / 24 := by dsimp [delta]; linarith
  have hwidth : tau * ((actualRoughVectorRankBound rho : ℝ) + 1) ≤ e / 2 := by
    have hRpos : 0 < (R : ℝ) + 1 := by positivity
    have heq : tau * ((R : ℝ) + 1) = e / 2 := by
      dsimp [tau]
      field_simp [hRpos.ne']
      <;> ring
    exact heq.le
  obtain ⟨k, hk⟩ := ((tendsto_logPrimeMeshStep 0 (19 / 96 : ℝ)).eventually
    (gt_mem_nhds hdelta)).exists
  obtain ⟨n, _hn, hcanonical⟩ := exists_uniform_canonical_endpoints tau htau
  refine ⟨delta, hdelta, hsmall, k, n, ?_⟩
  filter_upwards [hcanonical, eventually_ge_atTop (2 : ℕ)] with N hcanonicalN hN
  intro cap w z hrough hz weight rank hrank state hstate
  have hN' : 1 < N := by omega
  have hbox := actual_ancestor_in_cover_box records e chi m omega licensed
    N cap hN' w z hz weight rank hrank state hstate
  obtain ⟨l, hl, _hunique⟩ := finite_cover_unique records m k omega hbox
  have hclose := refinement_corner_close k delta hk.le hl.2.2
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight (roughPrimeUniverse N cap w z) state hstate
  have hendpoints (p : ℕ) (hp : p ∈ state.selectedPrefix.reverse) :
      p ≤ integerUpper n N p ∧
        (integerUpper n N p : ℝ) ≤ (N : ℝ) ^ tau * (p : ℝ) := by
    have hmem := hsub.subset hp
    exact hcanonicalN p (mem_roughPrimeUniverse_prime hmem).pos
      ((mem_roughPrimeUniverse_upper hmem).trans_le hz)
  have hfull := actual_full_vector_at_frozen_cap records e chi m omega licensed
    he.le rho hrho N cap hN' w z tau hrough htau.le hwidth weight rank hrank state hstate
    l.1 l.2.1 (logPrimeMeshLo 0 (19 / 96 : ℝ) k l.2.2) delta hdelta.le hsmall
    hl.1 hl.2.1 hclose (integerUpper n N) (fun p hp => (hendpoints p hp).2)
  have hlen := firstExitDepthFrontier_selected_length rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight [] (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hp := actual_ancestor_tuple_positive records e chi m omega licensed
    N cap w z weight rank hrank state hstate
  have hprofile := owned_exponent_on_source_branch records e chi m omega licensed
    N hN' state.selectedPrefix (by omega) hp l.1 hl.1
  have hcap := actual_profile_frozen_cap_bracket e (branchSeed e chi m l.1)
    (fourthFamily records) licensed l.2.1 (logPrimeMeshLo 0 (19 / 96 : ℝ) k l.2.2)
    (primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 state.selectedPrefix))
    delta hdelta.le hsmall hl.2.1 hclose
  rw [← hprofile] at hcap
  exact ⟨l, hl, (fun p hp => (hendpoints p hp).1), hfull, hcap.1, hcap.2⟩

end
end ImbalancedChen.OriginalFourthFiniteAtomEndpointRealization20261026b
