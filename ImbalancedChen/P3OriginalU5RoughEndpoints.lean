import ImbalancedChen.P3OriginalU5CoarseRootV
import ImbalancedChen.P2ActualPairPlanRunSupport
import ImbalancedChen.ActualRoughVectorEndpointBudget

/-!
# Literal U5 rough rank and actual fine upper endpoints

SOURCE ONLY / UNCOMPILED / NO KERNEL ACCEPTANCE.

Only t.2 :: t.1 :: chosen is counted by the fixed rough rank J.  The
native small witness is retained separately and never expanded into J.
Endpoint bounds come from the actual original PairRange cell membership;
neither an endpoint-size bound nor endpoint square support is an input.
The existing rank bound and upper-inflation proofs are called unchanged.

The auxiliary coarse and fine meshes are fixed before N and are both
independent of the original bank mesh.  Only an actual root origin is
transported to the coarse cover.  No tensor, F, common-Q or PP is claimed.
CoarseRootV is a frozen source-only dependency, not yet installed here.
-/

namespace ImbalancedChen.P3OriginalU5RoughEndpoints

noncomputable section
open scoped Classical Topology
open P2PhysicalIncomingPrefixCells
open P2LowerCapPlanIntegerRetention (coordinate coordinate_power)
open P2OriginalPairSourceReceiver
open P2OriginalPairRootRoughProducer (pairRoot)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData
open P2OriginalSelectedIntegerPrefixSquares
open P3OriginalU5AllSourceSquares
open P3OriginalU5CoarseRootV
open P5OriginalU5CausalFinite

/-- The existing fixed rank, depending only on the original rough exponent. -/
abbrev roughRank (epsilon : ℝ) : ℕ :=
  actualRoughVectorRankBound (attachmentNu * epsilon ^ 2)

/-- A fixed cell label determines the endpoint at scale N. -/
def upperByCode (R : PairRange) (m_fine N : ℕ) (code : CellCode m_fine) : ℕ :=
  Nat.floor ((N : ℝ) ^ (qHi R m_fine code : ℝ))

def upperAt (R : PairRange) (m_fine N p : ℕ) : ℕ :=
  upperByCode R m_fine N
    (exponentCode (R.epsilon : ℝ) (ceiling : ℝ) m_fine (coordinate N p))

/-- The old cap induction is instantiated with the literal selected plan. -/
theorem actual_trace_cap_le (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (N : ℕ) (t : ℕ × ℕ) (chosen : List ℕ) :
    (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t chosen).cap ≤
      (153 / 256 : ℝ) := by
  exact P2ActualPairPlanRawSupport.run_cap_le
    (pairPlan R bank (2 * buffer) (rootSeed false buffer N t)) (153 / 256)
    (fun rank code incoming hi => pairPlan_fresh_cap_bound R bank (2 * buffer)
      (rootSeed false buffer N t) rank code incoming hi)
    (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N t (rootSeed false buffer N t))
    (chosen.map (coordinate N)) (original_root_seed_bounded false buffer hb N t)

/-- Both sides of the endpoint bound follow from the actual cell code. -/
theorem actual_endpoint_bounds (R : PairRange) (m_fine : ℕ) {N p : ℕ}
    (hN : 1 < (N : ℝ)) (hp : 0 < p)
    (hx : coordinate N p ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ)) :
    p ≤ upperAt R m_fine N p ∧
      (upperAt R m_fine N p : ℝ) ≤ (N : ℝ) ^ meshStep R m_fine * (p : ℝ) := by
  let c := exponentCode (R.epsilon : ℝ) (ceiling : ℝ) m_fine (coordinate N p)
  have hlo := exponent_lower R m_fine hx
  have hhi := exponent_upper R m_fine hx
  change (qLo R m_fine c : ℝ) ≤ coordinate N p at hlo
  change coordinate N p ≤ (qHi R m_fine c : ℝ) at hhi
  have hwidth := code_width_le R m_fine c
  have hpow := coordinate_power hN hp
  have hnonneg : 0 ≤ (N : ℝ) ^ (qHi R m_fine c : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  change p ≤ Nat.floor ((N : ℝ) ^ (qHi R m_fine c : ℝ)) ∧
    (Nat.floor ((N : ℝ) ^ (qHi R m_fine c : ℝ)) : ℝ) ≤ _
  constructor
  · apply (Nat.le_floor_iff hnonneg).mpr
    calc
      (p : ℝ) = (N : ℝ) ^ coordinate N p := hpow.symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le hhi
  · calc
      _ ≤ (N : ℝ) ^ (qHi R m_fine c : ℝ) := Nat.floor_le hnonneg
      _ ≤ (N : ℝ) ^ (meshStep R m_fine + coordinate N p) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
      _ = _ := by rw [Real.rpow_add (zero_lt_one.trans hN), hpow]

/-- J and this mesh threshold precede N.  Reuse the coarse mesh existence. -/
theorem exists_fine_mesh (R : PairRange) (epsilon : ℝ) {buffer : ℝ} (hb : 0 < buffer) :
    ∃ m_fine : ℕ, meshStep R m_fine * ((roughRank epsilon : ℝ) + 1) ≤ buffer / 4 := by
  have hJ : 0 < (roughRank epsilon : ℝ) + 1 := by positivity
  obtain ⟨m_fine, hm⟩ := exists_auxiliary_mesh R
    (buffer := 8 * buffer / ((roughRank epsilon : ℝ) + 1)) (by positivity)
  have heq : (8 * buffer / ((roughRank epsilon : ℝ) + 1)) / 32 =
      (buffer / 4) / ((roughRank epsilon : ℝ) + 1) := by ring
  rw [heq] at hm
  exact ⟨m_fine, (le_div_iff₀ hJ).mp hm⟩

/-- The data refer to the same rough word and its actual frozen endpoint table. -/
structure RoughEndpointData (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (epsilon : ℝ) (m_fine N : ℕ) (t : ℕ × ℕ) (chosen : List ℕ) : Prop where
  length_le : (t.2 :: t.1 :: chosen).length ≤ roughRank epsilon
  bounds : ∀ p ∈ t.2 :: t.1 :: chosen, p ≤ upperAt R m_fine N p ∧
    (upperAt R m_fine N p : ℝ) ≤ (N : ℝ) ^ meshStep R m_fine * (p : ℝ)
  full : actualDwellSupport
    ((N : ℝ) ^ ((actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen).cap + meshStep R m_fine * ((roughRank epsilon : ℝ) + 1)))
    ((t.2 :: t.1 :: chosen).map (upperAt R m_fine N))

/-- The actual integer supply discharges the old rank and inflation inputs.
    This applies to every actual source, including short and inherited words. -/
theorem integer_supply_endpoints
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2) (m_fine : ℕ)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {chosen : List ℕ}
    (hsub : List.Sublist chosen (roughPrimeUniverse N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N))) {source : Origin mesh} {slots : List (ℕ × Bool)}
    (hsupply : IntegerSupply R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen source slots) : RoughEndpointData R bank buffer epsilon m_fine N t chosen := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hd := P3OriginalU5FreshFifthSquareSupplier.original_word_data
    R epsilon hepsilon hepsilon8 hgrid hN ht hsub
  have hcap := (actual_trace_cap_le R bank buffer hb N t chosen).trans
    (by norm_num : (153 / 256 : ℝ) ≤ 5 / 8)
  have heta : 0 < attachmentNu * epsilon ^ 2 := by dsimp [attachmentNu]; positivity
  have hg := hsupply.full
  rw [hsupply.values] at hg
  have hfull : actualDwellSupport
      ((N : ℝ) ^ (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
        N t chosen).cap) (t.2 :: t.1 :: chosen) := by
    intro i hi
    simpa only [Nat.one_mul, actualNatList_cast_prod] using integerSquareGates_at _ hg i hi
  have hlen := actualRoughPrimeVector_length_le hNr heta hcap
    (t.2 :: t.1 :: chosen) (by simp) (fun p hp => (hd.1 p hp).pos) hd.2.2.1 hfull
  have hbounds := fun p hp => actual_endpoint_bounds R m_fine hNr (hd.1 p hp).pos
    (hd.2.2.2 p hp)
  refine ⟨hlen, hbounds, ?_⟩
  have hinflate := actualDwellSupport_upper_inflation hNr (meshStep_pos R m_fine).le
    (fun p : ℕ => p) (upperAt R m_fine N) (t.2 :: t.1 :: chosen) hlen
    (fun p hp => (hbounds p hp).2) (by simpa only [List.map_id] using hfull) (le_refl _)
  simpa only [List.map_id] using hinflate

/-- The same native rho supplies all witnesses.  Root-only auxiliary support
    keeps a further b/4 margin after paying every fine endpoint square cost. -/
theorem native_U5_rough_endpoints
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    (m_aux m_fine : ℕ)
    (hfine : meshStep R m_fine * ((roughRank epsilon : ℝ) + 1) ≤ (buffer : ℝ) / 4)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k : ℕ}
    (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0) :
    let j := labelAt R m_aux (coordinates N t) (coordinates_mem_triangle hN ht)
    ∃ s ∈ actualSmallRosserSupport N (Nat.ceil (cutoff N)) (smallCutoff N epsilon),
      ∃ chosen : List ℕ,
        List.Sublist chosen (roughPrimeUniverse N (Nat.ceil (cutoff N))
          (smallCutoff N epsilon) (cutoff N)) ∧ k = s * chosen.prod ∧
        (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t chosen).accepted = true ∧
        ∃ source slots,
          IntegerSupply R bank (2 * buffer) (rootSeed false buffer N t)
            N t chosen source slots ∧
          RoughEndpointData R bank buffer epsilon m_fine N t chosen ∧
          (source = .root → actualDwellSupport
            ((N : ℝ) ^ (auxCover R (buffer : ℝ) j - (buffer : ℝ) / 4))
            ((t.2 :: t.1 :: chosen).map (upperAt R m_fine N))) := by
  obtain ⟨s, hs, chosen, hsub, hkprod, haccept, source, slots, hsupply⟩ :=
    native_U5_nonzero_all_source_squares R bank buffer hb' epsilon hgrid hN ht hk
  have hd := integer_supply_endpoints R bank buffer hb epsilon hepsilon hepsilon8 hgrid
    m_fine hN ht hsub hsupply
  refine ⟨s, hs, chosen, hsub, hkprod, haccept, source, slots, hsupply, hd, ?_⟩
  intro hsource
  subst source
  let j := labelAt R m_aux (coordinates N t) (coordinates_mem_triangle hN ht)
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hbR : 0 ≤ (buffer : ℝ) := by exact_mod_cast hb
  have hcover : rootLevel false N t - (buffer : ℝ) ≤
      auxCover R (buffer : ℝ) j - (buffer : ℝ) / 2 := by
    simpa [rootLevel, coordinates, actualPrimeTupleLog, coordinate] using
      whole_cell_cover R (buffer : ℝ) j
        (labelAt_closed R m_aux (coordinates N t) (coordinates_mem_triangle hN ht))
  have hcap : (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen).cap = rootLevel false N t - 2 * (buffer : ℝ) := by
    rw [hsupply.cap]
    rfl
  have hbudget : (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen).cap + meshStep R m_fine * ((roughRank epsilon : ℝ) + 1) ≤
      auxCover R (buffer : ℝ) j - (buffer : ℝ) / 4 := by
    rw [hcap]
    linarith
  intro i hi
  exact (hd.full i hi).trans (Real.rpow_le_rpow_of_exponent_le hNr.le hbudget)

end
end ImbalancedChen.P3OriginalU5RoughEndpoints
