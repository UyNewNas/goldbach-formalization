import ImbalancedChen.P4BOriginalMediumPhysicalAtomSum

/-! The dyadic owners actually summed in the signed word identity. -/
namespace ImbalancedChen.P4BOriginalMediumOccupiedLengths
noncomputable section
open Classical Filter
open P5Z.HBRightClosedDyadicRoles (Block owner owner_owns)
open P5Z.ActualHBDyadicProductWindow (lower owns_bounds)
open P4BOriginalMediumAtomFamily (Index support support_data third_data)
open P4BOriginalCollisionThirdFactor (splitAt thirdSupport gamma_range)
open P4AOriginalFiniteFallbackGroupedAtoms (slots group_support)
open P4BUpperSelectedBoxCapacity (endpoint groups)

private theorem left_cap {α : Type*} (w : α → ℝ) (A : ℝ) (hA : 1≤A) (J : List α) :
    ((actualTwoCapacityGreedy w A J).1.map w).prod≤A := by
  induction J using List.reverseRecOn with
  | nil => simpa only [actualTwoCapacityGreedy,List.foldl_nil,List.map_nil,List.prod_nil] using hA
  | append_singleton J j ih =>
    rw [actualTwoCapacityGreedy_append]
    unfold actualTwoCapacityStep
    split_ifs with h
    · simpa using h
    · exact ih

private theorem groups_left {α : Type*} (D A : ℝ) (upper : α→ℕ) (S R J : List α) (hA : 1≤A) :
    endpoint upper (groups D A upper S R J).1≤A := by
  unfold groups
  split <;> apply left_cap _ _ hA

variable {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0)

def firstOwners := (support I.P I.groups.1).image owner
def secondOwners := (support I.P I.groups.2.1).image owner
def thirdOwners := (thirdSupport I.P I.J I.groups.2.2).image owner
abbrev upper := actualPrimeFineLabelIntegerUpper I.P.N I.P.T

theorem factor_owner {S : List ℕ} {D : Block} (hD : D∈(support I.P S).image owner) :
    (lower D:ℝ)≤endpoint (upper I) S := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hD
  have h := (owns_bounds (owner_owns (support_data _ _ hq).1)).1
  exact (by exact_mod_cast h : (lower (owner q):ℝ)≤q).trans (group_support _ _ _ _ _ hq)

theorem small_rough_owner {D : Block} (hD : D∈thirdOwners I) :
    (lower D:ℝ)≤I.P.L*endpoint (upper I) I.groups.2.2 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hD
  have h := (owns_bounds (owner_owns (third_data _ _ _ hq).1)).1
  exact (by exact_mod_cast h : (lower (owner q):ℝ)≤q).trans (gamma_range _ hq)

theorem endpoint_first (hA : 1≤I.U/I.x^I.eta) :
    endpoint (upper I) I.groups.1≤I.U/I.x^I.eta := by
  dsimp only [Index.groups,splitAt,slots]
  split <;> apply groups_left _ _ _ _ _ _ hA

theorem first_length (K : ℕ) (D E G : Block) (hD : D∈firstOwners I)
    (hx : 1<I.x) (heta : 0<I.eta) (hU : I.x^(2*I.eta)≤I.U) :
    let d := (P4BOriginalMediumAtomReconstruction.withOwners I D E G).atom K
    d.Q1<d.U*d.scale^(-(I.eta/2000)) := by
  have hx0 := zero_lt_one.trans hx
  have hp := Real.rpow_pos_of_pos hx0 I.eta
  have hA : 1≤I.U/I.x^I.eta := (le_div_iff₀ hp).mpr (by
    rw [one_mul]
    exact (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : I.eta≤2*I.eta)).trans hU)
  have hu := (Real.rpow_pos_of_pos hx0 (2*I.eta)).trans_le hU
  change (lower D:ℝ)<I.U*I.x^(-(I.eta/2000))
  calc
    _≤I.U/I.x^I.eta := (factor_owner I hD).trans (endpoint_first I hA)
    _=I.U*I.x^(-I.eta) := by rw [Real.rpow_neg hx0.le,div_eq_mul_inv]
    _<_ := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)) hu

/-- All actual HB and policy indices come after this threshold. -/
theorem eventually_first (K order : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ (I : Index order zeta kap0),I.P.N=N → I.eta=zeta →
      ∀ D∈firstOwners I,∀ E G : Block,
        let d := (P4BOriginalMediumAtomReconstruction.withOwners I D E G).atom K
        d.Q1<d.U*d.scale^(-(zeta/2000)) := by
  filter_upwards [P4BOriginalHighRankLiveFibreModes.eventually_fixed_live_window
    K hz hz1 hk hkz ht ht1] with N hN
  intro I hn hη D hD E G
  rw [←hn] at hN
  obtain ⟨hx,_,_,hu,_⟩ := hN I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck
    I.bs I.i I.C I.live (P4BOriginalMediumFibreSWWindow.first_spec I.selected)
  simpa only [hη] using first_length I K D E G hD hx (hη.symm ▸ hz) (hη.symm ▸ hu)

end
end ImbalancedChen.P4BOriginalMediumOccupiedLengths
