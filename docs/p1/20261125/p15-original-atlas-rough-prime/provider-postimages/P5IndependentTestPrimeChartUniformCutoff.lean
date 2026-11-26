import ImbalancedChen.P1OriginalSingletonCutoffData
import ImbalancedChen.P5IndependentFourPrimeChartCutoff
import ImbalancedChen.P5OriginalWSelectedAtomFamily

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This extends the independent original PP TEST word cutoff from rank four
to every fixed 1 <= k <= K. The coefficient's selected ALL16 mark t and
modulus q=fullPrefix(t)*r are separate from the test tuple ps throughout.
The source assumes only the paper's geometric test support N^astar<=p<=N
and the genuine same-term dyadic psi windows.
-/
namespace ImbalancedChen.P5Z.IndependentTestPrimeChartUniformCutoff
noncomputable section
open Classical Filter
open scoped BigOperators
open ExactOriginalSmoothDyadicPartition OriginalChartRoughCutoff
open OriginalIndependentFourPrimeChartCutoff
open ActualMultiGroupHBChartScale HBRightClosedDyadicRoles
open OriginalWSelectedAtomFamily
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalSixteenPolicyBank U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenNearCapBoxProfiles
open U1011OriginalSixteenNearCapCommonSmallParameters
open U1011OriginalSixteenCommonSmallParameters (owner_mem_selected)
open OriginalCommonBetaActualParameters OriginalOrdinaryPresievedSigma
open OriginalWOwnerOccurrenceBinding OriginalWFixedMeshBudgets
open OriginalPresievedRoughPrimeSlots PresievedRoughGateMeshReserve
open U1011OriginalFifteenMediumNumericGates (NumericGates innerQuery)

/-- The SAME ordered independent test-word HB group list yields the
paper's local x floor directly. Individual HB groups may have different
y=(2R)^(1/3); no fictitious common-y vector is introduced. -/
theorem independent_grouped_local_x_floor
    (gs : List Group) {N : ℕ} {kappa0 : ℝ}
    (htrim : (N : ℝ) ^ (1 - kappa0) ≤ chartN gs)
    (left right : List Block) (b : Block)
    (hsplit : blocks gs = left ++ b :: right) :
    ∃ pl p pr, integers gs = pl ++ p :: pr ∧
      List.Forall₂ Owns left pl ∧ Owns b p ∧ List.Forall₂ Owns right pr ∧
      let x : ℝ := (lower b : ℝ) *
        (lower (owner (pl ++ pr).prod) : ℝ)
      0 < x ∧
        (1 / (2 * (256 : ℝ) ^ gs.length)) *
          (N : ℝ) ^ (1 - kappa0) ≤ x := by
  obtain ⟨pl,p,pr,hints,hl,hp,hr,howner,hxp,hXx,hS,hxX⟩ :=
    actual_complementary_scale gs left right b hsplit
  let x : ℝ := (lower b : ℝ) *
    (lower (owner (pl ++ pr).prod) : ℝ)
  have hchart := (original_product_geometry gs).2.1
  have hX : 0 ≤ chartX gs := (whole_geometry gs).1.le
  have hpow : 0 ≤ (2 : ℝ) ^ gs.length := by positivity
  have hfull : (N : ℝ) ^ (1 - kappa0) ≤
      2 * (256 : ℝ) ^ gs.length * x := by
    calc
      (N : ℝ) ^ (1 - kappa0) ≤ chartN gs := htrim
      _ ≤ (2 : ℝ) ^ gs.length * chartX gs := hchart
      _ ≤ (2 : ℝ) ^ gs.length * (scaleConstant gs.length * x) :=
        mul_le_mul_of_nonneg_left hXx hpow
      _ = 2 * (256 : ℝ) ^ gs.length * x := by
        unfold scaleConstant
        have hp : (2 : ℝ) ^ gs.length * (128 : ℝ) ^ gs.length =
            (256 : ℝ) ^ gs.length := by
          rw [← mul_pow]
          norm_num
        calc
          (2 : ℝ) ^ gs.length * (2 * (128 : ℝ) ^ gs.length * x) =
              2 * ((2 : ℝ) ^ gs.length * (128 : ℝ) ^ gs.length) * x := by ring
          _ = 2 * (256 : ℝ) ^ gs.length * x := by rw [hp]
  have hden : 0 < 2 * (256 : ℝ) ^ gs.length := by positivity
  have hfloor : (1 / (2 * (256 : ℝ) ^ gs.length)) *
      (N : ℝ) ^ (1 - kappa0) ≤ x := by
    have hq : (N : ℝ) ^ (1 - kappa0) / (2 * (256 : ℝ) ^ gs.length) ≤ x :=
      (div_le_iff₀ hden).mpr (hfull.trans_eq (mul_comm _ _))
    calc
      (1 / (2 * (256 : ℝ) ^ gs.length)) *
          (N : ℝ) ^ (1 - kappa0) =
          (N : ℝ) ^ (1 - kappa0) /
            (2 * (256 : ℝ) ^ gs.length) := by ring
      _ ≤ x := hq
  exact ⟨pl,p,pr,hints,hl,hp,hr,hxp,hfloor⟩

/-- One bank threshold pays the three scale monomials for the SAME
independent test-word HB group and the separate selected W modulus mark.
The actual geometric W_N(u) source identification remains explicit. -/
theorem independent_group_selected_W_atom_eventual
    (n K : ℕ) (eta : ℚ) (heta : 0 < eta)
    {nu0 epsilon z kappa0 : ℝ}
    (hnu0 : 0 < nu0) (heps : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    (hz : 0 < z) (hzu : z ≤ 1 / 128)
    (hsmall : z ≤ (ellMax n eta : ℝ) / 512)
    (hk0 : 0 ≤ kappa0) (hk : kappa0 ≤ z) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ (E : ℕ × ℕ → Prop) (t : Four)
        (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
        (hW : selectedPolicy n N t = wPolicy)
        (r : ℕ)
        (hr : r ∈ rowSupport n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) t)
        (hq : jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
          ((N : ℝ) ^ (nu0 * epsilon)) E (fullPrefix t * r) ≠ 0)
        (gs : List Group) (hrank : gs.length ≤ K)
        (htrim : (N : ℝ) ^ (1 - kappa0) ≤ chartN gs)
        (left right : List Block) (b : Block)
        (hsplit : blocks gs = left ++ b :: right) (U : ℝ),
        ∃ pl p pr, integers gs = pl ++ p :: pr ∧
          List.Forall₂ Owns left pl ∧ Owns b p ∧
          List.Forall₂ Owns right pr ∧
          let x : ℝ := (lower b : ℝ) *
            (lower (owner (pl ++ pr).prod) : ℝ)
          1 < x → 0 < U → 1 ≤ innerQuery x U z →
          innerQuery x U z ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
          ∃ key : WAtomKey n eta nu0 epsilon,
            ∃ e d : ℕ,
              let ps := canonicalSlots N
                (Nat.ceil (U1011OriginalW16NearCapNative.Z (atomOwner key) eta N))
                ((N : ℝ) ^ (nu0 * epsilon ^ 2))
                (U1011OriginalW16NearCapNative.Z (atomOwner key) eta N) d
              let actual := physicalOccurrence t ps
              let out := atomGroups (N := N) key (innerQuery x U z)
              let a := (out.left.map actual).prod
              let b := (out.middle.map actual).prod
              let c := e * (out.right.map actual).prod
              owner n (coordinates N t) = key.1.val ∧
                ps.length = key.2.1.val ∧
                actualPrimeTupleLog N (slotVector ps) ∈
                  PresievedRoughGateMeshReserve.cell (nu0 * epsilon ^ 2)
                    (U1011OriginalW16NearCapNative.cutoffExponent
                      (atomOwner key) eta : ℝ)
                    (roughMeshPrecision n eta nu0 epsilon) key.2.2 ∧
                1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
                a * b * c = fullPrefix t * r ∧
                NumericGates N x U (a : ℝ) (b : ℝ) (c : ℝ) (z / 2000) := by
  let c : ℝ := 1 / (2 * (256 : ℝ) ^ K)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N1,hpay⟩ := selected_W_family_common_threshold heta hc hz hzu
    hsmall hk0 hk
  refine ⟨max 2 N1,le_max_left _ _,?_⟩
  intro N hN E t ht hW r hr hq gs hrank htrim left right b hsplit U
  obtain ⟨pl,p,pr,hints,hl,hp,hright,hxpos,hxlower⟩ :=
    independent_grouped_local_x_floor gs htrim left right b hsplit
  let x : ℝ := (lower b : ℝ) *
    (lower (owner (pl ++ pr).prod) : ℝ)
  refine ⟨pl,p,pr,hints,hl,hp,hright,?_⟩
  intro hx hU hA1 hAupper
  have hpowlen : (256 : ℝ) ^ gs.length ≤ (256 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) hrank
  have hden1 : 0 < 2 * (256 : ℝ) ^ gs.length := by positivity
  have hdenK : 0 < 2 * (256 : ℝ) ^ K := by positivity
  have hcoeff : c ≤ 1 / (2 * (256 : ℝ) ^ gs.length) := by
    dsimp [c]
    apply (div_le_div_iff₀ hdenK hden1).mpr
    nlinarith [hpowlen]
  have hbase : 0 ≤ (N : ℝ) ^ (1 - kappa0) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlow : c * (N : ℝ) ^ (1 - kappa0) ≤ x :=
    (mul_le_mul_of_nonneg_right hcoeff hbase).trans hxlower
  let J := owner n (coordinates N t)
  have htag := (Finset.mem_filter.mp ht).2
  have hselected : J ∈ selectedCells n := owner_mem_selected htag
  have hJW : J ∈ selectedWCells n :=
    (mem_selectedWCells).mpr ⟨hselected,hW⟩
  have hpay' := hpay J hJW N ((le_max_right _ _).trans hN) x hlow
  have hdelta : (cellDelta n eta J : ℝ) =
      (delta wPolicy (ownerBox n N t) eta : ℝ) := by
    simp [cellDelta,selectedPolicy,ownerBox,hW]
  rw [hdelta] at hpay'
  have hNN : 1 < N := by omega
  exact active_W_mark_in_selected_atom hNN heta hnu0 heps heBudget E
    ht hW hr hq hx hz hU hA1 hAupper
    hpay'.1 hpay'.2.1 hpay'.2.2

end
end ImbalancedChen.P5Z.IndependentTestPrimeChartUniformCutoff
