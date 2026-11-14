import ImbalancedChen.P5OriginalWFixedMeshBudgets
import ImbalancedChen.P5OriginalWWholeBoxEndpointMonomials

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One actual nonzero ALL16 W mark is bound to one selected owner prefix box,
one canonical rough fine cell, and one fixed endpoint W completion run.
The whole-box group lists are then reused for its literal occurrence map.
No tuple-specific natural completedBins is promoted to a fixed witness.
-/
namespace ImbalancedChen.P5Z.OriginalWActiveMarkFixedMedium
noncomputable section
open Classical Set
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler
open U1011OriginalSixteenNearCapBoxProfiles
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalJointCommonBetaModel OriginalJointPresievedWFactors
open OriginalPresievedRoughPrimeSlots JointPresievedSlotAffineRealization
open OriginalPresievedRoughRank
open OriginalNearCapRealEndpointGeometry
open OriginalWCanonicalMeshEndpoint OriginalWOwnerOccurrenceBinding
open OriginalWFixedMeshBudgets OriginalWWholeBoxRealRun
open OriginalWWholeBoxEndpointMonomials
open PresievedRoughGateMeshReserve
open U1011OriginalFifteenMediumNumericGates (NumericGates innerQuery)

/-- The only free scale assumptions are the original eventual local
payments. All W geometry, fixed fine-cell selection, lengths, and actual
modulus product are derived from the same nonzero joint mark. -/
theorem active_W_mark_fixed_four_M {n N r : ℕ} {eta : ℚ}
    {nu0 epsilon : ℝ} (hN : 1 < N) (heta : 0 < eta)
    (hnu0 : 0 < nu0) (heps : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    (E : ℕ × ℕ → Prop) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hW : selectedPolicy n N t = wPolicy)
    (hr : r ∈ rowSupport n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) t)
    (hq : ImbalancedChen.P5Z.OriginalJointPresievedCompiler.jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      ((N : ℝ) ^ (nu0 * epsilon)) E (fullPrefix t * r) ≠ 0)
    {x U z : ℝ} (hx : 1 < x) (hz : 0 < z) (hU : 0 < U)
    (hA1 : 1 ≤ innerQuery x U z)
    (hAupper : innerQuery x U z ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hpay1 : (N : ℝ) ^ (1 - 2 *
      (delta wPolicy (ownerBox n N t) eta : ℝ)) ≤ x ^ (1 - 3 * z))
    (hpay2 : (N : ℝ) ^ (2 - 2 *
      (delta wPolicy (ownerBox n N t) eta : ℝ)) ≤ x ^ (2 - 3 * z))
    (hpay3 : (N : ℝ) ^ (2 - 39 *
      (delta wPolicy (ownerBox n N t) eta : ℝ) / 16) ≤ x ^ (2 - 3 * z)) :
    ∃ e d : ℕ,
      let B := ownerBox n N t
      let ps := canonicalSlots N
        (Nat.ceil (U1011OriginalW16NearCapNative.Z B eta N))
        ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        (U1011OriginalW16NearCapNative.Z B eta N) d
      let m := roughMeshPrecision n eta nu0 epsilon
      ∃ j : PresievedRoughGateMeshReserve.Grid ps.length m,
        let u := paddedOwnerCorner B eta
        let v := logPrimeMeshHi (nu0 * epsilon ^ 2)
          (U1011OriginalW16NearCapNative.cutoffExponent B eta : ℝ) m j
        let y := actualPrimeTupleLog N (slotVector ps)
        let actual := physicalOccurrence t ps
        let out := wGroups N B eta u v (innerQuery x U z)
        let a := (out.left.map actual).prod
        let b := (out.middle.map actual).prod
        let c := e * (out.right.map actual).prod
        ps.length ≤ rankBound nu0 epsilon ∧ r = e * d ∧
          y ∈ PresievedRoughGateMeshReserve.cell
          (nu0 * epsilon ^ 2)
          (U1011OriginalW16NearCapNative.cutoffExponent B eta : ℝ) m j ∧
          1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
          a * b * c = fullPrefix t * r ∧
          NumericGates N x U (a : ℝ) (b : ℝ) (c : ℝ) (z / 2000) := by
  let B := ownerBox n N t
  let rho : ℝ := nu0 * epsilon ^ 2
  let zeta : ℝ := (U1011OriginalW16NearCapNative.cutoffExponent B eta : ℝ)
  let ell : ℝ := (U1011OriginalW16NearCapNative.residualExponent B eta : ℝ)
  let m := roughMeshPrecision n eta nu0 epsilon
  let u := paddedOwnerCorner B eta
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hrho : 0 < rho := mul_pos hnu0 (sq_pos_of_pos heps)
  have hcut : rho < zeta := active_W_rho_lt_zeta hN heta hnu0 heps heBudget ht hW
  have hZ : U1011OriginalSixteenJointNearCapCompiler.Z n N eta t =
      U1011OriginalW16NearCapNative.Z B eta N := by
    change U1011OriginalSixteenJointNearCapCompiler.rowZ
      (selectedPolicy n N t) B eta N = _
    rw [hW]
    exact (U1011OriginalSixteenJointNearCapCompiler.W_native_binding B eta N).1
  have hD : U1011OriginalSixteenJointNearCapCompiler.D n N eta t =
      U1011OriginalW16NearCapNative.D B eta N := by
    change U1011OriginalSixteenJointNearCapCompiler.rowD
      (selectedPolicy n N t) B eta N = _
    rw [hW]
    exact (U1011OriginalSixteenJointNearCapCompiler.W_native_binding B eta N).2.1
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
  have hL : 1 < (N : ℝ) ^ ell := by
    simpa only [hD, U1011OriginalW16NearCapNative.D] using hlegal.2.1
  have hZmax : zeta ≤ (59 / 250 : ℝ) := by
    have hh := (parameters_on_joint_row hN heta hnu0 heps heBudget ht).2.1
    rw [hZ] at hh
    change (N : ℝ) ^ zeta ≤ (N : ℝ) ^ (59 / 250 : ℝ) at hh
    exact (Real.rpow_le_rpow_left_iff hn).mp hh
  have hR : ell = (physicalResidual wPolicy B eta : ℝ) := by
    simp [ell, U1011OriginalW16NearCapNative.residualExponent,
      U1011OriginalW16NearCapNative.nu, U1011OriginalW16NearCapNative.delta,
      physicalResidual, nu, delta, G, wPolicy,
      U1011OriginalSixteenNearCapBoxProfiles.Tplus,
      U1011OriginalW16FixedCellNative.Tplus,
      U1011OriginalFifteenFixedCellNative.Tplus]
  obtain ⟨e,he,d,hd,her,heActive,_,_,hpsprod,_⟩ :=
    active_joint_W_mark_factors hN heta hnu0 heps heBudget E ht hW hr hq
  let ps := canonicalSlots N
    (Nat.ceil (U1011OriginalW16NearCapNative.Z B eta N))
    ((N : ℝ) ^ rho)
    (U1011OriginalW16NearCapNative.Z B eta N) d
  have heData := U1011OriginalW16SmallBetaMonomials.active_small_beta_data heActive
  have hepos : 0 < e := heData.1
  have heSize : (e : ℝ) ≤ (N : ℝ) ^ (nu0 * epsilon) := heData.2.1.le
  have hdW : d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N
      (Nat.ceil ((N : ℝ) ^ zeta)) ((N : ℝ) ^ rho) ((N : ℝ) ^ zeta) := by
    simpa only [hZ, hD, U1011OriginalW16NearCapNative.Z,
      U1011OriginalW16NearCapNative.D] using hd
  have hrank : ps.length ≤ rankBound nu0 epsilon := by
    rw [ps, canonicalSlots_length hdW]
    exact active_joint_mark_rough_rank hN heta hnu0 heps heBudget E ht
      her hepos hd hq
  have hwidth : ((ps.length : ℝ) + 3) * logPrimeMeshStep rho zeta m ≤
      (delta wPolicy B eta : ℝ) :=
    active_W_mesh_width_le_delta heta hnu0 heps hrank hrho.le hZmax ht hW
  have hmesh := canonical_rough_fixed_endpoint hN rho zeta ell
    (((ps.length : ℝ) + 3) * logPrimeMeshStep rho zeta m)
    hrho.le hcut hL hdW le_rfl
  obtain ⟨j,hrough,hv0,hvanti,htotal,hcubes⟩ := hmesh
  have hs := (Finset.mem_filter.mp ht).1
  have hprefixCell := owner_mem n
    (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hs)
  have hbox : coordinates N t ∈ B.region :=
    cell_subset_closed_box n _ hprefixCell
  obtain ⟨hvalid,hpositive,hcert,hlo,hhi,hu2,hu10,hu32,hprefixSize⟩ :=
    active_W_owner_padded_corner hN heta ht hW
  have hpad := (endpointPadding_positive wPolicy B eta hvalid hpositive hcert heta).1.le
  have hlate : ∀ i, logPrimeMeshHi rho zeta m j i ≤ u 2 :=
    mesh_upper_late hcut (active_W_cutoff_le_u2 hN heta ht hW)
  have hpsPos : ∀ i : Fin ps.length, 0 < slotVector ps i := by
    intro i
    exact (canonicalSlots_prime_data (List.getElem_mem i.isLt)).1.pos
  have hsize : ∀ i : Occ ps.length,
      (physicalOccurrence t ps i : ℝ) ≤
        wWeight N u (logPrimeMeshHi rho zeta m j) i :=
    physicalOccurrence_size hN hs B eta hbox hpad ps rho zeta j hrough hpsPos
  have hactualPos : ∀ i, 0 < physicalOccurrence t ps i :=
    physicalOccurrence_pos hs (fun p hp => (canonicalSlots_prime_data hp).1)
  have hbeta : nu0 * epsilon ≤ (delta wPolicy B eta : ℝ) := by
    have hh := (parameters_on_joint_row hN heta hnu0 heps heBudget ht).2.2
    rw [hW] at hh
    have hdpos : 0 < (delta wPolicy B eta : ℝ) := by
      exact_mod_cast (rational_parameters wPolicy B eta hvalid hpositive hcert heta).2.2.1
    linarith
  have hM := W_fixed_box_every_tuple_M hN B eta hvalid hpositive hcert heta
    u hlo hhi hu2 hu10 hu32 (logPrimeMeshHi rho zeta m j)
    hv0 hvanti hlate
    (((ps.length : ℝ) + 3) * logPrimeMeshStep rho zeta m)
    hwidth (by simpa only [hR] using hcubes)
    hx hz hU hA1 hAupper hbeta hpay1 hpay2 hpay3
    (physicalOccurrence t ps) hactualPos hsize e hepos heSize
  have hphys : e * ((wholeLabels ps.length).map (physicalOccurrence t ps)).prod =
      fullPrefix t * r := by
    rw [physicalOccurrence_whole_product,canonicalSlots_prod hdW,her]
    ring
  refine ⟨e,d,j, hrank, her, hrough, hM.1, hM.2.1, hM.2.2.1,
    ?_, hM.2.2.2.2⟩
  exact hM.2.2.2.1.trans hphys

end
end ImbalancedChen.P5Z.OriginalWActiveMarkFixedMedium
