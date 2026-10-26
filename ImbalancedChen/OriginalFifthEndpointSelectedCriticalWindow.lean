import ImbalancedChen.OriginalFifthSelectedNaturalEndpoints

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The original nonseed raw winner's buffered selected-product bounds survive
inflation to the actual natural selected endpoint product. The fixed NEW
analytic cover lies strictly between 1/2 and 5/8. Its selected critical
interval retains explicit 2e lower and e/6 upper reserves. In particular
B_upper>=1 is proved; a quotient capacity D/(A*B_upper)>=1 is NOT inferred.

Only primitive canonical-compatible endpoint containment/inflation is
used. The native atom constructs its raw winner and the raw arithmetic
supplier proves the original selected bounds. No critical interval,
factorization, desired density, monomial estimate or license is assumed.
-/

namespace ImbalancedChen.OriginalFifthEndpointSelectedCriticalWindow20261026b

noncomputable section
open Set
open scoped Classical BigOperators
open VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open OriginalFifthInheritedParentGeometry20261026b
open OriginalFifthRawPositionalJointOwnership20261026b
open OriginalFifthRawWinnerArithmeticSupport20261026b
open OriginalFifthLiteralAffineSignBank20261026b
open OriginalFifthNativeAtomChoices20261026b
open OriginalFifthDualAnalyticCovers20261026b

theorem actual_endpoint_selected_critical_window
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (he : 0 < e)
    (chi : ℝ) (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1)))
    (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (L : ProducerRow → Prop) (sig : SignWord R4 R5) (hsig : (signAtom R4 R5 e m j sig).Nonempty)
    (k : Fin R5.length) (hnonseed : (atomChoice R4 R5 e m j L sig hsig).2 = k.succ)
    (corner : Fin 5 → ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hsmall : delta ≤ (e : ℝ) / 30)
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ q, Nat.Prime (p q))
    (hatom : actualPrimeTupleLog N p ∈ signAtom R4 R5 e m j sig)
    (hm : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hc : ∀ q, |actualPrimeTupleLog N p q - corner q| ≤ delta)
    (tau : ℝ) (htau : 0 ≤ tau) (hcost : tau * 5 ≤ (e : ℝ) / 2)
    (upper : ℕ → ℕ)
    (hlower : ∀ q ∈ (rawRowAt R5 m j k).selected, p q ≤ upper (p q))
    (hsize : ∀ q ∈ (rawRowAt R5 m j k).selected,
      (upper (p q) : ℝ) ≤ (N : ℝ) ^ tau * (p q : ℝ)) :
    let P := atomChoice R4 R5 e m j L sig hsig
    let cover := (dualCovers R4 R5 e m j P corner delta).2
    let Bupper := selectedFactor (rawRowAt R5 m j k).selected (fun q => upper (p q))
    (1 / 2 : ℝ) < cover ∧ cover < (5 / 8 : ℝ) ∧
      (N : ℝ) ^ (2 * cover + 2 * (e : ℝ) - 1) ≤ (Bupper : ℝ) ∧
      (Bupper : ℝ) ≤ (N : ℝ) ^ ((2 / 3 : ℝ) * (57 / 64 - cover) - (e : ℝ) / 6) ∧
      (1 : ℝ) ≤ Bupper := by
  dsimp only
  let t := actualPrimeTupleLog N p
  let P := atomChoice R4 R5 e m j L sig hsig
  let cover := (dualCovers R4 R5 e m j P corner delta).2
  let I := (rawRowAt R5 m j k).selected
  let lam := actualNext5 e chi m omega j (fourthFamily R4) L (fifthFamily R5 m) t
  let B := selectedFactor I p
  let Bu := selectedFactor I (fun q => upper (p q))
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hNr
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hlabel := atomChoice_spec R4 R5 e m j L sig hsig hatom
  have hparent := congrArg Prod.fst hlabel
  have hwinner := congrArg Prod.snd hlabel
  change parentOwner R4 e m j L t = P.1 at hparent
  change fifthOwner R4 R5 e m j (parentOwner R4 e m j L t) t = P.2 at hwinner
  rw [hparent, hnonseed] at hwinner
  have hraw := nonseed_winner_arithmetic_support R4 R5 e chi m omega J j hj L
    N hN p hp hm P.1 hparent k hwinner
  dsimp only at hraw
  have hlam := exponent5_on_selected_owner e chi m omega (fourthFamily R4) L J (fifthFamily R5 m)
    N hN p (fun q => (hp q).pos) j hj hm
  rw [hlam] at hraw
  have hBbounds : (N : ℝ) ^ (2 * lam + 4 * (e : ℝ) - 1) ≤ (B : ℝ) ∧
      (B : ℝ) ≤ (N : ℝ) ^ ((2 / 3 : ℝ) * (57 / 64 - lam - 2 * (e : ℝ))) :=
    hraw.2.2.2.2.2
  have hbr := actual_atom_dualCovers R4 R5 e chi m omega J j hj L sig hsig
    corner t delta hd hsmall hatom hm hc
  have hcover : lam + (e : ℝ) / 2 ≤ cover ∧ cover ≤ lam + (e : ℝ) := hbr.2
  have hcaps := actual_caps_from_atomChoice R4 R5 e chi m omega J j hj L sig hsig hatom hm
  rw [hnonseed] at hcaps
  have hlamCandidate : lam = candidate (e : ℝ) I t := hcaps.2
  have hg := owned_raw_geometry R4 R5 e m j P.1 t hm k hwinner
  have hlamLow : (1 / 2 : ℝ) < lam := by rw [hlamCandidate]; exact hg.2.1
  have hlamHigh : lam ≤ VariableEnvelope.cap - 2 * (e : ℝ) := by
    rw [hlamCandidate, candidate, envelope_eq_v]
    exact sub_le_sub_right (v_le_cap _) _
  have hcoverLow : (1 / 2 : ℝ) < cover := by linarith
  have hcoverHigh : cover < (5 / 8 : ℝ) := by
    norm_num [VariableEnvelope.cap] at hlamHigh
    linarith
  have hBmono : (B : ℝ) ≤ (Bu : ℝ) := by
    have h := Finset.prod_le_prod (fun q (_hq : q ∈ I) => Nat.cast_nonneg (p q))
      (fun q hq => (show (p q : ℝ) ≤ upper (p q) by exact_mod_cast hlower q hq))
    simpa only [B, Bu, selectedFactor, Nat.cast_prod] using h
  have hcard : (I.card : ℝ) ≤ 5 := by exact_mod_cast (Finset.card_le_univ I)
  have hselectedCost : tau * (I.card : ℝ) ≤ (e : ℝ) / 2 := by nlinarith
  have hBuSize : (Bu : ℝ) ≤ (N : ℝ) ^ (tau * (I.card : ℝ)) * (B : ℝ) := by
    calc
      (Bu : ℝ) = ∏ q ∈ I, (upper (p q) : ℝ) := by simp only [Bu, selectedFactor, Nat.cast_prod]
      _ ≤ ∏ q ∈ I, (N : ℝ) ^ tau * (p q : ℝ) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun q hq => hsize q hq)
      _ = ((N : ℝ) ^ tau) ^ I.card * (B : ℝ) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, B, selectedFactor, Nat.cast_prod]
      _ = (N : ℝ) ^ (tau * (I.card : ℝ)) * (B : ℝ) := by rw [Real.rpow_mul_natCast hN0.le]
  have hLower : (N : ℝ) ^ (2 * cover + 2 * (e : ℝ) - 1) ≤ (Bu : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)).trans (hBbounds.1.trans hBmono)
  have hUpper : (Bu : ℝ) ≤ (N : ℝ) ^ ((2 / 3 : ℝ) * (57 / 64 - cover) - (e : ℝ) / 6) := by
    calc
      (Bu : ℝ) ≤ (N : ℝ) ^ (tau * (I.card : ℝ)) * (B : ℝ) := hBuSize
      _ ≤ (N : ℝ) ^ (tau * (I.card : ℝ)) *
          (N : ℝ) ^ ((2 / 3 : ℝ) * (57 / 64 - lam - 2 * (e : ℝ))) :=
        mul_le_mul_of_nonneg_left hBbounds.2 (Real.rpow_nonneg hN0.le _)
      _ = (N : ℝ) ^ (tau * (I.card : ℝ) + (2 / 3 : ℝ) * (57 / 64 - lam - 2 * (e : ℝ))) :=
        (Real.rpow_add hN0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNr.le (by nlinarith)
  refine ⟨hcoverLow, hcoverHigh, hLower, hUpper, ?_⟩
  exact (Real.one_le_rpow hNr.le (by linarith : 0 ≤ 2 * cover + 2 * (e : ℝ) - 1)).trans hLower

end
end ImbalancedChen.OriginalFifthEndpointSelectedCriticalWindow20261026b
