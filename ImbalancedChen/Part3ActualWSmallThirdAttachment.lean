import ImbalancedChen.Part3ActualWCloseSameKeyMonomials
import ImbalancedChen.Part3ActualSmallAttachmentSupport

/-!
# The same actual small Rosser factor on the frozen W third group

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The manuscript attaches beta only to group 3. The original frozen rough
slot lists are computed before that attachment and are not rerun for the
small factor. Its exact monomial costs are 2*epsilon, 2*epsilon and
(39/16)*epsilon. The physical alpha=1 bounds with delta=e/64 therefore
retain delta=e/128 under the actual small-factor bound epsilon<=e/128.

The final theorem extracts the SAME a, rough state and q from the literal
nonzero attachedUpperCoefficient. It covers both actual row-4 close/gap
decisions on the original atom; no small-factor license or monomial input
is supplied. Existing full-square attachment support is reused by import,
not re-proved. Analytic local alpha/theta perturbation, other winner rows,
and the full signed tensor/spectral license are separate obligations.
-/

namespace ImbalancedChen.Part3.ActualWSmallThirdAttachment

noncomputable section

open scoped Classical
open ActualWThreeCapacityRun ActualWResidualCompletion ActualWFineWordAdapter
open ActualWCloseFullRepair ActualWCloseSameKeyMonomials ActualWSameKeyMonomials
open ActualAttachedRoughFrontier VariableEnvelope

/-- The third-group attachment consumes exactly its proved power size.
This lemma is applied below to the original fixed-bin monomial theorem. -/
theorem third_attachment_monomials {x delta epsilon A a b c small : ℝ}
    (hx : 1 < x) (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsmall : 0 < small) (hsize : small ≤ x ^ epsilon) (heps : epsilon ≤ delta)
    (hmono : Monomials x delta A a b c) : Monomials x (delta / 2) A a b (small * c) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hsquare : small ^ 2 ≤ x ^ (2 * epsilon) := by
    calc
      _ ≤ (x ^ epsilon) ^ 2 := pow_le_pow_left₀ hsmall.le hsize 2
      _ = _ := by rw [← Real.rpow_mul_natCast hx0.le]; congr 1; norm_num; ring
  have hslog := (Real.le_rpow_iff_log_le hsmall hx0).mp hsize
  have hepsL := mul_le_mul_of_nonneg_right heps hL.le
  refine ⟨?_, ?_, ?_⟩
  · calc
      A ^ 2 * b * (small * c) ^ 2 = small ^ 2 * (A ^ 2 * b * c ^ 2) := by ring
      _ ≤ x ^ (2 * epsilon) * x ^ (1 - 4 * delta) :=
        mul_le_mul hsquare hmono.1 (by positivity) (Real.rpow_nonneg hx0.le _)
      _ = x ^ (2 * epsilon + (1 - 4 * delta)) := (Real.rpow_add hx0 _ _).symm
      _ ≤ x ^ (1 - 4 * (delta / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  · calc
      x ^ (7 / 32 : ℝ) * A * a * b ^ 5 * (small * c) ^ 2 =
          small ^ 2 * (x ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2) := by ring
      _ ≤ x ^ (2 * epsilon) * x ^ (2 - 4 * delta) :=
        mul_le_mul hsquare hmono.2.1 (by positivity) (Real.rpow_nonneg hx0.le _)
      _ = x ^ (2 * epsilon + (2 - 4 * delta)) := (Real.rpow_add hx0 _ _).symm
      _ ≤ x ^ (2 - 4 * (delta / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  · have hthird := (Real.le_rpow_iff_log_le (by positivity : (0 : ℝ) <
        (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2) hx0).mp hmono.2.2
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by positivity) hA.ne',
      Real.log_rpow (div_pos (mul_pos hA hc) hb),
      Real.log_div (mul_ne_zero hA.ne' hc.ne') hb.ne', Real.log_mul hA.ne' hc.ne'] at hthird
    simp only [Real.log_pow] at hthird
    apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by positivity) hA.ne',
      Real.log_rpow (div_pos (mul_pos hA (mul_pos hsmall hc)) hb),
      Real.log_div (mul_ne_zero hA.ne' (mul_ne_zero hsmall.ne' hc.ne')) hb.ne',
      Real.log_mul hA.ne' (mul_ne_zero hsmall.ne' hc.ne')]
    simp only [Real.log_pow, Real.log_mul hsmall.ne' hc.ne']
    nlinarith only [hthird, hslog, hepsL]

/-- One deterministic original-word assignment, before any small factor.
The real close/gap test chooses the already proved fixed-key programs. -/
def row4Slots (N : ℕ) (e sigma : ℝ) (m : ℕ) (j : ActualExtendedThirdDyadicLabel m)
    (t : Fin 3 → ℝ) (A : ℝ) (labels : Fin 3 → ℕ) (tail : List ℕ) : Bins ℕ :=
  if wInner (t 0) (t 1) (t 2) - v (t 0) ≤ e / 4 then
    closeSlots N sigma ((N : ℝ) ^ (actualExtendedThirdBaseParameter e m j - e / 32))
      A (labels 0) (labels 1 :: labels 2 :: tail)
  else
    let theta := actualExtendedThirdRescueParameter e m j t
    fineSlots N sigma A ((N : ℝ) ^ (2 * theta - 1))
      ((N : ℝ) ^ (1 - theta - e / 32) / A) labels tail

private theorem atom_product_pos (N : ℕ) (sigma : ℝ) (word primes : List ℕ)
    (hprimes : primes ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word) :
    (0 : ℝ) < primes.prod := by
  have hp := actualPrimeSlotBox_prime (actualPrimeFineLabelFinset N sigma) word
    (fun _ _ _ hq => (mem_actualPrimeFineLabelFinset.mp hq).1) primes hprimes
  have hh : 0 < primes.prod := List.prod_pos (fun q hq => (hp q hq).pos)
  exact_mod_cast hh

/-- Attach the actual small factor to group 3 while retaining the same
keyword assignment for the whole atom. Both W execution branches occur
inside this proof; no branch-dependent small factor is chosen. -/
theorem actual_row4_atom_small_attachment
    (e h sigma epsilon : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ e / 64)
    (hwidth : sigma * (k + 1) ≤ e / 2) (heps : epsilon ≤ e / 128)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (p labels : Fin 3 → ℕ) (primeTail labelTail : List ℕ)
    (hshape : state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: primeTail)
    (hatom : state.selectedPrefix.reverse ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
      (labels 0 :: labels 1 :: labels 2 :: labelTail))
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (small : ℕ) (hsmall : 0 < small) (hsmallSize : (small : ℝ) ≤ (N : ℝ) ^ epsilon) :
    let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
    let out := row4Slots N e sigma m j t A labels labelTail
    Monomials (N : ℝ) (e / 128) A (wp key out.left) (wp key out.middle)
      ((N : ℝ) ^ epsilon * wp key out.right) ∧
    (∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 128) A
      (wp key out.left) (wp key out.middle) ((N : ℝ) ^ epsilon * wp key out.right)) ∧
    ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
        (labels 0 :: labels 1 :: labels 2 :: labelTail),
      ∃ ls ms rs,
        ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
        ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
        rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
        ls.prod * ms.prod * (small * rs.prod) = small * ps.prod ∧
        (ls.prod : ℝ) ≤ A ∧
        Monomials (N : ℝ) (e / 128) A (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) ∧
        ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 128) A
          (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hspos : (0 : ℝ) < small := by exact_mod_cast hsmall
  have hhalve : (e / 64) / 2 = e / 128 := by ring
  have heps' : epsilon ≤ e / 64 := by linarith
  let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
  have consume (out : Bins ℕ) (hpositive : Positive key out)
      (hkeymono : Monomials (N : ℝ) (e / 64) A
        (wp key out.left) (wp key out.middle) (wp key out.right)) (hleft : wp
      (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) out.left ≤ A)
      (hwhole : ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
          (labels 0 :: labels 1 :: labels 2 :: labelTail),
        ∃ ls ms rs,
          ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
          ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
          rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
          ls.prod * ms.prod * rs.prod = ps.prod ∧
          (ls.prod : ℝ) ≤ wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) out.left ∧
          (ms.prod : ℝ) ≤ wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) out.middle ∧
          (rs.prod : ℝ) ≤ wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) out.right ∧
          Monomials (N : ℝ) (e / 64) A (ls.prod : ℝ) (ms.prod : ℝ) (rs.prod : ℝ) ∧
          ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 64) A
            (ls.prod : ℝ) (ms.prod : ℝ) (rs.prod : ℝ)) :
      Monomials (N : ℝ) (e / 128) A (wp key out.left) (wp key out.middle)
        ((N : ℝ) ^ epsilon * wp key out.right) ∧
      (∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 128) A
        (wp key out.left) (wp key out.middle) ((N : ℝ) ^ epsilon * wp key out.right)) ∧
      ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
          (labels 0 :: labels 1 :: labels 2 :: labelTail),
        ∃ ls ms rs,
          ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
          ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
          rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
          ls.prod * ms.prod * (small * rs.prod) = small * ps.prod ∧
          (ls.prod : ℝ) ≤ A ∧
          Monomials (N : ℝ) (e / 128) A (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) ∧
          ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 128) A
            (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) := by
    have hkeyAttached := third_attachment_monomials hNr (zero_lt_one.trans_le hA)
      hpositive.1 hpositive.2.1 hpositive.2.2
      (Real.rpow_pos_of_pos hNpos epsilon) le_rfl heps' hkeymono
    have hkeyAttached' : Monomials (N : ℝ) (e / 128) A
        (wp key out.left) (wp key out.middle) ((N : ℝ) ^ epsilon * wp key out.right) := by
      simpa only [hhalve] using hkeyAttached
    refine ⟨hkeyAttached', fun x hx => transport hNpos hx hkeyAttached', ?_⟩
    intro ps hps
    obtain ⟨ls, ms, rs, hls, hms, hrs, hprod, hL, hM, hR, hmono, hlocal⟩ := hwhole ps hps
    have hm := third_attachment_monomials hNr (zero_lt_one.trans_le hA)
      (atom_product_pos N sigma _ _ hls) (atom_product_pos N sigma _ _ hms)
      (atom_product_pos N sigma _ _ hrs) hspos hsmallSize heps' hmono
    have hm' : Monomials (N : ℝ) (e / 128) A
        (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) := by
      simpa only [hhalve, Nat.cast_mul] using hm
    refine ⟨ls, ms, rs, hls, hms, hrs, ?_, hL.trans hleft, hm',
      fun x hx => transport hNpos hx hm'⟩
    calc
      ls.prod * ms.prod * (small * rs.prod) = small * (ls.prod * ms.prod * rs.prod) := by ring
      _ = small * ps.prod := by rw [hprod]
  by_cases hclose : wInner (t 0) (t 1) (t 2) - v (t 0) ≤ e / 4
  · obtain ⟨hpositive, hleft, hkeymono, _, hwhole⟩ := actual_W_close_same_key_monomials
      e h sigma m N cap k hk w z weight state hstate hN he0 he hsigma0 hsigma hwidth hmesh
      hj howned hfull ht hwinner hclose p primeTail hshape (labels 0)
      (labels 1 :: labels 2 :: labelTail) hatom A hA hAupper
    simpa only [row4Slots, if_pos hclose] using consume _ hpositive hkeymono hleft hwhole
  · obtain ⟨hpositive, hleft, hkeymono, _, hwhole⟩ := actual_W_gap_same_key_monomials
      e h sigma m N cap k hk w z weight state hstate hN he0 he hsigma0 hsigma hwidth hmesh
      hj howned hfull ht hwinner (lt_of_not_ge hclose) p labels primeTail labelTail hshape hatom A hA hAupper
    simpa only [row4Slots, if_neg hclose] using consume _ hpositive hkeymono hleft hwhole

/-- Literal nonzero attached rho supplies the small factor ONCE, before
any cell, atom or medium assignment. Both W branches retain that same
factor and the same original modulus q. No small-support license is an
input, and the existing rough-support theorem is not duplicated. -/
theorem actual_attached_row4_same_keyword
    (e h sigma epsilon : ℝ) (m N : ℕ) (cap : ℕ → ℕ)
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ e / 64) (heps : epsilon ≤ e / 128)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32) {q : ℕ}
    (hq : attachedUpperCoefficient 1 thirdPrefixRho epsilon
      (fun M => actualExtendedThirdCompactUpperPolicy e h m M false) cap N q ≠ 0) :
    ∃ small k (state : FirstExitDepthState ℕ),
      small ∈ actualSmallRosserSupport N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ∧
      (small : ℝ) < (N : ℝ) ^ epsilon ∧ state.selectedPrefix.length = k ∧
      state ∈ firstExitDepthFrontier k (actualExtendedThirdCompactUpperPolicy e h m N)
        (fun _ => 1) [] true 1
        (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)) ∧
      q = small * state.selectedPrefix.prod ∧
      ∀ j : ActualExtendedThirdDyadicLabel m, j ∈ actualExtendedThirdCompactCells e h m →
        3 ≤ k → sigma * (k + 1) ≤ e / 2 →
        primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
          actualExtendedThirdOwnedCell m j →
        actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e →
        ∀ t : Fin 3 → ℝ, t ∈ actualExtendedThirdPhysicalCell m j →
          actualExtendedThirdLeastWinningIndex e m j = 4 →
        ∀ (p labels : Fin 3 → ℕ) (primeTail labelTail : List ℕ),
          state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: primeTail →
          state.selectedPrefix.reverse ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
            (labels 0 :: labels 1 :: labels 2 :: labelTail) →
        ∀ A : ℝ, 1 ≤ A → A ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
          let out := row4Slots N e sigma m j t A labels labelTail
          ∃ ls ms rs,
            ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
            ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
            rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
            ls.prod * ms.prod * (small * rs.prod) = q ∧ (ls.prod : ℝ) ≤ A ∧
            Monomials (N : ℝ) (e / 128) A (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) ∧
            ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 128) A
              (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) := by
  obtain ⟨small, k, state, hsmall, hsize, hlen, hstate, hqprod, hrough, hsupport⟩ :=
    actual_attached_upper_ne_zero_frontier e h epsilon m N cap hq
  have hpositive : 0 < small := Nat.pos_of_mem_divisors hsmall
  refine ⟨small, k, state, hsmall, hsize, hlen, hstate, hqprod, ?_⟩
  intro j hj hk hwidth howned hfull t ht hwinner p labels primeTail labelTail hshape hatom A hA hAupper
  obtain ⟨hkeyMono, hkeyLocal, hwhole⟩ := actual_row4_atom_small_attachment e h sigma epsilon m N (cap N) k hk
    ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho) (fun _ => 1)
    state hstate hN he0 he hsigma0 hsigma hwidth heps hmesh hj howned hfull ht hwinner
    p labels primeTail labelTail hshape hatom A hA hAupper small hpositive hsize.le
  obtain ⟨ls, ms, rs, hls, hms, hrs, hprod, hleft, hmono, hlocal⟩ :=
    hwhole state.selectedPrefix.reverse hatom
  refine ⟨ls, ms, rs, hls, hms, hrs, ?_, hleft, hmono, hlocal⟩
  calc
    ls.prod * ms.prod * (small * rs.prod) = small * state.selectedPrefix.reverse.prod := hprod
    _ = q := by rw [List.prod_reverse, ← hqprod]

end

end ImbalancedChen.Part3.ActualWSmallThirdAttachment
