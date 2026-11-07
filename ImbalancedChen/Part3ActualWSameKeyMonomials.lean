import ImbalancedChen.Part3ActualWFineKeyInitialization
import ImbalancedChen.P5ZU1011OriginalW16FactorMonomials

/-!
# Three monomials on the same actual W-gap frozen bins

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual frozen-key program and actual theta cap supply both numerical
cases. The successful case reuses P5's W_success_monomials; the first-
overflow case uses selectedPair_monomials with its derived middle product.
No initialization, factorization or desired monomial is supplied to the
final retained-atom theorem. Every tuple uses the same original bin labels.

The physical residue exponent is 1 and the spectral exponent is 7/32.
Local transport retains qscale in ALL powers, including N^(7/32).
This is not an assertion with an independently reset local alpha or theta.
W-close, small attachment and the final signed tensor remain separate.
-/

namespace ImbalancedChen.Part3.ActualWSameKeyMonomials

noncomputable section

open ActualWThreeCapacityRun ActualWResidualCompletion ActualWFineWordAdapter
open ActualWFineKeyInitialization VariableEnvelope

def Monomials (x delta A a b c : ℝ) : Prop :=
  A ^ 2 * b * c ^ 2 ≤ x ^ (1 - 4 * delta) ∧
    x ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 4 * delta) ∧
    (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 39 * delta / 8)

def LocalMonomials (N x delta A a b c : ℝ) : Prop :=
  let qscale := Real.log N / Real.log x
  A ^ 2 * b * c ^ 2 ≤ x ^ (qscale * (1 - 4 * delta)) ∧
    x ^ (qscale * (7 / 32)) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (qscale * (2 - 4 * delta)) ∧
    (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤
      x ^ (qscale * (2 - 39 * delta / 8))

theorem transport {N x delta A a b c : ℝ} (hN : 0 < N) (hx : 1 < x)
    (h : Monomials N delta A a b c) : LocalMonomials N x delta A a b c := by
  unfold Monomials at h
  simp_rw [ActualCompactInitialSupport.physical_power_eq_local hN hx] at h
  exact h

/-- The third monomial is increasing in all three positive factors,
including the middle factor despite its occurrence in the denominator. -/
theorem third_monomial_mono {A a b c a' b' c' : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c')
    (haa : a ≤ a') (hbb : b ≤ b') (hcc : c ≤ c') :
    (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤
      (A * c' / b') ^ (7 / 16 : ℝ) * A * a' * b' ^ 5 * c' ^ 2 := by
  have hlog (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
      Real.log ((A * w / v) ^ (7 / 16 : ℝ) * A * u * v ^ 5 * w ^ 2) =
        (23 / 16 : ℝ) * Real.log A + Real.log u +
          (73 / 16 : ℝ) * Real.log v + (39 / 16 : ℝ) * Real.log w := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hu.ne', Real.log_mul (by positivity) hA.ne',
      Real.log_rpow (div_pos (mul_pos hA hw) hv),
      Real.log_div (mul_ne_zero hA.ne' hw.ne') hv.ne', Real.log_mul hA.ne' hw.ne']
    simp only [Real.log_pow]
    ring
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [hlog a b c ha hb hc, hlog a' b' c' ha' hb' hc']
  have hla := (Real.log_le_log_iff ha ha').mpr haa
  have hlb := (Real.log_le_log_iff hb hb').mpr hbb
  have hlc := (Real.log_le_log_iff hc hc').mpr hcc
  linarith

/-- Coordinatewise reduction from the fixed keys preserves every target. -/
theorem monomials_downward {x delta A a b c a' b' c' : ℝ}
    (hx : 0 < x) (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c')
    (haa : a ≤ a') (hbb : b ≤ b') (hcc : c ≤ c')
    (h : Monomials x delta A a' b' c') : Monomials x delta A a b c := by
  have hb5 := pow_le_pow_left₀ hb.le hbb 5
  have hc2 := pow_le_pow_left₀ hc.le hcc 2
  have hAa := mul_le_mul_of_nonneg_left haa hA.le
  have hcommon : A * a * b ^ 5 * c ^ 2 ≤ A * a' * b' ^ 5 * c' ^ 2 :=
    mul_le_mul (mul_le_mul hAa hb5 (pow_nonneg hb.le 5) (mul_nonneg hA.le ha'.le)) hc2
      (sq_nonneg c) (mul_nonneg (mul_nonneg hA.le ha'.le) (pow_nonneg hb'.le 5))
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_le_mul (mul_le_mul_of_nonneg_left hbb (sq_nonneg A)) hc2
      (sq_nonneg c) (mul_nonneg (sq_nonneg A) hb'.le)).trans h.1
  · have hh := mul_le_mul_of_nonneg_left hcommon (Real.rpow_nonneg hx.le (7 / 32))
    have hh' : x ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤
        x ^ (7 / 32 : ℝ) * A * a' * b' ^ 5 * c' ^ 2 := by
      simpa only [mul_assoc] using hh
    exact hh'.trans h.2.1
  · exact (third_monomial_mono hA ha hb hc ha' hb' hc' haa hbb hcc).trans h.2.2

private theorem atom_product_pos (N : ℕ) (sigma : ℝ) (word primes : List ℕ)
    (hprimes : primes ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word) :
    (0 : ℝ) < primes.prod := by
  have hp := actualPrimeSlotBox_prime (actualPrimeFineLabelFinset N sigma) word
    (fun _ _ _ hq => (mem_actualPrimeFineLabelFinset.mp hq).1) primes hprimes
  have hnat : 0 < primes.prod := List.prod_pos (fun q hq => (hp q hq).pos)
  exact_mod_cast hnat

/-- All three bounds belong to the SAME fixed key bins in BOTH actual
execution branches. Actual tuples inherit them by reduction of those keys.
The universally quantified local conclusion preserves exact qscale. -/
theorem actual_W_gap_same_key_monomials
    (e h sigma : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ e / 64)
    (hwidth : sigma * (k + 1) ≤ e / 2)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hgap : e / 4 < wInner (t 0) (t 1) (t 2) - v (t 0))
    (p labels : Fin 3 → ℕ) (primeTail labelTail : List ℕ)
    (hshape : state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: primeTail)
    (hatom : state.selectedPrefix.reverse ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
      (labels 0 :: labels 1 :: labels 2 :: labelTail))
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    let theta := actualExtendedThirdRescueParameter e m j t
    let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
    let out := fineSlots N sigma A ((N : ℝ) ^ (2 * theta - 1))
      ((N : ℝ) ^ (1 - theta - e / 32) / A) labels labelTail
    Positive key out ∧ wp key out.left ≤ A ∧
      Monomials (N : ℝ) (e / 64) A (wp key out.left) (wp key out.middle) (wp key out.right) ∧
      (∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 64) A
        (wp key out.left) (wp key out.middle) (wp key out.right)) ∧
      ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
          (labels 0 :: labels 1 :: labels 2 :: labelTail),
        ∃ ls ms rs,
          ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
          ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
          rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
          ls.prod * ms.prod * rs.prod = ps.prod ∧
          (ls.prod : ℝ) ≤ wp key out.left ∧ (ms.prod : ℝ) ≤ wp key out.middle ∧
          (rs.prod : ℝ) ≤ wp key out.right ∧
          Monomials (N : ℝ) (e / 64) A (ls.prod : ℝ) (ms.prod : ℝ) (rs.prod : ℝ) ∧
          ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 64) A
            (ls.prod : ℝ) (ms.prod : ℝ) (rs.prod : ℝ) := by
  obtain ⟨hperm, hcases, hwhole⟩ := actual_W_gap_frozen_atom e h sigma m N cap k hk w z weight
    state hstate hN he0 he hsigma0 hsigma hwidth hmesh hj howned hfull ht hwinner hgap
    p labels primeTail labelTail hshape hatom A hA hAupper
  let theta := actualExtendedThirdRescueParameter e m j t
  let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
  let out := fineSlots N sigma A ((N : ℝ) ^ (2 * theta - 1))
    ((N : ℝ) ^ (1 - theta - e / 32) / A) labels labelTail
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hApos : 0 < A := zero_lt_one.trans_le hA
  obtain ⟨ls0, ms0, rs0, hls0, hms0, hrs0, hprod0, hL0, hM0, hR0⟩ :=
    hwhole state.selectedPrefix.reverse hatom
  have ha : 0 < wp key out.left := (atom_product_pos N sigma _ _ hls0).trans_le hL0
  have hb : 0 < wp key out.middle := (atom_product_pos N sigma _ _ hms0).trans_le hM0
  have hc : 0 < wp key out.right := (atom_product_pos N sigma _ _ hrs0).trans_le hR0
  have hcapTheta : theta ≤ (153 / 256 : ℝ) := by
    have hh := actual_W_gap_theta_cap he0 he hmesh hfull ht hwinner hgap
    dsimp [theta]
    linarith
  have hdelta : 2 * (e / 64) = e / 32 := by ring
  have hresult : wp key out.left ≤ A ∧
      Monomials (N : ℝ) (e / 64) A (wp key out.left) (wp key out.middle) (wp key out.right) := by
    rcases hcases with hbounded | ⟨hlower, hupper, hleft, hright⟩
    · refine ⟨hbounded.1, ?_⟩
      exact P5Z.U1011OriginalW16FactorMonomials.W_success_monomials
        hNr hApos ha hb hc hcapTheta hbounded.1 hbounded.2.1
        (by simpa only [hdelta] using hbounded.2.2)
    · have hupper' : wp key out.middle ≤ (N : ℝ) ^ actualSelectedSubproductUpper 1 theta := by
        calc
          _ ≤ (N : ℝ) ^ (2 * theta - 1) *
              (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 16) := hupper
          _ = (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 16) := by
            rw [← Real.rpow_add hNpos]
            congr 1
            ring
          _ ≤ (N : ℝ) ^ actualSelectedSubproductUpper 1 theta :=
            Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)
      have hproduct : A * wp key out.middle * wp key out.right ≤
          (N : ℝ) ^ (theta - 2 * (e / 64)) := by
        have hh := (le_div_iff₀ (mul_pos hApos hb)).mp hright
        rw [hdelta]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
      refine ⟨hleft, ?_⟩
      simpa only [Monomials, mul_one] using selectedPair_monomials (α := 1)
        hNr hApos ha hb hc hproduct hlower.le hupper' hleft
  refine ⟨⟨ha, hb, hc⟩, hresult.1, hresult.2, ?_, ?_⟩
  · intro x hx
    exact transport hNpos hx hresult.2
  · intro ps hps
    obtain ⟨ls, ms, rs, hls, hms, hrs, hprod, hL, hM, hR⟩ := hwhole ps hps
    have hmono := monomials_downward hNpos hApos
      (atom_product_pos N sigma _ _ hls) (atom_product_pos N sigma _ _ hms)
      (atom_product_pos N sigma _ _ hrs) ha hb hc hL hM hR hresult.2
    exact ⟨ls, ms, rs, hls, hms, hrs, hprod, hL, hM, hR, hmono,
      fun x hx => transport hNpos hx hmono⟩

end

end ImbalancedChen.Part3.ActualWSameKeyMonomials
