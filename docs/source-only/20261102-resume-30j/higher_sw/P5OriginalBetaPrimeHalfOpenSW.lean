import ImbalancedChen.P5OriginalBetaPrimeSW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual modulus dyadics are [U,2U), whereas the prime SW primitive
uses (U,2U]. Their two point masses are retained and paid, not discarded
as measure zero. This file proves the same source licence for [U,2U).
-/

namespace ImbalancedChen.P5Z.OriginalBetaPrimeHalfOpenSW
noncomputable section
open Classical Finset Filter Set
open scoped BigOperators Topology
open ImbalancedChen ImbalancedChen.Part3
open All16MarkedCommonFineSource All16FineMeshGateScalar
open All16MarkedFineScalarBudget All16ComputedWholeWordAssignment
open ActualAll16UnrestrictedResidualConvolution ActualInnerPerLabelGamma
open SameWholeAssignmentPerLabel OriginalSingletonPrimeSource OriginalSingletonPrimeSW
open ComputedSingletonPrimeSWConsumer OriginalBetaPrimeSource OriginalBetaPrimeSW
open PrimeMellinProfileVariation20261026b

def halfOpenCarrier (N cap m : ℕ) (i : Fin (m+1)) (w U : ℝ) : Finset ℕ :=
  (attachedSupport (commonAlphabet N m) [i] N cap w).filter
    (fun n => U ≤ (n : ℝ) ∧ (n : ℝ) < 2*U)

theorem exactKernel_norm_le {q : ℕ} (hq : 0 < q) (b d : ℕ) :
    ‖exactKernel q b d‖ ≤ 2 := by
  have hphi : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hi : ‖(1 : ℂ)/(q.totient : ℂ)‖ ≤ 1 := by
    simpa only [norm_div,norm_one,Complex.norm_natCast] using
      (div_le_one (zero_lt_one.trans_le hphi)).mpr hphi
  by_cases ha : Nat.ModEq q d b <;> by_cases hc : d.Coprime q
  · simp only [exactKernel,if_pos ha,if_pos hc]
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_left hi 1)
  · simp [exactKernel,ha,hc]
  · simpa only [exactKernel,if_neg ha,if_pos hc,zero_sub,norm_neg] using
      hi.trans (by norm_num : (1 : ℝ) ≤ 2)
  · simp [exactKernel,ha,hc]

/-- An endpoint contributes at most one integer, with the exact mean
included. No prime endpoint is identified with a null set. -/
theorem endpoint_mass_norm_le (S : Finset ℕ) (c : ℕ → ℂ) (v M : ℝ)
    (hM : 0 ≤ M) (hc : ∀ d ∈ S, (d : ℝ) = v → ‖c d‖ ≤ M)
    {q b : ℕ} (hq : 0 < q) :
    ‖∑ d ∈ S, if (d : ℝ) = v then c d * exactKernel q b d else 0‖ ≤ 2*M := by
  rw [← Finset.sum_filter]
  let E := S.filter (fun d => (d : ℝ) = v)
  have hcard : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have heq : (a : ℝ) = b :=
      (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    exact_mod_cast heq
  calc
    _ ≤ ∑ d ∈ E, ‖c d * exactKernel q b d‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ E, M*2 := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
      exact mul_le_mul (hc d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2)
        (exactKernel_norm_le hq b d) (norm_nonneg _) hM
    _ = (E.card : ℝ)*(M*2) := by simp
    _ ≤ 2*M := by
      have hh : (E.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith

theorem halfOpen_error_eq (S : Finset ℕ) (c : ℕ → ℂ) {U : ℝ}
    (hU : 0 < U) (q b : ℕ) :
    auxiliarySWError (S.filter (fun d => U ≤ (d : ℝ) ∧ (d : ℝ) < 2*U)) c 1 q b =
      auxiliarySWError (S.filter (fun d => U < (d : ℝ) ∧ (d : ℝ) ≤ 2*U)) c 1 q b +
      (∑ d ∈ S, if (d : ℝ) = U then c d*exactKernel q b d else 0) -
      (∑ d ∈ S, if (d : ℝ) = 2*U then c d*exactKernel q b d else 0) := by
  simp only [error_eq_kernel,Finset.sum_filter,← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h1 : (d : ℝ) = U
  · have h2 : (d : ℝ) ≠ 2*U := by linarith
    simp [h1,h2,show U < 2*U by linarith]
  · by_cases h2 : (d : ℝ) = 2*U
    · simp [h1,h2,show U < 2*U by linarith,show U ≤ 2*U by linarith]
    · have hsame : (U ≤ (d : ℝ) ∧ (d : ℝ) < 2*U) ↔
          (U < (d : ℝ) ∧ (d : ℝ) ≤ 2*U) := by
        constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
      simp only [h1,h2,if_false,add_zero,sub_zero,hsame]

theorem value_norm_le {N cap m r : ℕ} (hN : 1 < N) (i : Fin (m+1))
    {w B U M : ℝ} (hw : w ≤ lower N m i) (hU : 0 < U) (hM : 0 ≤ M)
    (Phi : ℝ → ℝ) (hPhi : ∀ y ∈ Icc (1 : ℝ) 2, |Phi y| ≤ M) (t : ℝ)
    {d : ℕ} (hd : d ∈ attachedSupport (commonAlphabet N m) [i] N cap w)
    (hdU : U ≤ (d : ℝ)) (hd2U : (d : ℝ) ≤ 2*U) :
    ‖value N cap m r i w B Phi t U d‖ ≤ M := by
  change d ∈ (smallRoughPairs (actualSmallRosserSupport N cap w)
    (support (commonAlphabet N m) [i])).image (fun x => x.1*x.2) at hd
  obtain ⟨⟨e,p⟩,hep,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨he,hp⟩ := Finset.mem_product.mp hep
  rw [singleton_support] at hp
  have hc := original_beta_prime_value (r := r) (B := B) hN i hw he hp
  have hy : (((e*p : ℕ) : ℝ)/U) ∈ Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ hU).mpr (by simpa using hdU),(div_le_iff₀ hU).mpr hd2U⟩
  simp only [value,hc,norm_mul,physicalProfile,profile,phase_norm,mul_one,
    Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (hPhi _ hy) (raw_beta_abs_le_one N cap r w B e)
    (abs_nonneg _) hM).trans_eq (mul_one M)

theorem halfOpen_error_norm_le {N cap m r : ℕ} (hN : 1 < N)
    (i : Fin (m+1)) {w B U M : ℝ} (hw : w ≤ lower N m i) (hU : 0 < U)
    (hM : 0 ≤ M) (Phi : ℝ → ℝ)
    (hPhi : ∀ y ∈ Icc (1 : ℝ) 2, |Phi y| ≤ M) (t : ℝ)
    {q b : ℕ} (hq : 0 < q) :
    ‖auxiliarySWError (halfOpenCarrier N cap m i w U)
      (value N cap m r i w B Phi t U) 1 q b‖ ≤
      ‖auxiliarySWError (carrier N cap m i w U)
        (value N cap m r i w B Phi t U) 1 q b‖ + 4*M := by
  rw [halfOpenCarrier,halfOpen_error_eq _ _ hU]
  have hleft := endpoint_mass_norm_le
    (attachedSupport (commonAlphabet N m) [i] N cap w)
    (value N cap m r i w B Phi t U) U M hM
    (fun d hd heq => value_norm_le hN i hw hU hM Phi hPhi t hd
      (by rw [heq]) (by rw [heq]; linarith)) hq
  have hright := endpoint_mass_norm_le
    (attachedSupport (commonAlphabet N m) [i] N cap w)
    (value N cap m r i w B Phi t U) (2*U) M hM
    (fun d hd heq => value_norm_le hN i hw hU hM Phi hPhi t hd
      (by rw [heq]; linarith) (by rw [heq])) hq
  dsimp only [carrier]
  exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (by linarith))

theorem occupied_halfOpen_power {N cap m : ℕ} (hN : 1 < N) (i : Fin (m+1))
    {w rho U : ℝ} (hlower : (N : ℝ)^rho ≤ lower N m i)
    (hs : (halfOpenCarrier N cap m i w U).Nonempty) : (N : ℝ)^rho ≤ 2*U := by
  obtain ⟨d,hd⟩ := hs
  obtain ⟨hd,hlo,hhi⟩ := Finset.mem_filter.mp hd
  change d ∈ (smallRoughPairs (actualSmallRosserSupport N cap w)
    (support (commonAlphabet N m) [i])).image (fun x => x.1*x.2) at hd
  obtain ⟨⟨e,p⟩,hep,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨he,hp⟩ := Finset.mem_product.mp hep
  rw [singleton_support] at hp
  have hepos : 0 < e := Nat.pos_of_mem_divisors he
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast hepos
  have hpR := ((mem_commonAlphabet_iff hN i).mp hp).2.2.1
  have hprod : (p : ℝ) ≤ (e : ℝ)*p :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) heR
  exact (hlower.trans hpR).trans (hprod.trans (by simpa only [Nat.cast_mul] using hhi.le))

/-- Genuine original-N SW on the actual HALF-OPEN grouped dyadic block.
Only one extra fixed constant is needed to pay both endpoint integers. -/
theorem beta_prime_halfOpen_SW (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {rho : ℝ} (hrho : 0 < rho) (J L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ cap m r : ℕ, ∀ i : Fin (m+1), ∀ w B : ℝ,
      w ≤ lower N m i → (N : ℝ)^rho ≤ lower N m i → B ≤ N →
      ∀ U : ℝ, 0 < U → ∀ t : ℝ, |t| ≤ Real.log (N : ℝ)^L →
      ∀ q b : ℕ, 0 < q → b.Coprime q →
      ‖auxiliarySWError (halfOpenCarrier N cap m i w U)
        (value N cap m r i w B Phi t U) 1 q b‖ ≤
          C*U/Real.log (N : ℝ)^J := by
  obtain ⟨M0,hM0⟩ := (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    hPhi.continuous.continuousOn
  let M := max M0 1
  have hM : 0 ≤ M := le_trans (by norm_num) (le_max_right _ _)
  have hbound : ∀ y ∈ Icc (1 : ℝ) 2, |Phi y| ≤ M := by
    intro y hy
    exact (show |Phi y| ≤ M0 by simpa only [Real.norm_eq_abs] using hM0 y hy).trans
      (le_max_left _ _)
  obtain ⟨C,hC,hSW⟩ := beta_prime_profile_SW Phi hPhi hrho J L
  have hpay := eventually_exclusion_payment (2*M*Real.log 2) rho hrho J
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [hSW,hpay,eventually_one_le_nat_log,eventually_ge_atTop (2 : ℕ)]
    with N hSW hpay hlog hN
  intro cap m r i w B hw hlower hB U hU t ht q b hq hb
  by_cases hs : (halfOpenCarrier N cap m i w U).Nonempty
  · have hpower := occupied_halfOpen_power (by omega) i hlower hs
    have hp := hpay U hpower
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have he : 2*(2*M*Real.log 2)*(Real.log (N : ℝ)/Real.log 2) =
        4*M*Real.log (N : ℝ) := by field_simp [hlog2]; ring
    rw [he] at hp
    have hendpoint : 4*M ≤ U/Real.log (N : ℝ)^J :=
      (le_mul_of_one_le_right (by positivity) hlog).trans hp
    have hraw := halfOpen_error_norm_le (r := r) (B := B) (by omega)
      i hw hU hM Phi hbound t hq
    have hmain := hSW cap m r i w B hw hlower hB U hU t ht q b hq hb
    calc
      _ ≤ C*U/Real.log (N : ℝ)^J + U/Real.log (N : ℝ)^J :=
        hraw.trans (add_le_add hmain hendpoint)
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [auxiliarySWError,Finset.sum_empty,zero_div,sub_zero,norm_zero]
    have hlp : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
    positivity

/-- The exact original computed third coefficient, restricted by the
half-open convention used in the W dyadic consumer. The assignment and
all its marked occurrences remain fixed before q,b and the beta divisor. -/
theorem actual_computed_beta_third_halfOpen_SW
    (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {rho : ℝ} (hrho : 0 < rho) (J L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ n m r : ℕ, ∀ eta : ℚ, ∀ M : Set (ℝ × ℝ), ∀ k : Key n m r,
      WholeCell eta rho M k.1 k.2.1 k.2.2 → rho ≤ cellZeta n eta k.1 →
      ∀ A epsilon : ℝ, epsilon ≤ 1 → ∀ i : Fin (m+1),
      (labelGroups n N m r eta A k).2.2 = [i] →
      ∀ U : ℝ, 0 < U → ∀ t : ℝ, |t| ≤ Real.log (N : ℝ)^L →
      ∀ q b : ℕ, 0 < q → b.Coprime q →
      ‖auxiliarySWError
        ((attachedSupport (commonAlphabet N m) (labelGroups n N m r eta A k).2.2
          N (cellCap n N eta k.1) ((N : ℝ)^rho)).filter
          (fun d => U ≤ (d : ℝ) ∧ (d : ℝ) < 2*U))
        (fun d => physicalProfile Phi t U d *
          (SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m)
            (labelGroups n N m r eta A k).2.2 N (cellCap n N eta k.1) r
            ((N : ℝ)^rho) ((N : ℝ)^epsilon) d : ℂ)) 1 q b‖ ≤
        C*U/Real.log (N : ℝ)^J := by
  obtain ⟨C,hC,hSW⟩ := beta_prime_halfOpen_SW Phi hPhi hrho J L
  refine ⟨C,hC,?_⟩
  filter_upwards [hSW,eventually_ge_atTop (2 : ℕ)] with N hSW hN
  intro n m r eta M k h hcut A epsilon hepsilon i hi U hU t ht q b hq hb
  have hlow := computed_third_lower (by omega) h hcut A hi
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hB : (N : ℝ)^epsilon ≤ N :=
    (Real.rpow_le_rpow_of_exponent_le hNr hepsilon).trans_eq (Real.rpow_one _)
  rw [hi]
  exact hSW (cellCap n N eta k.1) m r i ((N : ℝ)^rho) ((N : ℝ)^epsilon)
    hlow hlow hB U hU t ht q b hq hb

end
end ImbalancedChen.P5Z.OriginalBetaPrimeHalfOpenSW
