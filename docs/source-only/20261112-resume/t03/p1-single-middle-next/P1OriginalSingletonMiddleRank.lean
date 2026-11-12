import ImbalancedChen.P1OriginalSharpFiniteReceiver
import ImbalancedChen.P4BOriginalCollisionPhysical

/-! The original sharp middle of the finite rectangle can be tested on the
whole high rough-rank carrier, with its signed coefficient and primitive
mean. The modulus height can therefore be removed before splitting slots. -/
namespace ImbalancedChen.P1OriginalSingletonMiddleRank
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalCollisionWords (Params)
open P4BOriginalFiniteSmoothCount (Q)
open P4BOriginalAllRankClassicalRange (lowRank lowRank_subset_below)
open P4AHeldTaggedCompilerSupport (J0)
open P1OriginalSharpFiniteReceiver (cut middle)
open P4AOriginalFull87SignedSharpReceiver (sharpPrimeError)
open P4BPositiveUpperPrimeBV (primeError eventually_primeError_log_saving)
open P4BOriginalCollisionPhysical (supported_physical)

def live (P : Params) := P.S.filter (fun d => P.rho d ≠ 0)

theorem read_live (P : Params) (G : ℕ → ℝ) :
    (∑ d ∈ live P, P.rho d * G d) = ∑ d ∈ P.S, P.rho d * G d := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hn
  have hz : P.rho d = 0 := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hd,h⟩)
  simp [hz]

theorem live_data (P : Params) (hN : 1 < P.N) (he : 0 ≤ P.e)
    (ho : 0 < P.omega) (hell : P.ell < 1/1000)
    (ht : P.ell + P.T*(J0 P.omega : ℝ) < 1/1000) {d : ℕ} (hd : d ∈ live P) :
    d ∈ Finset.Icc 1 P.N ∧ Squarefree d ∧ d.Coprime P.N ∧ |P.rho d| ≤ 1 := by
  obtain ⟨hS,hc⟩ := Finset.mem_filter.mp hd
  have hQ := (Finset.mem_sdiff.mp hS).1
  have hs := P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hQ
  have hu := (supported_physical P hN he ho hell ht hc).trans_le
    (show (P.N:ℝ)^(599/1000:ℝ) ≤ P.N by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN.le : 1 ≤ (P.N:ℝ)) (by norm_num : (599/1000:ℝ) ≤ 1))
  exact ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hs.ne_zero,by exact_mod_cast hu.le⟩,
    hs,P4AUpperTaggedBetaAttachment.support_coprime_target _ _ _ _ hQ,
    P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d⟩

theorem middle_on_rank (P : Params) (hN : 1 < P.N) (he : 0 ≤ P.e)
    (ho : 0 < P.omega) (hell : P.ell < 1/1000)
    (ht : P.ell + P.T*(J0 P.omega : ℝ) < 1/1000) :
    middle P.N (Q P.omega P.N) P.rho =
      ∑ d ∈ (live P).filter (fun d => cut P.N < d), P.rho d * sharpPrimeError P.N d := by
  let B := (Q P.omega P.N).filter
    (fun d => cut P.N < d ∧ (d:ℝ) < (P.N:ℝ)^(599/1000:ℝ))
  have hle : (P.N:ℝ)^(2/5:ℝ) ≤ (P.N:ℝ)^(9/20:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) (by norm_num)
  have ident : (live P).filter (fun d => cut P.N < d) =
      B.filter (fun d => P.rho d ≠ 0) := by
    ext d
    simp only [live,B,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hd,hn⟩,hc⟩
      exact ⟨⟨(Finset.mem_sdiff.mp hd).1,hc,supported_physical P hN he ho hell ht hn⟩,hn⟩
    · rintro ⟨⟨hQ,hc,hu⟩,hn⟩
      refine ⟨⟨Finset.mem_sdiff.mpr ⟨hQ,?_⟩,hn⟩,hc⟩
      intro hl
      have hsmall := lowRank_subset_below P.m P.r P.n P.e P.q P.a P.omega P.k P.N hN P.ell hell hl
      exact hc.not_ge (Nat.le_floor ((Finset.mem_filter.mp hsmall).2.le.trans hle))
  rw [ident]
  change (∑ d ∈ B, _) = _
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hn
  have hzero : P.rho d = 0 := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hd,h⟩)
  simp [hzero]

/-- The one classical low component and the change of the prime-divisor
mean buy back the complete modulus cut. All parameters of the rectangle
and its original upper policy remain inside the same prime sum. -/
theorem eventually_primitive (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ P : Params, P.N=N → 0 ≤ P.e → 0 < P.omega →
      P.ell < 1/1000 → P.ell+P.T*(J0 P.omega : ℝ)<1/1000 →
      |middle N (Q P.omega N) P.rho -
        Part3.primeProductSignedError 1 N N P.S P.rho
          (P5S1SingletonPP.singletonWeight N (fun _ => 1))| ≤ eta*singularNormalization N := by
  obtain ⟨C,hC,hBV⟩ := eventually_primeError_log_saving 3
  filter_upwards [hBV,p5z_eventually_logCube_le_singularNormalization C (eta/2) (half_pos heta),
    P5PrimeDivisorMean.eventually_log_square_cap_le_normalization (eta/2) (half_pos heta),
    eventually_ge_atTop (2:ℕ)] with N hbv hpay hmod hN
  intro P hPN he ho hell ht
  subst N
  let A := live P
  let S := A.filter (fun d => d ≤ cut P.N)
  let B := A.filter (fun d => cut P.N < d)
  have data (d : ℕ) (hd : d ∈ A) := live_data P (by omega) he ho hell ht hd
  have lo (d : ℕ) (hd : d ∈ S) := data d (Finset.mem_filter.mp hd).1
  have hi (d : ℕ) (hd : d ∈ B) := data d (Finset.mem_filter.mp hd).1
  have hS : S ⊆ Finset.Icc 1 (cut P.N) := fun d hd =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (lo d hd).1).1,(Finset.mem_filter.mp hd).2⟩
  have hlow : |∑ d ∈ S,P.rho d*primeError P.N P.N d| ≤ eta/2*singularNormalization P.N := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun d hd => show |P.rho d * primeError P.N P.N d| ≤
      |primeError P.N P.N d| by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (lo d hd).2.2.2)).trans
    exact (hbv S hS (fun d hd => (lo d hd).2.1) (fun _ => P.N) (fun _ => P.N)
      (fun _ _ => le_rfl) (fun d hd => (lo d hd).2.2.1.symm)).trans hpay
  have hu := P5PrimeDivisorMean.abs_singleton_PP_sub_total_pi_error_le P.N P.N B P.rho
    (fun d hd => (hi d hd).1) (fun d hd => (hi d hd).2.1) (fun d hd => (hi d hd).2.2.2)
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq] at hu
  have hupper : |(∑ d ∈ B,P.rho d*primeError P.N P.N d)-
      ∑ d ∈ B,P.rho d*sharpPrimeError P.N d| ≤ eta/2*singularNormalization P.N := by
    simpa only [primeError,sharpPrimeError,P4AOriginalFull87EighthPrimeMeanLedger.primeMass,
      P4AOriginalFull87EighthPrimeMeanLedger.densityTest,mul_one_div] using hu.trans (hmod P.N le_rfl)
  have divide : (∑ d ∈ A, P.rho d*primeError P.N P.N d) =
      (∑ d ∈ S,P.rho d*primeError P.N P.N d)+(∑ d ∈ B,P.rho d*primeError P.N P.N d) := by
    dsimp only [S,B]
    rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : d ≤ cut P.N <;> simp [h,show cut P.N < d ↔ ¬d ≤ cut P.N from lt_iff_not_ge]
  rw [middle_on_rank P (by omega) he ho hell ht,P5S1SingletonPP.primeProductSignedError_singleton_eq]
  change |(∑ d ∈ B,P.rho d*sharpPrimeError P.N d)-(∑ d ∈ P.S,P.rho d*primeError P.N P.N d)| ≤ _
  rw [←read_live P (primeError P.N P.N),divide,abs_sub_comm]
  calc
    _ = |(∑ d ∈ S,P.rho d*primeError P.N P.N d)+
          ((∑ d ∈ B,P.rho d*primeError P.N P.N d)-(∑ d ∈ B,P.rho d*sharpPrimeError P.N d))| := by
      congr 1; ring
    _ ≤ _ := (abs_add _ _).trans (by linarith only [hlow,hupper])

end
end ImbalancedChen.P1OriginalSingletonMiddleRank
