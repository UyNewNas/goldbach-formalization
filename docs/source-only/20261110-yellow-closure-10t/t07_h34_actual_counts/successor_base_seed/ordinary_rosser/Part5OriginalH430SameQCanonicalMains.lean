import ImbalancedChen.P2SameQPhysicalRosserSeed
import ImbalancedChen.Part5OriginalH430SignedSeedCount
import MathlibNt.Wu2008DoubleSieve.PhiBounded

/-! Uniform canonical Rosser main sums on an arbitrary physical residual.
The polynomial-size parameter for the moving local product is derived from
d ≤ N and z ≥ N^κ. No fixed half-level representation of Q is used. -/
namespace ImbalancedChen.Part5OriginalH430SameQCanonicalMains
noncomputable section
open Set Finset Filter Real Wu2008DoubleSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2ActualMarkedCountState (rootLevel)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5CanonicalUpperCancellation (upperA lowerBar)
open scoped Classical BigOperators Topology

def model (side : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (z : ℝ) : ℝ :=
  logarithmicIntegral N/(Nat.totient d:ℝ)*ordinaryRosserMainSum side N d (rootLevel Q d) z

/-- A true integer Rosser main sum, at its full physical modulus, has the
correct two one-sided normalized prices. The real cutoff z can originate
from the unchanged parent; its own child argument is the actual log ratio. -/
theorem physical_main_sides {κ ε : ℝ} (hκ : 0<κ) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (Q z s : ℝ) (d : ℕ),
      0<d → d≤N → 1<Q/(d:ℝ) → (N:ℝ)^κ≤z →
      s=log (Q/(d:ℝ))/log z → 2≤s → s≤10 →
      model true N Q d z ≤ (upperA s + ε)*thetaAtom N Q d ∧
      (lowerBar s - ε)*thetaAtom N Q d ≤ model false N Q d z := by
  let δ := min 1 (ε/15)
  have hδ : 0<δ := lt_min (by norm_num) (div_pos he (by norm_num))
  have hδ1 : δ≤1 := min_le_left _ _
  have he' : 15*δ≤ε := by linarith only [show δ≤ε/15 from min_le_right _ _]
  let τ := exp eulerMascheroniConstant*δ/2
  have hτ : 0<τ := by dsimp only [τ]; positivity
  obtain ⟨Zu,hZu⟩ := ordinaryRosser_upper_density_canonical_bounded_local hτ
  obtain ⟨Zl,hZl⟩ := ordinaryRosser_lower_density_canonical_bounded_local hτ
  obtain ⟨Z,hZ⟩ := eventually_atTop.mp (eventually_localSieveProduct_relative (2/κ) δ
    (div_nonneg (by norm_num) hκ.le) hδ)
  let A := max 3 (max Z (max Zu Zl))
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop A)
  refine ⟨max T 4,le_max_right _ _,?_⟩
  intro N hN hEven Q z s d hd hdN hR hz hs hs2 hs10
  have h4 := (le_max_right _ _).trans hN
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hN0 := zero_lt_one.trans hNr
  have hA : A≤z := (hT N ((le_max_left _ _).trans hN)).trans hz
  have hz3 := (le_max_left (3:ℝ) _).trans hA
  have hZs : max Z (max Zu Zl)≤z := (le_max_right (3:ℝ) _).trans hA
  have hZul := (le_max_right Z (max Zu Zl)).trans hZs
  have hM := Nat.mul_pos hd (show 0<N by omega)
  have hpoly : ((d*N:ℕ):ℝ)≤z^(2/κ) := by
    calc
      _ ≤ (N:ℝ)^(2:ℝ) := by
        rw [Nat.cast_mul,rpow_two,pow_two]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdN) hN0.le
      _ = ((N:ℝ)^κ)^(2/κ) := by rw [←rpow_mul hN0.le]; congr 1; field_simp [hκ.ne']
      _ ≤ _ := rpow_le_rpow (rpow_nonneg hN0.le _) hz (by positivity)
  let C := wuSingularSeries (d*N)
  let l := log (Q/(d:ℝ))
  have hC : 0<C := wuSingularSeries_pos _ hM
  have hl : 0<l := log_pos hR
  have hlogz : 0<log z := log_pos (by linarith)
  have hs' : s*log z=l := (eq_div_iff hlogz.ne').mp hs
  have hM' : 0<2*s*C/(exp eulerMascheroniConstant*l) := by positivity
  have hrel := hZ z ((le_max_left _ _).trans hZs) (d*N) hM (hEven.mul_left d) hpoly
  have heq : 2*exp (-eulerMascheroniConstant)*C/log z =
      2*s*C/(exp eulerMascheroniConstant*l) := by
    rw [exp_neg,←hs']
    field_simp [(by linarith : s≠0),hlogz.ne',(exp_pos _).ne'] <;> ring
  change |localSieveProduct (d*N) z/(2*exp (-eulerMascheroniConstant)*C/log z)-1|≤δ at hrel
  rw [heq] at hrel
  have hV := (div_le_iff₀ hM').mp (show localSieveProduct (d*N) z/
      (2*s*C/(exp eulerMascheroniConstant*l)) ≤ 1+δ by linarith only [(abs_le.mp hrel).2])
  have hU := hZu N d hEven z (Q/d) s ((le_max_left _ _).trans hZul)
    (by linarith) (zero_lt_one.trans hR) hs (by linarith) hs10
  have hL := hZl N d hEven z (Q/d) s ((le_max_right _ _).trans hZul)
    (by linarith) (zero_lt_one.trans hR) hs hs2 hs10
  have hu := hU.trans ((mul_le_mul_of_nonneg_left hV
    (add_nonneg (jr1965F_pos (show 0<s by linarith)).le hτ.le)).trans
    (canonical_upper_bounded_normalization_budget (by linarith) hs10 hC.le hl hδ.le hδ1))
  have hdwn := (canonical_lower_bounded_normalization_budget hs2 hs10 hC hl hδ.le hδ1 hrel).trans hL
  have hli : 0≤logarithmicIntegral N := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg
    0 le_rfl (by exact_mod_cast (show 2≤N by omega))
  have hsc : 0≤logarithmicIntegral N/(Nat.totient d:ℝ) := div_nonneg hli (Nat.cast_nonneg _)
  have hB : 0≤4*C/l := by positivity
  have hθ : logarithmicIntegral N/(Nat.totient d:ℝ)*(4*C/l)=thetaAtom N Q d := by
    dsimp [C,l,thetaAtom]; ring
  have hu' := hu.trans (mul_le_mul_of_nonneg_right (add_le_add_left he' _) hB)
  have hd' := (mul_le_mul_of_nonneg_right (sub_le_sub_left he' _) hB).trans hdwn
  constructor
  · trans logarithmicIntegral N/(Nat.totient d:ℝ)*((upperA s+ε)*(4*C/l))
    · simpa only [model,rootLevel,upperA,jr1965DelayConstant] using mul_le_mul_of_nonneg_left hu' hsc
    · exact le_of_eq (by rw [←hθ]; ring)
  · calc
      _ = logarithmicIntegral N/(Nat.totient d:ℝ)*((lowerBar s-ε)*(4*C/l)) := by rw [←hθ]; ring
      _ ≤ _ := by simpa only [model,rootLevel,lowerBar,jr1965DelayConstant] using
        mul_le_mul_of_nonneg_left hd' hsc

end
end ImbalancedChen.Part5OriginalH430SameQCanonicalMains
