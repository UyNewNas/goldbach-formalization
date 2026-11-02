import ImbalancedChen.P2SameQSeedCoprimeMean
import ImbalancedChen.P2AllW1SameQRawCountInduction
import MathlibNt.Wu2008DoubleSieve.CanonicalBoundedDensity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An actual count seed at the physical level floor(Q/d)+1.  A fixed positive
residual exponent supplies one threshold before Q,d,s,E and the generation.
The imported canonical density theorem derives its dimension-one hypothesis
from the actual Goldbach sieve.  The signed AP and finite-coprime mean terms
remain explicit: this is not an error-paid positive enhanced seed.
-/
namespace ImbalancedChen.P2SameQPhysicalRosserSeed

noncomputable section
open Finset Filter Topology Wu2008DoubleSieve
open P2FrozenReceiverCountActions P2SameQSeedCoprimeMean
open P2ActualMarkedCountState (Query rootLevel root_level_geometry)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical BigOperators

theorem cutoff_log_coordinate {Q s : ℝ} {d : ℕ}
    (hR : 1<Q/(d:ℝ)) (hs : 0<s) :
    s=Real.log (Q/(d:ℝ))/Real.log (cutoff Q d s) := by
  have hlog : Real.log (Q/(d:ℝ))≠0 := (Real.log_pos hR).ne'
  rw [cutoff,Real.log_rpow (by linarith : 0<Q/(d:ℝ))]
  field_simp [hlog,ne_of_gt hs]

/-- The physical cutoff threshold is derived from the residual power gate;
there is no threshold premise for an individual child or a moving query. -/
theorem physical_cutoff_uniform_threshold {nu : ℝ} (hnu : 0<nu) (Z : ℝ) :
    ∃ N0 : ℕ, 4≤N0 ∧ ∀ N : ℕ, N0≤N → ∀ Q : ℝ, ∀ d : ℕ, ∀ s : ℝ,
      (N:ℝ)^nu≤Q/(d:ℝ) → 1≤s → s≤10 → Z≤cutoff Q d s := by
  have hlarge : ∀ᶠ N : ℕ in atTop, Z≤(N:ℝ)^(nu/10) :=
    ((tendsto_rpow_atTop (show 0<nu/10 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop Z)
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp hlarge
  refine ⟨max N1 4,le_max_right _ _,?_⟩
  intro N hN Q d s hres hs hs10
  have hN4 : 4≤N := (le_max_right _ _).trans hN
  have hNreal : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hspos : 0<s := by linarith
  have hrecip : (1:ℝ)/10≤1/s := one_div_le_one_div_of_le hspos hs10
  have hexp : nu/10≤nu*(1/s) := by nlinarith
  calc
    Z≤(N:ℝ)^(nu/10) := hN1 N ((le_max_left _ _).trans hN)
    _≤(N:ℝ)^(nu*(1/s)) := Real.rpow_le_rpow_of_exponent_le hNreal hexp
    _=((N:ℝ)^nu)^(1/s) := Real.rpow_mul (Nat.cast_nonneg N) _ _
    _≤cutoff Q d s := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      hres (by positivity)

def seedMain (side : Bool) (N d : ℕ) (Q s eta : ℝ) : ℝ :=
  (logarithmicIntegral N/(Nat.totient d:ℝ))*
    ((if side then jr1965F s+eta else jr1965f s-eta)*
      localSieveProduct (d*N) (cutoff Q d s))

def seedError (side : Bool) (N d : ℕ) (Q s : ℝ) (E : ℕ → Prop) : ℝ :=
  signedAPDiscrepancy side N d (rootLevel Q d) E (cutoff Q d s)+
    signedMeanShift side N d (rootLevel Q d) E (cutoff Q d s)

/-- Both signs use one same-Q residual and the same true finite source.
This theorem makes no classical half-level restriction, but it keeps the
unpaid arithmetic errors instead of inferring their smallness. -/
theorem sameQ_polynomial_seed {nu eta : ℝ} (hnu : 0<nu) (heta : 0<eta) :
    ∃ N0 : ℕ, 4≤N0 ∧ ∀ N : ℕ, N0≤N → Even N →
      ∀ Q : ℝ, ∀ d : ℕ, ∀ s : ℝ, ∀ E : ℕ → Prop,
      (N:ℝ)^nu≤Q/(d:ℝ) → 2≤s → s≤10 →
      seedMain false N d Q s eta+seedError false N d Q s E≤
        frozenPolynomial false N d (rootLevel Q d) E (cutoff Q d s) ∧
      frozenPolynomial true N d (rootLevel Q d) E (cutoff Q d s)≤
        seedMain true N d Q s eta+seedError true N d Q s E := by
  obtain ⟨Zlo,hlo⟩ := ordinaryRosser_lower_density_canonical_bounded_local heta
  obtain ⟨Zup,hup⟩ := ordinaryRosser_upper_density_canonical_bounded_local heta
  obtain ⟨N0,hN0,hcut⟩ := physical_cutoff_uniform_threshold hnu (max 2 (max Zlo Zup))
  refine ⟨N0,hN0,?_⟩
  intro N hN he Q d s E hres hs hs10
  have hN4 := hN0.trans hN
  have hNreal : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hR : 1<Q/(d:ℝ) := (Real.one_lt_rpow hNreal hnu).trans_le hres
  have hli : 0≤logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2≤N by omega))
  have hscale : 0≤logarithmicIntegral N/(Nat.totient d:ℝ) :=
    div_nonneg hli (Nat.cast_nonneg _)
  have hz := hcut N hN Q d s hres (by linarith) hs10
  have hz2 := (le_max_left 2 (max Zlo Zup)).trans hz
  have hzlo := (le_max_left Zlo Zup).trans ((le_max_right 2 (max Zlo Zup)).trans hz)
  have hzup := (le_max_right Zlo Zup).trans ((le_max_right 2 (max Zlo Zup)).trans hz)
  have hl := mul_le_mul_of_nonneg_left
    (hlo N d he (cutoff Q d s) (Q/(d:ℝ)) s hzlo hz2
      (by linarith) (cutoff_log_coordinate hR (by linarith)) hs hs10) hscale
  have hu := mul_le_mul_of_nonneg_left
    (hup N d he (cutoff Q d s) (Q/(d:ℝ)) s hzup hz2
      (by linarith) (cutoff_log_coordinate hR (by linarith)) (by linarith) hs10) hscale
  constructor
  · rw [frozenPolynomial_eq_coprime_split]
    dsimp [seedMain,seedError,rootLevel] at *
    linarith
  · rw [frozenPolynomial_eq_coprime_split]
    dsimp [seedMain,seedError,rootLevel] at *
    linarith

abbrev rawIterate := P2AllW1SameQRawCountInduction.iterate

/-- H's actual old-generation recursion keeps both initial alternatives.
No seed licence or Sound invariant is supplied to this induction. -/
theorem rawIterate_retains_initial (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (bank : List Query) (rounds d : ℕ) (z : ℝ) :
    frozenPolynomial false N d (rootLevel Q d) E z≤
      (rawIterate N Q E bank rounds).lower d z ∧
    (rawIterate N Q E bank rounds).upper d z≤
      frozenPolynomial true N d (rootLevel Q d) E z := by
  induction rounds with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ n ih =>
    have h := P2AllW1SameQRawCountInduction.iterate_retains_previous N Q E bank n d z
    exact ⟨ih.1.trans h.1,h.2.trans ih.2⟩

/-- The complete arithmetic attachment: analytic local-product seed,
actual H state, actual count, actual H state, analytic local-product seed.
Both signed source errors are still present, at their original level. -/
theorem sameQ_seed_attached_to_H {nu eta : ℝ} (hnu : 0<nu) (heta : 0<eta) :
    ∃ N0 : ℕ, 4≤N0 ∧ ∀ N : ℕ, N0≤N → Even N →
      ∀ Q : ℝ, ∀ d : ℕ, ∀ s : ℝ, ∀ E : ℕ → Prop,
      ∀ bank : List Query, ∀ rounds : ℕ,
      0<d → (N:ℝ)^nu≤Q/(d:ℝ) → 2≤s → s≤10 →
      seedMain false N d Q s eta+seedError false N d Q s E≤
        (rawIterate N Q E bank rounds).lower d (cutoff Q d s) ∧
      (rawIterate N Q E bank rounds).lower d (cutoff Q d s)≤
        (frozenCount N d E (cutoff Q d s):ℝ) ∧
      (frozenCount N d E (cutoff Q d s):ℝ)≤
        (rawIterate N Q E bank rounds).upper d (cutoff Q d s) ∧
      (rawIterate N Q E bank rounds).upper d (cutoff Q d s)≤
        seedMain true N d Q s eta+seedError true N d Q s E := by
  obtain ⟨N0,hN0,hseed⟩ := sameQ_polynomial_seed hnu heta
  refine ⟨N0,hN0,?_⟩
  intro N hN he Q d s E bank rounds hd hres hs hs10
  have hNreal : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hR := (Real.one_lt_rpow hNreal hnu).trans_le hres
  have hbase := hseed N hN he Q d s E hres hs hs10
  have hretain := rawIterate_retains_initial N Q E bank rounds d (cutoff Q d s)
  have hcount := P2AllW1SameQRawCountInduction.iterate_encloses N Q E bank rounds
    d (cutoff Q d s) (P2AllW1SameQRawCountInduction.cutoff_query hd hR (by linarith))
  exact ⟨hbase.1.trans hretain.1,hcount.1,hcount.2,hretain.2.trans hbase.2⟩

end
end ImbalancedChen.P2SameQPhysicalRosserSeed
