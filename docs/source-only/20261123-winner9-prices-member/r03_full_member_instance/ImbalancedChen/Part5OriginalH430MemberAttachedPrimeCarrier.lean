import ImbalancedChen.Part5OriginalH430AttachedUpperMember
import ImbalancedChen.Part5OriginalH430LowerRoughMember
import ImbalancedChen.Part5OriginalH430AllRootRejectedWindows
import ImbalancedChen.P4BActualSmoothHyperbolaCorrection

/-! Native signed coefficients on the same marked history. The old prime
product is rough up to the Member's physical cutoff. At the enhanced
retained positions this identifies the entire residual attached function
with an actual admissible input to the two-integer-chart proper-power
and Fourier estimates, using the history-dependent ordinary retention. -/
namespace ImbalancedChen.Part5OriginalH430MemberAttachedPrimeCarrier
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalUpsilon5CausalDictionary (a)
open P5Z.OriginalOrdinaryCommonBetaModel (ordinaryRetainOdd presievedCoefficient)
open P5Z.OriginalPresievedActiveDeltaFactors (ordinary_rough_supported_native_active)
open Part5OriginalH430PhysicalRoots Part5OriginalH430RootSourceDictionary Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430OwnedRootCounts Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells
open Part5OriginalH430EnhancedPhysicalGrid
open Part5OriginalH430RetainedRejectedPayment (retainedEdge)
open Part5OriginalH430OriginalReceiptMemberPullback (memberCutoff)
open Part5OriginalH430HistoryQuotientCounts (history_integer_roughness)
open Part5OriginalH430AllRootRejectedWindows (enhanced_retained_cutoff)
open Part5OriginalH430AttachedUpperMember (coefficientAt)
open P4BActualSmoothHyperbolaCorrection (actualActiveUpperCap)

private theorem primes {N B cap : ℕ} {Z z : ℝ} (hB : ChenPrimeRough Z B)
    (hz : z≤Z) (u : ℝ) : roughPrimeFinset (N*B) cap u z=roughPrimeFinset N cap u z := by
  ext p
  rw [mem_roughPrimeFinset,mem_roughPrimeFinset]
  constructor
  · rintro ⟨hc,hp,hn,hu,ht⟩
    exact ⟨hc,hp,(fun hd=>hn (dvd_mul_of_dvd_left hd B)),hu,ht⟩
  · rintro ⟨hc,hp,hn,hu,ht⟩
    refine ⟨hc,hp,?_,hu,ht⟩
    intro hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · exact hn hd
    · exact (not_lt_of_ge (hB p hp hd)) (ht.trans_le hz)

/-- Both actual sign attachments, including their complete displayed
modulus sets, survive deletion of the old product from the prime mask.
This applies also after a fresh read and to arbitrary causal retainers. -/
theorem history_signed_carriers {N n m p : ℕ} {k : Root} {t u : ℝ} {key : RootKey n m} {o : Occurrence N}
    (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (ht' : t≤1/12)
    (hp : p∈rootFibre N n m k t key) (ho : o∈rootHistory N n k t p)
    (hu : u≤memberCutoff (cellQ N n key.1) o) (cap : ℕ) (f g : List ℕ→Bool) (M : ℝ) :
    let B := parentProduct o.current.old
    let Z := memberCutoff (cellQ N n key.1) o
    actualSmallRoughModuli f (N*B) cap u Z=actualSmallRoughModuli f N cap u Z ∧
    actualSmallRoughRho f (N*B) cap u Z M=actualSmallRoughRho f N cap u Z M ∧
    actualLowerSmallRoughModuli g (N*B) cap u Z=actualLowerSmallRoughModuli g N cap u Z ∧
    actualLowerSmallRoughRho g (N*B) cap u Z M=actualLowerSmallRoughRho g N cap u Z M := by
  dsimp only
  let Z := memberCutoff (cellQ N n key.1) o
  let B := parentProduct o.current.old
  have hb := (Finset.mem_filter.mp hp).1
  have hQ := (original_fibre_geometry hN ht ht' (precision_error hn) hp).1
  have hB : ChenPrimeRough Z B := by
    dsimp only [Z]
    rw [hQ]
    exact (history_integer_roughness hN ht ht' (precision_error hn) hb ho).1
  have hU : roughPrimeUniverse (N*B) cap u Z=roughPrimeUniverse N cap u Z := by
    unfold roughPrimeUniverse
    rw [primes hB (le_refl Z)]
  have hP : actualSmallPrimeProduct (N*B) cap u=actualSmallPrimeProduct N cap u := by
    unfold actualSmallPrimeProduct actualSmallPrimeFinset
    rw [primes hB hu]
  change actualSmallRoughModuli f (N*B) cap u Z=_ ∧ actualSmallRoughRho f (N*B) cap u Z M=_ ∧
    actualLowerSmallRoughModuli g (N*B) cap u Z=_ ∧ actualLowerSmallRoughRho g (N*B) cap u Z M=_
  simp only [actualSmallRoughModuli,actualSmallRoughRho,actualLowerSmallRoughModuli,actualLowerSmallRoughRho,
    fixedRoughSupport,fixedRoughCoefficient,fixedEvenRoughSupport,fixedEvenRoughCoefficient,
    actualSmallRosserSupport,actualSmallRosserPlus,actualSmallRosserMinus,hU,hP] <;> exact ⟨rfl,rfl,rfl,rfl⟩

def memberRetention {N : ℕ} (Q : ℝ) (o : Occurrence N) : ℕ→List ℕ→Bool :=
  fun _ => ordinaryRetainOdd (Q/(parentProduct o.current.old:ℝ))

def memberModuli {N : ℕ} (cap : ℕ) (Q rho : ℝ) (o : Occurrence N) :=
  let B := parentProduct o.current.old
  actualSmallRoughModuli (ordinaryRetainOdd (Q/(B:ℝ))) (N*B) cap ((N:ℝ)^rho) (memberCutoff Q o)

/-- Each actual sifted receiver determines its unique original additive
prime. A residual divisor test is precisely a congruence to the global
N on the complete marked modulus B*h. Every displayed attached modulus
in this receipt is primitive to N and its residual factor is prime to B. -/
theorem original_marked_progression {N r : ℕ} (cap : ℕ) (Q rho : ℝ) (o : Occurrence N)
    (hr : r∈chenSiftedQuotientPrimeSource N (parentProduct o.current.old) (memberCutoff Q o)) :
    let B := parentProduct o.current.old
    ∃! ell : ℕ, ell∈chenQuotientPrimeCarrier N B ∧ (N-ell)/B=r ∧
      (∀ h : ℕ, h∣r ↔ Nat.ModEq (B*h) ell N) ∧
      (∀ h∈memberModuli cap Q rho o,(B*h).Coprime N ∧ h.Coprime B) := by
  dsimp only
  let B := parentProduct o.current.old
  have hu : r∈chenQuotientPrimeSource N B := (Finset.mem_filter.mp hr).1
  obtain ⟨ell,hcarrier,hdiv⟩ := Finset.mem_image.mp hu
  have hc := mem_chenQuotientPrimeCarrier.mp hcarrier
  have hdata := mem_chenAdditivePrimeCarrier.mp hc.1
  have hmul : B*r=N-ell := by rw [←hdiv]; exact Nat.mul_div_cancel' hc.2
  have hB : 0<B := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz,zero_mul] at hmul
    have he := hdata.1
    omega
  have hcop := ((Nat.coprime_self_sub_left hdata.1.le).mpr hdata.2.2).of_dvd_left hc.2
  refine ⟨ell,⟨hcarrier,hdiv,?_,?_⟩,?_⟩
  · intro h
    rw [Nat.modEq_iff_dvd' hdata.1.le,←hmul]
    exact (Nat.mul_dvd_mul_iff_left hB).symm
  · intro h hh
    have hc' := (Nat.coprime_mul_iff_right.mp (actualSmallRoughModuli_coprime_target
      (ordinaryRetainOdd (Q/(B:ℝ))) (N*B) cap ((N:ℝ)^rho) (memberCutoff Q o) hh))
    exact ⟨hcop.mul_left hc'.1,hc'.2⟩
  · intro ell' h'
    exact chenQuotientPrimeSource_injective h'.1 hcarrier (h'.2.1.trans hdiv.symm)

private theorem scale {nu : ℝ} (hnu : 0<nu) : nu*(a/nu)=a := by field_simp [ne_of_gt hnu] <;> ring

/-- The positive small beta may be chosen last. The true native rough
support bounds every residual modulus after beta attachment. This gives
the cap in the analytic estimates on the physical support itself. -/
theorem retained_residual_binding {N n m p cap : ℕ} {k : Root} {t nu beta : ℝ} {key : RootKey n m}
    {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (ht' : t≤1/12)
    (hp : p∈rootFibre N n m k t key) (ho : o∈rootHistory N n k t p)
    (hen : rootSource k (physicalPrime N p)=.enhanced) (hret : o.path.all retainedEdge=true)
    (hnu : 0<nu) (hu : nu*beta^2≤a) (hlevel : nu*beta≤1/1000) :
    let Q := cellQ N n key.1
    let f := memberRetention Q o
    memberModuli cap Q (nu*beta^2) o=attachedUpperModuli nu (a/nu) beta f (fun _=>cap) N ∧
      coefficientAt cap Q (nu*beta^2) (nu*beta) o=attachedUpperCoefficient nu (a/nu) beta f (fun _=>cap) N ∧
      (actualActiveUpperCap nu (a/nu) beta f (fun _=>cap) N:ℝ)≤(N:ℝ)^(599/1000:ℝ) := by
  dsimp only
  let Q := cellQ N n key.1
  let B := parentProduct o.current.old
  let Z := memberCutoff Q o
  let R := Q/(B:ℝ)
  let f := memberRetention Q o
  let u := (N:ℝ)^(nu*beta^2)
  have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hNp := zero_lt_one.trans_le hNr
  have hz : Z=(N:ℝ)^a := enhanced_retained_cutoff hN hn ht ht' hp ho hen hret
  have hw : u≤Z := hz ▸ Real.rpow_le_rpow_of_exponent_le hNr hu
  have hsc := scale hnu
  have heq := history_signed_carriers hN hn ht ht' hp ho hw cap (ordinaryRetainOdd R) (fun _=>true) ((N:ℝ)^(nu*beta))
  have hq := (original_fibre_geometry hN ht ht' (precision_error hn) hp).1
  have hb := (Finset.mem_filter.mp hp).1
  have hg := original_band_geometry hN hb
  have hs := rootHistory_support (by omega : 1<N) ht ht' (precision_error hn) (original_band_prime hb) hg ho
  have hR : 1<R := by dsimp only [R,Q]; rw [hq]; exact (parentWindow_logs hs.1).2.1
  have hB1 : (1:ℝ)≤B := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hs.1.2.1.ne')
  have hQcap : Q≤(N:ℝ)^(153/256:ℝ) := by
    rw [show Q=rootQ N n k t p from hq]
    apply Real.rpow_le_rpow_of_exponent_le hNr
    exact (frozenLevel_bounds (root_total_bounds ht ht' hg) n).1.trans
      ((enhanced_root_total (tau:=t) hen).le.trans (VariableEnvelope.v_le_cap _))
  have hRcap : R≤(N:ℝ)^(153/256:ℝ) :=
    (div_le_self (by rw [show Q=rootQ N n k t p from hq]; exact Real.rpow_nonneg hNp.le _) hB1).trans hQcap
  have hpow := Real.rpow_nonneg hNp.le (599/1000:ℝ)
  refine ⟨?_,?_,?_⟩
  · change actualSmallRoughModuli (ordinaryRetainOdd R) (N*B) cap u Z=_
    change actualSmallRoughModuli (ordinaryRetainOdd R) (N*B) cap u Z=
      actualSmallRoughModuli (ordinaryRetainOdd R) N cap u ((N:ℝ)^(nu*(a/nu)))
    rw [hsc,←hz]
    exact heq.1
  · change actualSmallRoughRho (ordinaryRetainOdd R) (N*B) cap u Z ((N:ℝ)^(nu*beta))=_
    change actualSmallRoughRho (ordinaryRetainOdd R) (N*B) cap u Z ((N:ℝ)^(nu*beta))=
      actualSmallRoughRho (ordinaryRetainOdd R) N cap u ((N:ℝ)^(nu*(a/nu))) ((N:ℝ)^(nu*beta))
    rw [hsc,←hz]
    exact heq.2.1
  · have hc : actualActiveUpperCap nu (a/nu) beta f (fun _=>cap) N≤⌊(N:ℝ)^(599/1000:ℝ)⌋₊ := by
      apply Finset.sup_le
      intro d hd
      have hact := (Finset.mem_filter.mp hd).2
      change actualSmallRoughRho (ordinaryRetainOdd R) N cap u ((N:ℝ)^(nu*(a/nu))) ((N:ℝ)^(nu*beta)) d≠0 at hact
      rw [hsc,←hz] at hact
      obtain ⟨e,_,r,hr,hprod,he,_⟩ := actualSmallRoughRho_ne_zero_factors _ _ _ _ _ _ hact
      have hr' := (actualSmallRosserPlus_active (ordinary_rough_supported_native_active hR hw hr)).2.1
      apply (Nat.le_floor_iff hpow).mpr
      change (d:ℝ)≤(N:ℝ)^(599/1000:ℝ)
      rw [hprod,Nat.cast_mul]
      calc
        (e:ℝ)*(r:ℝ) ≤ (N:ℝ)^(nu*beta)*(N:ℝ)^(153/256:ℝ) :=
          mul_le_mul he.le (hr'.le.trans hRcap) (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _)
        _ = (N:ℝ)^(nu*beta+153/256) := (Real.rpow_add hNp _ _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNr (by linarith only [hlevel])
    exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hpow)

end
end ImbalancedChen.Part5OriginalH430MemberAttachedPrimeCarrier
