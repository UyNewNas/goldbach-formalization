import ImbalancedChen.Part5OriginalH430AllRootRejectedWindows
import ImbalancedChen.Part5OriginalH430AllTaggedHistoryUnits
import ImbalancedChen.Part5OriginalH430AbsoluteWordBox

/-! Genuine positive mass on every preassigned interval in the common
decreasing enhanced tent branch. The level is the actual lower frozen
level of each selected prime; neither the precision nor the interval
is chosen after the target. The inherited positions use their own
word products and the original H430 multiplicities. -/
namespace ImbalancedChen.Part5OriginalH430EnhancedPositivePrices
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open P2EnhancedLowerPrimeChildCarriers (physicalPrime parentProduct)
open P2OriginalChildPhysicalNormalization (thetaAtom localPrimeFactor localPrimeFactor_pos)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430EnhancedPhysicalGrid Part5OriginalH430RootSourceDictionary
open Part5OriginalH430AllRootRejectedWindows Part5OriginalH430OwnedRootCounts Part5OriginalH430SameQHistoryCells
open Part5OriginalH430RootIntervalTheta
open Part5OriginalH430AbsoluteWordBox (literalScale_tendsto)
open Part5OriginalH430RequestedHistory Part5OriginalH430ZeroFreshReceiverPayment
open Part5OriginalH430AllTaggedHistoryUnits (multiplicity_range)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables.OriginalU34 (tailCutoff)

private def pivot : ℝ := 57/160

/-- This value is a closed integral on the actual descending branch. -/
def priceLimit (b c : ℝ) := (2/5:ℝ)*intervalMass b c pivot

def originMass (N n m : ℕ) (k : Root) (t b c : ℝ) :=
  ∑ p∈primeBand N b c, thetaAtom N (cellQ N n (keyAt N n m k t p).1) p / singularNormalization N

def inheritedAtom (N n m : ℕ) (k : Root) (t : ℝ) (p : ℕ) :=
  chargedList (fun o => thetaAtom N (cellQ N n (keyAt N n m k t p).1) (parentProduct o.current.old) /
    singularNormalization N) (rootHistory N n k t p)

/-- Every positive original receipt has exactly these compatible
fixed/retained positions. The raw inherited own-theta includes all their
marks, even when a later read repeats the same request. -/
theorem inheritedAtom_eq (N n m : ℕ) (k : Root) (t : ℝ) (p : ℕ) :
    inheritedAtom N n m k t p = listBudget (rootHistory N n k t p) *
      (thetaAtom N (cellQ N n (keyAt N n m k t p).1) p / singularNormalization N) := by
  let F := fun o : Occurrence N => thetaAtom N (cellQ N n (keyAt N n m k t p).1) (parentProduct o.current.old) /
    singularNormalization N
  let A := thetaAtom N (cellQ N n (keyAt N n m k t p).1) p / singularNormalization N
  have H (os : List (Occurrence N)) (h : ∀ o∈os,o∈rootHistory N n k t p) :
      chargedList F os=listBudget os*A := by
    induction os with
    | nil => simp [chargedList,listBudget]
    | cons o os ih =>
      rw [chargedList,listBudget,add_mul,ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]
      by_cases hz : o.path.all zeroFreshEdge=true
      · have hw := zeroFresh_original_word (h o (List.mem_cons_self ..)) hz
        have eq : F o=A := by simp [F,A,hw,parentProduct]
        rw [eq]
      · simp only [occurrenceBudget,if_neg hz,zero_mul]
  exact H _ (fun _ ho=>ho)

private theorem in_band {N p : ℕ} {b c : ℝ} (k : Root) (hN : 2≤N)
    (hb : 1/5≤b) (hc : c≤59/250) (hp : p∈primeBand N b c) :
    p∈originalBand N k ∧ physicalPrime N p∈Ico b c ∧ rootSource k (physicalPrime N p)=.enhanced := by
  obtain ⟨hcar,hlo,hhi⟩ := Finset.mem_filter.mp hp
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hl := Real.rpow_le_rpow_of_exponent_le hNr.le (show a≤b by dsimp [a]; linarith)
  have H (u : ℝ) (hu : c≤u) := hhi.trans_le (Real.rpow_le_rpow_of_exponent_le hNr.le hu)
  have hor : p∈originalBand N k := by
    cases k with
    | U3 => exact Finset.mem_filter.mpr ⟨hcar,hl.trans hlo,H _ (by linarith)⟩
    | U4 => exact Finset.mem_filter.mpr ⟨hcar,hl.trans hlo,H _ hc⟩
  have rpow : (N:ℝ)^physicalPrime N p = (p:ℝ) :=
    actualPrimeTupleLog_rpow (by omega : 1<N) (fun _ : Fin 1=>p) (fun _=>(original_band_prime hor).1.pos) 0
  rw [←rpow] at hlo hhi
  have hx := (Real.strictMono_rpow_of_base_gt_one hNr).le_iff_le.mp hlo
  have hx' := (Real.strictMono_rpow_of_base_gt_one hNr).lt_iff_lt.mp hhi
  refine ⟨hor,⟨hx,hx'⟩,?_⟩
  cases k with
  | U3 => exact (U3_source_split _).1.mpr (by dsimp [tailCutoff]; linarith)
  | U4 => rfl

private def base (N : ℕ) (b c : ℝ) :=
  (2/5:ℝ) * ((∑ p∈primeBand N b c,thetaAtom N ((N:ℝ)^pivot) p) / singularNormalization N)

private theorem comparison {N n m p : ℕ} {b c t : ℝ} (k : Root) (hN : 2≤N) (hn : 111≤n)
    (ht : 0≤t) (hu : t≤1/12) (hb : 1/5≤b) (hc : c≤59/250)
    (hp : p∈primeBand N b c) (hp2 : 2<p) (hscale : 0≤literalScale N) :
    let ref := (2/5:ℝ)*(thetaAtom N ((N:ℝ)^pivot) p / singularNormalization N)
    let own := thetaAtom N (cellQ N n (keyAt N n m k t p).1) p / singularNormalization N
    0≤ref ∧ ref≤own ∧ own≤(1+4*(1/((n:ℝ)+1)))*ref := by
  dsimp only
  let x := physicalPrime N p
  let nu := VariableEnvelope.v x
  let lam := frozenLevel n nu
  obtain ⟨hband,hx,hen⟩ := in_band k hN hb hc hp
  have hgeom := original_band_geometry hN hband
  have hpr := original_band_prime hband
  have hroot := enhanced_root_total (tau:=t) hen
  have hnu := root_total_bounds ht hu hgeom
  rw [hroot] at hnu
  have hfloor := enhanced_level_floor hn ht hu hgeom hen
  have hround := frozenLevel_bounds hnu n
  have hc' : nu=57/64-3*x/2 := by
    rw [show nu=VariableEnvelope.v x from rfl,VariableEnvelope.v_eq_min]
    rw [min_eq_right (by dsimp [VariableEnvelope.A,VariableEnvelope.C]; linarith only [hb,hx.1] :
      VariableEnvelope.C x ≤ VariableEnvelope.A x)]
    dsimp [VariableEnvelope.C]
    ring
  have hl : 1/4 < lam-x := by linarith only [hfloor,hx.2,hc]
  have hD : 0<pivot-x := by dsimp [pivot]; linarith only [hx.2,hc]
  have hn' : 0<nu-x := by linarith only [hround.1,hl]
  have identity : nu-x=(5/2:ℝ)*(pivot-x) := by rw [hc']; dsimp [pivot]; ring
  have hk : p∈rootFibre N n m k t (keyAt N n m k t p) := Finset.mem_filter.mpr ⟨hband,rfl⟩
  have hQ : cellQ N n (keyAt N n m k t p).1=(N:ℝ)^lam := by
    rw [(original_fibre_geometry hN ht hu (precision_error hn) hk).1,rootQ,rootLevel,hroot]
  have actual := normalized_root_atom (by omega : 1<N) hpr.1 hp2 hpr.2 (show x<lam by linarith only [hl])
  have comp := normalized_root_atom (by omega : 1<N) hpr.1 hp2 hpr.2 (show x<pivot by linarith only [hD])
  rw [hQ,actual,comp]
  let B := literalScale N * localPrimeFactor 1 p
  have hB : 0≤B := mul_nonneg hscale (localPrimeFactor_pos (d:=1) (by exact_mod_cast hp2)).le
  have baseEq : (2/5:ℝ)*(literalScale N*(localPrimeFactor 1 p*intervalProfile pivot x))=B*(4/(nu-x)) := by
    unfold intervalProfile
    rw [identity]
    dsimp [B]
    field_simp [hD.ne'] <;> ring
  rw [baseEq,show literalScale N*(localPrimeFactor 1 p*intervalProfile lam x)=B*(4/(lam-x)) by
    unfold intervalProfile; dsimp [B]; ring]
  have hl0 : 0<lam-x := lt_trans (by norm_num) hl
  have herr := one_div_pos.mpr (by positivity : 0<(n:ℝ)+1)
  have hsmall : (nu-x) ≤ (1+4*(1/((n:ℝ)+1)))*(lam-x) := by
    nlinarith only [hround.2,mul_nonneg herr.le (sub_nonneg.mpr hl.le)]
  refine ⟨mul_nonneg hB (div_nonneg (by norm_num) hn'.le),
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num) hl0
      (by linarith only [hround.1])) hB,?_⟩
  have hI : 4/(lam-x) ≤ (1+4*(1/((n:ℝ)+1)))*(4/(nu-x)) := by
    rw [←mul_div_assoc,div_le_div_iff₀ hl0 hn']
    nlinarith only [hsmall]
  exact (mul_le_mul_of_nonneg_left hI hB).trans_eq (by ring)

/-- For BOTH original tagged roots, the full integer prime interval has
a common positive price. n and N thresholds are uniform over both
tags, tau, and the original root-key precision m. -/
theorem positive_interval {b c : ℝ} (hb : 1/5≤b) (hbc : b<c) (hc : c≤59/250) :
    0<priceLimit b c ∧ ∀ eps : ℝ, 0<eps → ∃ T : ℕ, ∀ n≥T, ∃ N₀ : ℕ, ∀ N≥N₀,
      ∀ (m : ℕ) (k : Root) (t : ℝ), 0≤t → t≤1/12 →
      |originMass N n m k t b c-priceLimit b c|<eps ∧
      originMass N n m k t b c ≤ ∑ p∈primeBand N b c,inheritedAtom N n m k t p ∧
      (∑ p∈primeBand N b c,inheritedAtom N n m k t p / listBudget (rootHistory N n k t p)) =
        originMass N n m k t b c := by
  have hb0 : 0<b := by linarith only [hb]
  have hP : c<pivot := by dsimp [pivot]; linarith only [hc]
  have hpos : 0<priceLimit b c := mul_pos (by norm_num) (intervalMass_positive hb0 hbc hP)
  refine ⟨hpos,?_⟩
  intro eps he
  have hbase : Tendsto (fun N=>base N b c) atTop (𝓝 (priceLimit b c)) :=
    (actual_interval_theta_limit hb0 hbc (by linarith only [hc]) hP).const_mul (2/5:ℝ)
  have hpow : Tendsto (fun N : ℕ => (N:ℝ)^b) atTop atTop := (tendsto_rpow_atTop hb0).comp tendsto_natCast_atTop_atTop
  have hw : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdev := (Metric.tendsto_nhds.mp hbase) (eps/2) (half_pos he)
  let lim := priceLimit b c
  have hR : 0<4*(lim+1) := by dsimp [lim]; linarith
  apply eventually_atTop.1
  filter_upwards [hw.eventually (eventually_lt_nhds (div_pos (half_pos he) hR)),eventually_ge_atTop (111:ℕ)] with n hnerr hn
  apply eventually_atTop.1
  filter_upwards [hdev,hbase.eventually (eventually_lt_nhds (lt_add_one _)),eventually_ge_atTop (2:ℕ),
    hpow.eventually_gt_atTop 2,literalScale_tendsto.eventually (eventually_gt_nhds zero_lt_one)] with N hclose hmax hN hbig hs
  intro m k t ht hu
  have point (p) (hp : p∈primeBand N b c) := comparison (m:=m) k hN hn ht hu hb hc hp
    (by exact_mod_cast hbig.trans_le (Finset.mem_filter.mp hp).2.1 : 2<p) hs.le
  let A := fun p => (2/5:ℝ)*(thetaAtom N ((N:ℝ)^pivot) p/singularNormalization N)
  let S := fun p => thetaAtom N (cellQ N n (keyAt N n m k t p).1) p / singularNormalization N
  have hbal : (∑ p∈primeBand N b c,A p)=base N b c := by simp only [A,base,Finset.sum_div,Finset.mul_sum]
  have hlow := Finset.sum_le_sum (s:=primeBand N b c) (fun p hp=>(point p hp).2.1)
  have hhi := Finset.sum_le_sum (s:=primeBand N b c) (fun p hp=>(point p hp).2.2)
  change (∑ p∈primeBand N b c,A p) ≤ originMass N n m k t b c at hlow
  change originMass N n m k t b c ≤ ∑ p∈primeBand N b c,(1+4*(1/((n:ℝ)+1)))*A p at hhi
  rw [hbal] at hlow
  rw [←Finset.mul_sum,hbal] at hhi
  have step := (lt_div_iff₀ hR).mp hnerr
  have hprod := mul_le_mul_of_nonneg_left hmax.le (show 0≤4*(1/((n:ℝ)+1)) by positivity)
  rw [Real.dist_eq] at hclose
  obtain ⟨hl,hh⟩ := abs_lt.mp hclose
  refine ⟨abs_lt.mpr ⟨by linarith only [hl,hlow],by dsimp [lim] at step; nlinarith only [hh,hhi,step,hprod]⟩,?_,?_⟩
  · apply Finset.sum_le_sum
    intro p hp
    rw [inheritedAtom_eq]
    have hh := mul_le_mul_of_nonneg_right (multiplicity_range N n k t p).1
      ((point p hp).1.trans (point p hp).2.1)
    simpa only [one_mul] using hh
  · apply Finset.sum_congr rfl
    intro p hp
    rw [inheritedAtom_eq,mul_div_cancel_left₀ _ (lt_of_lt_of_le zero_lt_one (multiplicity_range N n k t p).1).ne']

end
end ImbalancedChen.Part5OriginalH430EnhancedPositivePrices
