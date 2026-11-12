import ImbalancedChen.Part5OriginalH430ClassicalFixedClampGeometry

/-! Exact prime-coordinate description of the geometric switched carrier.
The inverse uses unique factorization of the sorted tail. The critical
upper product boundary is a radial inequality on the complete product. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalFixedClampPrimeGeometry
noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedSwitchedUnsiftedSource (labels)
open P2EnhancedNonunitLabelGeometry (label_data label_prod_pos)
open P2EnhancedUnitSourceGeometry (labels_power)
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)
open Part5UpperTables.OriginalU34 (clampStart)
open Part5OriginalH430ClassicalCausalSeedScale (smallProduct)
open Part5OriginalH430ClassicalSmallSwitchedIntegers (largeIntegers testWeight)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum)
open Part5OriginalH430ClassicalFixedClampMarks
open Part5OriginalH430ClassicalFixedClampGeometry (prime_divisor_floor)
open scoped Classical BigOperators

abbrev Tuple := ℕ × List ℕ × List ℕ
def tuple (u : Mark) : Tuple := (u.1,u.2.1,u.2.2.primeFactorsList)
def tuples (N : ℕ) (ν κ : ℝ) (cs : List ℕ) : Finset Tuple :=
  (marks 1 N ν κ cs).image tuple

def sharp (N : ℕ) (ν κ : ℝ) (cs : List ℕ) (v : Tuple) : Prop :=
  let p := v.1; let qs := v.2.1; let rs := v.2.2
  let R := (N:ℝ)^ν/(p:ℝ); let M := p*qs.prod*rs.prod
  (p.Prime ∧ (N:ℝ)^clampStart≤(p:ℝ) ∧ (p:ℝ)<(N:ℝ)^(1/3:ℝ)) ∧
  (qs.length=cs.length ∧ qs.Pairwise (·<·) ∧
    (∀q∈qs,q.Prime ∧ R^a0≤(q:ℝ) ∧ (q:ℝ)<R^b) ∧
    qs.map (secondFunctionalMotherColour (R^a1) (R^a2) (R^a3))=cs) ∧
  (rs.Pairwise (·≤·) ∧ ∀ r∈rs,r.Prime ∧ qs.getD (qs.length-2) 0≤r) ∧
  (smallProduct N κ<(M:ℝ) ∧ M≤N)

theorem tuple_mem {N : ℕ} {ν κ : ℝ} {cs : List ℕ} {v : Tuple} :
    v∈tuples N ν κ cs ↔ sharp N ν κ cs v := by
  rcases v with ⟨p,qs,rs⟩
  change (p,qs,rs)∈(marks 1 N ν κ cs).image tuple ↔ _
  constructor
  · rintro hv
    obtain ⟨⟨p',qs',m⟩,hu,he⟩ := mem_image.mp hv
    change (p',qs',m.primeFactorsList)=(p,qs,rs) at he
    have he' : p'=p ∧ qs'=qs ∧ m.primeFactorsList=rs := by simpa only [Prod.mk.injEq] using he
    obtain ⟨hep,heq,her⟩ := he'
    subst p
    subst qs
    subst rs
    obtain ⟨hp,hq,hm⟩ := flags.mp hu
    have hP := mem_primeWindow.mp hp
    obtain ⟨hlen,ho,hw,hc⟩ := label_data hq
    obtain ⟨hr,hlarge⟩ := mem_filter.mp hm
    obtain ⟨hmpos,hcap,hcut⟩ := mem_roughNumbers.mp hr
    have hD : 0<p'*qs'.prod := Nat.mul_pos hP.1.pos (label_prod_pos hq)
    have hpr := Nat.prod_primeFactorsList hmpos.ne'
    refine ⟨⟨hP.1,hP.2.2⟩,⟨hlen,ho,fun q h => ?_,hc⟩,
      ⟨(Nat.primeFactorsList_sorted _).pairwise,fun r hrs => ?_⟩,?_⟩
    · have h := mem_primeWindow.mp (hw q h)
      exact ⟨h.1,h.2.2⟩
    · have h := Nat.prime_of_mem_primeFactorsList hrs
      exact ⟨h,by exact_mod_cast hcut r h (Nat.dvd_of_mem_primeFactorsList hrs)⟩
    · rw [hpr]
      refine ⟨hlarge,?_⟩
      have hh := (le_div_iff₀ (Nat.cast_pos.mpr hD : (0:ℝ)<(p'*qs'.prod:ℕ))).mp hcap
      exact_mod_cast (by simpa only [mul_comm] using hh : ((p'*qs'.prod:ℕ):ℝ)*(m:ℝ)≤N)
  · rintro ⟨⟨hp,hlo,hhi⟩,⟨hlen,hord,hw,hcolour⟩,⟨hsort,hr⟩,hlarge,hcap⟩
    let u : Mark := ⟨p,qs,rs.prod⟩
    have hrs : 0<rs.prod := List.prod_pos (fun r h => (hr r h).1.pos)
    have hD : 0<p*qs.prod := Nat.mul_pos hp.pos (List.prod_pos (fun q h => (hw q h).1.pos))
    have he : rs=rs.prod.primeFactorsList :=
      (Nat.primeFactorsList_unique rfl (fun r h => (hr r h).1)).eq_of_pairwise'
        hsort (Nat.primeFactorsList_sorted _).pairwise
    apply mem_image.mpr
    refine ⟨u,flags.mpr ⟨mem_primeWindow.mpr ⟨hp,Nat.coprime_one_right _,hlo,hhi⟩,?_,?_⟩,?_⟩
    · rw [labels_power]
      exact mem_filter.mpr ⟨(secondFunctionalMother_tuple_mem _ _ _).mpr ⟨hlen,hord,
        fun q h => mem_primeWindow.mpr ⟨(hw q h).1,Nat.coprime_one_right _,(hw q h).2⟩⟩,hcolour⟩
    · refine mem_filter.mpr ⟨mem_roughNumbers.mpr ⟨hrs,?_,?_⟩,hlarge⟩
      · apply (le_div_iff₀ (Nat.cast_pos.mpr hD)).mpr
        have hh : ((p*qs.prod*rs.prod:ℕ):ℝ)≤N := by exact_mod_cast hcap
        simpa only [Nat.cast_mul,mul_comm,mul_left_comm,mul_assoc] using hh
      · intro r hprime hd
        exact prime_divisor_floor (z:=(qs.getD (qs.length-2) 0:ℝ))
          (fun r h => ⟨(hr r h).1,by exact_mod_cast (hr r h).2⟩) r hprime hd
    · dsimp only [u,tuple]
      rw [←he]

/-- The exact count before distribution, including multiplicities across
different original colour words. The strict tested endpoint is in testWeight. -/
theorem count_tuples (tested : Bool) (N : ℕ) (ν κ : ℝ) :
    count tested 1 N ν κ=wordsSum (fun cs => ∑ v∈tuples N ν κ cs,
      testWeight tested N (v.1*v.2.1.prod) v.2.2.prod) := by
  apply congrArg wordsSum
  funext cs
  have hpos {u : Mark} (h : u∈marks 1 N ν κ cs) : 0<u.2.2 :=
    (mem_roughNumbers.mp (mem_filter.mp (flags.mp h).2.2).1).1
  have hinj : Set.InjOn tuple (marks 1 N ν κ cs : Set Mark) := by
    rintro ⟨p,qs,m⟩ h ⟨p',qs',m'⟩ h' he
    have he' : p=p' ∧ qs=qs' ∧ m.primeFactorsList=m'.primeFactorsList := by
      simpa only [tuple,Prod.mk.injEq] using he
    obtain ⟨hep,heq,he''⟩ := he'
    subst p'
    subst qs'
    have hm := congrArg List.prod he''
    rw [Nat.prod_primeFactorsList (hpos h).ne',Nat.prod_primeFactorsList (hpos h').ne'] at hm
    cases hm
    rfl
  rw [tuples,sum_image hinj]
  exact sum_congr rfl (fun u h => by simp only [tuple,Nat.prod_primeFactorsList (hpos h).ne'])

/-- Applied to each of the five fixed endpoints and to each ordered prime
coordinate. It also controls the strict upper tests by taking complements. -/
theorem affine_colour_wall {N p q : ℕ} (hN : 1<N) (hp : 0<p) (hq : 0<q)
    (ν v : ℝ) :
    ((N:ℝ)^ν/(p:ℝ))^v≤(q:ℝ) ↔
      v*ν≤v*(log (p:ℝ)/log (N:ℝ))+log (q:ℝ)/log (N:ℝ) := by
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have hpr : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hqr : (0:ℝ)<q := Nat.cast_pos.mpr hq
  have hlog := log_pos hNr
  rw [←log_le_log_iff (rpow_pos_of_pos (div_pos (rpow_pos_of_pos h0 _) hpr) _) hqr,
    log_rpow (div_pos (rpow_pos_of_pos h0 _) hpr),
    log_div (rpow_pos_of_pos h0 _).ne' hpr.ne',log_rpow h0]
  rw [←mul_div_assoc,←add_div,le_div_iff₀ hlog]
  constructor <;> intro h <;> linarith only [h]

end
end ImbalancedChen.Part5OriginalH430ClassicalFixedClampPrimeGeometry
