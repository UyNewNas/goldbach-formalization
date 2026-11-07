import ImbalancedChen.P4AOrdinarySixTentRange32Leaf
import ImbalancedChen.P4ASymmetricSixTentRange32Leaf

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Executable INTEGER outer operation tree for the original P160, 256-term
positive-series ln32 compact reader. The only supplied arithmetic primitive
is `ln : Int -> Int -> IV`, whose arguments are denominator then numerator.
Its exact identity with originalLn32 is a separate, explicit OPEN primitive
obligation. The paired-renewal P160/W224 96-term logarithm is a different ABI.

All outer operations below use integer/rational data only. In particular no
real floor, ideal moment, target leaf inequality, log enclosure, or positive
log output is supplied to the executable tree. Signed four-product floors,
reciprocal-V division, direct rational weight division, SAME-reader queries,
clipping, the ordinary factor four, one symmetric /2, and final UP retain
the original evaluation order. The theorems identify these integers with
the existing original Range32 consumer; they do not implement ln32 or assert
the original full K certificate.
-/

namespace ImbalancedChen.P4ARange32IntegerOuterABI

open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdP4ASixTentRange32Moments OriginalThirdP4ASixTentRange32OldWeight
open OriginalThirdP4AOrdinarySixTentRange32Leaf
open P4AOriginalRange32MassCeil20261024zSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites
open OriginalThirdBelowMuBRoundedSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- V(F(n,d)): integer floor and UP, without Real or an ideal enclosure. -/
def vRatio (n d : ℤ) : IV := ⟨n*P160/d, up (n*P160) d⟩

def vRat (q : ℚ) : IV := vRatio q.num (q.den:ℤ)

def planeConstQ : TentSide → ℚ
  | .rise => 1/2 | .fall => 57/64

def planeSlopeQ : TentSide → ℚ
  | .rise => 1/2 | .fall => -3/2

def oldXQ (s : TentSum) (k : TentSide) : ℚ :=
  planeSlopeQ k*(literalTentX s:ℚ)-1
def oldYQ (s : TentSum) (k : TentSide) : ℚ :=
  planeSlopeQ k*(literalTentY s:ℚ)-1
def oldZQ (s : TentSum) (k : TentSide) : ℚ :=
  planeSlopeQ k*(literalTentZ s:ℚ)-1

def coordinateEx (ln : ℤ → ℤ → IV) (lo hi : Fin 3 → ℤ) (i : Fin 3) : IV :=
  divide (vRatio (hi i-lo i) sourceD) (ln (lo i) (hi i))

def invZ (lo hi : Fin 3 → ℤ) : IV :=
  vRatio (sourceD*(lo 2+hi 2)) (2*lo 2*hi 2)

def newValue (ln : ℤ → ℤ → IV) (lo hi : Fin 3 → ℤ) : IV :=
  sub (mul (sub (sub (vRat (299/500)) (coordinateEx ln lo hi 0))
    (coordinateEx ln lo hi 1)) (invZ lo hi)) (vRat 1)

def oldValue (ln : ℤ → ℤ → IV) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) : IV :=
  add (mul (add (add (vRat (planeConstQ k))
    (mul (coordinateEx ln lo hi 0) (vRat (oldXQ s k))))
    (mul (coordinateEx ln lo hi 1) (vRat (oldYQ s k))))
    (invZ lo hi)) (vRat (oldZQ s k))

/-- Direct rational division. In particular this is not reciprocal-V. -/
def rationalDivide (v : IV) (q : ℚ) : IV :=
  ⟨v.lo*(q.den:ℤ)/q.num, up (v.hi*(q.den:ℤ)) q.num⟩

def weight (ln : ℤ → ℤ → IV) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (low high : ℚ) : IV :=
  rationalDivide (sub (oldValue ln s k lo hi) (vRat low)) (high-low)

/-- Same reader at all three arguments, with exact Fraction normalization
at OLD endpoints and the actual rounded NEW high/P160 argument. -/
def mean (ln : ℤ → ℤ → IV) (readLo readHi : ℤ → ℤ → ℤ)
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ) : ℤ :=
  let low := savedLow32 s k hi
  let high := savedHigh32 s k lo
  let wt := weight ln s k lo hi low high
  meanHigh wt.lo wt.hi (readLo low.num (low.den:ℤ))
    (readLo high.num (high.den:ℤ)) (readHi (newValue ln lo hi).hi P160)

/-- Full ordinary reciprocal mass: multiply lx,ly first, then V(4D dz/z0z1). -/
def mass (ln : ℤ → ℤ → IV) (lo hi : Fin 3 → ℤ) : IV :=
  mul (mul (ln (lo 0) (hi 0)) (ln (lo 1) (hi 1)))
    (vRatio (4*sourceD*(hi 2-lo 2)) (lo 2*hi 2))

def ordinaryCost (ln : ℤ → ℤ → IV) (readLo readHi : ℤ → ℤ → ℤ)
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ) : ℤ :=
  up (mean ln readLo readHi s k lo hi*(mass ln lo hi).hi) P160

def symmetricCost (ln : ℤ → ℤ → IV) (readLo readHi : ℤ → ℤ → ℤ)
    (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) : ℤ :=
  up (mean ln readLo readHi s k ![x0,x0,z0] ![x1,x1,z1]*
    (divNat (mass ln ![x0,x0,z0] ![x1,x1,z1]) 2).hi) P160

/-- The OPEN primitive ABI: exact original ln32 output on the source grid.
This specifies a primitive implementation; it is not an enclosure supplier
or a target leaf bound, and no implementation of it is asserted here. -/
def Log32ABI (ln : ℤ → ℤ → IV) : Prop :=
  ∀ u v, sourceH≤u → u<v → v≤sourceR →
    ln u v=originalLn32 ((v:ℝ)/(u:ℝ))

theorem vRatio_eq_ofReal (n d : ℤ) (hd : 0<d) :
    vRatio n d=ofReal ((n:ℝ)/(d:ℝ)) :=
  (ofReal_int_div_source n d hd).symm

theorem vRat_eq_ofReal (q : ℚ) : vRat q=ofReal (q:ℝ) := by
  have hd : (0:ℤ)<(q.den:ℤ) := by exact_mod_cast q.den_pos
  simpa only [vRat,Rat.cast_def,Int.cast_natCast] using vRatio_eq_ofReal q.num (q.den:ℤ) hd

theorem planeConstQ_cast (k : TentSide) : (planeConstQ k:ℝ)=planeConst k := by
  cases k <;> norm_num [planeConstQ,planeConst]

theorem oldXQ_cast (s : TentSum) (k : TentSide) : (oldXQ s k:ℝ)=oldX s k := by
  cases s <;> cases k <;>
    norm_num [oldXQ,planeSlopeQ,literalTentX,oldX,planeSlope,sumX]

theorem oldYQ_cast (s : TentSum) (k : TentSide) : (oldYQ s k:ℝ)=oldY s k := by
  cases s <;> cases k <;>
    norm_num [oldYQ,planeSlopeQ,literalTentY,oldY,planeSlope,sumY]

theorem oldZQ_cast (s : TentSum) (k : TentSide) : (oldZQ s k:ℝ)=oldZ s k := by
  cases s <;> cases k <;>
    norm_num [oldZQ,planeSlopeQ,literalTentZ,oldZ,planeSlope,sumZ]

theorem coordinateEx_eq_grid (ln : ℤ → ℤ → IV) (lo hi : Fin 3 → ℤ) (i : Fin 3)
    (hln : ln (lo i) (hi i)=originalLn32 ((hi i:ℝ)/(lo i:ℝ))) :
    coordinateEx ln lo hi i=gridCoordinateEx32 lo hi i := by
  unfold coordinateEx gridCoordinateEx32 gridWidth32 vRatio
  rw [hln]

theorem invZ_eq_grid (lo hi : Fin 3 → ℤ) : invZ lo hi=gridInvZ32 lo hi := by rfl

theorem newValue_eq_grid (ln : ℤ → ℤ → IV) (lo hi : Fin 3 → ℤ)
    (hln : ∀ i,ln (lo i) (hi i)=originalLn32 ((hi i:ℝ)/(lo i:ℝ))) :
    newValue ln lo hi=gridNew32 lo hi := by
  have ht : vRat (299/500)=ofReal thirdPrefixTheta := by
    rw [vRat_eq_ofReal]
    congr 1
    norm_num [thirdPrefixTheta]
  have h1 : vRat 1=ofReal 1 := by simpa only [Rat.cast_one] using vRat_eq_ofReal 1
  unfold newValue gridNew32
  rw [ht,h1,coordinateEx_eq_grid ln lo hi 0 (hln 0),
    coordinateEx_eq_grid ln lo hi 1 (hln 1),invZ_eq_grid]

theorem oldValue_eq_grid (ln : ℤ → ℤ → IV) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ)
    (hln : ∀ i,ln (lo i) (hi i)=originalLn32 ((hi i:ℝ)/(lo i:ℝ))) :
    oldValue ln s k lo hi=gridTentOld32 s k lo hi := by
  unfold oldValue gridTentOld32
  rw [vRat_eq_ofReal,vRat_eq_ofReal,vRat_eq_ofReal,vRat_eq_ofReal,
    planeConstQ_cast,oldXQ_cast,oldYQ_cast,oldZQ_cast,
    coordinateEx_eq_grid ln lo hi 0 (hln 0),
    coordinateEx_eq_grid ln lo hi 1 (hln 1),invZ_eq_grid]

theorem weight_eq_grid (ln : ℤ → ℤ → IV) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (low high : ℚ)
    (hln : ∀ i,ln (lo i) (hi i)=originalLn32 ((hi i:ℝ)/(lo i:ℝ))) :
    weight ln s k lo hi low high=gridTentWeight32 s k lo hi low high := by
  unfold weight gridTentWeight32
  rw [oldValue_eq_grid ln s k lo hi hln,vRat_eq_ofReal]
  rfl

theorem mean_eq_grid (ln : ℤ → ℤ → IV) (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ)
    (hln : ∀ i,ln (lo i) (hi i)=originalLn32 ((hi i:ℝ)/(lo i:ℝ))) :
    mean ln (readQueryLo160 (assembledRead table.blocks))
      (readQueryHi160 (assembledRead table.blocks)) s k lo hi=
        gridMeanHigh32 table s k lo hi := by
  unfold mean gridMeanHigh32 savedFl32 savedFh32
  rw [weight_eq_grid ln s k lo hi _ _ hln,newValue_eq_grid ln lo hi hln]

theorem mass_eq_original (ln : ℤ → ℤ → IV) (lo hi : Fin 3 → ℤ)
    (hln : ∀ i,ln (lo i) (hi i)=originalLn32 ((hi i:ℝ)/(lo i:ℝ)))
    (hl : 0<lo 2) (hu : 0<hi 2) :
    mass ln lo hi=ordinaryMass32 lo hi := by
  rw [ordinaryMass32_source_tree]
  unfold mass
  rw [hln 0,hln 1,vRatio_eq_ofReal _ _ (mul_pos hl hu)]
  rfl

/-- Literal ordinary reader result, with Real completely absent from the
left-hand program. The primitive log equality is the only arithmetic ABI
obligation; positive raw divisors are proved by the existing source guard. -/
theorem ordinaryCost_eq_original (ln : ℤ → ℤ → IV) (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lo i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(hi i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lo i) (hwidth : ∀ i,lo i<hi i)
    (hln : ∀ i,ln (lo i) (hi i)=originalLn32 ((hi i:ℝ)/(lo i:ℝ))) :
    ordinaryCost ln (readQueryLo160 (assembledRead table.blocks))
      (readQueryHi160 (assembledRead table.blocks)) s k lo hi=
        ordinaryCost32 table s k lo hi a b := by
  have hl : 0<lo 2 := lt_of_lt_of_le (by norm_num [sourceH]) (hH 2)
  rw [ordinaryCost32_grid_abi table s k lo hi a b haBind hbBind hH hwidth]
  unfold ordinaryCost
  rw [mean_eq_grid ln table s k lo hi hln,mass_eq_original ln lo hi hln hl (hl.trans (hwidth 2))]

theorem symmetricMean_eq_original (ln : ℤ → ℤ → IV) (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (haBind : ∀ i,(![a,a,c]) i=((![x0,x0,z0]) i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,(![b,b,d]) i=((![x1,x1,z1]) i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤(![x0,x0,z0]) i)
    (hwidth : ∀ i,(![x0,x0,z0]) i<(![x1,x1,z1]) i)
    (hln : ∀ i,ln ((![x0,x0,z0]) i) ((![x1,x1,z1]) i)=
      originalLn32 (((![x1,x1,z1]) i:ℝ)/((![x0,x0,z0]) i:ℝ))) :
    mean ln (readQueryLo160 (assembledRead table.blocks))
      (readQueryHi160 (assembledRead table.blocks)) s k ![x0,x0,z0] ![x1,x1,z1]=
        symmetricMeanHigh32 table s k x0 x1 z0 z1 a b c d := by
  have hnew := ordinaryNew32_grid_abi ![x0,x0,z0] ![x1,x1,z1]
    ![a,a,c] ![b,b,d] haBind hbBind hH hwidth
  have hweight := tentWeight32_grid_abi s k ![x0,x0,z0] ![x1,x1,z1]
    ![a,a,c] ![b,b,d] (savedTentLow s k x1 z1) (savedTentHigh s k x0 z0)
    haBind hbBind hH hwidth
  have hleft : realBox ![a,a,c]=symmetricLeft (a:ℝ) (c:ℝ) := by
    funext i
    fin_cases i <;> rfl
  have hright : realBox ![b,b,d]=symmetricRight (b:ℝ) (d:ℝ) := by
    funext i
    fin_cases i <;> rfl
  rw [hleft,hright] at hnew hweight
  rw [mean_eq_grid ln table s k ![x0,x0,z0] ![x1,x1,z1] hln]
  unfold gridMeanHigh32 symmetricMeanHigh32 savedFl32 savedFh32
  rw [hnew,hweight]
  rfl

/-- One symmetric /2 occurs after the full ordinary mass tree and before
the final product/UP. Both OLD reader calls and NEW use the same table. -/
theorem symmetricCost_eq_original (ln : ℤ → ℤ → IV) (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (haBind : ∀ i,(![a,a,c]) i=((![x0,x0,z0]) i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,(![b,b,d]) i=((![x1,x1,z1]) i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤(![x0,x0,z0]) i)
    (hwidth : ∀ i,(![x0,x0,z0]) i<(![x1,x1,z1]) i)
    (hln : ∀ i,ln ((![x0,x0,z0]) i) ((![x1,x1,z1]) i)=
      originalLn32 (((![x1,x1,z1]) i:ℝ)/((![x0,x0,z0]) i:ℝ))) :
    symmetricCost ln (readQueryLo160 (assembledRead table.blocks))
      (readQueryHi160 (assembledRead table.blocks)) s k x0 x1 z0 z1=
        P4ASymmetricSixTentRange32Leaf.symmetricSixTentRange32Cost table s k
          x0 x1 z0 z1 a b c d := by
  have hz0 : 0<z0 := lt_of_lt_of_le (by norm_num [sourceH]) (hH 2)
  have hz1 : 0<z1 := hz0.trans (hwidth 2)
  unfold symmetricCost P4ASymmetricSixTentRange32Leaf.symmetricSixTentRange32Cost
  rw [symmetricMean_eq_original ln table s k x0 x1 z0 z1 a b c d
    haBind hbBind hH hwidth hln,mass_eq_original ln _ _ hln hz0 hz1]
  rfl

/-- A genuine implementation of the OPEN log ABI supplies precisely the
pointwise primitive equality required above from original integer bounds. -/
theorem Log32ABI.on_box {ln : ℤ → ℤ → IV} (hln : Log32ABI ln)
    (lo hi : Fin 3 → ℤ) (hH : ∀ i,sourceH≤lo i)
    (hwidth : ∀ i,lo i<hi i) (hR : ∀ i,hi i≤sourceR) :
    ∀ i,ln (lo i) (hi i)=originalLn32 ((hi i:ℝ)/(lo i:ℝ)) := by
  intro i
  exact hln (lo i) (hi i) (hH i) (hwidth i) (hR i)

end ImbalancedChen.P4ARange32IntegerOuterABI
