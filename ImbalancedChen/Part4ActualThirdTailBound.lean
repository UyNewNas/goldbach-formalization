/-
SOURCEONLY COMPLETE / UNCOMPILED / HOLD, continuation 23 October 2026.
This bundle proves the original ideal-cap small-z tail bound as proposed Lean
source. It includes the repaired pure-List D10 V2 finite supplier, literal ideal
rho geometry, ordered-half improper integral, actual-log certificate, and final
actual tuple-space manuscript integral. No final Tnew/integral premise occurs.
All source-only parents remain uncompiled. In particular the existing
SymmetricTriangleIntegral source has not been promoted to an owned/kernel receipt.
Only the withdrawn finite-selector application comment of the generic ordered
bridge is corrected; that parent's theorem/proof body is unchanged.
The withdrawal is the literal-ideal addendum
20261022-original-third-tail-rho-margin-and-endpoint-binding-SOURCEONLY.txt,
SHA8170bd71a51f5402460a5bfe149c1c64f62943776ce67a62529775a127b3a46c.
Its superseded suggestion currentExtendedThirdCap 0 (select x y z) is not the
numerical tail cap. The actual application here is actualExtendedThirdIdealCap.
The old 15bd8854 parent file is preserved without modification.
No Lean/lake/typechecker/compiler/CI was run. The original mathematical constants
and both global reserves are unchanged; no global U/K ledger is asserted.

-/

import ImbalancedChen.ActualSieveGapTailBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import ImbalancedChen.ActualExtendedThirdIdealCap
import ImbalancedChen.ActualThirdPrefixTailIntegralCore
import ImbalancedChen.SymmetricTriangleIntegral
import ImbalancedChen.Certificates.RationalLogCertificate
import ImbalancedChen.ActualExtendedThirdClosedIntegral
import ImbalancedChen.ActualExtendedThirdCompactKernelApproximation

/- SOURCEONLY parent: 20261022-D10-dyadic-list-complete-V2-SOURCEONLY.txt; SHA256 12ac60f46610022a0ae2022e068456ffcc19b06a42973d2927d39ce5c21fe83b -/
namespace ImbalancedChen.D10DyadicListCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Set
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

def scale : ℤ := 1208925819614629174706176
def residualBound : ℤ := 268436897

def row : ℕ → List ℤ
  | 2 => [1208925819614629174706176]
  | 3 => [1208925819614629174706176]
  | 4 => [1208925819614629174706176, -604462909807314587353088, 151115727451828646838272, -50371909150609548946091, 18889465931478580854784, -7555786372591432341914, 3148244321913096809130, -1349247566534184346770, 590295810358705651711, -262353693492758067428, 118059162071741130342, -53663255487155059247, 24595658764946068821, -11351842506898185610, 5270498306774157604, -2459565876494606882, 1152921504606846975, -542551296285575048, 256204778801521550, -121360158379668103, 57646075230342348, -27450512014448738, 13101380734168715, -6265877742428516, 3002399751580330, -1441151880758559, 692861481133922, -333599972397815, 160842843834660, -77648269437423, 37529996894754, -18159675916817, 8796093022208, -4264772374404, 2069668946401, -1005267773967, 488671834567, -237732243844, 115738066081, -56385211681, 27487790694, -13408678388, 6544712070, -3196254732, 1561806289, -763549742, 373475417, -182764566, 89478485, -43826197, 21474836, -10526881, 5162220]
  | 5 => [718748581469832325566911, -402975273204876391568726, 67162545534146065261454, -14925010118699125613657, 3731252529674781403414, -995000674579941707578, 276389076272206029882, -78968307506344579967, 23032423022683835823, -6824421636350766170, 2047326490905229851, -620401966940978743, 189567267676410171, -58328390054280053, 18054025492991444, -5616807931152894, 1755252478485279, -550667444230676, 173358269480027, -54744716677904, 17335826948002, -5503437126350, 1751093631111, -558319708471, 178352129094, -57072681311, 18292526061, -5871675032, 1887324117, -607414659, 195722501, -63136291, 20387760, -6589984, 2132053, -690380, 223734, -72563, 23551, -7650, 2486, -809, 263, -86, 28, -10, 3, -1, 0, 0, 0, 0, 0]
  | 6 => [370962296242627935085055, -302231454903657293676544, 113336795588871485128704, -31482443219130968091307, 9051202425500153326250, -2754713781673959707990, 888723136706717953411, -302877969362621590343, 108418542252266733724, -40490115232689986709, 15669118264674198695, -6244326016329161757, 2548975868057829970, -1061218638108462086, 449065800041217727, -192623658455853430, 83576886770818880, -36619877837352192, 16181794715563365, -7203645837916607, 3227867866251045, -1454802768516230, 659106479014654, -300018731222730, 137149047505742, -62939768917182, 28986981766231, -13393731546815, 6207417180016, -2884918317889, 1344257505468, -627884855313, 293938331496, -137894845683, 64818399131, -30524960835, 14400287522, -6804609361, 3220413093, -1526370280, 724460328, -344306121, 163840650, -78058253, 37231588, -17777757, 8497547, -4065759, 1947162, -933379, 447808, -215026, 103332]
  | 7 => [157546683099873079721016, -143749716293966465113383, 54672498949884285668210, -11767169562260975773192, 2511325940274102646661, -551062251630847679603, 125010397757806003519, -29327184651972630029, 7106465001753824754, -1775203178593654086, 456025004873873058, -120137755266253827, 32365287914496180, -8891549579236375, 2484550494062184, -704503098798161, 202304430164066, -58730863071887, 17212134627252, -5086070450217, 1513800552320, -453446076138, 136598224774, -41358735445, 12579755197, -3842130031, 1177891785, -362353426, 111822982, -34609432, 10740587, -3341550, 1042027, -325653, 101979, -31997, 10057, -3167, 998, -316, 99, -32, 10, -4, 1, -1, 0, -1, 0, 0, 0, 0, 0]
  | 8 => [58763935655002374961763, -61827049373771322514176, 30338208689785718015893, -9667400720469051175583, 2520193557522421734085, -637732555186328008753, 165093793266822215326, -44744902293039315366, 12835255946122849956, -3909270181874991359, 1261225781159415149, -428505698125278034, 152192898551489168, -56093469880457693, 21314687458981096, -8305238049632812, 3304189887503600, -1337685538930162, 549634555547823, -228729971187932, 96245960754060, -40895135566129, 17527277389431, -7570337547697, 3292614547359, -1441145310950, 634412831352, -280751329515, 124845341926, -55764866402, 25011663575, -11261330176, 5088469222, -2306915892, 1049132696, -478518623, 218857002, -100356485, 46130698, -21253760, 9813612, -4540670, 2105053, -977725, 454925, -212031, 98982, -46280, 21669, -10161, 4770, -2243, 1055]
  | 9 => [19620374313591120054637, -22506669014267582817288, 11875456093445289137905, -3734448149370231616382, 820375500370416807940, -165509369764450567955, 32824026201264298080, -6570501121742689633, 1345012366145918883, -283596252871764696, 61822420777707662, -13951288475986360, 3257165815501235, -785178875829792, 194886479234935, -49647249555727, 12939391447625, -3439787338875, 930216252640, -255308474999, 70978081965, -19954844841, 5665570245, -1622613480, 468326461, -136111945, 39807300, -11708369, 3461629, -1028319, 306812, -91913, 27637, -8340, 2524, -767, 233, -72, 21, -7, 2, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0]
  | 10 => [5936944813785768896608, -7345491956875296870221, 4323283833165413711524, -1624365681504856059956, 454390555155738104857, -108443894453634353838, 24582333905302078707, -5581924941047047993, 1309662138755760176, -323785459113457381, 85291741423701347, -24024354493141235, 7216391641144079, -2296053829280944, 767340800545624, -267145488888499, 96190784241877, -35612076730689, 13493686412165, -5213953361624, 2048719281617, -816787776110, 329816357184, -134691506780, 55563761477, -23130724115, 9708718335, -4105738464, 1748242268, -749121231, 322872425, -139910631, 60931873, -26660187, 11715816, -5169538, 2289765, -1017867, 454005, -203151, 91177, -41039, 18521, -8381, 3801, -1729, 787, -360, 164, -76, 34, -16, 7]
  | 11 => [1656370713161842264165, -2180041590399013339405, 1371483922481477564260, -541423108829934972831, 148853263218334348190, -31461967849861204460, 5978133500254751671, -1090362336552266796, 197264409411229961, -36087995573280971, 6759869033681038, -1307283950651698, 262327888269954, -54744448502058, 11879815129813, -2675584378166, 623479272418, -149771632721, 36950031451, -9329338122, 2403143885, -629846348, 167583930, -45180758, 12323013, -3395906, 944485, -264873, 74841, -21292, 6095, -1756, 508, -148, 43, -13, 3, -2, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 12 => [428835849236372341398, -593694481378576889661, 396959321912693687994, -170573415899693369584, 53402148230098404217, -13359982961522634435, 2920730154354125433, -601524497591811876, 122407455302371639, -25432464235274815, 5526776372309307, -1277813683152677, 317335875065172, -84803247245586, 24274971739096, -7381269365954, 2361653308611, -788101395175, 272276669159, -96814033985, 35267100036, -13114577535, 4964517747, -1908851077, 744146173, -293693079, 117204042, -47244532, 19219074, -7884057, 3259196, -1356931, 568673, -239787, 101685, -43352, 18574, -7996, 3457, -1501, 654, -287, 125, -56, 24, -11, 4, -3, 1, -1, 0, -1, 0]
  | 13 => [103990119950977087537, -150579155741985660379, 105937306642772681808, -47980561689909785694, 15576472588628734770, -3839257337688168860, 767549311186394678, -137447134641209348, 23323775898190139, -3877319359563143, 645307907357720, -109197918241804, 19003492812966, -3429159454725, 644957931256, -126722582833, 26002404094, -5558918385, 1233703258, -283046365, 66850995, -16191186, 4007691, -1010882, 259208, -67433, 17768, -4736, 1275, -347, 95, -27, 7, -3, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 14 => [23755025269884529113, -35736320769697695117, 26226283422844774365, -12483663576621756576, 4333841804782471652, -1178958590820471514, 267427443272569333, -53872557309399303, 10194087487058406, -1888519955544805, 353576198626483, -68655593625562, 14118230646068, -3120222069347, 746226988970, -192900831026, 53514488704, -15773946706, 4890085598, -1580255307, 528495353, -181892886, 64145182, -23100405, 8472779, -3158310, 1194393, -457588, 177379, -69500, 27498, -10979, 4420, -1794, 732, -302, 124, -52, 21, -10, 3, -2, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
  | 15 => [5138364527250469481, -7999239996229006734, 6099169066854410273, -3029119096832859035, 1097459980392468515, -307174038618440136, 68911891420261147, -12978249007779798, 2195143054766037, -349443763558278, 54017794089135, -8290110826917, 1284545752165, -203657052302, 33388467772, -5704597334, 1020632417, -191549877, 37672078, -7740084, 1654261, -366067, 83491, -19547, 4680, -1144, 284, -72, 18, -5, 1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 16 => [1057286621636934423, -1696787519277466366, 1336896724606255767, -688097068382316331, 259784906817298313, -76756877600738071, 18604083081240022, -3867876956734791, 722747285772703, -126794172803493, 21640482219830, -3701175459902, 651003117169, -120495978309, 23911580547, -5147567223, 1205867586, -305917522, 83232319, -24016043, 7273429, -2292395, 746860, -250237, 85880, -30097, 10743, -3899, 1435, -536, 202, -78, 29, -12, 4, -2, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 17 => [207677436580061951, -342557635150031299, 278059921045967934, -147895309087696581, 57880083734932479, -17719737537762646, 4397474736747259, -907587998483283, 161094708309689, -25806672009212, 3878025410941, -562412413325, 80425818741, -11536695267, 1683971860, -253173662, 39592509, -6486716, 1117866, -202785, 38643, -7706, 1599, -344, 76, -18, 4, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 18 => [39073320327008704, -66080413852308402, 55089622910305461, -30147416050559723, 12164676820843679, -3855545176258413, 1000360452937813, -219698623204169, 42232557180968, -7365331550142, 1206763479717, -191523392143, 30249649861, -4874994787, 820852279, -147514636, 28751120, -6124580, 1423733, -358091, 96311, -27380, 8145, -2517, 802, -263, 88, -31, 10, -4, 1, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 19 => [7060815346243408, -12216319798827174, 10434528086731131, -5861352494498632, 2433520096635183, -795460754370274, 212716091270725, -47678750288838, 9127494489008, -1530161204064, 232812487328, -33187969435, 4546470966, -610784934, 81835711, -11096753, 1542738, -222410, 33554, -5331, 894, -159, 29, -6, 1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | _ => []

def addList : List ℤ → List ℤ → List ℤ :=
  fun a b =>
    List.rec (motive := fun _ => List ℤ → List ℤ)
      (fun ys => ys)
      (fun x xs ih ys =>
        match ys with
        | [] => x :: xs
        | y :: rest => (x + y) :: ih rest)
      a b

def scaleList (j : ℤ) (a : List ℤ) : List ℤ := a.map (fun x => j * x)

def derivativeFrom : ℕ → List ℤ → List ℤ :=
  fun n a =>
    List.rec (motive := fun _ => ℕ → List ℤ)
      (fun _ => [])
      (fun x _xs ih k => ((k : ℤ) * x) :: ih (k + 1))
      a n

def derivList (a : List ℤ) : List ℤ := derivativeFrom 1 a.tail

def residualList (j : ℤ) (a b : List ℤ) : List ℤ :=
  addList (addList (scaleList j (derivList a)) (0 :: derivList a)) b

def absSum (a : List ℤ) : ℤ := (a.map abs).sum
def startValue (i : ℕ) : ℤ := ((row i).head?).getD 0
def endValue (i : ℕ) : ℤ := (row i).sum
def err (i : ℕ) : ℤ := (2 ^ (i - 3) - 1) * residualBound

/-- Pure finite List/integer proposition. `decide` is only proposed source. -/
theorem finiteGood : ∀ k : Fin 16,
    startValue (k.val + 4) = endValue (k.val + 3) ∧
      absSum (residualList ((k.val + 2 : ℕ) : ℤ)
        (row (k.val + 4)) (row (k.val + 2))) ≤ residualBound ∧
      err (k.val + 2) ≤ err (k.val + 3) ∧
      err (k.val + 4) = 2 * err (k.val + 3) + residualBound := by
  decide

theorem finiteNonneg : ∀ k : Fin 18, 0 ≤ err (k.val + 2) := by decide
theorem row_two : row 2 = [scale] := by decide
theorem row_three : row 3 = [scale] := by decide
theorem endpoint : endValue 19 = 1228568788472664 := by decide
theorem endpoint_error : err 19 = 17592012044895 := by decide
theorem endpoint_integer_slack :
    10 * (668681894992131129186433 : ℤ) -
      (1228568788472664 + 17592012044895) * 4294967296 =
        1334599066141215513113866 := by decide

noncomputable section

/-- Dense coefficients interpreted as the actual real Horner function. -/
def evalList : List ℤ → ℝ → ℝ :=
  fun a t => a.foldr (fun x acc => (x : ℝ) + t * acc) 0

private theorem evalList_nil (t : ℝ) : evalList [] t = 0 := by
  rfl

private theorem evalList_cons (x : ℤ) (a : List ℤ) (t : ℝ) :
    evalList (x :: a) t = (x : ℝ) + t * evalList a t := by
  rfl

private theorem addList_nil (b : List ℤ) : addList [] b = b := by
  rfl

private theorem addList_cons_nil (x : ℤ) (a : List ℤ) :
    addList (x :: a) [] = x :: a := by
  rfl

private theorem addList_cons_cons (x y : ℤ) (a b : List ℤ) :
    addList (x :: a) (y :: b) = (x + y) :: addList a b := by
  rfl

private theorem eval_addList (a b : List ℤ) (t : ℝ) :
    evalList (addList a b) t = evalList a t + evalList b t := by
  induction a generalizing b with
  | nil => simp only [addList_nil, evalList_nil, zero_add]
  | cons x a ih =>
      cases b with
      | nil => simp only [addList_cons_nil, evalList_nil, add_zero]
      | cons y b =>
          simp only [addList_cons_cons, evalList_cons, ih, Int.cast_add]
          ring

private theorem eval_scaleList (j : ℤ) (a : List ℤ) (t : ℝ) :
    evalList (scaleList j a) t = (j : ℝ) * evalList a t := by
  induction a with
  | nil => simp [scaleList, evalList]
  | cons x a ih =>
      change (((j * x : ℤ) : ℝ) + t * evalList (scaleList j a) t) =
        (j : ℝ) * ((x : ℝ) + t * evalList a t)
      rw [ih, Int.cast_mul]
      ring

private theorem eval_derivativeFrom (a : List ℤ) (t : ℝ) :
    ∀ n : ℕ, evalList (derivativeFrom n a) t =
      (n : ℝ) * evalList a t + t * evalList (derivList a) t := by
  induction a with
  | nil => intro n; simp [derivativeFrom, derivList, evalList]
  | cons x a ih =>
      intro n
      change ((((n : ℤ) * x : ℤ) : ℝ) +
        t * evalList (derivativeFrom (n + 1) a) t) =
          (n : ℝ) * ((x : ℝ) + t * evalList a t) +
            t * evalList (derivativeFrom 1 a) t
      rw [ih (n + 1), ih 1]
      push_cast
      ring

/-- The integer derivative list is the genuine real derivative. -/
private theorem hasDerivAt_evalList (a : List ℤ) (t : ℝ) :
    HasDerivAt (evalList a) (evalList (derivList a) t) t := by
  induction a with
  | nil =>
      change HasDerivAt (fun _ : ℝ => 0) 0 t
      convert! (hasDerivAt_const t (0 : ℝ)) using 1
  | cons x a ih =>
      have h := (hasDerivAt_const t (x : ℝ)).add ((hasDerivAt_id t).mul ih)
      change HasDerivAt (fun y : ℝ => (x : ℝ) + y * evalList a y)
        (evalList (derivativeFrom 1 a) t) t
      convert! h using 1
      simpa only [Nat.cast_one, zero_add, one_mul, id_eq] using eval_derivativeFrom a t 1

/-- Structural semantic bridge for the finite residual checker. -/
private theorem eval_residualList (j : ℤ) (a b : List ℤ) (t : ℝ) :
    evalList (residualList j a b) t =
      ((j : ℝ) + t) * evalList (derivList a) t + evalList b t := by
  simp only [residualList, eval_addList, eval_scaleList, evalList_cons,
    Int.cast_zero, zero_add]
  ring

private theorem eval_zero (a : List ℤ) :
    evalList a 0 = (((a.head?).getD 0 : ℤ) : ℝ) := by
  cases a <;> simp [evalList]

private theorem eval_one (a : List ℤ) : evalList a 1 = (a.sum : ℝ) := by
  induction a with
  | nil => simpa only [List.sum_nil, Int.cast_zero] using evalList_nil 1
  | cons x a ih =>
      change (x : ℝ) + 1 * evalList a 1 = ((x + a.sum : ℤ) : ℝ)
      rw [ih, one_mul, Int.cast_add]

private theorem absSum_nonneg (a : List ℤ) : 0 ≤ absSum a := by
  induction a with
  | nil => simp [absSum]
  | cons x a ih =>
      have h : absSum (x :: a) = |x| + absSum a := by simp [absSum]
      rw [h]
      exact add_nonneg (abs_nonneg x) ih

/-- Coefficient l1 is a uniform bound on the actual real function on [0,1]. -/
private theorem abs_evalList_le (a : List ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |evalList a t| ≤ (absSum a : ℝ) := by
  induction a with
  | nil => simp [evalList, absSum]
  | cons x a ih =>
      have ha : (0 : ℝ) ≤ (absSum a : ℝ) := by exact_mod_cast absSum_nonneg a
      have hsum : absSum (x :: a) = |x| + absSum a := by simp [absSum]
      change |(x : ℝ) + t * evalList a t| ≤ _
      calc
        _ ≤ |(x : ℝ)| + |t * evalList a t| := abs_add_le _ _
        _ = |(x : ℝ)| + t * |evalList a t| := by rw [abs_mul, abs_of_nonneg ht.1]
        _ ≤ |(x : ℝ)| + t * (absSum a : ℝ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left ih ht.1)
        _ ≤ |(x : ℝ)| + (absSum a : ℝ) :=
          add_le_add le_rfl
            (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 ha)
        _ = (absSum (x :: a) : ℝ) := by simp [hsum]

/-- Closed-interval MVT, requiring differentiability only on the interior. -/
private theorem abs_sub_le_of_hasDerivAt_bound
    {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hb : ∀ x ∈ Ioo a b, |f' x| ≤ C) {x : ℝ} (hx : x ∈ Icc a b) :
    |f x - f a| ≤ C * (x - a) := by
  have hdiff : DifferentiableOn ℝ f (interior (Icc a b)) := by
    intro y hy
    have hy' : y ∈ Ioo a b := by simpa only [interior_Icc] using hy
    exact (hd y hy').differentiableAt.differentiableWithinAt
  have hupper : ∀ y ∈ interior (Icc a b), deriv f y ≤ C := by
    intro y hy
    have hy' : y ∈ Ioo a b := by simpa only [interior_Icc] using hy
    rw [(hd y hy').deriv]
    exact (abs_le.mp (hb y hy')).2
  have hlower : ∀ y ∈ interior (Icc a b), -C ≤ deriv f y := by
    intro y hy
    have hy' : y ∈ Ioo a b := by simpa only [interior_Icc] using hy
    rw [(hd y hy').deriv]
    exact (abs_le.mp (hb y hy')).1
  have hu := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    hc hdiff hupper a ⟨le_rfl, hab⟩ x hx hx.1
  have hl := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hc hdiff hlower a ⟨le_rfl, hab⟩ x hx hx.1
  exact abs_le.mpr ⟨by linarith, hu⟩

private theorem cell_step
    (V : ℝ → ℝ) (a : ℝ) (ha : 2 ≤ a) (j : ℤ)
    (haj : (j : ℝ) = 2 * (a - 1))
    (u v : List ℤ) (B S : ℝ) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hc : ContinuousOn V (Icc a (a + 1 / 2)))
    (hd : ∀ s ∈ Ioo a (a + 1 / 2), HasDerivAt V (-V (s - 1) / (s - 1)) s)
    (hleft : |V a - evalList u 0| ≤ B)
    (hdelay : ∀ s ∈ Icc (a - 1) (a - 1 / 2),
      |V s - evalList v (2 * (s - (a - 1)))| ≤ B)
    (hresidual : ∀ t ∈ Icc (0 : ℝ) 1, |evalList (residualList j u v) t| ≤ S) :
    ∀ s ∈ Icc a (a + 1 / 2), |V s - evalList u (2 * (s - a))| ≤ 2 * B + S := by
  let f : ℝ → ℝ := fun s => V s - evalList u (2 * (s - a))
  let f' : ℝ → ℝ := fun s =>
    -V (s - 1) / (s - 1) - 2 * evalList (derivList u) (2 * (s - a))
  have huc : Continuous (evalList u) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_evalList u t).continuousAt)
  have hpc : Continuous (fun s : ℝ => evalList u (2 * (s - a))) :=
    huc.comp (continuous_const.mul (continuous_id.sub continuous_const))
  have hfc : ContinuousOn f (Icc a (a + 1 / 2)) := hc.sub hpc.continuousOn
  have hfd : ∀ s ∈ Ioo a (a + 1 / 2), HasDerivAt f (f' s) s := by
    intro s hs
    have ht : HasDerivAt (fun s : ℝ => 2 * (s - a)) 2 s := by
      simpa using ((hasDerivAt_id s).sub_const a).const_mul 2
    have hp := (hasDerivAt_evalList u (2 * (s - a))).comp s ht
    dsimp only [f, f']
    convert! (hd s hs).sub hp using 1
    ring
  have hfb : ∀ s ∈ Ioo a (a + 1 / 2), |f' s| ≤ B + S := by
    intro s hs
    let t : ℝ := 2 * (s - a)
    have ht : t ∈ Icc (0 : ℝ) 1 := by dsimp [t]; constructor <;> linarith [hs.1, hs.2]
    have hden : 0 < s - 1 := by linarith [hs.1]
    have hden1 : 1 ≤ s - 1 := by linarith [hs.1]
    have hds : s - 1 ∈ Icc (a - 1) (a - 1 / 2) := by
      constructor <;> linarith [hs.1, hs.2]
    have he : |V (s - 1) - evalList v t| ≤ B := by
      convert hdelay (s - 1) hds using 1; dsimp [t]; ring
    let R : List ℤ := residualList j u v
    have hR : |evalList R t| ≤ S := hresidual t ht
    have hEval : evalList R t =
        ((j : ℝ) + t) * evalList (derivList u) t + evalList v t :=
      eval_residualList j u v t
    have hIdentity : f' s =
        -(V (s - 1) - evalList v t) / (s - 1) - evalList R t / (s - 1) := by
      rw [hEval]
      dsimp [f', t]
      rw [haj]
      field_simp [hden.ne']
      ring
    calc
      |f' s| = |-(V (s - 1) - evalList v t) / (s - 1) - evalList R t / (s - 1)| :=
        congrArg abs hIdentity
      _ ≤ |-(V (s - 1) - evalList v t) / (s - 1)| + |evalList R t / (s - 1)| :=
        by
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le (-(V (s - 1) - evalList v t) / (s - 1)) 0
              (evalList R t / (s - 1))
      _ = (|V (s - 1) - evalList v t| + |evalList R t|) / (s - 1) := by
        simp only [abs_div, abs_neg, abs_of_pos hden]
        ring
      _ ≤ (B + S) / (s - 1) :=
        div_le_div_of_nonneg_right (add_le_add he hR) hden.le
      _ ≤ B + S := div_le_self (add_nonneg hB hS) hden1
  intro s hs
  have hmv := abs_sub_le_of_hasDerivAt_bound (by linarith : a ≤ a + 1 / 2)
    hfc hfd hfb hs
  have hfa : |f a| ≤ B := by simpa only [f, sub_self, mul_zero] using hleft
  change |f s| ≤ _
  calc
    |f s| ≤ |f s - f a| + |f a| := by
      simpa only [sub_add_cancel] using abs_add_le (f s - f a) (f a)
    _ ≤ (B + S) * (s - a) + B := add_le_add hmv hfa
    _ ≤ (B + S) * (1 / 2) + B := by
      have hlen : s - a ≤ (1 / 2 : ℝ) := by linarith only [hs.2]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlen (add_nonneg hB hS)) le_rfl
    _ ≤ 2 * B + S := by linarith

def scaledSource (s : ℝ) : ℝ :=
  (scale : ℝ) * (s * suzukiProposition118SourceQ s) /
    (2 * Real.exp Real.eulerMascheroniConstant)

private theorem scaled_history {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    scaledSource s = (scale : ℝ) := by
  have hAmp := suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract
  have hs0 : s ≠ 0 := ne_of_gt (by linarith : 0 < s)
  have hW : s * suzukiProposition118SourceQ s =
      2 * Real.exp Real.eulerMascheroniConstant := by
    by_cases hs : s < 2
    · rw [suzukiProposition118SourceQ, if_pos hs, hAmp]
      field_simp [hs0]
    · have hs : s = 2 := by linarith
      subst s
      rw [suzukiProposition118SourceQ_at_two jr1965Section13HatSourceContract,
        suzukiLowerBoundaryLimit_eq_zero_of_sourceContract jr1965Section13HatSourceContract,
        hAmp]
      ring
  rw [scaledSource, hW]
  field_simp [ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]

private theorem scaled_continuous : ContinuousOn scaledSource (Icc (2 : ℝ) 10) := by
  have h := continuousOn_weighted_suzukiProposition118SourceQ
    jr1965Section13HatSourceContract (M := (10 : ℝ)) (by norm_num)
  exact (continuousOn_const.mul h).div_const _

private theorem scaled_hasDeriv {s : ℝ} (hs : 2 < s) (hs3 : s ≠ 3) :
    HasDerivAt scaledSource (-scaledSource (s - 1) / (s - 1)) s := by
  have h := ((hasDerivAt_weighted_suzukiProposition118SourceQ
    jr1965Section13HatSourceContract hs hs3).const_mul (scale : ℝ)).div_const
      (2 * Real.exp Real.eulerMascheroniConstant)
  have he : (scale : ℝ) * (-suzukiProposition118SourceQ (s - 1)) /
      (2 * Real.exp Real.eulerMascheroniConstant) =
        -scaledSource (s - 1) / (s - 1) := by
    dsimp only [scaledSource]
    field_simp [ne_of_gt (by linarith : 0 < s - 1),
      ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]
  convert! h.congr_deriv he using 1

private def left (i : ℕ) : ℝ := (i : ℝ) / 2
private def right (i : ℕ) : ℝ := left i + 1 / 2
private def value (i : ℕ) (s : ℝ) : ℝ := evalList (row i) (2 * (s - left i))

private theorem finite_good_at (i : ℕ) (hi4 : 4 ≤ i) (hi19 : i ≤ 19) :
    startValue i = endValue (i - 1) ∧
      absSum (residualList ((i - 2 : ℕ) : ℤ) (row i) (row (i - 2))) ≤ residualBound ∧
      err (i - 2) ≤ err (i - 1) ∧
      err i = 2 * err (i - 1) + residualBound := by
  let k : Fin 16 := ⟨i - 4, by omega⟩
  have h4 : k.val + 4 = i := by dsimp [k]; omega
  have h3 : k.val + 3 = i - 1 := by dsimp [k]; omega
  have h2 : k.val + 2 = i - 2 := by dsimp [k]; omega
  simpa only [h4, h3, h2] using finiteGood k

private theorem finite_nonneg_at (i : ℕ) (hi2 : 2 ≤ i) (hi19 : i ≤ 19) :
    0 ≤ err i := by
  let k : Fin 18 := ⟨i - 2, by omega⟩
  have h2 : k.val + 2 = i := by dsimp [k]; omega
  simpa only [h2] using finiteNonneg k

private theorem initial_cell (i : ℕ) (hi : i = 2 ∨ i = 3) :
    ∀ s ∈ Icc (left i) (right i),
      |scaledSource s - value i s| ≤ (err i : ℝ) := by
  rcases hi with rfl | rfl
  · intro s hs
    have hVs := scaled_history (s := s)
      (by norm_num [left, right] at hs; linarith [hs.1])
      (by norm_num [left, right] at hs; linarith [hs.2])
    simp [value, row_two, evalList, hVs, err]
  · intro s hs
    have hVs := scaled_history (s := s)
      (by norm_num [left, right] at hs; linarith [hs.1])
      (by norm_num [left, right] at hs; linarith [hs.2])
    simp [value, row_three, evalList, hVs, err]

private theorem all_cells (i : ℕ) : i ≤ 19 → 2 ≤ i →
    ∀ s ∈ Icc (left i) (right i),
      |scaledSource s - value i s| ≤ (err i : ℝ) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi19 hi2
      by_cases hi4 : i < 4
      · exact initial_cell i (by omega)
      have hi4' : 4 ≤ i := by omega
      have hcert := finite_good_at i hi4' hi19
      have hprev := ih (i - 1) (by omega) (by omega) (by omega)
      have hdelay := ih (i - 2) (by omega) (by omega) (by omega)
      have hcast1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ i)]
        norm_num
      have hcast2 : ((i - 2 : ℕ) : ℝ) = (i : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ i)]
        norm_num
      have hleft1 : left (i - 1) = left i - 1 / 2 := by
        dsimp [left]; rw [hcast1]; ring
      have hleft2 : left (i - 2) = left i - 1 := by
        dsimp [left]; rw [hcast2]; ring
      have hB : (0 : ℝ) ≤ (err (i - 1) : ℝ) := by
        exact_mod_cast finite_nonneg_at (i - 1) (by omega) (by omega)
      have hS : (0 : ℝ) ≤ (residualBound : ℝ) := by norm_num [residualBound]
      have hc : ContinuousOn scaledSource (Icc (left i) (left i + 1 / 2)) := by
        apply scaled_continuous.mono
        intro s hs
        have hiR : (i : ℝ) ≤ 19 := by exact_mod_cast hi19
        have hi4R : (4 : ℝ) ≤ i := by exact_mod_cast hi4'
        dsimp [left] at hs
        constructor <;> linarith [hs.1, hs.2]
      have hd : ∀ s ∈ Ioo (left i) (left i + 1 / 2),
          HasDerivAt scaledSource (-scaledSource (s - 1) / (s - 1)) s := by
        intro s hs
        have hs2 : 2 < s := by
          have hi4R : (4 : ℝ) ≤ i := by exact_mod_cast hi4'
          dsimp [left] at hs
          linarith [hs.1]
        have hs3 : s ≠ 3 := by
          intro heq
          dsimp [left] at hs
          have hlt : i < 6 := by exact_mod_cast (show (i : ℝ) < 6 by linarith [hs.1])
          have hgt : 6 < i + 1 := by
            exact_mod_cast (show (6 : ℝ) < (i : ℝ) + 1 by linarith [hs.2])
          omega
        exact scaled_hasDeriv hs2 hs3
      have hjoin : evalList (row i) 0 = evalList (row (i - 1)) 1 := by
        rw [eval_zero, eval_one]
        exact_mod_cast hcert.1
      have hl : |scaledSource (left i) - evalList (row i) 0| ≤
          (err (i - 1) : ℝ) := by
        have hmem : left i ∈ Icc (left (i - 1)) (right (i - 1)) := by
          rw [right, hleft1]
          constructor <;> linarith
        have h := hprev (left i) hmem
        simpa only [value, hleft1, show 2 * (left i - (left i - 1 / 2)) = 1 by ring,
          ← hjoin] using h
      have hdel : ∀ s ∈ Icc (left i - 1) (left i - 1 / 2),
          |scaledSource s - evalList (row (i - 2)) (2 * (s - (left i - 1)))| ≤
            (err (i - 1) : ℝ) := by
        intro s hs
        have hmem : s ∈ Icc (left (i - 2)) (right (i - 2)) := by
          rw [right, hleft2]
          constructor <;> linarith [hs.1, hs.2]
        have h := hdelay s hmem
        have hmono : (err (i - 2) : ℝ) ≤ (err (i - 1) : ℝ) := by
          exact_mod_cast hcert.2.2.1
        simpa only [value, hleft2] using h.trans hmono
      have hr : ∀ t ∈ Icc (0 : ℝ) 1,
          |evalList (residualList ((i - 2 : ℕ) : ℤ) (row i) (row (i - 2))) t| ≤
            (residualBound : ℝ) := by
        intro t ht
        exact (abs_evalList_le _ ht).trans (by exact_mod_cast hcert.2.1)
      have hstep := cell_step scaledSource (left i)
        (by
          have hi4R : (4 : ℝ) ≤ i := by exact_mod_cast hi4'
          dsimp [left]; linarith)
        ((i - 2 : ℕ) : ℤ)
        (by simp only [Int.cast_natCast, hcast2]; dsimp [left]; ring)
        (row i) (row (i - 2)) (err (i - 1) : ℝ) (residualBound : ℝ)
        hB hS hc hd hl hdel hr
      intro s hs
      have h := hstep s hs
      change |scaledSource s - value i s| ≤ _ at h
      have he : (err i : ℝ) = 2 * (err (i - 1) : ℝ) + (residualBound : ℝ) := by
        exact_mod_cast hcert.2.2.2
      simpa only [he] using h

theorem scaled_at_ten_le : scaledSource 10 ≤ (1246160800517559 : ℝ) := by
  have h := all_cells 19 (by norm_num) (by norm_num) 10 (by norm_num [left, right])
  have hp : value 19 10 = (1228568788472664 : ℝ) := by
    dsimp [value, left]
    norm_num only
    rw [eval_one]
    change (endValue 19 : ℝ) = _
    rw [endpoint]
    norm_num
  rw [hp, endpoint_error] at h
  norm_num only [Int.cast_ofNat] at h
  have hh := (abs_le.mp h).2
  linarith

end
end ImbalancedChen.D10DyadicListCertificate

namespace ImbalancedChen
noncomputable section

theorem actualSieveGap_normalized_at_ten_upper_dyadic_list :
    actualSieveGap (10 : ℝ) / (2 * Real.exp Real.eulerMascheroniConstant) ≤
      (668681894992131129186433 /
        5192296858534827628530496329220096 : ℝ) := by
  have h := D10DyadicListCertificate.scaled_at_ten_le
  have hscale : (0 : ℝ) < (D10DyadicListCertificate.scale : ℝ) := by
    norm_num [D10DyadicListCertificate.scale]
  have heq : actualSieveGap (10 : ℝ) /
      (2 * Real.exp Real.eulerMascheroniConstant) =
        D10DyadicListCertificate.scaledSource 10 /
          (10 * (D10DyadicListCertificate.scale : ℝ)) := by
    rw [actualSieveGap_eq_source (by norm_num : (2 : ℝ) ≤ 10)]
    dsimp [D10DyadicListCertificate.scaledSource]
    field_simp [hscale.ne', ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]
  rw [heq]
  calc
    D10DyadicListCertificate.scaledSource 10 /
        (10 * (D10DyadicListCertificate.scale : ℝ)) ≤
        1246160800517559 / (10 * (D10DyadicListCertificate.scale : ℝ)) :=
      div_le_div_of_nonneg_right h (by positivity)
    _ ≤ (668681894992131129186433 /
        5192296858534827628530496329220096 : ℝ) := by
      norm_num [D10DyadicListCertificate.scale]

end
end ImbalancedChen

/- SOURCEONLY parent: 20261022-original-third-tail-literal-ideal-rho-margin-SOURCEONLY.lean.txt; SHA256 0f690f04ff0879341d4d561c34e903b1eb5e1433d107cf74468f45a3bb9b7fc7 -/
/-!
SOURCEONLY / UNCOMPILED / HOLD.
The literal original analytic cap, not the rounded finite coarse policy.
Original binding: extended-prefix-upper.tex L12--20; main manuscript L364--366;
certify_extended_prefix.py phi_range L133--158 and tail_upper L374--388.
All original Phi gates and equality at x=mu stay in actualExtendedThirdIdealCap.
No assumption about an arbitrary selector, Gamma, cap, or free target bound.
-/

namespace ImbalancedChen.OriginalThirdIdealRhoMarginSourceOnly

noncomputable section
open VariableEnvelope

/-- The complete original cap retains its literal baseline. -/
theorem v_le_literal_ideal (x y z : ℝ) :
    v x ≤ actualExtendedThirdIdealCap x y z := by
  have hroot : v x ≤ thirdPrefixTheta := by
    exact (v_le_cap x).trans (by norm_num [VariableEnvelope.cap, thirdPrefixTheta])
  have henv := v_le_actualExtendedThirdEnvelope x y z
  unfold actualExtendedThirdIdealCap actualExtendedThirdBufferedCap thirdPrefixBufferedCap
  simp only [mul_zero, sub_zero]
  exact le_min hroot henv

/-- Exact rho geometry, including the original closed endpoints. -/
theorem literal_ideal_rho_geometry {x y z : ℝ}
    (hyx : y ≤ x) (hxrho : x ≤ thirdPrefixRho) :
    thirdPrefixRho ≤ actualExtendedThirdIdealCap x y z - x - y ∧
      actualExtendedThirdIdealCap x y z ≤ thirdPrefixTheta := by
  have hv : thirdPrefixRho + x + y ≤ v x := by
    rw [v_eq_min]
    apply le_min <;> dsimp [A, C, thirdPrefixRho] at * <;> linarith
  have hcap := v_le_literal_ideal x y z
  constructor
  · linarith
  · unfold actualExtendedThirdIdealCap actualExtendedThirdBufferedCap thirdPrefixBufferedCap
    simp only [mul_zero, sub_zero]
    exact min_le_left _ _

/-- Strict residual margin is available before the first-stop endpoint. -/
theorem literal_ideal_rho_margin_strict {x y z : ℝ}
    (hyx : y ≤ x) (hxrho : x < thirdPrefixRho) :
    thirdPrefixRho < actualExtendedThirdIdealCap x y z - x - y := by
  have hv : thirdPrefixRho + x + y < v x := by
    rw [v_eq_min]
    apply lt_min <;> dsimp [A, C, thirdPrefixRho] at * <;> linarith
  have hcap := v_le_literal_ideal x y z
  linarith

/-- The ideal point cap has the strict raw-cube margin at every x<rho. -/
theorem literal_ideal_gt_three_x {x y z : ℝ}
    (hxrho : x < thirdPrefixRho) :
    3 * x < actualExtendedThirdIdealCap x y z := by
  have hv : 3 * x < v x := by
    rw [v_eq_min]
    apply lt_min <;> dsimp [A, C, thirdPrefixRho] at * <;> linarith
  exact hv.trans_le (v_le_literal_ideal x y z)
/-- The original closed endpoint attains the baseline and the 3x wall. -/
theorem literal_ideal_at_rho (z : ℝ) :
    actualExtendedThirdIdealCap thirdPrefixRho thirdPrefixRho z =
      3 * thirdPrefixRho := by
  rw [actualExtendedThirdIdealCap_eq]
  norm_num [thirdPrefixRho, thirdPrefixTheta, VariableEnvelope.mu,
    v_eq_min, A, C]

/-- Thus neither >rho residual nor >3x holds on the entire closed domain. -/
theorem literal_ideal_closed_endpoint (z : ℝ) :
    actualExtendedThirdIdealCap thirdPrefixRho thirdPrefixRho z -
        thirdPrefixRho - thirdPrefixRho = thirdPrefixRho ∧
      ¬ 3 * thirdPrefixRho <
        actualExtendedThirdIdealCap thirdPrefixRho thirdPrefixRho z := by
  constructor
  · rw [literal_ideal_at_rho]
    ring
  · rw [literal_ideal_at_rho]
    exact lt_irrefl _

/-- Exact geometric supplier for the original h=1/100, s0=10 tail.
The stronger 451/24 bound licenses the anchor without a strict endpoint claim.
The optional z<=y part of the ordered domain is unnecessary for these bounds. -/
theorem literal_ideal_original_tail_geometry {x y z : ℝ}
    (hz : 0 < z) (hzh : z ≤ 1 / 100)
    (hyx : y ≤ x) (hxrho : x ≤ thirdPrefixRho) :
    (19 / 96 : ℝ) ≤ actualExtendedThirdIdealCap x y z - x - y ∧
      actualExtendedThirdIdealCap x y z ≤ thirdPrefixTheta ∧
      (451 / 2400 : ℝ) ≤ actualExtendedThirdIdealCap x y z - x - y - z ∧
      (451 / 24 : ℝ) ≤
        (actualExtendedThirdIdealCap x y z - x - y - z) / z ∧
      (10 : ℝ) ≤
        (actualExtendedThirdIdealCap x y z - x - y - z) / z := by
  obtain ⟨hm, hc⟩ := literal_ideal_rho_geometry (z := z) hyx hxrho
  dsimp only [thirdPrefixRho] at hm
  have hres : (451 / 2400 : ℝ) ≤
      actualExtendedThirdIdealCap x y z - x - y - z := by
    linarith
  have hs : (451 / 24 : ℝ) ≤
      (actualExtendedThirdIdealCap x y z - x - y - z) / z := by
    apply (le_div_iff₀ hz).mpr
    linarith
  exact ⟨hm, hc, hres, hs, by linarith⟩

end
end ImbalancedChen.OriginalThirdIdealRhoMarginSourceOnly

/- SOURCEONLY parent: 20261022-original-third-tail-ordered-half-pointwise-integral-bridge-SOURCEONLY.txt; SHA256 15bd8854edb08a33df552fb17a767eb25bad3914bffc96de01f4abee5b79412d -/
/-!
SOURCEONLY / UNCOMPILED / HOLD.
One missing interface: a pointwise bound for the SAME old/cap kernel gives
its complete ordered nonnegative tail integral, preserving the factor1/2.
The existing symmetric-triangle theorem and existing improper log-square
primitive are reused. No D10 value, selector margin, or final log certificate
is asserted. SymmetricTriangleIntegral is not owned in the196 census.
-/

namespace ImbalancedChen.OriginalThirdOrderedTailSourceOnly

noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- Specialize the existing symmetric-triangle identity, then convert the
    genuinely integrable positive profile to its nonnegative integral. -/
private theorem lintegral_ordered_reciprocal_triangle {c z rho : ℝ}
    (hc : 0 ≤ c) (hz : 0 < z) (hzrho : z ≤ rho) :
    (∫⁻ x in Ioc z rho, ∫⁻ y in Ioc z x,
      ENNReal.ofReal (c * (1 / x) * (1 / y))) =
      ENNReal.ofReal ((c / 2) * Real.log (rho / z) ^ 2) := by
  have hrho : 0 < rho := hz.trans_le hzrho
  have hInv : ContinuousOn (fun x : ℝ => 1 / x) (Icc z rho) :=
    continuousOn_const.div continuousOn_id (fun x hx => (hz.trans_le hx.1).ne')
  have hLog : ContinuousOn (fun x : ℝ => Real.log (x / z)) (Icc z rho) :=
    (continuousOn_id.div_const z).log
      (fun x hx => (div_pos (hz.trans_le hx.1) hz).ne')
  have hCont : ContinuousOn
      (fun x : ℝ => c * (1 / x) * Real.log (x / z)) (Icc z rho) :=
    (continuousOn_const.mul hInv).mul hLog
  have hint : IntegrableOn
      (fun x : ℝ => c * (1 / x) * Real.log (x / z)) (Ioc z rho) :=
    hCont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc z rho)]
      (fun x : ℝ => c * (1 / x) * Real.log (x / z)) := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
    exact ae_of_all _ (fun x hx =>
      mul_nonneg (mul_nonneg hc (one_div_nonneg.mpr (hz.trans hx.1).le))
        (Real.log_nonneg ((le_div_iff₀ hz).2 (by simpa using hx.1.le))))
  have hK : ContinuousOn
      (Function.uncurry (fun x y : ℝ => c * (1 / x) * (1 / y)))
      (Icc z rho ×ˢ Icc z rho) := by
    have hX : ContinuousOn (fun p : ℝ × ℝ => 1 / p.1)
        (Icc z rho ×ˢ Icc z rho) :=
      continuousOn_const.div continuousOn_fst
        (fun p hp => (hz.trans_le hp.1.1).ne')
    have hY : ContinuousOn (fun p : ℝ × ℝ => 1 / p.2)
        (Icc z rho ×ˢ Icc z rho) :=
      continuousOn_const.div continuousOn_snd
        (fun p hp => (hz.trans_le hp.2.1).ne')
    exact (continuousOn_const.mul hX).mul hY
  have hhalf := SymmetricTriangleIntegral.half_square_eq_triangle
    (K := fun x y : ℝ => c * (1 / x) * (1 / y)) hzrho hK
    (by intro x _ y _; ring)
  have hsquare :
      (∫ x in z..rho, ∫ y in z..rho, c * (1 / x) * (1 / y)) =
        c * Real.log (rho / z) ^ 2 := by
    simp only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, integral_one_div_of_pos hz hrho]
    ring
  have hReduced :
      (∫ x in z..rho, c * (1 / x) * Real.log (x / z)) =
        ∫ x in z..rho, ∫ y in z..x, c * (1 / x) * (1 / y) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hzrho] at hx
    change c * (1 / x) * Real.log (x / z) =
      ∫ y in z..x, c * (1 / x) * (1 / y)
    rw [intervalIntegral.integral_const_mul,
      integral_one_div_of_pos hz (hz.trans_le hx.1)]
  have hReal :
      (∫ x in z..rho, c * (1 / x) * Real.log (x / z)) =
        (c / 2) * Real.log (rho / z) ^ 2 := by
    rw [hReduced, ← hhalf, hsquare]
    ring
  calc
    _ = ∫⁻ x in Ioc z rho,
        ENNReal.ofReal (c * (1 / x) * Real.log (x / z)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact thirdTail_lintegral_const_mul_one_div
        (mul_nonneg hc (one_div_nonneg.mpr (hz.trans hx.1).le)) hz hx.1.le
    _ = ENNReal.ofReal
        (∫ x in Ioc z rho, c * (1 / x) * Real.log (x / z)) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = _ := by rw [← intervalIntegral.integral_of_le hzrho, hReal]

/-- The complete improper threefold majorant on the ORDERED xy triangle.
    The coefficient is c/2, never c from a square enlargement. -/
private theorem lintegral_ordered_majorant {c rho h : ℝ}
    (hc : 0 ≤ c) (hrho : 0 < rho) (hh : 0 < h) (hhrho : h ≤ rho) :
    (∫⁻ z in Ioc 0 h, ∫⁻ x in Ioc z rho, ∫⁻ y in Ioc z x,
      ENNReal.ofReal (c * (1 / x) * (1 / y))) =
      ENNReal.ofReal ((c / 2) * thirdTailLogPrimitive rho h) := by
  have hhalf : 0 ≤ c / 2 := div_nonneg hc (by norm_num)
  calc
    _ = ∫⁻ z in Ioc 0 h,
        ENNReal.ofReal ((c / 2) * Real.log (rho / z) ^ 2) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro z hz
      exact lintegral_ordered_reciprocal_triangle hc hz.1 (hz.2.trans hhrho)
    _ = ENNReal.ofReal (c / 2) *
        ∫⁻ z in Ioc 0 h, ENNReal.ofReal (Real.log (rho / z) ^ 2) := by
      simp_rw [ENNReal.ofReal_mul hhalf]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      rw [thirdTail_lintegral_logSq hrho hh, ENNReal.ofReal_mul hhalf]

/-- One missing application bridge, with the pointwise supplier EXPLICIT.
    old and cap are the original functions, unchanged. For the manuscript
    use old=thirdPrefixTheta and cap=actualExtendedThirdIdealCap.
    This corrects the application comment withdrawn by the literal-ideal
    rho addendum SHA8170bd71a51f5402460a5bfe149c1c64f62943776ce67a62529775a127b3a46c;
    the generic theorem and all proof text are unchanged. The old 15bd8854
    file itself is preserved; its former currentExtendedThirdCap/select
    application suggestion does not bind this numerical tail.
    All0<z<=1/100 and z<y<=x<=rho are integrated, including arbitrarily smallz.
    The original strict own-cube gate is kept inside thirdPrefixTailMass. -/
theorem originalNumericalTailMass_le_of_pointwise
    (old : ℝ) (cap : ℝ → ℝ → ℝ → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hpoint : ∀ x y z : ℝ, 0 < z → z ≤ 1 / 100 → z ≤ y →
      y ≤ x → x ≤ thirdPrefixRho →
      thirdPrefixCorrectionKernel old (cap x y z) x y z ≤
        (400 * d / (thirdPrefixRho - 1 / 100) ^ 2) * (1 / x) * (1 / y)) :
    thirdPrefixTailMass old cap thirdPrefixRho (1 / 100) ≤
      ENNReal.ofReal
        ((2 * d * 100 * (1 / 100) / ((19 / 96 : ℝ) - 1 / 100) ^ 2) *
          (Real.log (475 / 24 : ℝ) ^ 2 + 2 * Real.log (475 / 24 : ℝ) + 2)) := by
  have hc : 0 ≤ 400 * d / (thirdPrefixRho - 1 / 100) ^ 2 := by positivity
  calc
    _ ≤ ∫⁻ z in Ioc (0 : ℝ) (1 / 100),
        ∫⁻ x in Ioc z thirdPrefixRho, ∫⁻ y in Ioc z x,
          ENNReal.ofReal
            ((400 * d / (thirdPrefixRho - 1 / 100) ^ 2) * (1 / x) * (1 / y)) := by
      unfold thirdPrefixTailMass
      apply setLIntegral_mono' measurableSet_Ioc
      intro z hz
      apply setLIntegral_mono' measurableSet_Ioc
      intro x hx
      apply setLIntegral_mono' measurableSet_Ioc
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      split_ifs
      · exact hpoint x y z hz.1 hz.2 hy.1.le hy.2 hx.2
      · exact mul_nonneg
          (mul_nonneg hc (one_div_nonneg.mpr (hz.1.trans hx.1).le))
          (one_div_nonneg.mpr (hz.1.trans hy.1).le)
    _ = ENNReal.ofReal
        (((400 * d / (thirdPrefixRho - 1 / 100) ^ 2) / 2) *
          thirdTailLogPrimitive thirdPrefixRho (1 / 100)) :=
      lintegral_ordered_majorant hc (by norm_num [thirdPrefixRho])
        (by norm_num) (by norm_num [thirdPrefixRho])
    _ = _ := by
      congr 1
      norm_num [thirdTailLogPrimitive, thirdPrefixRho]
      ring

end
end ImbalancedChen.OriginalThirdOrderedTailSourceOnly

/- SOURCEONLY parent: 20261022-original-third-tail-rational-log-Tnew-final-scalar-SOURCEONLY.txt; SHA256 18f47a4b7668b2994c4bfca84e054a2ff0c898687069d31c255720299ff2b3b4 -/
/-!
SOURCEONLY / UNCOMPILED / HOLD.
Exact numerical last step of the original ORDERED third-prefix tail.
The independent numerical input is 668681894992131129186433 / 2^112.
This file does not prove that it bounds the actual normalized sieve gap.
It preserves the ordered-domain half, rho=19/96,h=1/100 and Tnew/2^111.
No exp(gamma) factor belongs in this already normalized numerical expression.
No selector margin, integral identity, D10 semantics or kernel receipt is claimed.
-/

namespace ImbalancedChen.OriginalThirdTailNumericalScalarSourceOnly

open ImbalancedChen.Certificates

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Actual-log certificate with the exact Mathlib remainder used by check_sound. -/
def logTwoCertificate : RationalLogCertificate where
  argument := 2
  terms := 40
  lower := 3599025928123676973540407451845618 / 2^112
  upper := 3599025928123676973540407451845619 / 2^112

/-- 475/24 = 2^4*(475/384); the second argument is close to one. -/
def logResidualCertificate : RationalLogCertificate where
  argument := 475 / 384
  terms := 20
  lower := 1104257463085342339033427219398629 / 2^112
  upper := 1104257463085342339033427219398630 / 2^112

theorem logTwoCertificate_checked : logTwoCertificate.check = true := by
  norm_num [logTwoCertificate, RationalLogCertificate.check,
    RationalLogCertificate.Valid, logSeriesLower, logSeriesUpper,
    logParameter, Finset.sum_range_succ]

theorem logResidualCertificate_checked : logResidualCertificate.check = true := by
  norm_num [logResidualCertificate, RationalLogCertificate.check,
    RationalLogCertificate.Valid, logSeriesLower, logSeriesUpper,
    logParameter, Finset.sum_range_succ]

/-- A proved enclosure of the ACTUAL logarithm; no logarithm bound is a premise. -/
theorem real_log_475_24_enclosure :
    (15500361175580050233195057026781101 / 2^112 : ℝ) ≤
        Real.log (475 / 24 : ℝ) ∧
      Real.log (475 / 24 : ℝ) ≤
        (15500361175580050233195057026781106 / 2^112 : ℝ) := by
  have hTwo := RationalLogCertificate.check_sound
    logTwoCertificate logTwoCertificate_checked
  have hResidual := RationalLogCertificate.check_sound
    logResidualCertificate logResidualCertificate_checked
  norm_num [logTwoCertificate, logResidualCertificate] at hTwo hResidual
  have hSplit : Real.log (475 / 24 : ℝ) =
      4 * Real.log (2 : ℝ) + Real.log (475 / 384 : ℝ) := by
    calc
      Real.log (475 / 24 : ℝ) =
          Real.log (((2 : ℝ)^4) * (475 / 384 : ℝ)) := by
        congr 1
        norm_num
      _ = 4 * Real.log (2 : ℝ) + Real.log (475 / 384 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
        norm_num
  constructor
  · rw [hSplit]
    linarith [hTwo.1, hResidual.1]
  · rw [hSplit]
    linarith [hTwo.2, hResidual.2]

/-- Literal original ordered-tail scalar <= the literal original Tnew.
The numerical D10 input is explicit; no target or free-log hypothesis occurs. -/
theorem original_ordered_tail_log_scalar_le_Tnew :
    (2 * (668681894992131129186433 / 2^112 : ℝ) * 100 * (1 / 100) /
      ((19 / 96 : ℝ) - 1 / 100)^2) *
        (Real.log (475 / 24 : ℝ)^2 +
          2 * Real.log (475 / 24 : ℝ) + 2) ≤
      (319683857488126290909150567 / 2^111 : ℝ) := by
  let U : ℝ := 15500361175580050233195057026781106 / 2^112
  have hLogUpper : Real.log (475 / 24 : ℝ) ≤ U := by
    simpa only [U] using real_log_475_24_enclosure.2
  have hLogNonneg : 0 ≤ Real.log (475 / 24 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hUNonneg : 0 ≤ U := by norm_num [U]
  have hSq : Real.log (475 / 24 : ℝ)^2 ≤ U^2 :=
    (sq_le_sq₀ hLogNonneg hUNonneg).2 hLogUpper
  have hPoly : Real.log (475 / 24 : ℝ)^2 +
      2 * Real.log (475 / 24 : ℝ) + 2 ≤ U^2 + 2 * U + 2 := by
    linarith [hSq, hLogUpper]
  have hCoeff : 0 ≤
      2 * (668681894992131129186433 / 2^112 : ℝ) * 100 * (1 / 100) /
        ((19 / 96 : ℝ) - 1 / 100)^2 := by norm_num
  calc
    _ ≤ (2 * (668681894992131129186433 / 2^112 : ℝ) * 100 * (1 / 100) /
          ((19 / 96 : ℝ) - 1 / 100)^2) * (U^2 + 2 * U + 2) :=
      mul_le_mul_of_nonneg_left hPoly hCoeff
    _ ≤ _ := by norm_num [U]

end ImbalancedChen.OriginalThirdTailNumericalScalarSourceOnly

/- SOURCEONLY parent: 20261022-original-third-tail-actual-ideal-Tnew-assembly-SOURCEONLY.txt; SHA256 16148cdb2e231936a1d285845448b254868a508004d4ba67b7d8ab6806002a0b -/
-- The complete bundle inserts the D10 List V2, literal ideal rho-margin,
-- ordered-half bridge and actual-log scalar declarations before this section.

namespace ImbalancedChen.OriginalThirdTailActualIdealSourceOnly

noncomputable section
open Set MeasureTheory
open scoped ENNReal

def d10 : ℝ := 668681894992131129186433 / 2^112
def Tnew : ℝ := 319683857488126290909150567 / 2^111

theorem actual_d10_le :
    actualSieveGap (10 : ℝ) / (2 * Real.exp Real.eulerMascheroniConstant) ≤ d10 := by
  convert actualSieveGap_normalized_at_ten_upper_dyadic_list using 1; norm_num [d10]

/-- Concrete canonical kernel bound, on all closed ordered tail points.
No pointwise, numerical-function, selector, or integral bound is a premise. -/
theorem ideal_kernel_bound {x y z : ℝ}
    (hz : 0 < z) (hzh : z ≤ 1 / 100) (hzy : z ≤ y)
    (hyx : y ≤ x) (hxrho : x ≤ thirdPrefixRho) :
    0 ≤ thirdPrefixCorrectionKernel thirdPrefixTheta
        (actualExtendedThirdIdealCap x y z) x y z ∧
      thirdPrefixCorrectionKernel thirdPrefixTheta
        (actualExtendedThirdIdealCap x y z) x y z ≤
        (400 * d10 / (thirdPrefixRho - 1 / 100)^2) * (1 / x) * (1 / y) := by
  have hx : 0 < x := hz.trans_le (hzy.trans hyx)
  have hy : 0 < y := hz.trans_le hzy
  have hgeom := OriginalThirdIdealRhoMarginSourceOnly.literal_ideal_original_tail_geometry
    hz hzh hyx hxrho
  have hs := hgeom.2.2.2.2
  have hlevels := hgeom.2.1
  have hst : (actualExtendedThirdIdealCap x y z - x - y - z) / z ≤
      (thirdPrefixTheta - x - y - z) / z :=
    (div_le_div_iff_of_pos_right hz).mpr (by linarith)
  have hdiff := thirdTailLowerFactor_difference
    (by linarith : (2 : ℝ) ≤ (actualExtendedThirdIdealCap x y z - x - y - z) / z) hst
  have hdecay := actualSieveGap_normalized_le_quadratic_tail
    (s0 := (10 : ℝ)) (by norm_num) hs
  have hgap : actualSieveGap ((actualExtendedThirdIdealCap x y z - x - y - z) / z) /
      (2 * Real.exp Real.eulerMascheroniConstant) ≤
      d10 * (10 / ((actualExtendedThirdIdealCap x y z - x - y - z) / z))^2 :=
    hdecay.trans (mul_le_mul_of_nonneg_right actual_d10_le (sq_nonneg _))
  have hd : 0 ≤ d10 := by norm_num [d10]
  have hmargin : thirdPrefixRho ≤ actualExtendedThirdIdealCap x y z - x - y := by
    simpa only [thirdPrefixRho] using hgeom.1
  have hres : thirdPrefixRho - 1 / 100 ≤ actualExtendedThirdIdealCap x y z - x - y - z := by
    linarith
  have hlow : 0 < thirdPrefixRho - 1 / 100 := by norm_num [thirdPrefixRho]
  have hrespos : 0 < actualExtendedThirdIdealCap x y z - x - y - z := hlow.trans_le hres
  have hden : 0 < x * y * z^2 := by positivity
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hdiff.1) hden.le
  · unfold thirdPrefixCorrectionKernel
    calc
      _ ≤ 4 * (d10 * (10 /
          ((actualExtendedThirdIdealCap x y z - x - y - z) / z))^2) /
            (x * y * z^2) :=
        (div_le_div_iff_of_pos_right hden).mpr
          (mul_le_mul_of_nonneg_left (hdiff.2.trans hgap) (by norm_num))
      _ = 400 * d10 / (x * y * (actualExtendedThirdIdealCap x y z - x - y - z)^2) := by
        field_simp [hx.ne', hy.ne', hz.ne', hrespos.ne']; ring
      _ ≤ 400 * d10 / (x * y * (thirdPrefixRho - 1 / 100)^2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
      _ = (400 * d10 / (thirdPrefixRho - 1 / 100)^2) * (1 / x) * (1 / y) := by
        field_simp [hx.ne', hy.ne', hlow.ne']

/-- The strict old own-cube gate is open on this entire small-z tail.
In particular no closed endpoint requires a false strict rho residual. -/
theorem ideal_old_cube_gate {x y z : ℝ}
    (hz : 0 < z) (hzh : z ≤ 1 / 100) (hyx : y ≤ x)
    (hxrho : x ≤ thirdPrefixRho) : x + y + 3 * z < thirdPrefixTheta := by
  have hg := OriginalThirdIdealRhoMarginSourceOnly.literal_ideal_rho_geometry
    (z := z) hyx hxrho
  have hm : (19 / 96 : ℝ) ≤ actualExtendedThirdIdealCap x y z - x - y := hg.1
  linarith [hg.2]

/-- Original complete ordered nonnegative mass <= the literal original Tnew.
The c/2 identity supplies the ordered factor; no square enlargement is used. -/
theorem ideal_tailMass_le_Tnew :
    actualExtendedThirdIdealTailMass 0 (1 / 100) ≤ ENNReal.ofReal Tnew := by
  have hmass := OriginalThirdOrderedTailSourceOnly.originalNumericalTailMass_le_of_pointwise
    thirdPrefixTheta actualExtendedThirdIdealCap d10 (by norm_num [d10])
    (by
      intro x y z hz hzh hzy hyx hxrho
      exact (ideal_kernel_bound hz hzh hzy hyx hxrho).2)
  have hscalar :
      (2 * d10 * 100 * (1 / 100) / ((19 / 96 : ℝ) - 1 / 100)^2) *
        (Real.log (475 / 24 : ℝ)^2 + 2 * Real.log (475 / 24 : ℝ) + 2) ≤ Tnew := by
    simpa only [d10, Tnew] using
      OriginalThirdTailNumericalScalarSourceOnly.original_ordered_tail_log_scalar_le_Tnew
  have hbound := hmass.trans (ENNReal.ofReal_le_ofReal hscalar)
  have hcap : actualExtendedThirdIdealCap = actualExtendedThirdBufferedCap 0 := by
    funext x y z
    rfl
  rw [hcap] at hbound
  simpa only [actualExtendedThirdIdealTailMass, mul_zero, sub_zero] using hbound

theorem ideal_tailMass_ne_top : actualExtendedThirdIdealTailMass 0 (1 / 100) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top ideal_tailMass_le_Tnew

theorem ordered_tailMass_le_Tnew :
    actualExtendedThirdOrderedTailMass 0 (1 / 100) ≤ ENNReal.ofReal Tnew := by
  rw [actualExtendedThirdOrderedTailMass_eq_core
    (by norm_num : (0 : ℝ) ≤ 1 / 384)
    (by norm_num [thirdPrefixTailMargin] : (1 / 100 : ℝ) ≤ thirdPrefixTailMargin / 4)]
  exact ideal_tailMass_le_Tnew

/-- Genuine Bochner integrability is supplied by the existing actual
measurability/positive-mass theorem, not by a numerical integral hypothesis. -/
theorem original_manuscript_tail_integrable :
    IntegrableOn (fun t : Fin 3 → ℝ => actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2))
      (actualExtendedThirdManuscriptTailRegion 0 (1 / 100)) := by
  exact integrableOn_actualExtendedThirdManuscriptKernel
    (by norm_num : (0 : ℝ) ≤ 1 / 384) (by norm_num)
    (by norm_num [thirdPrefixTailMargin] : (1 / 100 : ℝ) ≤ thirdPrefixTailMargin / 4)

theorem ideal_tail_toReal_le_Tnew :
    (actualExtendedThirdIdealTailMass 0 (1 / 100)).toReal ≤ Tnew := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top ideal_tailMass_le_Tnew
  have hT : 0 ≤ Tnew := by norm_num [Tnew]
  simpa only [ENNReal.toReal_ofReal hT] using h

/-- The actual original closed manuscript integral: ideal cap, actual lower
factor, actual ordering walls and old-cube face. Every supplier is proved
above or reused from the explicit actual source; no final integral premise. -/
theorem original_manuscript_tail_integral_le_Tnew :
    (∫ t in actualExtendedThirdManuscriptTailRegion 0 (1 / 100),
      actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)) ≤
        (319683857488126290909150567 / 2^111 : ℝ) := by
  rw [integral_actualExtendedThirdManuscriptKernel_eq_core
    (by norm_num : (0 : ℝ) ≤ 1 / 384)
    (by norm_num [thirdPrefixTailMargin] : (1 / 100 : ℝ) ≤ thirdPrefixTailMargin / 4)]
  exact ideal_tail_toReal_le_Tnew

/-- Equivalent canonical finite real tail. Its NN mass was bounded first. -/
theorem original_canonical_tail_le_Tnew :
    thirdPrefixTail thirdPrefixTheta actualExtendedThirdIdealCap thirdPrefixRho (1 / 100) ≤
      (319683857488126290909150567 / 2^111 : ℝ) := by
  have hcap : actualExtendedThirdIdealCap = actualExtendedThirdBufferedCap 0 := by
    funext x y z
    rfl
  simpa only [thirdPrefixTail, hcap, actualExtendedThirdIdealTailMass,
    Tnew, mul_zero, sub_zero] using ideal_tail_toReal_le_Tnew

end
end ImbalancedChen.OriginalThirdTailActualIdealSourceOnly
