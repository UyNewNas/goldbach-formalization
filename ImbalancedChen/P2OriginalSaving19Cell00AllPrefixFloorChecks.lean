import ImbalancedChen.P2OriginalSaving19Cell00Row000PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row001PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row002PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row003PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row004PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row005PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row006PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row007PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row008PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row009PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row010PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row011PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row012PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row013PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row014PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row015PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row016PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row017PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row018PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row019PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row020PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row021PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row022PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row023PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row024PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row025PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row026PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row027PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row028PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row029PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row030PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row031PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row032PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row033PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row034PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row035PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row036PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row037PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row038PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row039PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row040PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row041PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row042PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row043PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row044PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row045PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row046PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row047PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row048PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row049PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row050PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row051PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row052PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row053PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row054PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19Cell00Row055PrefixFloorChecks

/-! Finite assembly of every cell00 row's exact degree-six prefix and floor
certificates. No original row or factor is omitted. The five original floor
clauses and both Q80 bounds are retained. All concrete row certificates are
reused; the connection to rationalMoment remains a separate semantic owner. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00AllPrefixFloorChecks

set_option maxRecDepth 1000000
set_option Elab.async false

open scoped BigOperators
open P2OriginalSaving19Archive
open P2OriginalSaving19Geometry00Decoding
open P2OriginalSaving19Geometry00BoundedAccess
open P2OriginalSaving19Moment00Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

def prefixMoments : Fin 56 → Fin 10 → Nat → ℚ :=
  ![P2OriginalSaving19Cell00Row000MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row001MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row002MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row003MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row004MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row005MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row006MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row007MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row008MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row009MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row010MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row011MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row012MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row013MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row014MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row015MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row016MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row017MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row018MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row019MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row020MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row021MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row022MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row023MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row024MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row025MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row026MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row027MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row028MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row029MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row030MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row031MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row032MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row033MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row034MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row035MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row036MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row037MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row038MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row039MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row040MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row041MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row042MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row043MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row044MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row045MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row046MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row047MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row048MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row049MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row050MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row051MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row052MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row053MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row054MomentFloor.prefixMoment,
    P2OriginalSaving19Cell00Row055MomentFloor.prefixMoment]

def gapScales : Fin 56 → Nat :=
  ![P2OriginalSaving19Cell00Row000MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row001MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row002MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row003MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row004MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row005MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row006MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row007MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row008MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row009MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row010MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row011MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row012MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row013MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row014MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row015MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row016MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row017MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row018MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row019MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row020MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row021MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row022MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row023MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row024MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row025MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row026MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row027MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row028MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row029MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row030MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row031MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row032MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row033MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row034MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row035MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row036MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row037MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row038MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row039MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row040MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row041MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row042MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row043MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row044MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row045MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row046MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row047MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row048MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row049MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row050MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row051MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row052MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row053MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row054MomentFloor.gapScale,
    P2OriginalSaving19Cell00Row055MomentFloor.gapScale]

def gapNumerators : Fin 56 → Fin 9 → Nat :=
  ![P2OriginalSaving19Cell00Row000MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row001MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row002MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row003MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row004MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row005MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row006MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row007MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row008MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row009MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row010MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row011MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row012MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row013MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row014MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row015MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row016MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row017MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row018MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row019MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row020MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row021MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row022MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row023MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row024MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row025MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row026MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row027MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row028MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row029MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row030MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row031MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row032MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row033MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row034MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row035MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row036MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row037MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row038MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row039MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row040MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row041MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row042MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row043MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row044MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row045MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row046MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row047MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row048MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row049MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row050MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row051MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row052MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row053MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row054MomentFloor.gapNats,
    P2OriginalSaving19Cell00Row055MomentFloor.gapNats]

def deviationDenominators : Fin 56 → Fin 10 → Nat :=
  ![P2OriginalSaving19Cell00Row000MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row001MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row002MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row003MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row004MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row005MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row006MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row007MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row008MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row009MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row010MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row011MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row012MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row013MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row014MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row015MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row016MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row017MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row018MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row019MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row020MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row021MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row022MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row023MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row024MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row025MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row026MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row027MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row028MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row029MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row030MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row031MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row032MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row033MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row034MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row035MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row036MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row037MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row038MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row039MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row040MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row041MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row042MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row043MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row044MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row045MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row046MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row047MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row048MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row049MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row050MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row051MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row052MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row053MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row054MomentFloor.deviationDenominators,
    P2OriginalSaving19Cell00Row055MomentFloor.deviationDenominators]

def deviationNumerators : Fin 56 → Fin 10 → Fin 9 → Nat :=
  ![P2OriginalSaving19Cell00Row000MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row001MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row002MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row003MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row004MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row005MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row006MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row007MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row008MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row009MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row010MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row011MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row012MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row013MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row014MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row015MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row016MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row017MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row018MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row019MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row020MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row021MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row022MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row023MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row024MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row025MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row026MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row027MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row028MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row029MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row030MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row031MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row032MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row033MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row034MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row035MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row036MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row037MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row038MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row039MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row040MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row041MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row042MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row043MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row044MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row045MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row046MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row047MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row048MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row049MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row050MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row051MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row052MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row053MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row054MomentFloor.deviationNats,
    P2OriginalSaving19Cell00Row055MomentFloor.deviationNats]

theorem prefixMoments_eq_normalized (r : Fin 56) (j : Fin 10) (k : Nat) :
    prefixMoments r j k = normalizedMoment (gapNumerators r)
      (deviationNumerators r j) (deviationDenominators r j) k := by
  fin_cases r <;> rfl

theorem all_gapScales_ne (r : Fin 56) : gapScales r ≠ 0 := by
  fin_cases r
  · exact P2OriginalSaving19Cell00Row000MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row001MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row002MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row003MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row004MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row005MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row006MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row007MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row008MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row009MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row010MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row011MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row012MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row013MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row014MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row015MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row016MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row017MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row018MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row019MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row020MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row021MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row022MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row023MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row024MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row025MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row026MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row027MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row028MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row029MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row030MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row031MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row032MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row033MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row034MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row035MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row036MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row037MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row038MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row039MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row040MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row041MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row042MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row043MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row044MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row045MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row046MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row047MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row048MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row049MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row050MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row051MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row052MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row053MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row054MomentFloor.gapScale_ne
  · exact P2OriginalSaving19Cell00Row055MomentFloor.gapScale_ne

theorem all_deviationDenominators_ne (r : Fin 56) (j : Fin 10) :
    deviationDenominators r j ≠ 0 := by
  fin_cases r
  · exact P2OriginalSaving19Cell00Row000MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row001MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row002MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row003MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row004MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row005MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row006MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row007MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row008MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row009MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row010MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row011MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row012MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row013MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row014MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row015MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row016MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row017MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row018MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row019MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row020MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row021MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row022MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row023MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row024MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row025MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row026MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row027MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row028MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row029MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row030MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row031MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row032MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row033MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row034MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row035MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row036MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row037MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row038MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row039MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row040MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row041MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row042MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row043MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row044MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row045MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row046MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row047MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row048MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row049MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row050MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row051MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row052MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row053MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row054MomentFloor.deviationDenominators_ne j
  · exact P2OriginalSaving19Cell00Row055MomentFloor.deviationDenominators_ne j

theorem all_gap_encoding (r : Fin 56) : ∀ i : Fin 9,
    gapQ (boundedRowVertex r i) = (gapNumerators r i : ℚ) / (gapScales r : ℚ) := by
  intro i
  fin_cases r
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row000.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row000MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row001.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row001MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row002.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row002MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row003.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row003MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row004.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row004MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row005.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row005MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row006.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row006MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row007.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row007MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row008.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row008MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row009.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row009MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row010.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row010MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row011.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row011MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row012.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row012MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row013.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row013MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row014.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row014MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row015.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row015MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row016.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row016MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row017.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row017MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row018.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row018MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row019.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row019MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row020.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row020MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row021.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row021MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row022.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row022MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row023.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row023MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row024.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row024MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row025.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row025MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row026.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row026MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row027.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row027MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row028.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row028MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row029.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row029MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row030.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row030MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row031.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row031MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row032.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row032MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row033.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row033MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row034.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row034MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row035.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row035MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row036.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row036MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row037.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row037MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row038.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row038MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row039.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row039MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row040.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row040MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row041.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row041MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row042.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row042MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row043.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row043MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row044.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row044MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row045.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row045MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row046.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row046MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row047.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row047MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row048.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row048MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row049.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row049MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row050.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row050MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row051.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row051MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row052.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row052MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row053.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row053MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row054.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row054MomentFloor.gap_encoding i)
  · exact (congrArg gapQ (congrFun P2OriginalSaving19Cell00Row055.boundedRowVertex_eq i)).trans
      (P2OriginalSaving19Cell00Row055MomentFloor.gap_encoding i)

theorem all_deviation_encoding (r : Fin 56) : ∀ (j : Fin 10) (i : Fin 9),
    1 - factorsQ (boundedRowVertex r i) j / topsOf (boundedRow r) j =
      (deviationNumerators r j i : ℚ) / (deviationDenominators r j : ℚ) := by
  intro j i
  fin_cases r
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row000.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row000.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row000MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row001.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row001.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row001MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row002.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row002.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row002MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row003.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row003.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row003MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row004.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row004.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row004MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row005.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row005.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row005MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row006.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row006.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row006MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row007.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row007.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row007MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row008.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row008.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row008MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row009.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row009.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row009MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row010.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row010.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row010MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row011.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row011.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row011MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row012.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row012.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row012MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row013.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row013.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row013MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row014.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row014.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row014MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row015.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row015.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row015MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row016.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row016.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row016MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row017.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row017.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row017MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row018.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row018.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row018MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row019.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row019.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row019MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row020.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row020.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row020MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row021.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row021.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row021MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row022.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row022.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row022MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row023.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row023.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row023MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row024.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row024.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row024MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row025.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row025.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row025MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row026.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row026.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row026MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row027.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row027.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row027MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row028.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row028.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row028MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row029.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row029.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row029MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row030.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row030.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row030MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row031.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row031.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row031MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row032.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row032.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row032MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row033.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row033.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row033MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row034.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row034.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row034MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row035.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row035.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row035MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row036.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row036.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row036MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row037.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row037.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row037MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row038.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row038.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row038MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row039.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row039.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row039MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row040.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row040.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row040MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row041.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row041.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row041MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row042.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row042.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row042MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row043.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row043.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row043MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row044.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row044.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row044MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row045.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row045.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row045MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row046.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row046.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row046MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row047.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row047.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row047MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row048.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row048.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row048MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row049.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row049.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row049MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row050.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row050.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row050MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row051.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row051.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row051MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row052.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row052.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row052MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row053.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row053.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row053MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row054.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row054.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row054MomentFloor.deviation_encoding j i)
  · exact (congrArg₂ (fun vertex row => 1 - factorsQ vertex j / topsOf row j)
      (congrFun P2OriginalSaving19Cell00Row055.boundedRowVertex_eq i) P2OriginalSaving19Cell00Row055.boundedRow_eq).trans
      (P2OriginalSaving19Cell00Row055MomentFloor.deviation_encoding j i)

def PrefixFloorChecksFor (row : GeometryRow) (momentRow : MomentRecord)
    (moments : Fin 10 → Nat → ℚ) : Prop :=
  (∀ j : Fin 10, moments j 1 = 1 - meansOf row j / topsOf row j) ∧
  (∀ j : Fin 10, momentRow.factorFloorsQ80[j.val]! = factorFloorQ80 (moments j)) ∧
  momentRow.oldFloorQ96 = row.jensenFloorQ96 ∧
  momentRow.oldFloorQ96 = oldFloorQ96 (massOf row) (meansOf row) ∧
  momentRow.newFloorQ96 =
    max (oldFloorQ96 (massOf row) (meansOf row))
      (newFloorQ96 (massOf row) (meansOf row) moments)

theorem all_bounded_prefix_floor_checks (r : Fin 56) :
    PrefixFloorChecksFor (boundedRow r) (momentConcrete00.rows[r.val]!)
      (prefixMoments r) := by
  fin_cases r
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row000MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row000.boundedRow_eq P2OriginalSaving19Cell00Row000.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row000MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row001MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row001.boundedRow_eq P2OriginalSaving19Cell00Row001.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row001MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row002MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row002.boundedRow_eq P2OriginalSaving19Cell00Row002.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row002MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row003MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row003.boundedRow_eq P2OriginalSaving19Cell00Row003.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row003MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row004MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row004.boundedRow_eq P2OriginalSaving19Cell00Row004.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row004MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row005MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row005.boundedRow_eq P2OriginalSaving19Cell00Row005.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row005MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row006MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row006.boundedRow_eq P2OriginalSaving19Cell00Row006.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row006MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row007MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row007.boundedRow_eq P2OriginalSaving19Cell00Row007.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row007MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row008MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row008.boundedRow_eq P2OriginalSaving19Cell00Row008.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row008MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row009MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row009.boundedRow_eq P2OriginalSaving19Cell00Row009.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row009MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row010MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row010.boundedRow_eq P2OriginalSaving19Cell00Row010.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row010MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row011MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row011.boundedRow_eq P2OriginalSaving19Cell00Row011.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row011MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row012MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row012.boundedRow_eq P2OriginalSaving19Cell00Row012.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row012MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row013MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row013.boundedRow_eq P2OriginalSaving19Cell00Row013.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row013MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row014MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row014.boundedRow_eq P2OriginalSaving19Cell00Row014.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row014MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row015MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row015.boundedRow_eq P2OriginalSaving19Cell00Row015.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row015MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row016MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row016.boundedRow_eq P2OriginalSaving19Cell00Row016.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row016MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row017MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row017.boundedRow_eq P2OriginalSaving19Cell00Row017.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row017MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row018MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row018.boundedRow_eq P2OriginalSaving19Cell00Row018.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row018MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row019MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row019.boundedRow_eq P2OriginalSaving19Cell00Row019.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row019MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row020MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row020.boundedRow_eq P2OriginalSaving19Cell00Row020.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row020MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row021MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row021.boundedRow_eq P2OriginalSaving19Cell00Row021.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row021MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row022MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row022.boundedRow_eq P2OriginalSaving19Cell00Row022.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row022MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row023MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row023.boundedRow_eq P2OriginalSaving19Cell00Row023.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row023MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row024MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row024.boundedRow_eq P2OriginalSaving19Cell00Row024.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row024MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row025MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row025.boundedRow_eq P2OriginalSaving19Cell00Row025.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row025MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row026MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row026.boundedRow_eq P2OriginalSaving19Cell00Row026.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row026MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row027MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row027.boundedRow_eq P2OriginalSaving19Cell00Row027.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row027MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row028MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row028.boundedRow_eq P2OriginalSaving19Cell00Row028.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row028MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row029MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row029.boundedRow_eq P2OriginalSaving19Cell00Row029.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row029MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row030MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row030.boundedRow_eq P2OriginalSaving19Cell00Row030.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row030MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row031MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row031.boundedRow_eq P2OriginalSaving19Cell00Row031.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row031MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row032MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row032.boundedRow_eq P2OriginalSaving19Cell00Row032.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row032MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row033MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row033.boundedRow_eq P2OriginalSaving19Cell00Row033.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row033MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row034MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row034.boundedRow_eq P2OriginalSaving19Cell00Row034.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row034MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row035MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row035.boundedRow_eq P2OriginalSaving19Cell00Row035.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row035MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row036MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row036.boundedRow_eq P2OriginalSaving19Cell00Row036.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row036MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row037MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row037.boundedRow_eq P2OriginalSaving19Cell00Row037.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row037MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row038MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row038.boundedRow_eq P2OriginalSaving19Cell00Row038.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row038MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row039MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row039.boundedRow_eq P2OriginalSaving19Cell00Row039.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row039MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row040MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row040.boundedRow_eq P2OriginalSaving19Cell00Row040.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row040MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row041MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row041.boundedRow_eq P2OriginalSaving19Cell00Row041.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row041MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row042MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row042.boundedRow_eq P2OriginalSaving19Cell00Row042.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row042MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row043MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row043.boundedRow_eq P2OriginalSaving19Cell00Row043.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row043MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row044MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row044.boundedRow_eq P2OriginalSaving19Cell00Row044.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row044MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row045MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row045.boundedRow_eq P2OriginalSaving19Cell00Row045.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row045MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row046MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row046.boundedRow_eq P2OriginalSaving19Cell00Row046.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row046MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row047MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row047.boundedRow_eq P2OriginalSaving19Cell00Row047.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row047MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row048MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row048.boundedRow_eq P2OriginalSaving19Cell00Row048.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row048MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row049MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row049.boundedRow_eq P2OriginalSaving19Cell00Row049.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row049MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row050MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row050.boundedRow_eq P2OriginalSaving19Cell00Row050.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row050MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row051MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row051.boundedRow_eq P2OriginalSaving19Cell00Row051.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row051MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row052MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row052.boundedRow_eq P2OriginalSaving19Cell00Row052.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row052MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row053MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row053.boundedRow_eq P2OriginalSaving19Cell00Row053.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row053MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row054MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row054.boundedRow_eq P2OriginalSaving19Cell00Row054.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row054MomentFloor.prefix_floor_checks
  · exact Eq.mpr
      (congrArg₂ (fun row momentRow =>
        PrefixFloorChecksFor row momentRow P2OriginalSaving19Cell00Row055MomentFloor.prefixMoment)
        P2OriginalSaving19Cell00Row055.boundedRow_eq P2OriginalSaving19Cell00Row055.raw_moment_row_eq)
      P2OriginalSaving19Cell00Row055MomentFloor.prefix_floor_checks

theorem all_raw_prefix_floor_checks (r : Fin 56) :
    PrefixFloorChecksFor (concreteGeometry00.rows[r.val]!)
      (momentConcrete00.rows[r.val]!) (prefixMoments r) := by
  rw [row_lookup_no_fallback]
  exact all_bounded_prefix_floor_checks r

theorem all_first_moments (r : Fin 56) (j : Fin 10) :
    prefixMoments r j 1 = 1 - meansOf (boundedRow r) j / topsOf (boundedRow r) j :=
  (all_bounded_prefix_floor_checks r).1 j

theorem all_saved_Q80 (r : Fin 56) (j : Fin 10) :
    (momentConcrete00.rows[r.val]!).factorFloorsQ80[j.val]! =
      factorFloorQ80 (prefixMoments r j) :=
  (all_bounded_prefix_floor_checks r).2.1 j

theorem all_Q80_bounds (r : Fin 56) (j : Fin 10) :
    (((momentConcrete00.rows[r.val]!).factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
        gapEvaluator (prefixMoments r j) * (2 : ℚ)^80 ∧
      gapEvaluator (prefixMoments r j) * (2 : ℚ)^80 <
        (((momentConcrete00.rows[r.val]!).factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1 := by
  fin_cases r
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row000MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row000MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row000.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row000MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row001MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row001MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row001.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row001MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row002MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row002MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row002.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row002MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row003MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row003MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row003.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row003MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row004MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row004MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row004.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row004MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row005MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row005MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row005.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row005MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row006MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row006MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row006.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row006MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row007MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row007MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row007.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row007MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row008MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row008MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row008.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row008MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row009MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row009MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row009.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row009MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row010MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row010MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row010.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row010MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row011MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row011MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row011.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row011MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row012MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row012MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row012.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row012MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row013MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row013MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row013.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row013MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row014MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row014MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row014.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row014MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row015MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row015MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row015.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row015MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row016MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row016MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row016.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row016MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row017MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row017MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row017.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row017MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row018MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row018MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row018.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row018MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row019MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row019MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row019.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row019MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row020MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row020MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row020.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row020MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row021MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row021MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row021.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row021MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row022MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row022MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row022.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row022MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row023MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row023MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row023.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row023MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row024MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row024MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row024.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row024MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row025MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row025MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row025.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row025MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row026MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row026MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row026.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row026MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row027MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row027MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row027.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row027MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row028MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row028MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row028.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row028MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row029MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row029MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row029.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row029MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row030MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row030MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row030.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row030MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row031MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row031MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row031.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row031MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row032MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row032MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row032.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row032MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row033MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row033MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row033.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row033MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row034MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row034MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row034.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row034MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row035MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row035MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row035.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row035MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row036MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row036MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row036.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row036MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row037MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row037MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row037.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row037MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row038MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row038MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row038.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row038MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row039MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row039MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row039.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row039MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row040MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row040MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row040.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row040MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row041MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row041MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row041.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row041MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row042MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row042MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row042.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row042MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row043MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row043MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row043.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row043MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row044MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row044MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row044.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row044MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row045MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row045MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row045.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row045MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row046MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row046MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row046.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row046MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row047MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row047MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row047.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row047MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row048MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row048MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row048.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row048MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row049MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row049MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row049.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row049MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row050MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row050MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row050.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row050MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row051MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row051MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row051.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row051MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row052MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row052MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row052.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row052MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row053MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row053MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row053.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row053MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row054MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row054MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row054.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row054MomentFloor.all_Q80_bounds j)
  · exact Eq.mpr
      (congrArg (fun momentRow : MomentRecord =>
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
            gapEvaluator (P2OriginalSaving19Cell00Row055MomentFloor.prefixMoment j) * (2 : ℚ)^80 ∧
          gapEvaluator (P2OriginalSaving19Cell00Row055MomentFloor.prefixMoment j) * (2 : ℚ)^80 <
            ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1)
        P2OriginalSaving19Cell00Row055.raw_moment_row_eq)
      (P2OriginalSaving19Cell00Row055MomentFloor.all_Q80_bounds j)

theorem all_saved_new_Q96_max (r : Fin 56) :
    (momentConcrete00.rows[r.val]!).newFloorQ96 =
      max (oldFloorQ96 (massOf (boundedRow r)) (meansOf (boundedRow r)))
        (newFloorQ96 (massOf (boundedRow r)) (meansOf (boundedRow r)) (prefixMoments r)) :=
  (all_bounded_prefix_floor_checks r).2.2.2.2

theorem saved_old_Q96_total :
    (∑ r : Fin 56, (momentConcrete00.rows[r.val]!).oldFloorQ96) = 1052519148976369882 := by
  decide +kernel

theorem saved_new_Q96_total :
    (∑ r : Fin 56, (momentConcrete00.rows[r.val]!).newFloorQ96) = 1055527309463438251 := by
  decide +kernel

theorem saved_replacement_increment :
    (∑ r : Fin 56, ((momentConcrete00.rows[r.val]!).newFloorQ96 -
      (momentConcrete00.rows[r.val]!).oldFloorQ96)) = 3008160487068369 := by
  rw [Finset.sum_sub_distrib, saved_new_Q96_total, saved_old_Q96_total]
  norm_num

#print axioms prefixMoments_eq_normalized
#print axioms all_gapScales_ne
#print axioms all_deviationDenominators_ne
#print axioms all_gap_encoding
#print axioms all_deviation_encoding
#print axioms all_bounded_prefix_floor_checks
#print axioms all_raw_prefix_floor_checks
#print axioms all_first_moments
#print axioms all_saved_Q80
#print axioms all_Q80_bounds
#print axioms all_saved_new_Q96_max
#print axioms saved_old_Q96_total
#print axioms saved_new_Q96_total
#print axioms saved_replacement_increment

end ImbalancedChen.P2OriginalSaving19Cell00AllPrefixFloorChecks
