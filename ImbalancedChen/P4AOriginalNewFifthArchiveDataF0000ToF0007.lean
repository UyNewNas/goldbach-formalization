import ImbalancedChen.P4AOriginalNewFifthArchiveReader

/-! Original G3 block definitions, retaining their exact fixture paths and names. -/
namespace ImbalancedChen.P4AOriginalNewFifthArchiveData
open P4AOriginalNewFifthArchiveReader

def F0000 : Block := include_new_fifth_pair% "g3-fixtures/F0000-cells.npy" "g3-fixtures/F0000-floors.npy"
def F0001 : Block := include_new_fifth_pair% "g3-fixtures/F0001-cells.npy" "g3-fixtures/F0001-floors.npy"
def F0002 : Block := include_new_fifth_pair% "g3-fixtures/F0002-cells.npy" "g3-fixtures/F0002-floors.npy"
def F0003 : Block := include_new_fifth_pair% "g3-fixtures/F0003-cells.npy" "g3-fixtures/F0003-floors.npy"
def F0004 : Block := include_new_fifth_pair% "g3-fixtures/F0004-cells.npy" "g3-fixtures/F0004-floors.npy"
def F0005 : Block := include_new_fifth_pair% "g3-fixtures/F0005-cells.npy" "g3-fixtures/F0005-floors.npy"
def F0006 : Block := include_new_fifth_pair% "g3-fixtures/F0006-cells.npy" "g3-fixtures/F0006-floors.npy"
def F0007 : Block := include_new_fifth_pair% "g3-fixtures/F0007-cells.npy" "g3-fixtures/F0007-floors.npy"

end ImbalancedChen.P4AOriginalNewFifthArchiveData
