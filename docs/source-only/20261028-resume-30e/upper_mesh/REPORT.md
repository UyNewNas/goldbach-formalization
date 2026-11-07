# upper_mesh 第五批：全原档索引与真实共同祖先

交付4份Lean、登记和本报告，共580行、39个公开定理。源码文本闭合，未编译，正式信用为0；`local_step_complete=true`，原完整任务与本批全目标仍false。

## 原档与索引的真实实例

这次直接导入已经存在的143个原始typed literal block，不另造小型model，也没有用两个named parent代替全档。`ArchiveIndex`取该独立数据 `rows.toList` 的全部位置，由原shape源码得到292633；`archiveRow i`始终保留同一位置的全部十个signed字段，顺序和重复记录均保留，未用row-value toFinset代替源序列。

原始cells.npy的23410768字节及SHA d6c599…、typed hub/shape/manifest和143 block原始字节SHA全部绑定在REGISTRY中。这里仅做静态字节hash核对，没有运行payload decoder或geometry checker。独立NPY字节与typed literals的**形式化身份等式仍欠**；typed自编码roundtrip或SHA不能替代它。

`licensedIndices`只按B13必要的grid400、非负mask、正lower keys和key0≤77筛选，`residualIndices`精确保留其余全部源位置。每个源owner仍来自相同raw decoder，保存相同mask；更严格的`licensedOwners`除D两端selected/firstStop外，再保留原始0/e两端完整与selected-complement square gateCheck。`missingOwners`显式保存其余原始decoded labels。代码未宣称这些filter对全档都通过。

## 同一e/q与真实余项

`IndexedBankError`把真正B13、完整父减baseline的遗漏积分，以及M×实际遗漏体积实例化到原始source INDEX求和，因此重复位置没有被抹去。具体rowModulus/M先选一个共同正有理e，再选同一refinement q，得到实际licensed index bank误差 `<eta/2+licensedTrimCost`。只有真几何trim符合剩余预算时才能推出规定总误差。`residualIndices`中的源行没有被赋予未经证明的零质量。

upper_jensen已冻结的独立接口进一步把这个**同一个**strict indexed trim精确拆成canonical遗漏和额外真实gate拒绝域，二者互斥；全292633源位置的canonical trim只剩原mask5/6 margin licence失败位置。其`exists_actual_indexed_schedule_with_geometric_remainder`接这里同一参数，给 `<eta/2+residualParentCost+gateRejectedBankCost`（omega≤1/400）。三个peer源raw SHA见登记。它依赖本作者的两个indexed源码，因此本交付不反向import它，避免循环。该式仍未证明两个真实余项足够小。

## 真实共同祖先的接口

`CommonPolicyInputs`消费physical作者独立冻结的 `P5OriginalCommonRefinedConstructor`，把完整档案过滤得到的globalOwners/rows5接入真实OriginalData；原第四rows/licensed4保持独立输入，没有变成checker flag。证明每个保留source index的真实candidate eligibility、candidate进入以**新共同第四祖先**为seed的第五maximum，以及最终policy8保留的实际rank5测试。

新common第四seed与旧source inherited4没有被等同。`changedParentPrefixes`显式保留其差异位置；仅在残域外证明两个独立定义的第五maximum相等。第四源复用physical作者真实cap包含定理，构造非负 `parentExcess=newCommon4−oldInherited4`，并证明真实rank5残域恰为excess>0。全局只保留cap包含；它不是signed系数单调或gain保持。

因此，旧historical fullCell上的B13**尚未升级为新common density误差**；changed-parent source-domain/gain比较或对应支付仍是精确未完成义务。此外仍需原档byte identity、残余行质量、原key injectivity、第四原始licence实例、全87域共同分割和K。窄审阅未发现新的原稿数学缺陷。

## 最终源码

{
  "lines": 580,
  "public_theorems": 39,
  "all_declarations": 60,
  "sources": [
    {
      "path": "docs/source-only/20261028-resume-30e/upper_mesh/P1HistoricalFifthCommonAncestorExcess.lean",
      "raw_sha256": "0fec96d00e0edade8a2cca33dc18cae1dbf22ff547a35c9984f6863517c92b45",
      "lines": 73
    },
    {
      "path": "docs/source-only/20261028-resume-30e/upper_mesh/P1HistoricalFifthCommonPolicyInputs.lean",
      "raw_sha256": "3c5a5a4d30a9e7967797d6062502a9444b52c5fe802d3aa73a6390b40b866499",
      "lines": 134
    },
    {
      "path": "docs/source-only/20261028-resume-30e/upper_mesh/P1HistoricalFifthIndexedBankError.lean",
      "raw_sha256": "dce27f276f83bebf4008ef39b03ca4459d12af948087b5e461eefb30c5b23081",
      "lines": 162
    },
    {
      "path": "docs/source-only/20261028-resume-30e/upper_mesh/P1HistoricalFifthIndexedOwnerArchive.lean",
      "raw_sha256": "373591a7d4d5b4468d01bd8b56ad2327bed3285465298d4c9e4c1ec2a1381b7a",
      "lines": 211
    }
  ]
}
