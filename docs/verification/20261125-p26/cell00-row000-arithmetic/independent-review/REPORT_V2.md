# Saving19 纯数值命名空间与桥接独立审查

## 结论

采用 `representation-v2` 是可行的最小集成方式。三种纯表示使用新命名空间，原分析 Q96、Winner9 checker、Core、Consumer 的源码和对象保持原样。新 Q96 等式桥与 RowDataChecks 的等价桥是独立待验收 owner，不把源字符串比较当作 Lean 证明，也不转移任何旧对象接受信用。

本审查只读，未运行 Lean、kernel、P1 或本地编译驱动，未修改作者候选或主仓。作者已报告三纯 owner 正常及独立 kernel 通过；本文自己的证据仅是逐字、范围、量词和集成审查。两个桥仍按源码候选记录，不能提前称它们已通过。

## 精确审查源

| Owner | SHA256 | 字节 |
|---|---|---:|
| `P2OriginalLogMomentQ96ArithmeticPure.lean` | `754f6bc945a37636ec9bc62224e9b842a97d3f2718990b59aa2caa8e9f164424` | 2332 |
| `P2Winner9FastDetPure.lean` | `d1a0d2ae8af1cf90e05af11b983c5c41ea97a42387eb6c6b9c32ff176e2258ac` | 6729 |
| `P2OriginalSaving19RowNumericsPure.lean` | `d39f14310722214e47e5b25c093ec1fb17fe61c3880ab1355867401187cb45e6` | 5359 |
| `P2OriginalLogMomentQ96ArithmeticBridge.lean` | `e2904e79be8c9c1ee4b982d3bf90bca451efb0a2667bafc3ba97fa44fc383bb4` | 3831 |
| `P2OriginalSaving19RowNumericsPureBridge.lean` | `57e18693e4eb8b80487c4ebebbd9f5a3edf73668e10711799d2a4240e0b9ed06` | 807 |

## 纯表示保留的内容

Q96 的13个声明分别与原 `49dddfb3…` 的精确 byte spans 比较，完整声明文本各自原样出现一次。`{ι : Type*} [Fintype ι]` 保留，未固定为 Fin10。`fixedNumerator` 仍是整数 `num * 2^bits / den`，Q80因子取整、Q80总和、三次修正、旧/新 evaluator、Q96取整和 stored检查全部保留。新模块只提供数值函数，不据此获得解析、实际矩、积分或 floor 正确性结论。

FastDet 原 force block 和3991字节 determinant block 均与 `bef1fb6c…` 逐字相同。14个原 private 声明仍为 private；只有新命名空间下的 `fastDet`、`fastDet_eq` 为原本的公开接口。任意维数 `{n : ℕ}` 与任意有理方阵 A 的规格仍是 `fastDet A = Matrix.det A`，包括0维、无非零首列pivot和一般换行pivot分支。代码没有采用浮点、外部 determinant 或新成功假设。最终 Row guard 自身仍使用 Matrix.det，所以无需导入旧重型Winner9模块，也无需证明新旧算法对象具有相同身份。

PureRow 的 QPoint/比较函数/PhysicalQ及 Decidable 原段，与7项数值接口、完整十合取、Decidable 和通用 iff 原段，均按原 `4be5f940…` 精确字节核对。只改变命名空间、imports/open目标和说明文字；GeometryRow 仍是同一个 ArchiveSchema 结构。行列式非零、9个原8维顶点物理条件、gap正性、physicalVolume、meanGap、十个means、tops双向界、Jensen值和Q96 floor十项均未删改。

## 独立桥接的证明义务

Q96 bridge 的13条定理均没有数据成功前提，逐项连接新旧相同参数的 evaluator，源码proof为 rfl。新旧公共函数都是透明定义，算术和隐式类型参数相同；未发现definitional equality障碍。Bool `checkStoredQ96` 也保持相同整数≤decide，未改成外部布尔结论。

Row bridge 对任意 `(v : Fin 9 → Fin 8 → ℚ)` 和精确 `Archive.GeometryRow` 证明 PureRow.RowDataChecksFor v g 与既有 RowNumerics.RowDataChecksFor v g 等价，proof为 Iff.rfl。它不假设任一检查成立，也没有Fin56或cell00限制。该桥连接纯表示与原函数后的完整十合取；PureRow内部名称为 `rowDataChecksFor_iff_originalForm` 的模板 iff 本身仍仅是纯表示内部展开，不代替这条跨命名空间桥。

这些源代码给出可信的完整证明候选，但仍须在原Q96和旧RowNumerics真实对象就绪后，单独通过normal/kernel/all-owned验证。当前本地没有原Q96三个supplier对象，不能为验证桥而重建分析链；P1只读对象导出清单另见 `Q96_SUPPLIER_READONLY_EXPORT.json`。

## 接受与集成边界

第一版同FQN提取与两heavy删除overlay仅保留为历史候选；它们会在合流时与旧对象产生重复公共FQN，因此不用于新路线。新namespace消除了这个问题，并避免修改旧分析supplier导致旧Core/Consumer context失效。实际读取主仓的Q96、Winner9 checker、RowNumerics v1、Core仍分别匹配原固定SHA，记录在 SOURCE_V2_REVIEW.json。

新纯owner与桥的所有新声明、private/compiler-generated声明都须接受自己的验算。旧Core或supplier接受回执继续指向其实际旧commit/context，不能重标为新的bridge commit。跨commit复用仍须按实际源/对象/import/trace/config/runtime等价验证；命名空间方案仅避免了不必要的源码修改，并不替代该证据。

本审查没有核验row000数值guard，没有声称Q80上/下界、实际Q96 floor、13项原解析、覆盖、ownership或端点积分已完成。12项Integral缓存仍为未下载的候选键清单。
