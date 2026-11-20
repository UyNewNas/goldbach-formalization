# WindowGate → FiniteCover: 最小命名解析后像

本包仅在原 `Part3MediumPrimitiveShiuWindowGate.lean` 的15行 `open scoped BigOperators` 后插入一行：

```lean
open ImbalancedChen.Part3.MediumPrimitiveShiuCover20261028
```

原caller为11839 B / SHA256 `565b9031c5576cea894a62e55c76cc91f01985453104cd2623ddcc3652d6a18c`；新caller为11898 B / SHA256 `6d47a7fb9a91a67ba330cd6ca519964b03cb81e2da5d358d14e50b010ebe3892`。零基byte offset619插入59B（LF行尾），零字节删除。`authorpre/`保留精确旧字节，`authorpost/`为独立候选。旧源、旧rawheader选择及旧HOLD记录均不修改。

## 需要修复的真实source edge

V17 special2 的 `SOURCE_SELECTIONS.json` 和 `REPORT.md` 已将该问题区分为：FiniteCover raw identity选定，WindowGate actual caller API另有静态HOLD。原caller11行进入 `ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028`，14–15行只open Classical/Finset与BigOperators scope；而原provider在同级 `ImbalancedChen.Part3.MediumPrimitiveShiuCover20261028` 定义实际window对象，未向caller或父namespace export。caller45行起使用未限定windowStart。

本包继续锁定原phase9 caller guard所选的 FiniteCover `7bdcfdbbff4382da1ee4ba16ba9296b8995ceb11a43f78cf70af21f852549d39`，13577B，blob `2b5a0295540cf6eb7125d420fc0661102e0cfcf0`。不选择更新provider来掩盖caller问题；caller/provider的source_commit仍null，不新造远端定位。

需解析的9个原对象为：`active_window_length_lower`、`shellBase`、`shellBase_le_windowStart`、`window`、`windowLength`、`windowLength_le_start`、`windowLength_pos`、`windowStart`、`windowStart_le_eight_B`。`STATIC_SOURCE_AUDIT.json`逐项给出同一provider全名、provider行号及所有caller前后行号。该open只改变这些原来缺失的名称解析上下文，不改变其Nat/Real类型、窗口端点、参数顺序或原证明计算。

## 查重、命名范围与shadowing核对

写候选前，对已知同专题draft和frozen WindowGate aliases及当前resume-20261121、N02既有报告作有界文本检索。原draft同565b，另两frozen caller分别为1a278...和26d05...；三种body均未open Cover，未发现现成WindowGate精确repair。固定 `PUBLICATION_SOURCE_INDEX.json`也无该basename或565b hit。不能据此断言全仓不存在任意别名repair。

同专题 `Part3MediumPrimitiveShiuActiveWindow.lean:15` 已有完全相同的显式Cover open；它属于另一module，不能当作修好本caller的现成postimage。这里只复用其本地命名模式。

对选定provider的28条顶层def/theorem与caller的9条structure/theorem核对，声明名集合交集为空。对caller去掉单行注释后的identifier逐项核对，provider声明名实际只出现上述9个名字；没有额外同名caller定义或局部binder会被此open替换。其余19个provider声明名未作为caller代码identifier出现。这是已读caller/provider源码范围的静态无冲突检查；没有伪称完成整个传递import环境的elaboration或名称唯一性认证。

## 原证明、声明头及历史边界

选择一行显式open，避免逐项重写大量type/proof中的名称。所有9条原声明的源码头、全部原proof、全部原结构字段及现有3 imports保持逐字节原样；声明full names不变，原line≥16的全部内容后移一行。声明头中的未限定Cover词因新open获得预期解析，这一语义变化明确记录；不把原未解析环境伪称为先前已成功编译。没有新增definition、notation、premise、import、theorem或数学证明。

完整变化见 `EXACT_CHANGE.diff`，身份/9对象映射/9声明对应见 `STATIC_SOURCE_AUDIT.json`。可安装路径仅作为后续意图记录为 `ImbalancedChen/Part3MediumPrimitiveShiuWindowGate.lean`，本轮不安装、不发表。

V16/V17已选565b/rawheader与 `HOLD_STATIC_UNQUALIFIED_SIBLING_NAMESPACE_REFERENCES` 保留为历史。此新source需ROOT/N02独审后决定该特定命名HOLD的后续状态；作者不直接改旧选择或声称全Native6兼容。原primitive Shiu analytic boundary、其阈值在全部变化参数之前的量词、所有窗口与算术假设完整保留，不新增也不证明Shiu analytic供应。完整Native6/source closure、数学acceptance、compatibility、编译/kernel、green均不因此得到认可。

本轮只作源文本、JSON及hash操作；未执行Lean/Lake/LSP/kernel、项目helper/fixture/validator、object load、CI、Git/GH写、artifact下载或额度调用，未派生代理。旧source和记录未写，所有文件只写新n08目录。旧pins见 `PINS.json`。
