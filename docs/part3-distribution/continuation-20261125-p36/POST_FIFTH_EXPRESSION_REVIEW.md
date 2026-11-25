# PostFifth 表达修复：独立只读审查

日期：2026-11-25。主体比较 `d4d176157102b622a5568e2d41d73413dcc1d03e` → `3d2ae714561f6b1fd909136e0b911620a99a007a` → `33c6790013ed57333f543034ce487435892ccd45`，并核对 `7bf26a1d5b447cdfb553b7680dc553fc747cd1d8` 的两处同模式 scope 修复。仅审查实际差异和失败诊断，不编译、不修改主源码或 manifest、不 stage 或提交。

**结论：修改与实际诊断相符，没有新增假设或改变原数学论证。需要明确区分：旧 `<+` 陈述没有成功解析，不能把“恢复原意的 `List.Sublist`”说成两个已经验收 Lean 类型的同一性。所有当前修复仍待真实编译及后续验收。**

## 1. 三项 PostFifth 修改

| 修改 | 独立核对 |
| --- | --- |
| 显式 `List.Sublist chosen (roughPrimeUniverse ...)` | 原 `pair_policy_support_iff` 已在 `open scoped List in` 下供应该关系；固定 Lean 的 `Init/Data/List/Basic.lean` 也明确把 scoped `<+` 记号定义为 `Sublist`。新写法消除实际 parser error；chosen、universe、乘积、接受条件和 rank-five 结论均保持原意。此处确实修改了声明文本，不能声称旧版本已存在一个验收类型。 |
| 两个局部列表恒等式归纳前 `clear` | `selectedWord (xs.map unselected)=[]` 与 `remainingWord (xs.map unselected)=xs` 本身不需要排序、非负、run 接受或 suffix gates。仅在各自 `have ... := by` 的局部子证明中清除这些依赖 `xs` 的上下文，避免它们成为 IH 的额外参数；外层定理的原假设与后续使用的 `hsuffix` 不会因此被删除或弱化。第二处同时清除前一局部恒等式，理由相同。 |
| `pair_atom_fifth_split` 在 `intro hlong` 前 `dsimp only` | 目标先含 `let H5 := ...; 3≤chosen.length → ...`。旧 `intro` 把 let 定义取名为 `hlong : Trace`；定义性化简先消去该 let，再引入真正长度条件。后面重新定义的 `H5` 与原表达式相同，原 `take 3`、`drop 3`、`run_append`、接受状态和 frozen-cap 论证均未修改。 |

PostFifth 原始 bytes 的 SHA 链已核对：

- 修复前：`6f03bfe87e40f8e48c2c485fc2f9b922b9e433e01bd780b75efb8e88b68c59f9`；诊断 pin `f51893bf...` 与比较基点 `d4d17615...` 相同。
- `3d2ae714`：`634dfe90902b0a8956ea7875d57145c29a59b22fcd359903397c4b5e9e407aa9`。
- `33c67900` 及 `7bf26a1d`：`241560a4a6c3348425c8ab29c957be2186e0f931720e1aa5c044ccfbaec24890`。

## 2. 第 12、13 份真实诊断

| 原始日志 | SHA-256 | 诊断 |
| --- | --- | --- |
| [twelfth-post-fifth-rough-squares-failure.log](twelfth-post-fifth-rough-squares-failure.log) | `10ba4eacb264af0c2689a6968c28e4fcb2a04cfc435039e1a5ec3961dbc4071e` | 1431 bytes / 22 lines；3 个 error：`<+` 的 `+` 解析失败，以及两个 IH 因多带外层条件而发生类型不匹配。 |
| [thirteenth-post-fifth-let-intro-failure.log](thirteenth-post-fifth-let-intro-failure.log) | `ae8767147b84696cdbe2c5ef6394b546b22206a3a3f8804ab810c8e1ec3a2997` | 1983 bytes / 36 lines；3 个 error：`hlong : Trace` 无法用于 `Nat.min_eq_left`，长度目标残留，以及仍为 implication 的目标不能使用 conjunction constructor。 |

两份日志的原始 bytes 与终点 Git 内容及修复记录的 SHA 一致。第 13 份日志不再报告第 12 份的 parser/IH 错误，但仍是失败记录，不能转为模块通过或 kernel 证据。

## 3. `7bf26a1d` 同模式跟进及验收边界

`P2OriginalSelectedPairNativeData` 与 `P3OriginalU5PhysicalModulusCap` 都只把 `open scoped Classical` 改为 `open scoped Classical List`，声明文本和证明体未改。修复记录明确写 `direct_failure_in_this_module_observed=false`；本审查保持这一事实，不伪造两个模块各自的失败记录或声称跟进已编译通过。

新源码 SHA 分别为 `38da3906fb03c458b54e7fbcc89bc0d742c6408128748559620d525395c4c78b` 与 `16789ed34e996b6eee3a00a18a1f73bbcb9427a238ab4ab480a705c56c9961d7`。在 `7bf26a1d` 核对 261 sources + 5 companions 共 266 项，SHA 均匹配提交及审查时工作树。manifest SHA 为 `07dc2b9e2f74252c07694e300d7f89b76c519f55e4922249f916c8a54b54b2a4`，source guard 绑定一致。

整个 `verification/` Git tree 在比较范围内保持 `879002f0dc10ca87c6c6069e13bdd7b2352cdfd2`，runner SHA 保持 `895a8bc67d6c28e4db0ce6954344e20679cb581e3b861bafed469852d5ee5d30`。没有降低 fresh strict compile、bundled kernel replay、完整 defining-module/type/传递公理及 cache/source/object 绑定检查。

审查时尚未收到本轮 P1 主/extra 的成功 archive；driver 报告当前主轮次 pin 为 `33c67900`，`7bf26a1d` 不属于该正在运行的 pin。本报告不计任何通过信用，也不代替之后对实际成功包的独立验收。旧 job `7a91...` 大包仍由 driver 统一回收，本次未重复获取。

## 4. 补充：02aebd19 的 FifthBudget 表达修复

补充核对 `02aebd195cb57c04005875568984f938590603c7`；最新 `93b715c2a36a5987021387fcfc4921fda1015f47` 只新增文档/候选出版，对主 Lean 源码及 SOURCE_SELECTION 与 `02aebd19` 相同。

[fourteenth-fifth-rough-budget-failure.log](fourteenth-fifth-rough-budget-failure.log) 为 1452 bytes / 23 lines，SHA-256 `adc563578d68aea612995a602279d0323338f040bd13200e693d8461be625da5`。它实际显示两项错误：泛化的 `rpow_mul` rewrite 命中了内层 `attachmentNu * epsilon^2`，以及最终 budget 的 local aliases 没有在目标中对齐。

已核对固定 Mathlib 的真实接口 `Real.rpow_mul_natCast (hx : 0≤x) (y : ℝ) (n : ℕ) : x^(y*n)=(x^y)^n`。修复明确传入原 `A=attachmentNu*epsilon^2` 和 `n=2`，取对称式，再用乘法交换处理 `A*2=2*A`；只使用原有 `hNpos.le`，没有新前提。最终 `change` 将目标写回其定义性相等的 `rough`、`physical`，`rw [hphysical]; exact hbudget` 消费原先已证明的同一个 budget。两个定理的声明、系数、buffer 和结论均未改。

FifthBudget 的 SHA 从 `86376360b56422ae7efaef8b4db4baae4e348a490abf29be984868e030160ca8` 变为 `81de8aadd6172f515503c6e579cf6d0e63e35eacd973d440fa8841ce324b9356`，这是 `7bf26a1d` 至 `93b715c2` 唯一主源码变化。后者再次核对 266 项 source/companion SHA 无差异；manifest SHA 为 `6447dbacc3b720d0206fe7e049d71463c681d8af74f4e80f3a62a91aed1c86bf`，guard 同步，verification tree 不变。补充审查仍未编译或取得成功 archive，不增加验收信用。

## 5. 预检冻结后的单文件 delta：ab0c6a5

后继 `ab0c6a5e26c6e65d88255155e363d6e1def385aa` 仅把上述最后 conjunction 构造的 `exact` 改为 `refine`。已读取 [fifteenth-fifth-budget-proof-block-failure.log](fifteenth-fifth-budget-proof-block-failure.log)，SHA-256 `55cad821aa0b11d576a6125ce613ce1785212ec420861dd8baf08963d32c7b94`：实际错误是无法合成最后 `right` placeholder，及由此残留的整个目标。`refine` 把该 hole 安排为后续 `change; rw [hphysical]; exact hbudget` 的子目标；没有改变声明或增加数学前提。

后继 FifthBudget SHA 为 `e744c477f17f6ff9818c6a022e560ba782798675f9bcd636219b2568a9c973da`，manifest SHA 为 `ec118d8d788f4d67758c0414fb53a3e1f59398d0e1f3cf8bf42398771f34bfbb`。这里只记录该精确单词修复及 delta，未重跑完整预检，未把它写入 `ROOT_V_COARSE_DEPENDENCY_PREFLIGHT_93B715C2.json` 的 `93b715c2/02aebd19` 快照。真正集成时须一次绑定最终成功 pin；当前仍无本次独立核证过的成功 receipt。
