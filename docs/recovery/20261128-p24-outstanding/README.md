# P2.4 原工件待恢复交接清单

这是**纯metadata交接清单，不是恢复完成或新证明验收**。只整合冻结输入；没有枚举workspace、网络、下载、搜carrier、读取normal对象body、执行proof/tests或改provider。

`new_formal_credit:false`，`formal_acceptance:false`，`P2_4_complete:false`，`original_full_snapshot_verified:false`。既有normal/replay/owned成功必须保留，不因工件缺失重复。

## 当前精确计数

| 类别 | 数量 | 工作性质 |
|---|---:|---|
| 原317内尚缺主对象 | 165 | 找回历史成功normal对象原字节；不是165个新normal待办。 |
| later4主对象 | 4 | 已有b55原successful compile-record及11 canonical owned成功；找回原对象，不重跑成功流程。 |
| later A主对象 | 1 | 已成功attempt5，307006600B，SHAd02eb743…；找回该原对象，不用旧attempt4记录。 |
| 以上missing successful normal对象合计 | 170 | 恢复/资格工作，不是新编译工作清单。 |
| 原native资格/input JSON | 518 | 原514 provider qualifications、fresh receipt、fresh setup、STAGED、EXTERNAL_SNAPSHOT；恢复原expected JSON，不冒充新normal。 |
| 总待恢复工件条目 | 688 | 170对象 + 518 JSON。 |
| 真正仍未执行的B/W endpoints | 2 | 与以上688历史工件分列；此清单不授权执行。 |

差集严格校验：

- 冻结remaining216已经扣掉原restoration001的101，不再重复扣101。
- restoration002的44和restoration003的7均为216的子集，彼此不相交。
- `216 − 44 − 7 = 165`。
- 三次restoration的101/44/7互不相交，actual raw152对象合计56892400B；只沿已封存actual restoration receipts记录其独立source/object/raw-record SHA，本任务没有重读对象本体。
- `317 = 101 ∪ 216`；`317 − restored152 = missing165`。
- later4与A都不混入原317；`152 restored + 170 missing = 322`个已有历史normal成功对象的物理状态分解。
- 21个same-source/different-object候选完全不并入清单，恢复数不因它们增加。

## MISSING.json 的结构

- `input_pins`：冻结audit/旧registry、三次restoration、later4/A metadata archives、权威SUPPLEMENT的绝对路径/bytes/SHA。
- `already_restored_raw152`：152项独立restoration receipt指针，actual restored source/object pins及原record-value pin；不重新授证明信用。
- `missing_legacy165_successful_normal_objects`：module、原source SHA、expected normal object SHA、原path、原record摘要及精确raw JSON-value pin。
- `missing_later4_successful_normal_objects`：四个原successful compile records的精确archive/member/bytes/SHA、原object/source/path、context签名等。四份原记录均完整精确取得，`metadata_gaps=[]`。
- `missing_later_A_successful_normal_object`：只使用later attempt5 selected-record，expected307006600B/SHAd02eb743…、closure60720a…、原新Loop/Cache依赖与前后检查；明确`use_old_attempt4_record:false`。
- `missing_original_native518_JSON`：直接从冻结AUDIT_DATA逐行复制category、expected origin/bytes/SHA、original_archive_member、JSON pointer；原snapshot SHAad4386…完整保留。
- `genuinely_unexecuted_endpoint_proofs`：B=CachedEndpointCandidate完整2M闭guard、W=WholeFunctionalEndpoint；B旧任务启动前取消、W未执行，不冒充历史已成功normal对象。
- `strict_set_and_pin_checks_passed`：实际通过的差集、source/object/rawrecord hash与输入约束。

## 原record与未知尺寸

旧registry原文件27051479B，SHA6ad38f…，本任务只读解析metadata，未修改。每个165项的`original_record_pin`给0-based byte offset、精确value bytes、raw SHA和container SHA；它指原JSON值原字节，**没有重新序列化冒充历史记录**。三次restoration的全部152条source/object SHA及其原record-value SHA/长度也逐条与该原registry核对一致。

later4读取原metadata archive的四个exact compile-record members；later A读取tiny archive的`canonical-A/selected-record.json`及READONLY_BINDINGS。没有抽取proof对象或遍读其他archive payload作为恢复。

原metadata没有给165+4共169个对象长度，`expected_normal_object_bytes:null`明确保留未知，不从donor/同源不同对象猜长度。A长度由原READONLY_BINDINGS确证。已知missing normal bytes为307006600B；518 JSON总长度2055198310B；合计**已知下界**2362204910B，另169个未知对象长度，不是总下载/存储预算。

## 三次实际恢复的独立收据

| receipt | bytes | SHA256 | count |
|---|---:|---|---:|
| `/workspace/p24-artifact-recovery-20261128/attempt-001/RESTORATION.json` | 142898 | `ed9c21072cb471cd409719b86e573931ec38e293d79a6e45b1849a074991246e` | 101 |
| `/workspace/p24-artifact-recovery-20261128/attempt-002/RESTORATION.json` | 77875 | `2e8b6d54e67ceed56313eac5e53d8e7c0eee1266f0157a98b4d56dd0062293d7` | 44 |
| `/workspace/p24-artifact-recovery-20261128/attempt-003/RESTORATION.json` | 10388 | `5a18ab9854ff854bdc90fd13cdd593a778a652acadb880efa11de0049d6efc48` | 7 |

## 边界

这些raw对象/source/record的恢复尚不等于canonical资格齐全。原native/runtime/actual imports/first LEAN_PATH/依赖签名/完整原receipt选择及缺失kernel/fullowned/export资格仍待按原规则完成；此清单不放宽任何门，不创建provider，不把source候选或同源不同对象当accepted。

A正常编译已支付新context，不再拿旧attempt4/2b551a barrier当当前状态；其canonical独立kernel/fullowned仍不能由capacity诊断替代。B/W才是实际尚未执行的新endpoint proofs；本清单只交接恢复状态，不启动它们。

`MISSING.json`：1457325B，SHA256 `73a9d8e83046e67d35de826b66e8b7d2688aeb8a41ee97e0136d3292a6c72196`。
