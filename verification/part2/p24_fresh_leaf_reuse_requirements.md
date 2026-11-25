# Architect.Command 已有 fresh 收据的取回与重绑要求

本记录只核对仓库现有生成与复用协议，不运行编译，不改写旧收据，也不声称已完成
P1 叶子迁移。P2 任务 `77e605315ba246b4a2c30811d34fe812` 的完整旧日志确认
`Architect.Command` fresh 源编译成功，但整批资格以 exit code 2 结束。整批缺项不抹去
该叶子的已有成功记录；叶子成功也不能改称整批已完成。
本轮只读 AST 对照确认：仓库保留的 `native-qualifier-before-batteries.py` 与当前
qualifier 的 `existing_fresh`、`compile_existing`、`freeze_core_imports` 三个方法完全
相同；下列协议说明适用于这份历史脚本，不是根据同名新实现猜测历史行为。

## 真实生成协议

`qualify_winner9_native_cache.py` 的 `Qualification.__init__` 把执行脚本原字节保存到：

```text
<stage>/tooling/qualifier-<SHA256-of-executed-script>.py
```

`compile_existing` 先写 `actual.setup.json`，冻结实际输入；对 Command 特例先递归冻结
`Lean` 的 core source/header 与 loadable facets。它在真实 `-t0` 源编译前、后分别运行
`recheck()`，只在后检通过后写 `input_files_unchanged: true`。收据包含编译前的
`input_files` SHA/bytes map；该协议不另写一份名为 AFTER 的逐文件 hash map，不能补造。

原生成命令结构是：

```text
<lean> -t0 -j1 -M6144 -DwarningAsError=true <source>
  -o <leaf-dir>/Architect/Command.olean
  -i <leaf-dir>/Architect/Command.ilean
  --setup <leaf-dir>/actual.setup.json --json
```

`activate` 随后将可装载输出复制到 `<stage>/active/lib/Architect/Command.*`，
因此 receipt 的 `objects` 键通常位于 fresh 子目录之外。不能只按字符串路径判断
fresh 子目录导出包缺少对象：先用 receipt 指定的 SHA 和长度核对包内同一模块的真实
fresh 输出；只有每个 loadable facet 均能一一对应时，才能形成显式 transport mapping。

## 收到 receipt 后必须核对的字段

| 字段 | 必须保留和核对的内容 |
| --- | --- |
| `schema`, `module`, `status`, `exit_code` | `p2-winner9-native-fresh-compile-v1`、`Architect.Command`、`FRESH_PRIVATE_SOURCE_COMPILATION`、0；不能仅凭目录存在选择记录。 |
| `input_files_unchanged`, `input_files` | 必须为 true；保留完整原始路径到 SHA/bytes 的 map。即使某些项看似与叶子无关，也不能删除原来被冻结的输入。 |
| `source`, `source_sha256` | 原始被编译路径与完整源字节身份，核对固定 LeanArchitect pin 的同一 Command 源。 |
| `command`, `cwd`, `lean_path`, `lean_sysroot` | 保留原 P2 字符串及完整 argv，核对生成协议；另建到 P1 的重绑表，不把旧 receipt 改写成在 P1 执行过。 |
| `actual_setup`, `actual_import_map` | 取回实际 setup 原字节，并与 `input_files[actual_setup]` 绑定。Command 适用空 `importArts`、`isModule: true`、空 options/plugins/dynlibs；仍必须核对其实际 Lean core 输入闭包。 |
| `producer_script`, `producer_script_sha256` | 必须取得对应原脚本字节；这是 fresh 目录扫描通常遗漏的外部文件。 |
| `log`, `log_sha256` | 取回真实编译日志，保留原始路径与 SHA；目录名或父任务 stdout 不替代这个日志。 |
| `objects` | 每个真实输出路径及 SHA/bytes；完整核对 `.olean`、`.olean.server`、`.olean.private`、`.ir`、`.ir.sig` 中实际存在且被记录的 facets。 |
| `receipt` | 原收据路径，与实际导出定位符和所选 attempt 对照，避免把不同 attempt 的 setup/log/output 混合。 |
| `original_classification_retained`, `original_checkpoint_cache_was_not_adopted_for_this_module`, `kernel_credit` | 原 quarantine 保留；该模块没有采用隔离旧对象；kernel_credit 必须仍为 false。 |

当前导出若只递归 fresh 目录中的 json/log/olean/ir 类文件，需要特别检查多段后缀。
单看 `Path.suffix` 的 `.private`、`.server` 或 `.sig`，会漏掉合法的 loadable facets。
`.ilean` 是原编译命令的输出，但不在此协议的 `LOAD_SUFFIXES` / `objects` 资格集合中；
若导出已有则保留，不用为它发起重复编译。

## producer_script 的精确判定与最小补取

仓库已保存成功轮次使用的一个原脚本候选：

```text
docs/verification/20261124-p2-private/native-qualifier-before-batteries.py
bytes: 41621
sha256: 5874aca907d2e6a776b03bb1e06c04b3dc6746bf4fffa0d3ffd0e951525ab9d8
```

必须先读取收到 receipt 的 `producer_script_sha256`，再选择供应：

1. 若它与上述 SHA 完全相同，直接采用仓库保存的精确原字节。记录历史 producer 路径、
   仓库供应路径、SHA 与 bytes；不需要再次排 P2 脚本导出。
2. 否则，对仓库已有候选或已知 Git 历史文件计算完整 SHA，只有精确匹配才使用。
   当前活动的 `qualify_winner9_native_cache.py` 不能仅因同名或功能类似而替代。
3. 若本地/Git 历史没有相同字节，补取 **receipt 的 `producer_script` 字段给出的绝对路径**。
   校验其文件名应为 `qualifier-<producer_script_sha256>.py`，并位于该 receipt 所属
   stage 的 `tooling` 目录。不要猜新的路径，也不要导出整个工具目录。

按已知 stage 结构，若收到的 SHA 确为上面的 `5874aca...`，其预期历史定位符是：

```text
/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/tooling/qualifier-5874aca907d2e6a776b03bb1e06c04b3dc6746bf4fffa0d3ffd0e951525ab9d8.py
```

这只是可核对的生成规则；最终以收到的真实字段和完整 SHA 为准。旧 task 的整批
`QUALIFICATION.json` 定位于 `qualifications/attempt-002`，但 leaf 的原定位仍须由实际
receipt 和导出清单确认。

## 其他外部文件不必一律重新导出

`source`、`input_files`、`objects` 指向的大量物理路径在 fresh 目录之外。先验证完整
receipt 和导出包身份，再逐项将原路径映射到已有 P1 同 pin source/object/runtime：
只接受相同 SHA 和 bytes，保留原路径、当前真实路径及重绑方法。
若一个外部对象在 fresh 包内已有精确相同输出，可以引用该原字节；若 P1 当前文件
精确相同，则可只读使用现有文件。缺失或不相等的项必须逐项列出，不能从当前文件
倒填一个假的历史 SHA。

最低限度的新增远程导出仅是：包中缺失、且本地/Git/P1 没有精确字节供应的
`producer_script`、实际 setup/log、或 receipt 明列的具体输出。输入 core/标准库
通常只需重绑已保存的 SHA 到当前 P1 字节；任何缺项必须明确处理，不能把当前新做的
core census 冒充 P2 当时的 input map。

成功迁移应写一份新的 P2.4 transport/rebind receipt，保持原 P2 receipt 原字节。
原 quarantine 仍作为历史事实保留；新 provider 的来源只能是已有 fresh 源编译。
本记录、本地测试、当前物理匹配或迁移本身均不授予 kernel/证明验收信用。
