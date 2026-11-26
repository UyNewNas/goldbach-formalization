# A 完整 owned 输出容量诊断：准备完成，尚未执行

本诊断只解决 canonical A 的实际序列化体积不确定性。它不替代原独立 replay、原完整 audit runner、原 receipt selection 或最终 exporter。

## 冻结入口

- Shell: `p2-a-owned-capacity-b55-draft01.sh`，24,479 B，SHA256 `518137dc36f4f7f14eac35ea595ea0c64a24bb2233e85570520298b0c5d3f712`。
- Python: `p2-a-owned-capacity-b55-draft01.py`，24,019 B，SHA256 `07ec67b10b3976a89e6daf374609ffe684433db80ca7cb3302a74a366c8b39d8`。
- 新逻辑 tail: `capacity-tail-draft01.py`，17,046 B，SHA256 `148f3cfd80c53349c7efaa86c1ef472bdeb1bd2e7f00dec439a3f4dbc251ad28`。
- Manifest: `capacity-draft01-manifest.json`，5,499 B，SHA256 `d9b0dac57c50a21395f4c1273a15d652e1da262c9cc69aa0032c6054eb1b0770`。

原 A b55 wrapper 的 setup 前半逐字继承，仅增加 Python gzip/io 导入；21 个 pinned source/tool hash、原 runtime、native context、324 顺序 fingerprint、321 与 A102 闭包边界保持。新独立输出目录固定为 canonical worktree 下 `.lake/p24-owned-capacity/b55-A-attempt-001`，不得覆盖已有目录。

## 检查内容与输入冻结

运行前先用原 `snapshot` 核全 324 source/object/runtime/native/tool，并调用原 `verify_compilation` 核当前 321 和 A102 编译绑定。它不会运行零预算编译驱动、改写 registry 或复用旧 A 的失效绑定。全量 registry 只留 bytes/SHA，避免另写约 27 MB 副本。

使用固定 SHA `2975fe...` 的原 audit template，仅按原 runner 的方式替换两处 target 为 canonical A。完整 `Audit.lean` 及原模板 bytes 均保存。Lean 参数恰为原 runner：

`-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=50000 -DmaxHeartbeats=40000000`

LEAN_PATH 和 qualified native environment 的构造顺序也沿原 runner。提交资源契约保持 outer 3600 s / 13107 MiB / 1 CPU；该草稿不自行提交任务。

执行后重新核全 324、registry、native、runtime、工具和当前 A 原审计目录，所有输入须与运行前一致。新诊断只能写自己新建的输出目录，不会写 `.lake/p2-private/audit` 或原 latest/receipt。

## 完整字节保全与原格式体积

Lean 的 stdout 与 stderr 按原 runner 合并，但直接由 PIPE 写入新 gzip，完全不按行过滤、截断或限制 declaration 个数。边读取边计算原始完整 bytes/SHA；成功结束后重新解压到 EOF，核对原始 bytes/SHA 和 gzip 自身 SHA。

随后直接导入固定 SHA `571b...` 的原 `parse_audit`。原函数对输入路径仅调用一次 `read_text()`；诊断对象只提供相同接口，从 gzip 通过标准 `TextIOWrapper` 返回完整文本，保留和 `Path.read_text()` 相同的编码/换行规则。project 参数仍是 exact A102 闭包，不扩大到 324 以容忍额外 imports。

原 parser 会照常核 imports、serialized/environment exact inventory、逐项覆盖、safety、允许 axioms 和完整未截断 types。不会跳过 helper、private 或 generated 声明。

三份原格式的计数方式：

- `audit.log`：本次完整原模板进程 stdout 的实际字节数和 SHA。
- `declarations.json`：原 `json.dumps(parsed, indent=2, sort_keys=True) + "\n"` 表达式，经过标准 `TextIOWrapper` 在内存中精确编码后计算 bytes/SHA。
- `types.txt`：原名称/类型 join 表达式，同样在内存中精确编码并计数。

没有创建再删除这三份松散文件；因此不涉及删除任何实际原 audit 原件。完整 gzip 足以重建本次 raw stdout，并用原 parser/序列化再次得到两份派生格式。结果包含完整类型 UTF-8 字节总量、声明数、axiom counts、三文件 bytes/SHA 及总量。

这些是本次 canonical A 对象、原模板运行的真实容量诊断结果；尚未执行时不能预填体积。未来原 runner 的实际 receipt 和日志仍由原 runner 自己产生，不能把诊断输出登记为它们。

## 失败与空间边界

持续守住 32 MiB 余量，并额外预留 metadata 与 gzip 尾流空间。若接近保留线，只停止此 wrapper 创建的诊断 Lean 子进程，尽量排空已产生的 pipe bytes 并完成 gzip；不会操作其他任务。已有部分诊断文件保留，失败或非完整 stdout 不被标为成功。

只有 Lean exit 0、完整 EOF、gzip roundtrip、原完整 parser、精确计数、所有 postcheck 同时成功，`diagnostic_passed` 才为 true。正常非零 Lean 状态或 postcheck 错误保留在诊断结果中；无任何 canonical accepted/latest 写入。

全部阶段均明确：

- `original_runner_main_called = False`
- `independent_replay_performed = False`
- `canonical_audit_credit = False`
- `full324_credit = False`

## 验证状态

已做 Python AST/compile 语法检查和 `bash -n`，未执行 wrapper、未启动远端任务、未导入 canonical A。原 `parse_audit` 的 read_text-only API 已按锁定源码 AST 核对。

Root 已对原 flags、native environment、parser 和 serializer 逐项复核；scope agent 已完整独立读冻结 source/tail，并回报没有具体 API、guard 或字节完整性缺陷。此静态 review 不代表运行成功，后续是否提交由 root 决定。
