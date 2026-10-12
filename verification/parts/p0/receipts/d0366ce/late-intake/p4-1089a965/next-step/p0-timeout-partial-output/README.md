# P0 source-only 超时记录补丁候选

**状态：Python 语法和修改范围检查通过；补丁尚未用于实际执行，未启动 Lean、Lake、leanchecker 或 CI，未接入集成分支。** 本目录与已封存的 actual-consumed 回执相互独立。

## 固定来源与所有权

- 来源提交：`1089a965e20664e63ffd51e0105c11befa406a1f`。
- 唯一改动目标：`verification/verify_part4_upper.py`，归 P0 验证运行器补丁；不修改任何 Part 的 Lean 源码或分支。
- 来源 Git blob：`865f7bda72b1d3b5e281cae63851ce7e38320da3`。
- 来源 SHA256：`4cccc00cbb5261aedd53d3fda6a8d3d630b751cfa6f788abe29747449bbc3818`。
- 候选 SHA256：`0b428167896c81f4129225984d808dd2fdaac30b9d050160dd94a5d9a32cb870`。
- 补丁 SHA256：`205cbafa14ebceb11e4c6370f5d60018043bf222418da15dd82ae144abfcb653`。

## 实际缺陷与最小修改

固定源码的 `run` 在 `subprocess.run` 超时时只经通用 `except BaseException` 记录 `FAILED` 与异常文字。实际 run `38288356713` 的 aggregate fresh 阶段于 1800.037 秒超时；其原始 `all-five-and-imports-fresh-replay.log` 只有 161 bytes 命令头，正文 0 bytes、完成 marker 0 个。现有证据仅证明时间预算耗尽，不能推断已重放任何模块，不能推断证明错误、卡死或特定缓存问题。

补丁在原通用异常分支之前加入 18 行专门的 `subprocess.TimeoutExpired` 分支：

1. 保持 `status="FAILED"` 和原异常文字，记录 `timed_out=true`、`exit_code=null`。这里 `null` 明确表示子进程 returncode 未知，不能填造 124、130 或其他退出码。
2. 只对异常实际提供的 `stdout` / `stderr`，追加到**原阶段日志**，标明来自对应异常字段；bytes 原样保存，str 编码成 UTF-8。`timeout_output_bytes` 每项为 `null`（不可得）、`0`（可得但为空）或实际字节数。
3. 如追加日志发生 `OSError`，记录这项次级日志错误，同时重新抛出原超时异常。原 `finally` 仍记录耗时和报告；成功路径、时间预算、命令、fresh marker 要求、源/对象/二进制最终绑定、公理及类型导出门槛全部保留。

当前固定运行器把 stdout 直接写到文件，并把 stderr 合并到 stdout；因此 `TimeoutExpired.stdout` 与 `.stderr` **可能都为 None**。这种情况下候选不会添加任何输出正文。它不能恢复旧运行中不可得或子进程内部尚未输出的数据，也没有解决 fresh 超时的根因。本候选只改善可得证据的保留与状态表达。

## 已执行的检查

真实执行了 `ast.parse` 原文件、`ast.parse` 候选和 `compile(..., "exec")` 生成内存代码对象，均通过；未执行该代码对象、未导入运行器、未创建通过 fixture。再从候选 AST 中删除唯一新加的 `TimeoutExpired` handler，整个剩余 AST 与固定来源完全一致，确认没有夹带其他代码变更。详情见 `PYTHON_SYNTAX_AND_SCOPE_CHECK.json`。

这项检查仅确认 Python 语法与补丁范围；不声称验证了 timeout 分支的实际运行行为，更不等同于 Lean 编译或完整 fresh 重放。

## 接入命令（尚未执行）

在从固定来源创建的 **P0 自己的候选工作树** 中执行，不能在 Part 4 来源分支或既有 d036 集成工作树中直接修改：

```bash
P0_PATCH=/workspace/scratch/535d89efd063/p0-round4/late-intake/p4-1089a965/next-step/p0-timeout-partial-output/p0-preserve-timeout-partial-output.patch
git apply --check "$P0_PATCH"
git apply "$P0_PATCH"
python - <<'CHECK'
from pathlib import Path
import ast
p = Path("verification/verify_part4_upper.py")
s = p.read_text(encoding="utf-8")
ast.parse(s, filename=str(p))
compile(s, str(p), "exec")
print("Python syntax passed; runner not executed")
CHECK
```

后续如安排新验证，须先固定新的 P0 候选提交身份，继续使用原工具链、原依赖、原时间预算和全部原门槛；不能把新运行的输出补写进 run `38288356713` 的原件，也不能把旧运行已通过的 17 阶段当作缺失的完整 fresh 与最终绑定。本目录没有启动该动作。

## 与实际接收回执的关系

`../../receipt-prep/actual-consumed/ACTUAL_P4_RECEIPT.md` 独立封存了五 strict、五 individual replay、73 个实际 pp.all 编译器声明及首次超时诊断。它仍判定真实 CI 为 FAILURE、缺失 aggregate fresh 和最终绑定/四个生产者导出。本补丁不会改变该历史结论，也不会闭合 K、c、完整 Chen mean、hLower 或 hUpper 的解析输入。
