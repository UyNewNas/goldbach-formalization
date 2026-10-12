# 证据消费者诊断

首次消费者在识别 Round3Audit 的 pp.all 配置时失败：解析器只检查带 Lean Name 引号的 API 写法，实际原源码为 `set_option pp.all true`。已保留首次消费者源码与异常，改为匹配该原始 directive，再读同一固定源码重跑。此处未修改 Lean 源码、CI 原件、类型记录或 proof 逻辑；不是 Lean 编译失败。

第二次消费者读取历史 producer commit 时遇到本恢复仓库缺少旧对象，`cat-file -t` 也确认本地对象不可用。这不判定历史源码不存在、不判定验证失效。接收过的 19 个生产模块改用实际核验的固定 28fd630 提交生产路径；旧候选改读该提交内归档 source snapshot，全部与原收据源哈希逐字绑定，并保留原来源完整 SHA 及读取路径。未触发 fetch、编译或修改原始证据。
