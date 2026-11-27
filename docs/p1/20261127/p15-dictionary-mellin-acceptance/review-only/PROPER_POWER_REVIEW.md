# P1.5 proper-power 依赖接续

原 21 项仍为 18 项接受、3 项 HOLD。三个 P1.5 owner 的共同 P3 闭包包含 19 个文件。在 P1 工作提交 `040d46058821746c69c5183b3f6c22792287c4ba` 逐件核对当前 Git blob 后，我用三个原 P3 `PASSED` 回执对齐源 SHA-256、对象 SHA-256 和 owned inventory。精确清单见 [VERIFIED_P3_OBJECT_PINS.json](VERIFIED_P3_OBJECT_PINS.json)。

| 原 P3 数学提交 | 同源依赖数 | 这批依赖的原 owned 声明数 |
| --- | ---: | ---: |
| `c509267dc630d91df33033abde1c484ec86b96ae` | 13 | 279 |
| `60cf3d49f8aefc687a6ce3dd7008ae5804cc61d3` | 4 | 68 |
| `70e8f69cbbacb2b851147a5fa51948a106beeca7` | 2 | 20 |

新版本 `Part3ProperPowerLogSaving` 使用 `70e8f69c` 的接受记录。上述 19 项与 `P3_REUSE.json` 的 19 个新增源码重叠 18 项。差异为已在 P1 接受的 `Part3BrunWeights` 和仍待 P1 接收的 `Part3LongSlotDistribution`。先前 `Part3LongSlotDistribution` 的 donor `.olean` 匹配旧接受 SHA。五组其他 donor 对象已完成 package-only ModuleData 比较，原证据的适用范围为固定五组 P3 对象。当前 P3 会话终止，现有 donor 文件可用性未重新核验。

## 当前第一个接收阻塞

原 `p3-20` 接收任务 `job_41c06d666c6642889cc27d82ee281eb7` 接受 `Part3BrunWeights` 后，停在 `Part3CompletedReciprocalWeil` 的 direct-import stock readiness。独立接收检查的首项 `LiLiuPrereqFouvryCompletion` depHash 查询退出 134。日志记录打开 `/dev/urandom` 的权限错误。对照探测确认同一 inode 的挂载由外层 `rw,nosuid` 变为内层 `ro,nosuid,nodev`，读一个字节由成功变为 errno 13。

原 receiver 在固定 Batch5 `h.guard` 内另建 Bubblewrap namespace，使用 `--unshare-user`、`--unshare-pid`、`--unshare-net`、`--cap-drop ALL` 和递归 `--ro-bind / /`。外层 `run_guarded.py` 的原回执 pin 为 891 bytes / SHA-256 `c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526`。发布内容含固定 wrapper、实际调用及 runtime 配置，原外层脚本正文位于云工作区固定路径。

当前已发布接收和设备诊断目录提供 checker、只读诊断与证据。原 checker 的挂载 argv 是固定字面值。Bubblewrap v0.12.0 中 `--dev-bind` 的单独使用会产生当前探测拒绝的可写挂载，随后追加普通 `--remount-ro` 又会带回 `nodev`。上游依据为 [挂载分派](https://github.com/containers/bubblewrap/blob/v0.12.0/bubblewrap.c#L1368-L1378) 和 [挂载标志](https://github.com/containers/bubblewrap/blob/v0.12.0/bind-mount.c#L460-L471)。

## 原合同下的最小接续

由环境维护方提供独立、经审查的新接收检查入口。只允许真实宿主 `/dev/urandom` 字符设备 `(1,9)`，使其成为唯一允许读的设备挂载。该路径需要 `ro,nosuid,noexec`，同时允许设备访问。平台设备策略或等效隔离须独立拦截写和 mknod。Linux 的只读挂载标志本身不承担字符设备写访问控制。原 outer guard 与 serializer 字节、隔离网络、清零 capabilities、14 个受保护路径、owned attempt 唯一可写范围和已接受证据均由新检查继承。先核验 mountinfo、设备身份、只读访问和只允许 owned 写，再发起 4 项原 stock depHash 查询。任一条件不满足保持 HOLD；原失败回执继续保留。

即使 entropy 部分通过，`LiLiuPrereqFouvryOddPrimePower`、`LiLiuPrereqFouvryTwoPower`、`LiLiuPrereqFouvryLocalGlobalBridge` 的原 P1 接收观察仍缺 `.olean` 和 `.trace`，且尚无完整 `LiLiuPrereqFouvryCompleteWeil` stock 收据。原始 19 项旧 P3 接受只在接收上下文得到验证后可复用其证明身份。接下来依原 P1 接收入口选择尚未接受的 owner，保持 Brun 原命令不重跑；最后交给原三个 P1.5 目标依赖链。

`Part3ProperPowerChartSum` → `P1OriginalSingletonProperPower` → `P1OriginalHistoricalProperPower` 与 `P1OriginalSingletonAtlasProperPower`。现有 21 项执行入口仍显式拒绝未接受的 P3 依赖，必须先取得单独真实回执。
