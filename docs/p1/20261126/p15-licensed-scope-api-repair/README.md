# Licensed 三 scope 的精确源码修复

固定源码 L 为 `972c2220d87669869a65c03fa64dc04562e37f0d`。真实失败 metadata、完整 Licensed probe、三份 scope splice 及 manifest 指纹均已绑定。当前仅 scratch 交付；部署须由根代理发布 M 后执行，未在本地或云运行更新器。

## 固定身份与本轮范围

- 失败：K `237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e`，`job_05205bc1d3f7442da9444752ab8a9972`，`runs/attempt-00001`；15 个所选 owner 尚无接受，只有 Licensed 正常编译失败。
- Cutoff：保持 K 的 `runs/attempt-00000` 成功身份，16 owned / 8 public。
- HB：保持 F `080d4178711ae042235104f7f4768649f51da2ab` 的原接受身份。
- Support：保持 B `3d292e4cd193ab422ca990e80a25165d5aca33a1` 的原接受身份。

只安装三份固定后像：Licensed、SingletonSmoothLicence、AdmissibleAllRankIntegerGeometricFamily。它们只开启官方 `ContDiff` scope；原声明、证明、imports 和原 CRLF 字节保留。更新器直接读取已发布候选记录中的精确 UTF-8 splice，不另行重写源码。

| 保护范围 | 数量 | 检查 |
|---|---:|---|
| Git 发布源码 | 360 | M 全部字节等于固定 L；只有三份不同于原 K |
| 所选 live closure | 157 | 原 K 全部前像和 import 图；安装后仅三份后像变化 |
| watched modules | 160 | active157 与原21 targets 的并集，逐模块完整21项产物保持 |
| 非选中依赖 | 142 | Support、HB、Cutoff，加13原 accepted suppliers 和126 fixed dependencies |
| 原 K current-owner states | 16 | Cutoff 完整接受，加15个 fresh selected owners |

真实有界收集只观测3源码和63项产物；不把它误写成完整157/160库存。完整范围在部署时由原图和真实现场重新检查。

## 已绑定的实际结果

完整 Licensed 候选3763字节 / `675cea556d3f85f4ca5e4e4c197b95ddd11e2e60f85e86de52388fe9b2531679` 已由独立任务 `job_f9f175857d0843b7b0ec7b5e8785378b` 做了一次无 `-o` typecheck，exit0、空日志、无 owner 输出。它不构成 normal/kernel/full-owned 接受；另外两份 scope 候选未试编。

失败元数据19586字节 / `62a5e300abe1a1455283d98bbde2ad7008b5dc0ecd730d6275ddab1bca461365` 和 probe记录1492字节 / `0b3f9bb588d1cad385d0b8da8d0319892a3fddbdc801e7b96b40deb5b2274f29` 将从 L 的 `p15-licensed-profile-first-compile-repair/` 读取。

唯一可归档文件是原 Licensed `.lake/build/ir/ImbalancedChen/P5LicensedOriginalIntegerProfile.setup.json`：6328250字节 / `692e72cd9914cd70c80d62a5c81e4530e3d1c7f8cde7f5f46b590a593e1f4744`。其余20项必须不存在，normal pass 必须不存在；其它14个 selected owners 必须仍 fresh。不存在通用 cache 清理例外。

## 执行顺序

先复用原 K 的只读前缀，完成旧 Support/HB readers、13供应者、126固定依赖，以及 Cutoff K 的原 normal 和完整 owned audit 检查。Licensed 此时不被伪造为 fresh 或 accepted。

随后沿原四个归档函数保存唯一已观察 setup：独占0600完整副本、flush/fsync、目录fsync、固定metadata回执、重新检查原inode/大小/mtime/全字节后，才移出原活跃路径。归档失败或未知内容一律停止并保留证据。

归档后，调用**真正未改的原 K `preflight`，输入完整15目标**，要求16个 current states 与142依赖匹配。这个门通过之后，才调用原 `h.install_sources` 一次安装三份固定 payload，并保留三份前像备份。安装后复核完整157 source图、160模块产物、全部原接受/失败回执与运行时；不重新执行旧 supplier 的编译或 kernel 验收。

`--check` 只检查，不创建 attempt 或归档，不写源码。`--apply` 使用原 serializer lane0 与原 helper；Git保护范围是原 HEAD/status，代码没有向 REPO 写入的路径。结果与详细证据留在本更新器独立 run 目录，公开输出仅有界状态。

## 发布与审查

未来 prefix 固定为 `docs/p1/20261126/p15-licensed-scope-api-repair/`，`--source-commit` 指向含本脚本的 M，源码 anchor 单独固定为 L。M runner 的 Cutoff@K historical overlay 由独立 owner 处理；本 updater 始终调用原 K 读取器，不把旧回执重绑到 M。

核心已获独立只读静态审查，未发现具体误放行或误阻断。一次最终静态检查已实际通过423项：360源码指纹与63项有界来源/图/归档继承/纯输入检查；另有5个错误payload拒绝例包含在该总数内。没有执行更新器入口或加载真实driver/helper，也没有重跑原K的54项旧检查。独立最终pin-delta结论另登记在STATIC_REVIEW。未运行本更新器、Lean、云任务、canonical 修改或 Git 提交。
