# upper_fifth 源码交付

新增 `P1FifthNamedParentActualIntegral.lean`，只写本任务独占目录；未编译、未执行 `decide`、未跑数值 checker，正式验收信用为 0。

本轮没有试图证明已知错误的“任意 J5 下 raw 行自动 selected”。已有 `namedJ5` 是原稿允许的一个局部有限选择，不能等同历史完整采用表。新证明沿该合法局部选择补齐真实第五候选的全部门槛，再接实际积分。

证明主线：

1. 对 literal parent0/1 各写一个小型有理 rawBoxGateCheck 证明（`by decide`，待编译专员执行）。手工核对其 selectedCapLower 均为 1/2，tent 下界分别为 939/1600 与 933/1600；`e≤3/51200` 留有严格余量。另证 raw check 对损失 e 单调，不把原始第三历史检查误当第五门槛。
2. 复用 `decoded_gateCheck_of_rawBoxGateCheck`，推出每一个实际 contained 解码 cell 的 gateCheck；与旧第三 firstStop/rough 身份合并得到真实 `eligible`。
3. 证明在原始 mesh/rough schedule 下 `selectedFifthCells ... (namedJ5 m) = namedJ5 m`。这里完整保留原始 filter，而非假设其无效。
4. literal 两父的首坐标 key 为 31 与 30，证明 KeyInjective 与半开 raw-box 互斥。复用现有 `fullSelectedIntegral_eq_sum_raw_owner_integrals`，得到本地选择族的真实积分精确两项拆账。旧/新 strict own-cube、真实 variable fourth producer profile 均由原有实际积分 API 保留。

已经消去本局部应用原来需要外供的 `hJ`、完整 fifth gate Boolean 和 key checker；没有把 `hUpper`、K 或 saving 作为假设。`rows4`/`licensed4` 保持原有实际第四 profile 参数，不替换为常数。

整个原分配目标仍属部分推进：历史完整 adopted J5 身份、NPZ bytes 到 typed row、全表语义、两项数值积分下界及当前 K 都未闭合。因此 `complete_module=true` 指文件文本闭合，`task_complete=false`，`ready_to_install=false`。未发现新的原稿数学缺口。

精确导入路径、哈希和暂存依赖安装映射见 REGISTRY.json；生产文件、旧草稿、Git 和看板未改。
