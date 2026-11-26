# P2 原导出包的 xz 保全：第一阶段已通过

本记录只涉及已生成导出证据的存储。它不改变源码、对象、registry、原 audit/exporter 或数学验收，也不增加任何编译、有限证明或 owned 审计 credit。

## 最新实测结果

任务 `1107b856458b46deadc06036604e39a7` 成功退出：`exit_code = 0`，191.281237866 秒，峰值内存 807424000 字节。完整 MCP stdout 为 4323 字节，SHA-256 为 `75d87b98951adee07f1176c6b891baaab33f9a35ae49138ad412b441f45c2efa`，没有截断。

持久文件为 `/workspace/p24-export-retention-20261126/attempt-001/preserved-members.tar.xz`，28798608 字节，SHA-256 为 `059f665f7dd471a5f19a8ec7fcce4302deb3ab0ba170b2a34bd1db214e94ad49`。原 `all.tar.gz` 仍保留在原路径：581735403 字节，SHA-256 `3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463`。第二阶段尚未执行，尚未取得完整原包重建成功结果。

## 保全范围与无损依据

原导出包有 13855 项 file index，加上原 `PACKAGE_MANIFEST.json`，共 13856 个成员、4302650543 字节成员数据。第一阶段逐项核验了全部成员的名称、类型、长度和 SHA。

- 12104 个原成员、213393692 字节原内容全部以原字节保存在保全包中，包括原 package manifest、源码、records、audit、synthetic 内容等。
- 只有 1752 个成员、4089256851 字节按原 origin 路径共享现有 immutable native 文件。每项须位于固定 qualified native root 内，并通过路径、文件类型、长度及 SHA 检查；没有仅依名字或 namespace 排除内容。
- 保全包再加入精确原 outer manifest、原 exporter、重建映射及其自身 package manifest，总共 12108 个成员。持久 xz 的全部成员再次逐 SHA 验证通过。

未改动的原 exporter `fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645` 先生成保全用 gzip trial：49692656 字节，SHA `db072ea9ea600ffda3905b8150edf81781bcd631bfe48988bb0f32dea305b771`。随后只将这个保全 tar 的完整解压字节流无损重压为 xz，包括 tar headers、padding 和所有 metadata，未重写任何 tar 成员。完整 tar 流为 261642240 字节，SHA `bbda6f1030bf2e245334c2f8da9e05d5398127283e09b3e6333fc7dc2edea5f3`；xz 解压后全流 SHA 相同。因此内部 package 字段仍为原 trial 的 `preserved-members.tar.gz`，reader 明确核验这个字段。

这不是已经重建原 581735403 字节 gzip 的声明。原包重建需要第二阶段将全部保留字节与精确 native 文件合并后，调用同一个未改 exporter `package`，取得原 gzip 的精确长度和 SHA。

## 空间与输入不变检查

原 32 MiB（33554432 字节）保留要求完全不变。复制前空闲 63270912 字节；xz 28798608 字节加 metadata 预算 122933 字节及保留空间，共需 62475973 字节，guard 余量为 794939 字节。复制及配套文件完成后记录空闲 34398208 字节，写入收据后又验证仍不少于 33554432 字节。

第一阶段前后源码 pin `6e616f4e0372555f7a78bcdba3e198d0e277eec8`、registry `64cb804725e2a497fbe11be56506fbf30cdf3be087f3bcdf2c51fe3935d6f0f6`、原 gzip、11997843 字节原 manifest、原 exporter 与所有共享 native 校验结果完全一致。第一阶段代码没有 unlink 操作。

## 第二阶段待主代理审查

持久收据路径：`/workspace/p24-export-retention-20261126/attempt-001/stage1-receipt.json`。按成功 stdout 的最终 JSON 和冻结 `retention_common.encoded` 重建的精确收据为 3780 字节，SHA `68695341a4cdc52c92f970f7e19d0342ea14bd385cb2478bcfbcef2563213d6e`；第二阶段必须首先独立核对远端实际文件的这个 SHA。

待审脚本 `stage2_verify_and_release.py` SHA 为 `d2aca533203a36494366fc594d5bf12acdfa1f2adced8d0c4521c7d7d49bb49c`。相对已审 gzip 版本只增加 xz 格式绑定；原 release block 逐字不变。它会核对第一阶段收据及冻结 recipe 文件，独立重建原 gzip，要求精确 581735403 字节、SHA `3fae348f...` 和全部 13856 个原成员验证成功，才可能执行显式 `--release-original` 分支。没有该参数时仅验证并保留原包。

第二阶段是一次性收据流程：无 release 的运行也会创建 `stage2-rebuild-verification.json`，之后同脚本拒绝覆盖。主代理应在审查后选择本次执行是否带 `--release-original`，不要把先执行无 release、再直接重复带 release 当作已支持的流程。重建器会构造原 exporter 的完整 Evidence，资源安排应按原完整重建处理，不能沿用只需 2 GiB 的第一阶段提交参数。

本代理未提交或执行第二阶段，未删除原 gzip，未修改主 checkpoint、旧发布清单或任何生产 Lean 文件。

## 失败历史保留

`97aa5cd3c2714fcaba5523723c74c19b` 在首次计数守卫失败，原因是 file index 与包含 package manifest 的 tar 成员数差一；`b16d0b8389ad4e2db380688dbe23ae25` 在通过原包/native/trial gzip 校验后因原 32 MiB 空间守卫失败。两次失败的原脚本、提交命令和任务输出均保留。它们没有删除原 gzip，也没有创建成功的持久保全目录。

本地小型 smoke 另验证了含 CRLF、UTF-8、NUL 和非 UTF-8 payload 的 gzip/xz 全 tar 字节相等、全部成员相等及未改原 package 可重建精确相同的小 gzip；它只提供脚本级验证，不替代尚待执行的完整第二阶段。
