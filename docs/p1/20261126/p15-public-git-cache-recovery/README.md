# P1 编译前的公共 Git 重复缓存回收

这是实际编译容量恢复记录，**不增加任何 Lean 验收**。最初只读检查发现
`/workspace` 可用 58,617,856 字节；计划中的十五个新模块仅 setup 文件就需要更多空间。

公共仓库 `.git/objects/pack` 中的 65 个 pack 共占 2,576,596,546 字节。
读取并校验所有 v2 index 后，9 个保留包已覆盖原全部 63,190 个对象；其余
56 个包只重复这些对象。两份带 `.keep` 的包始终保留。

任务 `job_2c55dac8d7ed4d8999a52468435d79bc` 实际对 9 个保留包执行了
`git verify-pack`，exit 0、空日志；所有 65 个包的流式 SHA1 与 index
中的 pack 标识匹配，文件 SHA256 和 inode/mtime 被固定在只读计划中。
计划为 63,906 字节，SHA256
`7873eca6900f3df6cb883ba8e49f337d361f5a798570db5d07e09dcae1f3ec92`。

任务 `job_581f81163c7a4574a834411c2dced485` 执行本目录的固定脚本，
exit 0、7.921 秒，完整输出 1,584 字节。它先将重复文件移到同一文件系统的
暂存目录，保存旧 multi-pack index，再实际读取全部 63,190 个对象并验证
新 multi-pack index。HEAD、refs、dirty status 前后相同后，才删除重复副本。
优化模式会被显式拒绝；真实 `.keep` 在搬移及删除时重新检查；首次成功删除前的
失败会回滚原包和原 index。

最终删除 168 个重复 pack/index/reverse-index 文件，共
**1,931,899,845 字节**。63,190 个 Git 对象全部保留并可读取，原 multi-pack
index 仍留在任务自己的证据目录。既有源码、Lean 产物、验收回执、runtime
和 guard 均不在脚本的修改路径中；Lean 执行次数为 0。

清理自身测得的可用空间从 5,500,600,320 增至 7,431,036,928 字节。
初次检查与清理开始之间另有可用空间变化，其来源未在本任务中调查；本记录仅把
上述实际删除的重复字节归于本操作。

[OBSERVATION.json](OBSERVATION.json) 保存有界实测摘要和原回执指纹。
完整私有证明审计归档未被导出；这些元数据也不替代任何 normal、kernel 或
full-owned 验收。
