# P2.4：复用已有有效 P2 项目缓存

`p24_migrate_verified_cache.py` 将已经通过既有编译记录契约的旧 P2 项目对象，
迁移到 P2.4 的独立 checkout。它不扩大旧 Winner9 固定迁移名单，不修改旧
`records.json`、源码、对象、资格快照或任何既有 verifier；也不把 diagnostic
PASS 转成有效编译记录。

## 为什么需要独立迁移

现有 `migrate_winner9_private_snapshot.py` 专用于 2026-11-24 的固定旧定义图及
schema 2 历史修复，不能直接用来接纳本次 P2.4 的范围。

现有 `ExternalSnapshot.binding()` 将实际项目搜索路径作为环境的一部分。
把旧记录文件复制到新 checkout，并把其 native 环境字段替换成当前字段，会失去
原始依赖证明。新工具先在旧目录中验证旧闭包，然后仅对经过验证、源码及所有项目
依赖完全相同的对象建立一次有证据的路径迁移。

本工具动态读取 `ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint` 的真实
项目闭包。当前准备源码为 322 个模块；这个数字不作为硬编码验收条件。旧目录中
其他模块的记录不会成为迁移来源。

## 接纳条件

1. 用旧 project library 和同一已有 external snapshot 建立旧环境，并用新 library
   建立新环境。两者的 binding 必须只有 `lean_path[0]` 改变：snapshot 路径和 SHA、
   context signature、验证 helper、native 名单、其余搜索根和 sysroot 均相同。
2. 用旧源码树、旧 `.olean`、旧 records 中原有的递归 dependency signatures 及旧
   external binding，调用原 `verify_compilation` 验证候选的完整旧项目闭包。
   在此之前不重建或补写任何旧 dependency signature。
3. 候选新旧项目闭包的模块集合相同，全部源码 SHA、实际源码字节及直接项目 imports
   相同。字节相同同时保持普通 imports 和 native imports。
4. 新路径的所有项目父模块必须已有通过原 verifier 的有效记录；它们可以来自此前
   同一事务中已验证的迁移项。任何缺项或不同源码都会阻塞该候选及相关后继。
   此外，候选完整项目依赖闭包的新旧 public object 及全部当前 loadable facet 集合、
   字节必须完全相同。即使某个新父对象有独立有效记录，只要字节不同，也必须阻塞
   旧 child 的迁移；不能给旧 child 换一套不同的实际输入。
5. 复制旧路径当前存在的全部 `.olean`、`.olean.server`、`.olean.private`、`.ir`、
   `.ir.sig`。新路径中已有不同字节或额外 loadable facet 时保留原文件并阻塞该项。
   对所有目标先检查，再复制，不覆盖不同字节。
6. 新记录保留原始证明来源，其新的 dependency signatures 仅由已验证的新父项生成。
   native binding 只应用第 1 项已验证的项目路径变换。新记录再通过原
   `verify_compilation`。`new_strict_compile` 明确为 `false`。
7. 批结束和 registry 发布前分别复核旧/新源码与对象、全部当前 loadable facets、
   facet 集合、external snapshot、Mathlib pin 及双方 records 原始字节。只有这些
   检查均通过，才原子写入目标 `records.json`。旧目录始终只读。

所有目标 facet、registry、临时 registry 和证据路径都逐级拒绝 symlink 祖先；
后检同时核对最初的逻辑路径是否仍指向原物理路径。目标 facet 从独立私有 inode
以不覆盖现有文件的方式创建，并记录创建者拥有的 inode、device 和 SHA。
所有权记录取自 link 之前的私有临时 inode；不在 link 后读取可能已被另一 writer
替换的目标 pathname 来认领其 inode。单模块
复制失败时立即回滚该模块本次新建文件；整个事务异常时回滚尚未发布的本次新建
文件。回滚不删除预存文件，也不删除已被并发替换或改写的文件。

工具持有 `.lake/p2-private/p24-migration.lock` 的非阻塞排他锁，防止合作的迁移
进程同时执行。实际执行应使用隔离 checkout 的单写者时段，与现有编译 runner
串行安排。最后的 records 比较放在耗时物理检查之后，并紧邻唯一 registry replace。
这封闭了后检期间发生变化的窗口；它不声称为不遵守该锁的其他 writer 提供原子 CAS。

旧的有效目标记录优先保留。目标 registry 中原有的范围外记录按原字节字段保留，
不授予它们本次迁移或 P2.4 验收。

## 证据与边界

每次必须使用不存在的新证据目录。目录保存旧 registry 的原字节副本、目标旧 registry
副本（若存在）及 `MIGRATION.json`。后者记录每个迁移项的原始完整 record、已验证
的旧闭包与 signatures、新 closure signature、逐 facet 传输路径和 SHA，以及物理
输入的前后绑定。新 registry 中的 `verified_cache_migration` 指向该收据及其 SHA。

只有命令成功返回且目标 record 实际携带该指针，才表明 registry 发布完成。
普通异常会撤销本事务未发布的新建目标 facets，私有证据或临时文件可能保留；
如果回滚时发现 inode 或字节已被并发替换，则保留该文件并明确失败。不得仅根据
临时文件或证据存在就接纳。下一次使用新 attempt，并先检查失败原因。

旧记录的编译资格由既有 `verify_compilation` 契约决定。本工具对额外 loadable
facets 声明的是本次旧/新路径的实际字节一致及前后不变，不伪造旧编译时未保存的
逐 facet 历史 hash。已有历史 receipt、job、command 等信息原样保留在原记录中。

该工具只执行版本读取和文件/记录检查，不对 Lean 源码调用编译器、不装载对象、
不执行 kernel replay。迁移成功不是新的严格编译，也不是新的独立证明验收；
后续原 strict runner、独立 leanchecker 和完整声明/axiom 审计仍须照常执行。

## P2 执行方式

在已同步本轮分支源码的独立目录中执行：

```bash
python3 -B verification/part2/p24_migrate_verified_cache.py \
  --project-root /workspace/p2-4-compact-proof-20261125 \
  --donor-root /workspace/p2-private-20261124 \
  --external-snapshot /workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json \
  --out /workspace/p2-4-compact-proof-20261125/.lake/p24-cache-migration/attempt-001
```

本轮只读目录清单表明旧 registry 有 619 条记录，旧 snapshot 有 515 个已 qualified
native providers；这些清单数不是本工具的执行结果。具体可迁移数必须等实际输入复核
后读取命令输出和收据，不能预先声明全部或某个固定数量可复用。

## 本地验证

```bash
python3 -B -m unittest discover -s verification/part2 -p test_p24_migrate_verified_cache.py
```

25 项针对性测试已经通过，使用真实临时文件、真实既有记录 verifier 和模拟编译器
程序；没有运行 Lean 或云端编译。测试覆盖准确迁移、原始记录保留、旧依赖签名或
native 批后检缺失、源码/对象变化、额外 facet、当前不同对象保留、范围外排除、
外部输入及双方 records 并发改变、迟发复制失败和 binding 变换边界。独立审阅提出的
六个反例另行执行并全部通过：有效但不同的父对象、长后检内 registry 变化、嵌套
symlink 越界、部分复制和全局失败意外启用预存旧记录，以及 link 后同字节换 inode
导致误认所有权。永久测试还覆盖完整依赖
facet 一致、回滚保留既有/并发替换文件、独占锁、重复迁移保持 registry 字节不变，
以及原 strict runner 对迁移后 fixture records 的实际缓存复用。

独立 reviewer 已在最终脚本 `a35e726fbb2d5df0d9ad39c6b13e88cee8722eae72549265581c2672f074e238`
和测试 `0ec557a8f29926e3b53b1c401abbeebd3c2fa78104c89802e84d1a719a72de11`
上重跑全部 25 项永久测试及 6 项独立反例，全部通过，复核后 SHA 稳定。
在隔离单写者时段与上述原契约边界内，没有剩余 Critical/Important 问题。
实际 P2 执行仍待完成；本说明不宣称已迁移任何实际证明对象。
