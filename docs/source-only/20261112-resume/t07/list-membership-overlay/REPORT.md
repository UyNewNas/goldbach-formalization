# 两处 List 首元素成员证明的安装选版

根库钉定 leanprover/lean4 v4.33.0-rc1。其 src/Init/Data/List/Lemmas.lean 第 367 行将元素与尾列表均声明为隐式参数。独立核对的原文件为 152635 字节，SHA256 为 0724ebc7c72c87ad6d480dba407c43cc60393e7a0facfbaa6670045f66f636ac。T09 还将其对到 commit 62eed1db4d67327ec8120be05f1a1b0847d74561 的同一 Git blob。

ClassicalClampLongCredit 第 39 行证明外前缀出现于原 rootHistory。ClassicalFixedClampGeometry 第 27 行证明首素数属于头部列表。两处改为直接使用 List.mem_cons_self，让原预期类型给出这两个参数。各选版仅删四个 ASCII 字节。全部声明、剩余证明及两个先前冻结源保留原字节。REGISTRY 记载逐文件 pre/post SHA256、Git blob、原路径和安装路径。选版未执行本地或远端编译。
