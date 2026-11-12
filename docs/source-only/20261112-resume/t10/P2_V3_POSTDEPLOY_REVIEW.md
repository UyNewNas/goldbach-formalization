# P2 R2 驱动发表核验

将先前清单允许的 25 个 blob 独立代入父提交 `356c3782e9428098a2fcbfb18c689bef264d84fa` 的 Git 树，重新按 Git tree 对象格式计算出的完整根树为 `1c9643bdb178a2f9c2f8c28a218c79055cf9212f`。远端 commit、唯一父头、分支 ref、三个未截断的子树与这个结果一致。25 个路径的本地 payload 均已逐字节再核 SHA-256、raw Git blob 和长度，总计 241,459 字节。其中六个继承工作流保留各自原 blob，VE 只加了精确分支排除。独审源清单为 `06c0ec79843935f339e33fd998b25391a005eaa879ac59538b4bdcd7f91b6898`，根发表收据为 `9c623d4265948a57d45167dd0619e214ef300127654d55de82d43bb591ce3d3f`。 [实际提交](https://github.com/UyNewNas/goldbach-formalization/commit/384d2d9070b3af90d95933e08eef964f7b1f7a64)

精确 head 的初始 Actions 快照列出一个 pending 作业运行 43157098719。这份结果覆盖驱动发表。本收据未观察该运行的编译、kernel、声明／公理或最终验收结果。 [远端运行](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43157098719)
