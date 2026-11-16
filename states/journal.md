# Hermes Journal（追加式，每任务 ≤5 行）


<!-- TOC START -->

- [Hermes Journal（追加式，每任务 ≤5 行）](#hermes-journal追加式每任务-5-行)
  - [2026-11-17 初始化（Kimi Code CLI）](#2026-11-17-初始化kimi-code-cli)
  - [2026-11-17 用户决策：四项依赖挂起](#2026-11-17-用户决策四项依赖挂起)

<!-- TOC END -->

## 2026-11-17 初始化（Kimi Code CLI）

- 项目切换至 hermes 持续推进模式：运行手册 `docs/hermes-runbook.md`，任务队列 `states/task-queue.yaml`（13 个任务：P0×3 / P1×7 / P2×3，PARKED×2）。
- 基线：活库 636 md（A329/B175/C132 豁免），归档 349；gate PASS；integrity_check 脚本已建。
- 历史事故备案：两波工作树文件失踪（246 归档 + docs 3 件）已从 git 恢复，零丢失；疑与 E:\_src 同步盘/安全软件有关，待用户排查。
- 用户依赖（blockers）：WSL 工具链、UPPAAL 许可证、GPU 端点配置、OneDrive 排查。
- 下轮 loop 建议起始：T-BREVIEW（若 GPU 就绪）或 T-R10 / T-R7-REST（纯 CPU 可先行）。

## 2026-11-17 用户决策：四项依赖挂起

- 挂起：WSL Coq/Isabelle、UPPAAL 许可证、GPU 端点配置、E:\_src 同步盘排查。
- 应对：T-BREVIEW 改两阶段（先 CPU 粗筛+hermes 精读，GPU 就绪后补语义复核）；形式化工件先出 draft 或本机可验子集（SMT/Z3）；integrity_check 维持失踪防线。
- 纪律：hermes 每轮不升级挂起项提醒，仅用户主动重启。
## 2026-11-17 配置一致性整理

- 新建根 AGENTS.md（与 README/治理规则/hermes 手册互指，含豁免清单 canonical 与脚本常量定位）。
- 修复全部失效 TOC CLI 引用：README.md、8 个域 README、.githooks/pre-commit 提示语；统一为 `toc_generator.py --all --apply .` / `toc_validate.py --all .`。
- README 工具指南增补质量审计三件套（audit/gate/integrity）；ci_toc_check.ps1 经核实本就使用真实 CLI，未改。
- 验证：toc_validate 987 文件 0 失败；integrity 干净；gate PASS。
- 补丁：AGENTS.md 加入审计豁免（EX_FILES），gate 复跑 PASS。
