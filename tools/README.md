# Markdown TOC 生成工具

多线程生成/更新 Markdown 目录（TOC）。自动在文档中按如下标记维护目录区块：

```text
<!-- TOC START -->
... 自动生成内容 ...
<!-- TOC END -->
```

- 默认在首个 H1 标题后插入；无 H1 则置于文件最前。
- 再次运行会就地更新该区块，非目录内容不被修改。
- 仅处理编号主题目录（如 `1.*`、`2.*` 等）及 `docs/Refactor`，除非使用 --all。

## 快速使用

- 干跑预览（不写文件）：

```bash
python tools/toc_generator.py --max-level 4 --workers 12
```

- 实际写入：

```bash
python tools/toc_generator.py --max-level 4 --workers 12 --apply
```

- 指定路径（可为文件或目录）：

```bash
python tools/toc_generator.py 1.* 2.* docs/Refactor --apply
```

- 不限制目录（全仓库 .md）：

```bash
python tools/toc_generator.py --all --apply
```

## 参数说明

- `paths`：可选。扫描目标，默认当前目录。
- `--max-level`：纳入目录的最大标题层级（1-6），默认 4。
- `--apply`：启用后写回文件；不带时为干跑。
- `--all`：不限制到编号目录与 `docs/Refactor`。
- `--workers`：并发线程数，默认 `CPU 核数`。

## 生成规则

- 标题锚点使用 GitHub 风格 slug，保留 CJK 字符；空白转 `-`，连续连字符折叠。
- 每级标题使用两个空格缩进：

```text
- H1
  - H2
    - H3
```

## 常见问题

- PowerShell 管道与 `cat`：如需显示长输出，直接运行命令即可；不要在 PowerShell 中使用 `| cat`。
- 已存在不完整标记：若发现 `<!-- TOC START -->` 无闭合 `<!-- TOC END -->`，会视为不存在并重新插入。

## 退出码与总结

执行结束会输出统计：处理文件数、变更数、未变更数、错误数，便于批量校验。
