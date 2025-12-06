# Wade 分析学学习项目 (An Introduction to Analysis with Lean)

这个项目用于使用 Lean 4 学习 William R. Wade 的《An Introduction to Analysis》第 4 版。

## 项目结构

```
.
├── lean-toolchain          # Lean 版本配置
├── lakefile.lean          # Lake 项目配置文件
├── Analysis/              # 分析学相关文件
│   ├── Basic.lean        # 第一章：实数系统
│   ├── Sequences.lean    # 第二章：序列
│   └── Functions.lean    # 第三章：函数
└── README.md             # 本文件
```

## 环境设置

### 1. 安装 Lean 4

如果您还没有安装 Lean 4，请按照以下步骤：

**macOS (使用 Homebrew):**
```bash
brew update && brew install elan
elan self update
```

**或者使用官方安装脚本:**
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### 2. 安装 VS Code 和 Lean 扩展

1. 安装 [VS Code](https://code.visualstudio.com/)
2. 在 VS Code 中安装 "Lean 4" 扩展

### 3. 初始化项目

在项目目录中运行：

```bash
cd "/Users/jianweiheng/Documents/wade lean"
lake exe cache get
```

这将下载并缓存 Mathlib（Lean 的数学库）。

### 4. 打开项目

在 VS Code 中打开项目目录，Lean 服务器会自动启动。

## 使用说明

1. 打开 `Analysis/` 目录下的 `.lean` 文件
2. 文件中的代码会实时检查，错误会在编辑器中显示
3. 将鼠标悬停在定理和定义上可以看到类型信息
4. 使用 `Ctrl+Shift+P` (或 `Cmd+Shift+P` on Mac) 打开命令面板，可以执行 Lean 相关命令

## 学习路径

按照 Wade 教材的章节顺序：

1. **第一章：实数系统** - `Analysis/Basic.lean`
2. **第二章：序列** - `Analysis/Sequences.lean`
3. **第三章：函数** - `Analysis/Functions.lean`
4. 后续章节可以继续添加新文件

## 参考资料

- [Lean 4 官方文档](https://leanprover.github.io/lean4/doc/)
- [Mathlib 文档](https://leanprover-community.github.io/)
- [Lean 中文社区](https://www.leanprover.cn/)

## 注意事项

- 确保使用 Lean 4.12.0 版本（在 `lean-toolchain` 中指定）
- Mathlib 版本与 Lean 版本需要匹配
- 如果遇到问题，可以运行 `lake clean` 然后重新运行 `lake exe cache get`

