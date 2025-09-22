# 开始

## 在线试用 Litex

要快速体验 Litex，您可以直接在我们的 [游乐场](https://litexlang.com/playground/syllogism) 中试用。您甚至可以在那里将您的 Litex 代码翻译成 LaTeX 代码。

## 本地运行 Litex

我们将介绍如何在您的本地机器上安装 Litex。

### 在 Mac 上安装 Litex

我们推荐 macOS 用户通过 Homebrew 使用以下命令安装 Litex：

```bash
brew install litexlang/tap/litex
```

要升级 Litex，请使用以下命令：

```bash
brew upgrade litexlang/tap/litex
```

### 在 Linux 上安装 Litex

对于 Ubuntu/Debian 用户，请将以下命令粘贴到您的终端：

```bash
wget https://github.com/litexlang/golitex/releases/download/0.1.11-beta/litex_0.1.11-beta_amd64.deb
sudo dpkg -i litex_0.1.11-beta_amd64.deb
```

### 在 Windows 上安装 Litex

对于 Windows 用户，请从 [**这里**](https://github.com/litexlang/golitex/releases/download/0.1.11-beta/litex_0.1.11-beta_amd64.msi) 下载 MSI 文件

### 在您的机器上运行 Litex

在您的终端中运行 `litex`

```bash
litex
```

您会看到以下行，这意味着您已成功安装 Litex！

```bash
Litex-beta - Type your code or 'exit' to quit
Warning: not yet ready for production use.
>>> 
```

### Litex 命令选项

除了在终端中输入 `litex` 外，Litex 还提供多种运行方式，取决于您的需求：

| 标志        | 示例用法                      | 描述 |
|-------------|------------------------------------|-------------|
| `--help`    | `litex --help`                     | 显示帮助信息以及所有可用的命令行选项。 |
| `--version` | `litex --version`                  | 显示当前安装的 Litex 版本。 |
| `-e`        | `litex -e "1 + 2 = 3"`                 | 直接执行给定的 Litex 代码。 |
| `-f`        | `litex -f example.litex`           | 执行 Litex 源文件。 |
| `-r`        | `litex -r my-repo`                 | 从给定仓库执行 Litex 代码。 |
| `--latex`   | `litex --latex example.litex`      | 将给定文件编译成 LaTeX 输出。 |

## 在 Python 中运行 Litex

我们希望 Litex 能在 AI 的未来中发挥重要作用。Litex 对 AI 开发者友好。您可以通过安装 `pylitex` 包在 Python 代码中使用 Litex。按照 [pylitex](https://github.com/litexlang/pylitex) 中的步骤开始。

## 在 Jupyter Notebook 中运行 Litex

Jupyter Notebook 的最大优势之一是文档、代码和可视化的无缝集成。这使得 Jupyter Notebook 成为 Litex 工作流程的完美选择。有了它，您可以编写数学文档，执行 Litex 代码来验证推理，甚至可视化地呈现结果。它将数学表达、逻辑验证和可视化结合在一起，在一个优雅的环境中，大大提高了生产力和可读性。

访问 [litex-jupyter-kernel](https://github.com/litexlang/litex-jupyter-kernel) 开始。
