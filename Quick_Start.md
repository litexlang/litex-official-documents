# Quick Start

## Run Litex Online

To quickly get a taste of Litex, you can try it directly in our [Playground](https://litexlang.com/playground/syllogism). You can even translate your Litex code into LaTeX code there.

## Install and Run Litex Locally

We will introduce how to install Litex on your local machine.

### Install Litex on Mac

We recommend macOS users to install Litex by Homebrew with following command:

```bash
brew install litexlang/tap/litex
```

For *upgrading* Litex to the latest version, please use following command:

```bash
brew reinstall litex
```

### Install Litex on Linux

For Ubuntu/Debian users, please paste following command to your terminal:

```bash
wget https://github.com/litexlang/golitex/releases/download/0.1.11-beta/litex_0.1.11-beta_amd64.deb
sudo dpkg -i litex_0.1.11-beta_amd64.deb
```

### Install Litex on Windows

For Windows users, please download MSI file form [**HERE**](https://github.com/litexlang/golitex/releases/download/0.1.11-beta/litex_0.1.11-beta_amd64.msi)

### Run Litex on your machine

Run `litex` on your terminal

```bash
litex
```

You would see next lines, which means you've installed Litex successfullly!

```bash
Litex-beta - Type your code or 'exit' to quit
Warning: not yet ready for production use.
>>> 
```

### Litex Command Options

Besides typing `litex` in your terminal, Litex provides multiple ways to run, depending on your needs:

| Flag        | Example usage                      | Description |
|-------------|------------------------------------|-------------|
| `--help`    | `litex --help`                     | Show the help message with all available command-line options. |
| `--version` | `litex --version`                  | Display the currently installed Litex version. |
| `-e`        | `litex -e "1 + 2 = 3"`                 | Execute the given Litex code directly. |
| `-f`        | `litex -f example.litex`           | Execute a Litex source file. |
| `-r`        | `litex -r my-repo`                 | Execute Litex code from a given repository. |
| `--latex`   | `litex --latex example.litex`      | Compile the given file into LaTeX output. |

## Run Litex in Python

We hope Litex can play an important role in the future of AI. Litex is user-friendly for AI developers. You can use Litex in your Python code by installing `pylitex` package. Follow steps in [pylitex](https://github.com/litexlang/pylitex) to get started.

### Warning: Install litex locally before using `pylitex` to run litex in your python environment. Remember to update your local litex from time to time.

```bash
# remember to install Litex (Visit https://litexlang.com/doc/Quick_Start for more details) to your machine before install pylitex
# change your Python env to which your are using
# then run following commands
pip install pylitex
```

pylitex is under development, update it to the latest version:

```bash
pip install -U pylitex
```

## Run Litex in Jupyter Notebook

One of the greatest strengths of Jupyter Notebook is the seamless integration of documentation, code, and visualizations. This makes Jupyter Notebook a perfect fit for the Litex workflow. With it, you can write mathematical documents, execute Litex code to verify reasoning, and even present results visually. It brings mathematical expression, logical verification, and visualization together in a single, elegant environment, greatly enhancing both productivity and readability.

Visit [litex-jupyter-kernel](https://github.com/litexlang/litex-jupyter-kernel) to get started.
