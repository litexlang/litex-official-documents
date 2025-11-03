# Import

_The most fundamental problem in software development is complexity. There is only one basic way of dealing with complexity: divide and conquer._

_— Bjarne Stroustrup_

It is important to break down a complex project into independent parts. For example, when a file becomes too long, we can split it into several independent files for easier reading.

Another benefit of doing this is that it facilitates collaboration among multiple people. In programming, users package their code and share it with others. This allows others to directly use these packages and build their own projects based on the tools within these packages, without having to build everything from scratch. The same applies to mathematics. If someone has already formalized mathematical knowledge into litex code, we can use it directly (provided we assume their code is accurate). Therefore, just like Python, a package management system is an important component of Litex. This allows us to share the code we write and use code written by others.

Litex has two ways to import: import a folder containing `main.lit` (which we call a package), or import a `.lit` file. The two have different usage:


## Import A File

Importing a file typically occurs when working on a large Litex project (for example, when formalizing a mathematics textbook). If we write all the code in a single document, it will be very long. A better approach is to import individual sub-files sequentially in one file (for example, `main.lit`). Just like a book with 5 chapters, we can place the Litex code for each chapter in `chap1.lit`, `chap2.lit`, `chap3.lit`, `chap4.lit`, `chap5.lit` respectively, and then import them in `textbook.lit`, as shown below:

```
# textbook.lit
import "chap1.lit"
import "chap2.lit"
import "chap3.lit"
import "chap4.lit"
import "chap5.lit"
```

It is equivalent to doing the following things:

```
line1_of_chap1
line2_of_chap1
..
final_line_of_chap1
line1_of_chap2
...
final_line_of_chap2
...
line1_of_chap1
...
final_line_of_chap5
```

This is equivalent to copying and pasting the contents of these `.lit` files one by one into the `textbook.lit` file, and then running them from front to back. Essentially, you could also put all the content in a single file `textbook.lit`, but the benefit of separating them is that it makes the entire project clearer. If you want to read a specific chapter, you can directly open the relevant `.lit` file.

## Import A Package(Folder)

When you install litex on your machine, there will be folder `~/litexlang/user_pkg` and `~/litexlang/std_pkg` on your machine. `~/litexlang/std_pkg` is the folder containing many folders ranging from number theories to basic set theory, maintained by the Litex team. `~/litexlang/user_pkg` contains folders (packages) you download using `lip install package_name` command. When you want to import a package without publishing it to the `lip` system, you can copy your folder into the  `~/litexlang/user_pkg` and use it as if you are using a package installed by `lip install`.

(`lip` works very much the same as how `pip` works for python.)

```
import "PACKAGE_NAME"
```

Example:

```
import "nat"  # nat is a standard package in `~/litexlang/std_pkg`
import "some_package_installed_by_lip" # When you type `lip install some_package_installed_by_lip`, some_package_installed_by_lip is installed to ~/litexlang/user_pkg
```

Now you use `PKGNAME::NAME` to use anything with name `NAME` in the `PKGNAME` in your current code. (It works like C++ or Rust.). `PKGNAME` is the folder name in `~/litexlang/user_pkg`, i.e. `xxx` in the `lip install xxx` command.

Example

```
# suppose there is a proposition called prop1 in pkg1, an object called obj2 in pkg2
import "pkg1"
import "pkg2"

$pkg1::prop1(pkg2::obj2)
```

Note: There cannot be packages (folders) with the same name in `~/litexlang/user_pkg` and `~/litexlang/std_pkg`, otherwise it will cause conflicts.