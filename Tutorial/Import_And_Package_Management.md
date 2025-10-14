# Import and Package Management

_The value of an idea lies in the using of it._

_- Thomas Edison_

After writing our own code, we take great pleasure in the joy of coding itself. But even more gratifying is when others can use our code to achieve their own goals—the joy of sharing. Therefore, like Python and other programming languages, Litex supports importing code from other files, making their contents available for use in the current file.

Litex provides two ways to import code from other files:

1. Import a single .lit file
2. Import a folder (which we call a package) containing a main.lit file, along with other .lit files and subdirectories.

## Importing .lit Files

Suppose we have a file a.lit containing the following code:

```litex
let a, b R:
    b > a
```

And we have another file b.lit containing the following code:

```litex
import "a.lit"

b > a
```

The above code works because a.lit has been imported into b.lit, so both a and b are already declared, and b > a holds true. This is equivalent to doing the following:

```litex
let a, b R:
    b > a

b > a
```

You can think of it this way: when you import a .lit file, it's as if the code from the imported file is copied into the current file at that line.

Importing a .lit file can be useful when you want to organize your code into smaller files.

## Importing Folders (Packages)

Suppose we have a folder containing a main.lit file called "folderA" containing the following structure:

```
folderA/
    folderB/
    ├── main.lit
    main.lit
```

In folderB/main.lit, we have the following code:

```litex
let a, b R:
    b > a
```

In folderA/main.lit, we have the following code:

```litex
import "folderB" as pkgB

pkgB::b > pkgB::a
```

When importing a folder, you can use the `as` keyword to give the imported package a name. When using anything in the imported package, you need to use the name of the package followed by `::` and then the name of the object. That is why `pkgB::b > pkgB::a` is true instead of `b > a`.

We call a folder containing a main.lit file a package. When you want to let other people use your code, you can package your code into a folder and share it with them.

## Importing Hierarchical Folders

Suppose we have a folder containing a main.lit file called "folderA" containing the following structure:

```
folderA/
    folderB/
    ├── main.lit
    ├── folderC/
    │   └── main.lit
    ├── fileB.lit
    main.lit
```

In folderC/main.lit, we have the following code:

```litex
let a, b R:
    b > a
```

In folderB/main.lit, we have the following code:

```litex
import "folderC" as pkgC
import ”fileB.lit"

know pkgC::b = 1
```

In folderB/fileB.lit, we have the following code:

```litex
let c R:
    c = 0
```

In folderA/main.lit, we have the following code:

```litex
import "folderB" as pkgB

pkgB::pkgC::b > pkgB::pkgC::a
pkgB::pkgC::b = 1
```

Notice the hierarchical import. When importing a folder, you can import other folders inside it. When using anything in the imported package, you need to use the name of the package followed by `::` and then the name of the object. That is why `pkgB::pkgC::b > pkgB::pkgC::a` is true instead of `b > a`.