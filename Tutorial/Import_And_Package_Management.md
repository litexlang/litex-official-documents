# Import and folderA Management

_The value of an idea lies in the using of it._

_- Thomas Edison_

After writing our own code, we take great pleasure in the joy of coding itself. But even more gratifying is when others can use our code to achieve their own goals—the joy of sharing. Therefore, like Python and other programming languages, Litex supports importing code from other files, making their contents available for use in the current file.

Litex provides two ways to import code from other files:

1. Import a single .lix file
2. Import a folder (which we call a package) containing a main.lix file, along with other .lix files and subdirectories.

## Importing .lix Files

Suppose we have a file a.lix containing the following code:

```litex
let a, b R:
    b > a
```

And we have another file b.lix containing the following code:

```litex
import "a.lix"

b > a
```

The above code works because a.lix has been imported into b.lix, so both a and b are already declared, and b > a holds true. This is equivalent to doing the following:

```litex
let a, b R:
    b > a

b > a
```

You can think of it this way: when you import a .lix file, it's as if the code from the imported file is copied into the current file at that line.

Importing a .lix file can be useful when you want to organize your code into smaller files.

## Importing Folders (Packages)

Suppose we have a folder containing a main.lix file called "folderA" containing the following structure:

```
folderA/
    folderB/
    ├── main.lix
    main.lix
```

In folderB/main.lix, we have the following code:

```litex
let a, b R:
    b > a
```

In folderA/main.lix, we have the following code:

```litex
import "folderB" as pkgB

pkgB::b > pkgB::a
```

When importing a folder, you can use the `as` keyword to give the imported package a name. When using anything in the imported package, you need to use the name of the package followed by `::` and then the name of the object. That is why `pkgB::b > pkgB::a` is true instead of `b > a`.

We call a folder containing a main.lix file a package. When you want to let other people use your code, you can package your code into a folder and share it with them.

## Importing Hierarchical Folders

Suppose we have a folder containing a main.lix file called "folderA" containing the following structure:

```
folderA/
    folderB/
    ├── main.lix
    ├── folderC/
    │   └── main.lix
    ├── fileB.lix
    main.lix
```

In folderC/main.lix, we have the following code:

```litex
let a, b R:
    b > a
```

In folderB/main.lix, we have the following code:

```litex
import "folderC" as pkgC
import ”fileB.lix"

know pkgC::b = 1
```

In folderB/fileB.lix, we have the following code:

```litex
let c R:
    c = 0
```

In folderA/main.lix, we have the following code:

```litex
import "folderB" as pkgB

pkgB::pkgC::b > pkgB::pkgC::a
pkgB::pkgC::b = 1
```

Notice the hierarchical import. When importing a folder, you can import other folders inside it. When using anything in the imported package, you need to use the name of the package followed by `::` and then the name of the object. That is why `pkgB::pkgC::b > pkgB::pkgC::a` is true instead of `b > a`.