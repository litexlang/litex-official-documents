# Import and Package Management

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