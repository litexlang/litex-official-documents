# Package

Like other programming language, there is a package system in Litex.

## Import from `.lix` File

If your Litex project maintains following file structure:

```bash
Litex_project
├── main.lix
├── folder
│   └── file_1.lix
└── file_2.lix
```

You can just import other `.lix` file via `import` in file `main.lix`:

```
import "file_2.lix"
import "folder/file_1.lix"
```

In this case, Litex would copy content from other `.lix` file and paste them into your `main.lix` file when Litex start to 

## Build your Litex Package

You can build your own Package by add a `main.lix` file into each folder:

```bash
Litex_Package
├── main.lix
├── folder_1
│   ├── main.lix
│   ├── folder_2
│   │   ├── main.lix
│   │   └── file_1.lix
│   ├── file_2.lix
│   └── file_3.lix
└── file_4.lix
```

Litex will search every `main.lix` file when you import your package.

## Import from Litex Package

If your Litex project maintains following file structure:

```bash
Litex_project
├── main.lix
├── Litex_Package
│   ├── main.lix
│   ├── folder_1
│   │   ├── main.lix
│   │   ├── file_1.lix
│   │   ├── file_2.lix
│   ├── folder_2
│   │   └── main.lix
│   │   └── file_3.lix
│   └── file_4.lix
└── file_5.lix
```

You can import Litex Package via `import` and `::`:

```
import "Litex_Package"
import "Litex_Package::folder_2"
```

To use anything form Package, you should use `::` to help Litex to locate which path it should be:

```
Litex_Package::obj_1
Litex_Package::folder_1::prop_1

folder_2::prop_2
```

> Note: `import` only support Obejects or Propositions or anything that in `main.lix`, you should import other `.lix` file into `main.lix` of each level so that you could use them directly.

## Rename Package when Importing

Different author names Package with different rules. You may want to rename Packages when importing them. You need `as`:

```
import "Litex_Package" as p
import "Litex_Package::folder_2" as f

p::obj_1
p::folder_1::prop_1

f::prop_2
```