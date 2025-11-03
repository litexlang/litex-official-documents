# Import

_

把一个复杂的工程分拆成独立的部分是重要的。比如，当我们一个文件太长了，我们就可以把它拆分成几个独立的文件，这样方便阅读。

这样做的另外一个好处是适合多人协作。编程中，用户通过把一些代码打包，分享出去。这样其他人就能直接拿来这些包，基于这些包里面的工具做自己的项目，而无需自己从头搭建。数学也一样。很多数学知识别人如果已经形式化成litex代码了，那就可以拿来直接用（前提是我们默认对方的代码是准确的）。所以和python一样，包管理系统是litex的重要组成部分。这样我们能分享自己写的代码，使用他人写好的代码。

Litex有两种import方式：import 一个含有main.lit的文件夹（我们称之为包），或import一个lit文件。二者用不同的用法：


## Import A File

import 文件通常发生在，当我自己在做一个大型litex工程时（比如我在形式化一本数学书），我如果把所有代码写在一个文档里，这会很长。更好的做法是，在一个文件里（比如main.lit）中，按顺序import一个个子文件。就好比一本书有5个章节，我把各个章节的litex代码分别放在 chap1.lit, chap2.lit, chap3.lit, chap4.lit, chap5.lit 里，然后在 textbook.lit 中import它们，具体写法如下:

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

这么做相当于，把这些.lit文件里的内容一一复制黏贴到 textbook.lit 文件里，然后从前往后运行。本质上你也可以把所有内容放在一个文件textbook.lit里，但这样分开写的好处是，让整个项目看起来更清晰。如果想读第几个chap，直接进入相关的 .lit 文件就行

