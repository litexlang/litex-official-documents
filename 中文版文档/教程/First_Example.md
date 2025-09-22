# 第一个示例

_"如果你正确定义了问题，你几乎就有了解决方案。"_
_— 史蒂夫·乔布斯_

数学是从既定事实中推导新事实的艺术。为了说明这一点，让我们从亚里士多德提出的经典三段论开始，它形式化了演绎推理。

这个例子说明：**所有人都是聪明的。乔丹是人。因此，乔丹是聪明的。**

```litex
have human nonempty_set, Jordan human
prop intelligent(x human)
know forall x human => $intelligent(x)
$intelligent(Jordan)
```

让我们逐步解析：

* `human` 被定义为所有人类的集合，它不是空的。
* 我们定义一个命题 `intelligent`，它适用于 `human` 的任何元素。
* 使用 `know`，我们建立普遍事实：所有人都是聪明的。
* 最后，当我们问 `Jordan` 是否聪明时，Litex 自动应用**匹配和替换**。

内核查看普遍事实 `forall x human => $intelligent(x)`，将 `x` 替换为 `Jordan`，并检查结果是否成立。由于 `Jordan ∈ human`，语句 `$intelligent(Jordan)` 被验证为真。

事实语句以 `$` 为前缀，以区别于函数。当事实语句恰好接受两个对象时，您可以写 `object1 $propName object2`。对于像 `=`、`>` 等内置命题，您不必写 `$`。

### 语句的结果

在 Litex 中，每个语句都有四种可能的结果之一：**真、假、未知或错误**。当您运行上述代码时，Litex 将打印一条消息，显示它如何验证语句。

您会看到 `$intelligent(Jordan)` 是通过将普遍事实 `forall x human => $intelligent(x)` 应用到 `Jordan` 的具体情况而建立的。在这种情况下，`forall x human => $intelligent(x)` 与 `$intelligent(Jordan)` 匹配，我们可以在普遍事实中将 `x` 替换为 `Jordan` 来得到 `$intelligent(Jordan)`。

这是**匹配和替换的经典示例**——人们推导新事实的最基本方式。在进入下一节时请记住这一点。
