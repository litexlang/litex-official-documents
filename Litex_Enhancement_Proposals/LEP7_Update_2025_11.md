litex 近期更新

1. **函数定义与计算的一致性保证** (Definition-Computation Consistency Guarantee)关键词 algo
    1. https://litexlang.com/doc/Tutorial/Algorithm_Evaluation
2. **prove_algo** 将包含条件检查、计算步骤和推理的证明过程封装成可重用算法，通过 by 调用时执行这些步骤并自动得到结论，实现证明过程的模块化与复用。
    1. 举例：证明某个数是素数，计算方程的根，在litex中定义类lisp的cons关键词
    2. https://litexlang.com/doc/Tutorial/Prove_Algo
3. 卡氏积(有限，无限）cart, cart_product
    1. https://litexlang.com/doc/Tutorial/Set_Theory
4. litex现支持中文、希腊文等非英文字母作为名称
5. 从数学的观点看litex 
    1. https://litexlang.com/doc/Tutorial/Litex_From_A_Mathematical_Perspective
    2. 意在尝试说明litex的严谨性和完备性

虽然一定存在软件上的bug，但litex的功能在工程上已经接近完备。工程归工程，现在litex缺少理论上的解释其严谨性和完备性。欢迎感兴趣的朋友欢迎交流。如果有想一同构建litex标准库、数据集、甚至搭建ai pipeline的朋友，也欢迎联系！：）

how litex verify a fact