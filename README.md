
# Rust study project from the scratch

## Solve 24 computation

_经典的 24 点计算_：给定任意 4 个 1-10 的整数，使用 ('+', '-', '*', '/') 四则计算和括号的组合成表达式，使其结果为目标数 24；

_泛化的 `24' 点计算_：给定任意个有理数，使用 ('+', '-', '*', '/') 四则计算和括号的组合成表达式，使其结果为预先给定的任意有理数；

_并且要求_：输出计算形式/方法/结构上不相同的所有表达式结果；

### (自上而下) 分集计算法

动态规划 vs 递归算法

### (自下而上) 递归构造法

在位递归构造 vs 复制递归构造

### 同样的算法用 C++ 实现并对比性能

用 C++ 实现了 上述前三种算法，性能都不如 Rust 的实现；是因为 Rust 编译器优化得更好？

## Game guess number

## Code snippet gems

+ 简单的幂集 (powerset) 算法
+ 流式 Pi 值计算
+ 命令管道

# 积累和 TODO

+ Continuous Integration (Github Action)
+ build timestamp & commit-ID
+ internationalization (i18n)
+ SVG/UI/WebAssembly/XR/Game
+ docs & playround
+ Code coverage
+ crates.io
+ CodeLLDB
+ C++ FFI

- flamegraph
- C FFI & build.rs
- benchmark/criterion
- Continuous (Unit/Integrate/Fuzz) Test
- cargo/crate/module organization
- conditional compilation
- Rust programming

# References
