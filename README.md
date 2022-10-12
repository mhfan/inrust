
![Build status](https://github.com/mhfan/inrust/actions/workflows/rust.yml/badge.svg)
[![codecov](https://codecov.io/gh/mhfan/inrust/graph/badge.svg)](https://codecov.io/gh/mhfan/inrust)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](https://opensource.org/licenses/MIT)

# Rust study project from scratch

A project to accumulate my knowledge about Rust programming and engineering.

## Solve [24 game/puzzle](https://zh.wikipedia.org/wiki/24点) calculation

**经典的 24 点计算**：给定任意 _4 个 1-10 或 1-13_ (扑克牌) 的整数，
使用 `(+, -, *, /)` 四则计算和括号的组合成表达式，使其结果为目标数 _24_；

**泛化的 '24' 点计算**：给定任意个 _有理数_， 使用 `(+, -, *, /)`
四则计算和括号的组合成表达式，使其结果为预先给定的任意 _目标有理数_；

**并且要求**：只输出计算形式/方法/结构上 _唯一/不相同的所有_ 表达式结果；
(all algebraically unique/inequivalent solutions)

    Input integers/rationals for 24: 1 2 3 4
    1*2*3*4
    (1+3)*(2+4)
    4*(1+2+3)

    Input integers/rationals for 24: 8 8 3 3
    8/(3-8/3)

    Input integers/rationals for 24: g100 13 14 15 16 17
    ### Reset GOAL to 100 ###
    16+(17-14)*(13+15)
    (17-13)*(14+15)-16

![24 cards game](assets/24-cards-cmdl.jpg?raw=true)

PS: 用 Yew 框架开发了一个 [在线的交互界面](https://github.com/mhfan/inyew)。

### 自上而下分集计算法 (Top-down divide)

全搜索的 [计算复杂度](http://oeis.org/A140606)：
    `O(n) ~= (2^(n - 1) * 5) * (2^ (n - 2) * 5) * ... * (2^0 * 5)`

_动态规划_ vs _递归分解_

### 自下而上递归构造法 (Bottom-up construct)

全搜索的 [计算复杂度](http://oeis.org/A140606)：
    `O(n) ~= (C^2_n * 5) * (C^2_(n-1) * 5) * ... * (C^2_2 * 5)`

_在位递归构造_ vs _复制递归构造_

### 同样的算法用 C++ 实现并对比性能

C++ 实现的上述前三种算法，在 **(Apple M1, macOS, Clang)** 上性能都比 Rust 的实现 _差 5%_；可能是因为该平台架构上 Rust 的编译器优化得更好？通过 GitHub Action/workflow 的 CI 测试发现，在 **(x86_64, Ubuntu, GCC)** 上 C++ 的实现比 Rust 要 _快 ~5%_。

Rust/C++ 版本前一类算法都比后一类算法性能高一个数量级，个数越多性能差异越大；
但它们在当前的主流 PC 上计算 9-10 个数的时间都难以忍受了；

## Code snippet gems

+ Game guess number
+ single linked list
+ 简单的幂集 (powerset) 算法
+ Fibonacci 数列迭代生成器
+ 流式 Pi 值计算
+ 命令管道

## 积累和 TODO

+ [ ] build timestamp & commit-ID
+ [ ] internationalization (i18n) with [Fluent](https://projectfluent.org)
+ [ ] SVG/UI/WebAssembly/XR/Game
+ [ ] crates.io
+ [ ] CodeLLDB
+ [ ] C++ FFI
+ [x] doc-tests
+ [x] flamegraph
+ [-] concurrency
+ [x] C FFI & build.rs
+ [x] benchmark/criterion
+ [x] Code coverage automatically
+ [x] Continuous Integration/Deployment (Github Action)
+ [x] Continuous (Unit/Integrate/Fuzz) Test
+ [x] cargo/crate/module organization
+ [x] conditional compilation
+ [x] Rust programming

## References

### 24-Game Solver

+ <https://github.com/MaigoAkisame/enumerate-expressions>
+ <https://zhuanlan.zhihu.com/p/34015231>
+ <https://github.com/wiebemarten/gamemn>
+ <https://github.com/auntyellow/24>
+ <https://github.com/mhfan/smonde>
+ <https://4shu.net/theory/>
