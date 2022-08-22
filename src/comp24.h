/****************************************************************
 * $ID: calc24.h         二, 21  6 2022 14:05:39 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 *                                                              *
 * Copyright (c) 2022 M.H.Fan, All Rights Reserved.             *
 *                                                              *
 * Last modified: 二, 21  6 2022 14:07:41 +0800       by mhfan #
 ****************************************************************/

#ifndef CALC24_H
#define CALC24_H

#include <cstdint>
#include <memory>   // shared_ptr

template <typename T> struct RNum { T n, d; RNum(auto n, T d = 1): n(n), d(d) {} };
typedef RNum<int32_t> Rational;

//typedef char Oper;
enum Oper: char { Num, Add = '+', Sub = '-', Mul = '*', Div = '/', };

struct Expr;
typedef std::shared_ptr<const Expr> PtrE;

struct Expr {
    Rational v; PtrE a, b; Oper op;     // anonymous structure

    Expr(auto n): Expr(Rational(n)) {}  // Constructor delegation
    Expr(const Rational& r, Oper op = Num,  // a & b refer to left & right operands
         const PtrE& a = nullptr, const PtrE& b = nullptr): v(r), a(a), b(b), op(op) {}

    //Expr(): Expr(Rational(0, 0)) {}
    //Expr(const Expr&) = delete;
    //~Expr();
};

#include <vector>
using std::vector;

typedef   enum Calc24Algo: uint8_t { DynProg, SplitSet, Inplace, Construct } Calc24Algo;
typedef struct Calc24IO {
    const Calc24Algo algo; bool ia;
    const Rational goal, *const nums;
    const size_t ncnt;

    size_t ecnt;
    const char* *exps;
    //const PtrE const *exps;
    //const Expr* const *exps;
}   Calc24IO;

extern "C" void calc24_algo(Calc24IO* calc24);

#endif//CALC24_H

// vim:sts=4 ts=8 sw=4 noet