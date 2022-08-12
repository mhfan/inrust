/****************************************************************
 * $ID: comp24.h         二, 21  6 2022 14:05:39 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 *                                                              *
 * Copyright (c) 2022 M.H.Fan, All Rights Reserved.             *
 *                                                              *
 * Last modified: 二, 21  6 2022 14:07:41 +0800       by mhfan #
 ****************************************************************/

#ifndef COMP24_H
#define COMP24_H

#include <cstdint>
#include <memory>   // shared_ptr

template <typename T> struct RNum { T n, d; RNum(auto n, T d = 1): n(n), d(d) {} };
typedef RNum<int32_t> Rational;

//typedef char Oper;
enum Oper: char { Num, Add = '+', Sub = '-', Mul = '*', Div = '/' };

struct Expr;
typedef std::shared_ptr<const Expr> PtrE;

struct Expr {
    Rational v; PtrE a, b; Oper op;     // anonymous structure

    Expr(auto n): Expr(Rational(n)) {}  // Constructor delegation
    Expr(const Rational& r, Oper op = Num,
         const PtrE& a = nullptr, const PtrE& b = nullptr): v(r), a(a), b(b), op(op) {}
    //Expr(): Expr(Rational(0, 0)) {}
    //Expr(const Expr&) = delete;
    //~Expr();
};

#include <vector>
using std::vector;

typedef   enum Comp24Algo: uint8_t { DynProg, SplitSet, Inplace, Construct } Comp24Algo;
typedef struct Comp24 {
    const Comp24Algo algo; bool ia;
    const Rational goal, *const nums;
    const size_t ncnt;

    size_t ecnt;
    const char* *exps;
    //const PtrE const *exps;
    //const Expr* const *exps;
}   Comp24;

extern "C" void comp24_algo(Comp24* comp24);

#endif

// vim:sts=4 ts=8 sw=4 noet