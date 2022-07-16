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

struct Rational {    int32_t n, d;
    Rational(auto n, int32_t d = 1): n(n), d(d) {}
};

//typedef char Oper;
enum Oper: char { Num, Add = '+', Sub = '-', Mul = '*', Div = '/' };

struct Expr;
typedef std::shared_ptr<const Expr> PtrE;

struct Expr {   Rational v;
    struct { PtrE a, b; Oper op; };     // anonymous structure

    Expr(auto n): Expr(Rational(n)) {}  // Constructor delegation
    Expr(const Rational& r, Oper op = Num,
        PtrE a = nullptr, PtrE b = nullptr): v(r), a(a), b(b), op(op) {}
    //Expr(): Expr(Rational(0, 0)) {}
    //Expr(const Expr&) = delete;
    //~Expr();

    Expr(auto a, auto b, auto op): v(0), a(a), b(b), op(op) {
        switch (op) {
            case '+': //v = a->v + b->v; break;
                v.n = a->v.n * b->v.d + a->v.d * b->v.n, v.d = a->v.d * b->v.d; break;
            case '-': //v = a->v - b->v; break;
                v.n = a->v.n * b->v.d - a->v.d * b->v.n, v.d = a->v.d * b->v.d; break;
            case '*': //v = a->v * b->v; break;
                v.n = a->v.n * b->v.n, v.d = a->v.d * b->v.d;  break;
            case '/': //v = a->v / b->v; break;
                0 ==  b->v.d ? (v.d = 0) :
               (v.n = a->v.n * b->v.d, v.d = a->v.d * b->v.n); break;
            default: v.d = 0;   // XXX:
        }
    }
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