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
#include <memory>

struct Rational {       int32_t n, d;
    Rational(int32_t n, int32_t d = 1): n(n), d(d) {}
};

//typedef char Oper;
enum Oper: char { Num, Add = '+', Sub = '-', Mul = '*', Div = '/' };

struct Expr;
typedef std::shared_ptr<const Expr> PtrE;

struct Expr {   Rational v;
    struct { Oper op; PtrE a, b; };     // anonymous structure

    Expr(auto n): Expr(Rational(n)) {}  // Constructor delegation
    Expr(const Rational& r, Oper op = Num,
        PtrE a = nullptr, PtrE b = nullptr): v(r), op(op), a(a), b(b) {}
    //Expr(): Expr(Rational(0, 0)) {}
    //Expr(const Expr&) = delete;

    //~Expr() { std::cerr << "Destruct: " << *this << std::endl; }

    Expr(auto a, auto op, auto b): v(0), op(op), a(a), b(b) {
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
            default: ;
        }
    }
};

#include <vector>
using std::vector;

#ifdef  USE_LIST
#include <list>
using std::list;
#else
#define list vector // XXX:
#endif

list<PtrE> comp24_dynprog (const Rational& goal, const vector<PtrE>& nums);
list<PtrE> comp24_splitset(const Rational& goal, const vector<PtrE>& nums);

#include <unordered_set>
void comp24_construct(const Rational& goal, const size_t n,
    vector<PtrE>& nums, std::unordered_set<PtrE>& exps);

#endif

// vim:sts=4 ts=8 sw=4 noet