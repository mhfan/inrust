//#!/usr/bin/tcc -run
/****************************************************************
 * $ID: calc24.cpp       二, 21  6 2022 14:05:39 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 *                                                              *
 * Copyright (c) 2022 M.H.Fan, All Rights Reserved.             *
 *                                                              *
 * Last modified: 四, 29  9 2022 14:42:33 +0800       by mhfan #
 ****************************************************************/

// https://changkun.de/modern-cpp/zh-cn/00-preface/

#include <string>
#include <cassert>
#include <iostream>
#include <algorithm>

#ifndef CALC24_H
#define CALC24_H
//#pragma once

#include <cstdint>
#include <memory>   // shared_ptr

template <typename T> struct RNum { T n, d; RNum(auto n, T d = 1): n(n), d(d) {} };
typedef RNum<int32_t> Rational;     // int32_t/int64_t/BigInt

enum Oper: char { Num, Add = '+', Sub = '-', Mul = '*', Div = '/', };
//typedef char Oper;    // XXX: '*' -> '×' ('\xD7'), '/' -> '÷' ('\xF7')

struct Expr;
typedef std::shared_ptr<Expr> PtrE;     //const Expr* PtrE;     // TODO:
struct Expr {   Rational v; PtrE a, b; Oper op;     // anonymous structure  // const

    Expr(const Rational& r, const Oper op = Num,
         const PtrE& a = nullptr, const PtrE& b = nullptr):
            v(std::move(r)), a(a), b(b), op(op) {}  // a & b refer to left & right operands
    //~Expr() { std::cerr << "Destruct: " << *this << std::endl; }

    //Expr(auto n): Expr(Rational(n)) {}  // Constructor delegation
    //Expr(): Expr(Rational(0, 0)) {}
    //Expr(const Expr&) = delete;
    //Expr(Expr&&) = delete;
};

#include <vector>
using std::vector;

typedef   enum Calc24Algo: uint8_t { DynProg, SplitSet, Inplace, Construct } Calc24Algo;
typedef struct Calc24IO {
    const Calc24Algo algo;
    const Rational goal, *const nums;
    const size_t ncnt;

    size_t ecnt;
    const char* *exps;
    //const PtrE* const exps;
    //const Expr* const *exps;
}   Calc24IO;

extern "C" void calc24_cffi(Calc24IO* calc24);

#else
#include "calc24.h"
#endif//CALC24_H

/* inline auto operator+(const Rational& lhs, const auto& rhs) noexcept {
    return Rational(lhs.n * rhs.d + lhs.d * rhs.n, lhs.d * rhs.d); }
inline auto operator-(const Rational& lhs, const auto& rhs) noexcept {
    return Rational(lhs.n * rhs.d - lhs.d * rhs.n, lhs.d * rhs.d); }
inline auto operator*(const Rational& lhs, const auto& rhs) noexcept {
    return Rational(lhs.n * rhs.n,  lhs.d * rhs.d); }
inline auto operator/(const Rational& lhs, const auto& rhs) noexcept {
    return 0 == rhs.d ? Rational(0, 0) : Rational(lhs.n * rhs.d,  lhs.d * rhs.n); } */

inline auto operator< (const Rational& lhs, const Rational& rhs) noexcept {
    return lhs.n * rhs.d < lhs.d * rhs.n; }
inline auto operator==(const Rational& lhs, const Rational& rhs) noexcept {
    return /*lhs.d != 0 && rhs.d != 0 && */lhs.n * rhs.d == lhs.d * rhs.n;
}

auto operator< (const Expr& lhs, const Expr& rhs) noexcept {
    auto lv = lhs.v.n * rhs.v.d, rv = lhs.v.d * rhs.v.n;
    if (lv  < rv) return true;
    if (lv == rv && rhs.op != Num) {
        if (lhs.op == Num) return true;
        if (*lhs.a < *rhs.a) return true;
        if (lhs.a->v == rhs.a->v) {
            if (lhs.a->op  < rhs.a->op) return true;
            if (lhs.a->op == rhs.a->op) return *lhs.b < *rhs.b;
        }
    }   return false;
}

/* inline auto operator+(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v + rhs.v, Add, &lhs, &rhs); }
inline auto operator-(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v - rhs.v, Sub, &lhs, &rhs); }
inline auto operator*(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v * rhs.v, Mul, &lhs, &rhs); }
inline auto operator/(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v / rhs.v, Div, &lhs, &rhs); }

// for implicit use in unordered_set
inline auto operator==(const PtrE& lhs, const PtrE& rhs) noexcept { return *lhs == *rhs; }
inline auto operator==(const Expr& lhs, const Expr& rhs) noexcept {
    if (lhs.op != rhs.op) return false; else
    if (lhs.op == Num) return lhs.v == rhs.v; else
        return lhs.op == rhs.op && lhs.a == rhs.a && lhs.b == rhs.b;
} */

#include <sstream>
using std::ostream; //, std::istream;

//inline istream& operator>>(istream& is, Rational& r) { return is >> r.n >> r.d; }
inline ostream& operator<<(ostream& os, const Rational& r) {
    return (1 == r.d && 0 <= r.n) ? os << r.n : os << '(' <<  r.n << '/' << r.d << ')';
}

ostream& operator<<(ostream& os, const Expr& e) {
    if (e.op == Num) return os << e.v;  //assert(e.a && e.b);

    if ((e.a->op == Add || e.a->op == Sub) && (e.op == Mul || e.op == Div))
        os << '(' << *e.a << ')'; else os << *e.a;      os << char(e.op);

    if ((e.op == Div && (e.b->op == Mul || e.b->op == Div)) ||
        (e.op != Add && (e.b->op == Add || e.b->op == Sub)))
        os << '(' << *e.b << ')'; else os << *e.b;  return os;
}

inline auto hash_combine(size_t lhs, auto rhs) {
  return lhs ^ (rhs + 0x9e3779b9 + (lhs << 6) + (lhs >> 2));
}

template <> struct std::hash<Expr> {
    auto operator()(const Expr& e) const noexcept {
        if (e.op == Num) return hash_combine(e.v.n, e.v.d); else {  // XXX:
            return hash_combine((*this)(*e.a), (*this)(*e.b)) ^ (char(e.op) << 11);
        }
    }
};

static const std::hash<Expr> hash_expr;
#define make_ptre(args...) std::make_shared<Expr>(args)     // XXX: PtrE(ep)

inline bool found_same(const auto& e, const auto& v, const Oper op) {
    return e.op == op && (e.a->v == v || e.b->v == v ||
        found_same(*e.a, v, op) || found_same(*e.b, v, op));
}

// several pruning rules to find inequivalent/unique expressions only
void form_compose(const auto& a, const auto& b, bool is_final, bool ngoal, auto&& new_expr) {
    // ((A . B) . b) => (A . (B . b)), kept right sub-tree only
    const auto nmd = a->v.n * b->v.d, dmn = a->v.d * b->v.n;
    const auto dmd = a->v.d * b->v.d;   Oper op;
    // XXX: check overflow and reduce?

    // ((A / B) * b) => ((A * b) / B), (a * (A / B)) => ((a * A) / B) if a != 1
    // (1 * x)  is only kept in final, (a * (A * B)) => (A * (a * B)) if A  < a
    if (!(a->op == (op = Mul) || a->op == Div || (Div == b->op && a->v.n != a->v.d) ||
        (!is_final && (a->v.n == a->v.d || b->v.n == b->v.d)) || (op == b->op && *b->a < *a)))
        new_expr(Expr(Rational(a->v.n * b->v.n, dmd), op, a, b));

    // ((A - B) + b) => ((A + b) - B), (a + (A - B)) => ((a + A) - B) if a != 0
    // (0 + x)  is only kept in final, (a + (A + B)) => (A + (a + B)) if A  < a
    if (!(a->op == (op = Add) || a->op == Sub || (Sub == b->op && a->v.n != 0) ||
        (!is_final && (a->v.n == 0 || b->v.n == 0)) || (op == b->op && *b->a < *a)))
        new_expr(Expr(Rational(nmd + dmn, dmd), op, a, b));

    /* auto found_same = [&](auto&& self, const auto& e, const auto& v, const auto op) {
        return e.op == op && (e.a->v == v || e.b->v == v ||     // XXX:
            self(self, *e.a, v, op) || self(self, *e.b, v, op));
    }; */

    // (b - (B - A)) => ((b + A) - B), (x - 0) => (0 + x), ((A + x) - x) is only kept in final
    if (!(a->op == (op = Sub) || op == b->op || a->v.n == 0 ||
        (!is_final && found_same(*b, a->v, Add)))) {   if (ngoal)
            new_expr(Expr(Rational(nmd - dmn, dmd), op, a, b)); else
            new_expr(Expr(Rational(dmn - nmd, dmd), op, b, a));
    }

    // (a / (A / B)) => ((a * B) / A)
    // (x / 1) => (1 * x), (0 / x) => (0 * x), ((x * B) / x) => ((x + B) - x)
    if (!(a->op == (op = Div) || op == b->op)) {
        if (!(dmn == 0 || b->v.n == b->v.d || a->v.n == 0 || found_same(*a, b->v, Mul)))
            new_expr(Expr(Rational(nmd, dmn), op, a, b));

        //std::swap(v.n, v.d);
        if (!(nmd == 0 || a->v.n == a->v.d || b->v.n == 0 ||
              nmd == dmn || found_same(*b, a->v, Mul)))    // order mattered only if a != b
            new_expr(Expr(Rational(dmn, nmd), op, b, a));
    }
}

#ifdef  USE_LIST
#include <list>
using std::list;
#else// list seems worse performance than vector
#define list vector
#endif

void calc24_dynprog (const Rational& goal, const list<PtrE>& nums,
    const bool ngoal, auto&& each_found) {
    const auto psn = 1 << nums.size();

    vector<list<PtrE>> vexp;       vexp.reserve(psn);
    for (auto i = 0; i < psn; ++i) vexp.push_back(list<PtrE>());
    if (2 < psn) { auto i = 0;
        for (const auto& e: nums)  vexp[1 << i++].push_back(e);
    }

    vector<size_t> hv;  hv.reserve(psn - 2);
    const auto get_hash = [&](auto x)/* -> auto*/ {     auto i = 0u, h0 = 0u;
#ifdef  LIST
        for (const auto& e: nums) if ((1 << i++) & x) h0 = hash_combine(h0, hash_expr(*e));
#else
        for (auto n = 1; n <= x; n <<= 1, ++i)
            if (n & x) h0 = hash_combine(h0, hash_expr(*nums[i]));
#endif
        return h0;
    };

    for (auto x = 3; x < psn; ++x) { if (!(x & (x - 1))) continue;
        const auto is_final = x == psn - 1;

        const auto lambda = [&, is_final](auto&& e) {
            if (!is_final) vexp[x].push_back(make_ptre(e)); else
            if (e.v == goal) each_found(e);
        };

        for (auto i = 1; i < (x+1)/2; ++i) { if ((x & i) != i) continue;

            const auto h0 = get_hash(i);
                if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                    continue; else hv.push_back(h0);
            const auto h1 = get_hash(x - i);    if (h1 != h0) {
                if (std::find(hv.begin(), hv.end(), h1) != hv.end())
                    continue; else hv.push_back(h1);
            }

            const auto &es0(vexp[i]), &es1(vexp[x - i]);
            for (auto i = 0u; i < es0.size(); ++i) {                      const auto& a(es0[i]);
                for (auto j = (h1 != h0 ? 0u : i); j < es1.size(); ++j) { const auto& b(es1[j]);
                    if (b->v < a->v) form_compose(b, a, is_final, ngoal, lambda); else
                                     form_compose(a, b, is_final, ngoal, lambda);
                }
            }
        }   hv.clear();
    }   //return vexp[psn - 1];
}

vector<PtrE> calc24_splitset(const Rational& goal, const vector<PtrE>& nums,
    const bool ngoal, auto&& each_found) {
    static const auto IR = Rational(0, 0);
    const auto is_final = &goal != &IR;
    const auto n = nums.size();
    const auto psn = 1 << n;
    vector<PtrE> exps;

    const auto lambda = [&, is_final](auto&& e) {
        if (!is_final) exps.push_back(make_ptre(e)); else
        if (e.v == goal) each_found(e);
    };

    vector<size_t> hv;       hv.reserve(psn - 2);
    vector<PtrE> ns0, ns1;  ns0.reserve(n - 1); ns1.reserve(n - 1);

    for (auto x = 1; x < psn/2; ++x) {  ns0.clear();    ns1.clear();    auto i = 0;
        for (const auto& e: nums) if ((1 << i++) & x) ns0.push_back(e); else ns1.push_back(e);

        auto h0 = 0u, h1 = 0u;
        for (const auto& e: ns0) h0 = hash_combine(h0, hash_expr(*e));
            if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                continue; else hv.push_back(h0);
        for (const auto& e: ns1) h1 = hash_combine(h1, hash_expr(*e));
        if (h1 != h0) {
            if (std::find(hv.begin(), hv.end(), h1) != hv.end())
                continue; else hv.push_back(h1);
        }

        //for (const auto& e: ns0) std::cerr << ' ' << *e; std::cerr << ';';
        //for (const auto& e: ns1) std::cerr << ' ' << *e; std::cerr << std::endl; //continue;

        // TODO: can be parallelised
        if (1 < ns0.size()) ns0 = calc24_splitset(IR, ns0, ngoal, each_found);
        if (1 < ns1.size()) ns1 = calc24_splitset(IR, ns1, ngoal, each_found);

        for (auto i = 0u; i < ns0.size(); ++i) {                      const auto& a(ns0[i]);
            for (auto j = (h1 != h0 ? 0u : i); j < ns1.size(); ++j) { const auto& b(ns1[j]);
                if (b->v < a->v) form_compose(b, a, is_final, ngoal, lambda); else
                                 form_compose(a, b, is_final, ngoal, lambda);
            }
        }
    }   return exps;
}

#include <unordered_set>
void calc24_inplace(const Rational& goal, vector<PtrE>& nums,
    const bool ngoal, auto&& each_found, const size_t n) {
    vector<size_t> hv;  hv.reserve(n * (n - 1) / 2);

    // XXX: skip duplicates over different combination order, as well in symmetric style
    for (size_t j = 1; j < n; ++j) {
        const auto b(std::move(nums[j]));   nums[j] = nums[n - 1];
        const auto h0 = hash_combine(0, hash_expr(*b));
        for (size_t i = 0; i < j; ++i) {

            const auto h1 = hash_combine(hash_expr(*nums[i]), h0);
            if (std::find(hv.begin(), hv.end(), h1) != hv.end())
                continue; else hv.push_back(h1);
            const auto a(std::move(nums[i]));

            const auto lambda = [&, n, i, ngoal](auto&& e) {
                if (n == 2) { if (e.v == goal) each_found(e); } else {  nums[i] = make_ptre(e);
                    calc24_inplace(goal, nums, ngoal, each_found, n - 1);
                }
            };

            // XXX: compare expr. rather than value to avoid more duplicate combinations
            if (*b < *a) form_compose(b, a, n == 2, ngoal, lambda); else
                         form_compose(a, b, n == 2, ngoal, lambda);
            nums[i] = std::move(a);
        }   nums[j] = std::move(b);
    }
}

void calc24_construct(const Rational& goal, const vector<PtrE>& nums,
    const bool ngoal, auto&& each_found, size_t j) {
    const auto n = nums.size();
    vector<PtrE> nsub;  nsub.reserve(n - 1);
    vector<size_t> hv;    hv.reserve(n * (n - 1) / 2);

    // XXX: skip duplicates in symmetric style, e.g.: [1 1 5 5]
    //for (auto ib = nums.begin() + j; ib != nums.end(); ++ib, ++j) {   const auto& b(*ib);
    //    for (auto ia = nums.begin(); ia != ib; ++ia) {                const auto& a(*ia);
    for (; j < n; ++j) {    const auto& b(nums[j]);
        const auto lambda = [&, n, ngoal](auto&& e) {
            if (n == 2) { if (e.v == goal) each_found(e); } else {
                nsub.push_back(make_ptre(e));
                calc24_construct(goal, nsub, ngoal, each_found, j - 1);
                nsub. pop_back();
            }
        };

        const auto h0 = hash_combine(0, hash_expr(*b));
        for (size_t i = 0; i < j; ++i) {    const auto& a(nums[i]);
            const auto h1 = hash_combine(hash_expr(*a), h0);
            if (std::find(hv.begin(), hv.end(), h1) != hv.end())
                continue; else hv.push_back(h1);

            for (const auto& e: nums) if (e != a && e != b) nsub.push_back(e);
            if (b->v < a->v) form_compose(b, a, n == 2, ngoal, lambda); else
                             form_compose(a, b, n == 2, ngoal, lambda);
            nsub.clear();
        }
    }
}

void calc24_algo(const Rational& goal, const vector<Rational>& rnv,
    Calc24Algo algo, auto&& each_found) {
    switch (rnv.size()) {   case 0: return;
        case 1: if (rnv[0] == goal) each_found(Expr(rnv[0]));   return;
    }

    const auto ngoal = goal < Rational(0);
    vector<PtrE> nums;       nums.reserve(rnv.size());
    for (const auto& n: rnv) nums.push_back(make_ptre(n));
    std::sort(nums.begin(),  nums.end(),
        [](const auto& a, const auto& b) -> bool { return a->v < b->v; });

    std::unordered_set<size_t> eset;
    const auto hash_unify = [&](auto&& e) {
        if (eset.insert(hash_expr(e)).second) each_found(e);
    };

    switch (algo) {
        case DynProg:   calc24_dynprog  (goal, nums, ngoal, each_found); break;
        case SplitSet:  calc24_splitset (goal, nums, ngoal, each_found); break;
        case Inplace:   calc24_inplace  (goal, nums, ngoal, hash_unify, nums.size()); break;
        case Construct: calc24_construct(goal, nums, ngoal, hash_unify, 1); break;
    }   //return exps;
}

using std::string;
inline list<string> calc24_coll(const Rational& goal, const vector<Rational>& nums,
    Calc24Algo algo) {  list<string> exps;
    calc24_algo(goal, nums, algo, [&](auto&& e) {
        std::stringstream ss; ss << e; exps.push_back(ss.str());
    }); return exps;
}

inline string calc24_first(const Rational& goal, const vector<Rational>& nums,
    Calc24Algo algo) {  string es;
    calc24_algo(goal, nums, algo,
        [&](auto&& e) { std::stringstream ss(es); ss << e; });     return es;
    // FIXME: do sth. (throw exception?) to stop on first found?
}

inline size_t calc24_print(const Rational& goal, const vector<Rational>& nums,
    Calc24Algo algo) {  auto cnt = 0;
    calc24_algo(goal, nums, algo,
        [&](auto&& e) { std::cout << e << std::endl; ++cnt; });    return cnt;
}

void calc24_cffi(Calc24IO* calc24) {
    /*assert(sizeof(calc24->algo == 1 && sizeof(bool) == 1);
    std::cerr << "algo: " << calc24->algo << ", ia: " << calc24->ia
            << ", goal: " << calc24->goal << ", nums: [";
    for (auto i = 0u; i < calc24->ncnt; ++i) std::cerr << calc24->nums[i] << ", ";
    std::cerr << "]\n"; */

    vector<Rational> nums;  nums.reserve(calc24->ncnt);
    for (auto i = 0u; i < calc24->ncnt; ++i) nums.push_back(calc24->nums[i]);

    //vector<const char*> exps;
    list<Expr> exps;  //size_t cnt = 0;
    calc24_algo(calc24->goal, nums, calc24->algo, [&](auto&& e) {
        //std::stringstream ss; ss << e; exps.push_back(std::move(ss.str()).c_str());
        // FIXME: keep data buf by customized allocator?
        exps.push_back(e);   //++cnt;
    });

    calc24->ecnt = exps.size(); //cnt;
    calc24->exps = nullptr; //std::move(exps).data();
}

#include <iomanip>
extern "C" void test_24calc() { // deprecated, unified with Rust unit test solve24
    using std::cout, std::cerr, std::endl, std::string;

    auto a = Expr(5), b = Expr(6); //e = a * (b - a / b) + b;
    cout << "Test format rational/expression: "
         << "a: " << a << ", b: " << b /*<< ", expr.: " << e*/ << endl;

    std::stringstream ss;   // test Rational/Expr output
    ss.str(""); ss << a; assert(ss.str() == "5");
    ss.str(""); ss << b; assert(ss.str() == "6");
    //ss.str(""); ss << e; assert(ss.str() == "1*(2-1/2)+2");

    struct CaseT { int32_t goal; vector<int32_t> nums; vector<string> exps; size_t cnt; };
    const vector<CaseT> cases {
        { 24, {    }, { }, 0 },
        { 24, {  0 }, { }, 0 },
        { 24, { 24 }, { "24" }, 0 },
        { 24, { 8, 8, 8, 8 }, { }, 0 },
        { 24, { 1, 2, 4,12 }, { }, 5 },
        { 24, { 2, 4, 4,12 }, { }, 5 },
        { -2, { 1, 2, 3, 4 }, { }, 11},
        { 24, { 8, 8, 3, 3 }, { "8/(3-8/3)" }, 0 },
        { 24, { 3, 3, 7, 7 }, { "(3/7+3)*7" }, 0 },
        { 24, { 5, 5, 5, 1 }, { "(5-1/5)*5" }, 0 },
        { 24, {10, 9, 7, 7 }, { "10+(9-7)*7" }, 0 },
        { 24, {12,12,13,13 }, { "12+12+13-13" }, 0 },
        { 24, {24,24,24,24 }, { "(24-24)*24+24" }, 0 },
        {  5, { 1, 2, 3    }, { "1*(2+3)", "2*3-1" }, 0 },
        { 24, { 1, 1, 2, 6 }, { "2*(1+1)*6", "(1+1+2)*6" }, 0 },
        { 24, { 1, 1, 2,12 }, { "1+2*12-1", "12/(1-1/2)" }, 0 },
        { 24, { 5, 5, 1, 1 }, { "1*(5*5-1)", "(5-1)*(1+5)" }, 0 },
        { 24, { 1, 2, 3, 4 }, { "1*2*3*4", "(1+3)*(2+4)", "4*(1+2+3)" }, 0 },
        {100, {13,14,15,16,17 }, { "16+(17-14)*(13+15)", "(17-13)*(14+15)-16" }, 0 },
        {100, { 1, 2, 3, 4, 5, 6 }, { }, 111 },
        { 24, { 1, 2, 3, 4, 5, 6 }, { }, 727 },
        { 24, { 1, 2, 3, 4, 5 }, { }, 45 },
    };

    for (const auto& it: cases) {
        cout << "Calculate " << std::setw(3) << it.goal << " from [";
        for (auto n: it.nums) cout << std::setw(2) << n << ",";
        cout << " ]" << endl;

        vector<Rational> nums;
        const Rational goal(it.goal);
        for (auto n: it.nums) nums.push_back(n);

        auto assert_closure = [&](auto algo, auto algs) {
            list<string> exps = calc24_coll(goal, nums, algo);

            for (const auto& es: exps) {
                if (it.cnt < 1 && std::find(it.exps.begin(),
                    it.exps.end(), es) == it.exps.end()) {
                    cerr << "Unexpect expr. by algo-" << algs << ": "
                         << ss.str() << endl;   abort();
                }
            }

            auto n = exps.size(), cnt = it.cnt;
            cout << "  Got " << n << " expr. by algo-" << algs << endl;

            if (cnt < 1) cnt = it.exps.size();
            if (cnt != n) {
                cerr << "Unexpect count by algo-" << algs << ": "
                     << n << " != " << cnt << endl;     abort();
            }
        };

#define ASSERT_CLOSURE(algo) assert_closure(algo, #algo)
        ASSERT_CLOSURE(DynProg);
        ASSERT_CLOSURE(SplitSet);
        if (100 < it.cnt) continue;
        ASSERT_CLOSURE(Inplace);
        ASSERT_CLOSURE(Construct);
//break;
    }
}

#ifdef  RUN_TEST
int main(int argc, char* argv[]) {
    (void)argc;     (void)argv;
    test_24calc();  return 0;
}
#endif

// vim:sts=4 ts=8 sw=4 noet
