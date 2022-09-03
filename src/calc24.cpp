//#!/usr/bin/tcc -run
/****************************************************************
 * $ID: calc24.cpp       二, 21  6 2022 14:05:39 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 *                                                              *
 * Copyright (c) 2022 M.H.Fan, All Rights Reserved.             *
 *                                                              *
 * Last modified: 二, 21  6 2022 14:07:41 +0800       by mhfan #
 ****************************************************************/

// https://changkun.de/modern-cpp/zh-cn/00-preface/

#include <string>
#include <cassert>
#include <iostream>
#include <algorithm>

#ifndef CALC24_H
#define CALC24_H

#include <cstdint>
#include <memory>   // shared_ptr

template <typename T> struct RNum { T n, d; RNum(auto n, T d = 1): n(n), d(d) {} };
typedef RNum<int32_t> Rational;     // int32_t/int64_t/BigInt

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
    const Calc24Algo algo;
    const Rational goal, *const nums;
    const size_t ncnt;

    size_t ecnt;
    const char* *exps;
    //const PtrE const *exps;
    //const Expr* const *exps;
}   Calc24IO;

extern "C" void calc24_algo(Calc24IO* calc24);

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

inline auto operator< (const auto& lhs, const auto& rhs) noexcept {
    return lhs.n * rhs.d < lhs.d * rhs.n; }
inline auto operator==(const Rational& lhs, const Rational& rhs) noexcept {
    return /*lhs.d != 0 && rhs.d != 0 && */lhs.n * rhs.d == lhs.d * rhs.n;
}

/* inline auto operator+(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v + rhs.v, Add, &lhs, &rhs); }
inline auto operator-(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v - rhs.v, Sub, &lhs, &rhs); }
inline auto operator*(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v * rhs.v, Mul, &lhs, &rhs); }
inline auto operator/(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v / rhs.v, Div, &lhs, &rhs); } */

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

// PtrE instead of Expr here regarding for implicit use in unordered_set
inline auto operator==(const PtrE& lhs, const PtrE& rhs) noexcept {
    if (lhs->op == Num && rhs->op == Num) return  lhs->v == rhs->v;
    if (lhs->op != Num && rhs->op != Num)
        return lhs->op == rhs->op && lhs->a == rhs->a && lhs->b == rhs->b;
    return false;
}

#include <sstream>
using std::ostream;

//inline istream& operator>>(istream& is, Rational& r) { return is >> r.n >> r.d; }
inline ostream& operator<<(ostream& os, const Rational& r) {
    return (1 == r.d && 0 <= r.n) ? os << r.n : os << '(' <<  r.n << '/' << r.d << ')';
}

ostream& operator<<(ostream& os, const Expr& e) {
    if (e.op == Num) return os << e.v;  //assert(e.a && e.b);

    if ((e.a->op == '+' || e.a->op == '-') && (e.op == '*' || e.op == '/'))
        os << '(' << *e.a << ')'; else os << *e.a;  os << char(e.op);

    if ((e.op == '/' && (e.b->op == '*' || e.b->op == '/')) ||
        (e.op != '+' && (e.b->op == '+' || e.b->op == '-')))
        os << '(' << *e.b << ')'; else os << *e.b;  return os;
}

//Expr::~Expr() { std::cerr << "Destruct: " << *this << std::endl; }

inline auto hash_combine(size_t lhs, auto rhs) {
  return lhs ^ (rhs + 0x9e3779b9 + (lhs << 6) + (lhs >> 2));
}

using std::hash; // #include <functional>

template <> struct std::hash<PtrE> {
    size_t operator()(const PtrE& e) const noexcept {
        if (e->op == Num) return hash_combine(e->v.n, e->v.d); else {  hash<PtrE> hasher;
            return hash_combine(hasher(e->a), hasher(e->b)) ^ (char(e->op) << 13);
        }
    }
};

inline bool find_factor(const Rational& av, const PtrE& b, const Oper op) {
    return b->op == op && (b->a->v == av || find_factor(av, b->a, op) ||
                           b->b->v == av || find_factor(av, b->b, op));
}

// several pruning rules to find inequivalent/unique expressions only
void form_compose(const auto& a, const auto& b, bool is_final/*, bool ngoal*/, auto func) {
    // ((A . B) . b) => (A . (B . b), kept right sub-tree only
    const auto nmd = a->v.n * b->v.d, dmn = a->v.d * b->v.n;
    const auto dmd = a->v.d * b->v.d;   Oper op;
    // XXX: check overflow and reduce?

    // ((A / B) * b) => ((A * b) / B), (a * (A / B)) => ((a * A) / B) if a != 1
    // (1 * x)  is only kept in final, (a * (A * B)) => (A * (a * B)) if A  < a
    if (!(a->op == (op = Mul) || a->op == '/' || (b->op == '/' && a->v.n != a->v.d) ||
        (!is_final && (a->v.n == a->v.d || b->v.n == b->v.d)) || (op == b->op && *b->a < *a)))
        func(std::make_shared<const Expr>(Rational(a->v.n * b->v.n, dmd), op, a, b));

    // ((A - B) + b) => ((A + b) - B), (a + (A - B)) => ((a + A) - B) if a != 0
    // (0 + x)  is only kept in final, (a + (A + B)) => (A + (a + B)) if A  < a
    if (!(a->op == (op = Add) || a->op == '-' || (b->op == '-' && a->v.n != 0) ||
        (!is_final && (a->v.n == 0 || b->v.n == 0)) || (op == b->op && *b->a < *a)))
        func(std::make_shared<const Expr>(Rational(nmd + dmn, dmd), op, a, b));

    /* auto find_factor = [](auto&& self, const auto& av, const auto& b, const auto op) {
        return b->op == op && (b->a->v == av || self(self, av, b->a, op) ||
                               b->b->v == av || self(self, av, b->b, op));
    }; */

    // (b - (B - A)) => ((b + A) - B), (x - 0) => (0 + x), ((A + x) - x) is only kept in final
    if (!(a->op == (op = Sub) || op == b->op || a->v.n == 0 ||
        (!is_final && find_factor(a->v, b, Add))))  // FIXME: select (a - b) if goal < 0?
        func(std::make_shared<const Expr>(Rational(dmn - nmd, dmd), op, b, a));

    // (a / (A / B)) => ((a * B) / A)
    // (x / 1) => (1 * x), (0 / x) => (0 * x), ((x * B) / x) => ((x + B) - x)
    if (!(a->op == (op = Div) || op == b->op)) {
        if (!(dmn == 0 || b->v.n == b->v.d || a->v.n == 0 || find_factor(b->v, a, Mul)))
            func(std::make_shared<const Expr>(Rational(nmd, dmn), op, a, b));

        //std::swap(v.n, v.d);
        if (!(nmd == 0 || a->v.n == a->v.d || b->v.n == 0 ||
              nmd == dmn || find_factor(a->v, b, Mul))) // order mattered only if a != b
            func(std::make_shared<const Expr>(Rational(dmn, nmd), op, b, a));
    }
}

#ifdef  USE_LIST
#include <list>
using std::list;
#else// list seems worse performance than vector
#define list vector
#endif

list<PtrE> calc24_dynprog (const Rational& goal, const list<PtrE>& nums) {
    auto psn = 1 << nums.size();

    vector<list<PtrE>> vexp;       vexp.reserve(psn);
    for (auto i = 0; i < psn; ++i) vexp.push_back(list<PtrE>());
    if (2 < psn) { auto i = 0;
        for (const auto& e: nums)  vexp[1 << i++].push_back(e);
    }

    vector<size_t> hv; hv.reserve(psn - 2);
    auto get_hash = [&](auto x) {   auto i = 0, h0 = 0;
#ifdef  LIST
        for (const auto& e: nums) if ((1 << i++) & x) h0 = hash_combine(h0, hash<PtrE>{}(e));
#else
        for (auto n = 1; n <= x; n <<= 1, ++i)
            if (n & x) h0 = hash_combine(h0, hash<PtrE>{}(nums[i]));
#endif
        return h0;
    };

    for (auto x = 3; x < psn; ++x) { if (!(x & (x - 1))) continue;
        const auto is_final = x == psn - 1;

        auto lambda = [&](const auto& e) {
            if (!is_final || e->v == goal) vexp[x].push_back(e);
        };

        for (auto i = 1; i < (x+1)/2; ++i) { if ((x & i) != i) continue;

            auto h0 = get_hash(i);
                if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                    continue; else hv.push_back(h0);
            auto h1 = get_hash(x - i); if (h1 != h0) {
                if (std::find(hv.begin(), hv.end(), h1) != hv.end())
                    continue; else hv.push_back(h1);
            }

            const auto &es0(vexp[i]), &es1(vexp[x - i]);
            for (auto i = 0u; i < es0.size(); ++i) { const auto& a(es0[i]);
                for (auto j = (h1 != h0 ? 0u : i); j < es1.size(); ++j) {
                                                     const auto& b(es1[j]);
                    if (a->v < b->v) form_compose(a, b, is_final, lambda); else
                                     form_compose(b, a, is_final, lambda);
                }
            }
        }   hv.clear();
    }   return vexp[psn - 1];
}

list<PtrE> calc24_splitset(const Rational& goal, const list<PtrE>& nums) {
    static auto IR = Rational(0, 0);
    auto is_final = &goal != &IR;
    auto n = nums.size();
    auto psn = 1 << n;
    list<PtrE> exps;

    auto lambda = [&](const auto& e) { if (!is_final || e->v == goal) exps.push_back(e); };
    vector<PtrE> ns0, ns1; ns0.reserve(n - 1); ns1.reserve(n - 1);
    vector<size_t> hv; hv.reserve(psn - 2);

    for (auto x = 1; x < psn/2; ++x) {  ns0.clear();    ns1.clear();    auto i = 0;
        for (const auto& e: nums) if ((1 << i++) & x) ns0.push_back(e); else ns1.push_back(e);

        auto h0 = 0, h1 = 0;
        for (const auto& e: ns0) h0 = hash_combine(h0, hash<PtrE>{}(e));
            if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                continue; else hv.push_back(h0);
        for (const auto& e: ns1) h1 = hash_combine(h1, hash<PtrE>{}(e));
        if (h1 != h0) {
            if (std::find(hv.begin(), hv.end(), h1) != hv.end())
                continue; else hv.push_back(h1);
        }

        //for (const auto& e: ns0) std::cerr << ' ' << *e; std::cerr << ';';
        //for (const auto& e: ns1) std::cerr << ' ' << *e; std::cerr << std::endl; //continue;

        if (1 < ns0.size()) ns0 = calc24_splitset(IR, ns0);
        if (1 < ns1.size()) ns1 = calc24_splitset(IR, ns1);

        for (auto i = 0u; i < ns0.size(); ++i) {                      const auto& a(ns0[i]);
            for (auto j = (h1 != h0 ? 0u : i); j < ns1.size(); ++j) { const auto& b(ns1[j]);
                if (a->v < b->v) form_compose(a, b, is_final, lambda); else
                                 form_compose(b, a, is_final, lambda);
            }
        }
    }   return exps;
}

#include <unordered_set>
void calc24_inplace(const Rational& goal, vector<PtrE>& nums,
    const size_t n, std::unordered_set<PtrE>& exps) {
    hash<PtrE> hasher; vector<size_t> hv; hv.reserve(n * (n - 1) / 2);

    for (size_t i = 0; i < n - 1; ++i) {
        const auto a(std::move(nums[i]));
        auto lambda = [&](const auto& e) {
            if (n == 2) { if (e->v == goal) exps.insert(e); } else {
                nums[i] = e;    calc24_inplace(goal, nums, n - 1, exps); }
        };

        for (size_t j = i + 1; j < n; ++j) {
            size_t h0 = hash_combine(hasher(a), hasher(nums[j]));
            if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                continue; else hv.push_back(h0);
            const auto b(std::move(nums[j]));

            nums[j] = nums[n - 1];
            if (b->v < a->v) form_compose(b, a, n == 2, lambda); else
                             form_compose(a, b, n == 2, lambda);
            nums[j] = std::move(b);
        }   nums[i] = std::move(a);
    }
}

void calc24_construct(const Rational& goal, const list<PtrE>& nums,
    size_t j, std::unordered_set<PtrE>& exps) {
    const auto n = nums.size();
    hash<PtrE> hasher; vector<size_t> hv; hv.reserve(n * (n - 1) / 2);

    for (auto ib = nums.begin() + j; ib != nums.end(); ++ib, ++j) {   const auto& b(*ib);
        for (auto ia = nums.begin(); ia != ib; ++ia) {                const auto& a(*ia);
    //for (; j < n; ++j) {                    const auto& b(nums[j]);
    //    for (size_t i = 0; i < j; ++i) {    const auto& a(nums[i]);
            size_t h0 = hash_combine(hasher(a), hasher(b));
            if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                continue; else hv.push_back(h0);

            vector<PtrE> nsub;  for (const auto& e: nums)
                if (e.get() != a.get() && e.get() != b.get()) nsub.push_back(e);

            auto lambda = [&](const auto& e) {
                if (n == 2) { if (e->v == goal) exps.insert(e); } else {
                    nsub.push_back(e);  calc24_construct(goal, nsub, j - 1, exps);
                    nsub.pop_back();
                }
            };

            if (b->v < a->v) form_compose(b, a, n == 2, lambda); else
                             form_compose(a, b, n == 2, lambda);
        }
    }
}

list<PtrE> calc24_algo(const Rational& goal, list<PtrE>& nums, Calc24Algo algo) {
    // TODO: utilize exception mechanism for achieve stop on first found
    list<PtrE> exps;
    if (nums.size() == 1) {
        const auto& e = nums.front();
        if (e->v == goal) exps.push_back(e);
        return exps;
    }

    std::sort(nums.begin(), nums.end(),
        [](const auto& a, const auto& b) -> bool { return a->v < b->v; });
    switch (algo) {
        case DynProg:  exps = calc24_dynprog (goal, nums); break;
        case SplitSet: exps = calc24_splitset(goal, nums); break;

        case Inplace: {
            std::unordered_set<PtrE> eset;
            calc24_inplace(goal, nums, nums.size(), eset);
            for (const auto& e: eset) exps.push_back(e);
        }   break;

        case Construct: {
            std::unordered_set<PtrE> eset;
            calc24_construct(goal, nums, 1, eset);
            for (const auto& e: eset) exps.push_back(e);
        }   break;

        default: ;
    }   return exps;
}

void calc24_algo(Calc24IO* calc24) {
    /*assert(sizeof(calc24->algo == 1 && sizeof(bool) == 1);
    std::cerr << "algo: " << calc24->algo << ", ia: " << calc24->ia
            << ", goal: " << calc24->goal << ", nums: [";
    for (auto i = 0u; i < calc24->ncnt; ++i) std::cerr << calc24->nums[i] << ", ";
    std::cerr << "]\n"; */

    vector<PtrE> nums;
    for (auto i = 0u; i < calc24->ncnt; ++i)
        nums.push_back(std::make_shared<const Expr>(calc24->nums[i]));
    const list<PtrE> exps = calc24_algo(calc24->goal, nums, calc24->algo);
    calc24->ecnt = exps.size();     // TODO:
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
        { 24, { 0  }, { }, 0 },
        { 24, { 24 }, { "24" }, 0 },
        { 24, { 8, 8, 8, 8 }, { }, 0 },
        { 24, { 1, 2, 4,12 }, { }, 5 },
        { 24, { 2, 4, 4,12 }, { }, 5 },
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
        { 24, { 1, 2, 3, 4, 5, 6 }, { }, 732 },
        { 24, { 1, 2, 3, 4, 5 }, { }, 45 },
    };

    for (auto it: cases) {
        cout << "Test compute " << std::setw(3) << it.goal << " from [";
        for (auto n: it.nums) cout << std::setw(2) << n << ",";
        cout << "]" << endl;

        vector<PtrE> nums;
        Rational goal(it.goal);
        for (auto n: it.nums) nums.push_back(std::make_shared<const Expr>(n));

        auto assert_closure = [&](auto algo, auto algs) {
            list<PtrE> exps = calc24_algo(goal, nums, algo);

            for (const auto& e: exps) {
                ss.str(""); ss << *e;   //cout << *e << endl;
                if (it.cnt < 1 && std::find(it.exps.begin(),
                    it.exps.end(), ss.str()) == it.exps.end()) {
                    cerr << "Unexpect expr. by algo-" << algs << ": "
                         << ss.str() << endl;   abort();
                }
            }

            auto n = exps.size(), cnt = it.cnt;
            cout << "  Got " << n << " expr. by algo-" << algs << endl;

            if (cnt < 1) cnt = it.exps.size();
            if (n != cnt) {
                cerr << "Unexpect count by algo-" << algs << ": "
                     << n << " != " << cnt << endl;     abort();
            }
        };

#define ASSERT_CLOSURE(algo) assert_closure(algo, #algo)
        ASSERT_CLOSURE(DynProg);
        ASSERT_CLOSURE(SplitSet);
        if (100 < it.cnt) continue;
        ASSERT_CLOSURE(Inplace);
//break;
    }
}

#ifdef  RUN_TEST
int main(int argc, char* argv[]) {
    (void)argc;     (void)argv;
    test_24calc();
    return 0;
}
#endif

// vim:sts=4 ts=8 sw=4 noet