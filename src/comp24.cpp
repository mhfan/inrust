//#!/usr/bin/tcc -run
/****************************************************************
 * $ID: comp24.cpp       二, 21  6 2022 14:05:39 +0800  mhfan $ *
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

#include "comp24.h"

/* inline auto operator+(const Rational& lhs, const auto& rhs) noexcept {
    return Rational(lhs.n * rhs.d + lhs.d * rhs.n, lhs.d * rhs.d); }
inline auto operator-(const Rational& lhs, const auto& rhs) noexcept {
    return Rational(lhs.n * rhs.d - lhs.d * rhs.n, lhs.d * rhs.d); }
inline auto operator*(const Rational& lhs, const auto& rhs) noexcept {
    return Rational(lhs.n * rhs.n,  lhs.d * rhs.d); }
inline auto operator/(const Rational& lhs, const auto& rhs) noexcept {
    return 0 == rhs.d ? Rational(0, 0) : Rational(lhs.n * rhs.d,  lhs.d * rhs.n); } */

inline auto operator< (const Rational& lhs, const auto& rhs) noexcept {
    return lhs.n * rhs.d < lhs.d * rhs.n; }
inline auto operator==(const Rational& lhs, const auto& rhs) noexcept {
    return lhs.d != 0 && rhs.d != 0 && lhs.n * rhs.d == lhs.d * rhs.n;
}

/* inline auto operator+(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v + rhs.v, Add, &lhs, &rhs); }
inline auto operator-(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v - rhs.v, Sub, &lhs, &rhs); }
inline auto operator*(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v * rhs.v, Mul, &lhs, &rhs); }
inline auto operator/(const Expr& lhs, const auto& rhs) noexcept {
    return Expr(lhs.v / rhs.v, Div, &lhs, &rhs); } */

auto operator< (const Expr& lhs, const auto& rhs) noexcept {
    if (lhs.v  < rhs.v) return true;
    if (lhs.v == rhs.v) {
        if (rhs.op != Num) {
            if (lhs.op == Num) return true;
            if (*lhs.a < *rhs.a) return true;
            if (lhs.a->v == rhs.a->v) {
                if (lhs.a->op  < rhs.a->op) return true;
                if (lhs.a->op == rhs.a->op) { if (*lhs.b < *rhs.b) return true; }
            }
        }
    }   return false;
}

inline auto operator==(const Expr& lhs, const auto& rhs) noexcept {
    if (lhs.op == Num && rhs.op == Num) return  lhs.v == rhs.v;
    if (lhs.op != Num && rhs.op != Num)
        return lhs.op == rhs.op && *lhs.a == *rhs.a && *lhs.b == *rhs.b;
    return false;
}

inline auto operator==(const PtrE& lhs, const PtrE& rhs) noexcept { return *lhs == *rhs; }

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

template <> struct hash<Expr> {
    size_t operator()(const Expr& e) const noexcept {
        if (e.op == Num) return hash_combine(e.v.n, e.v.d); else {  hash<Expr> hasher;
            return hash_combine(hasher(*e.a), hasher(*e.b)) ^ (char(e.op) << 13);
        }
    }
};

template <> struct hash<PtrE> {
    size_t operator()(const PtrE& e) const noexcept { return hash<Expr>{}(*e); }
};

/* bool is_subn_expr(const auto& e) {
    if (e->op == '*' || e->op == '/') return is_subn_expr(e->a) || is_subn_expr(e->b);
    return e->op == '-' && e->a->v < e->b->v;
} */

void form_expr(const auto a, const auto b, auto func) {
    const Oper OPS[] = { Add, Sub, Mul, Div };
    for (auto op: OPS) {
        // ((a . b) . B) => (a . (b . B)
        if (a->op == op) continue;

        // ((a - b) + B) => ((a + B) - b)
        // ((a / b) * B) => ((a * B) / b)
        if ((a->op == '-' && op == '+') || (a->op == '/' && op == '*')) continue;

        // (A + (a + b)) => (a + (A + b)) if a < A
        // (A * (a * b)) => (a * (A * b)) if a < A
        if (b->a && op == b->op && (op == '+' || op == '*') && b->a->v < a->v) continue;

        // (A + (a - b)) => ((A + a) - b), (A * (a / b)) => ((A * a) / b),
        // (A - (a - b)) => ((A + b) - a), (A / (a / b)) => ((A * b) / a),
        if ((op == '+' && b->op == '-') || (op == '*' && b->op == '/') ||
            (op == b->op && (op == '-'  ||  op == '/'))) continue;

        // swap sub-expr. for order mattered (different values) operators
        if ((op == '/' && a->v.n != 0) || (op == '-'/* && !is_subn_expr(a)*/)) {
            auto e = std::make_shared<const Expr>(b, a, op); func(e);
        }

        if ((op == '/' && b->v.n == 0) || (op == '-'/* &&  is_subn_expr(b)*/)) continue;
            auto e = std::make_shared<const Expr>(a, b, op); func(e);
    }
}

#ifdef  USE_LIST
#include <list>
using std::list;
#else// list seems worse performance than vector
#define list vector
#endif

list<PtrE> comp24_dynprog (const Rational& goal, const vector<PtrE>& nums) {
    auto pow = 1 << nums.size();

    vector<list<PtrE>> vexp;       vexp.reserve(pow);
    for (auto i = 0; i < pow; ++i) vexp.push_back(list<PtrE>());
    auto i = 0; for (auto e: nums) vexp[1 << i++].push_back(e);

    vector<size_t> hv; hv.reserve(pow - 2);
    for (auto x = 3; x < pow; ++x) {
        if (!(x & (x - 1))) continue;
         auto sub_round = x != pow - 1;

        if   (sub_round) {
            size_t h0 = (i = 0);
            //for (auto n = 1; n < x; n <<= 1, ++i) // XXX: for vector only
            //    if (n & x) h0 = hash_combine(h0, hash<Expr>{}(*nums[i]));
            for (auto e: nums) if ((1 << i++) & x) h0 = hash_combine(h0, hash<Expr>{}(*e));

            if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                continue; else hv.push_back(h0);
        }

        auto& exps = vexp[x];
        for (auto i = 1; i < (x+1)/2; ++i) {
            if ((x & i) != i) continue;

            for (auto ta: vexp[i]) for (auto tb: vexp[x - i]) {
                 auto a = ta, b = tb; if (*b < *a) a = tb, b = ta;   // swap for ordering
                form_expr(a, b, [&](auto e) {
                    if (sub_round || e->v == goal) exps.push_back(e);
                });
            }
        }
    }   return vexp[pow - 1];
}

list<PtrE> comp24_splitset(const Rational& goal, const   list<PtrE>& nums) {
    static auto IR = Rational(0, 0);
    auto n = nums.size();
    auto pow = 1 << n;
    list<PtrE> exps;

    vector<PtrE> ns0, ns1;
    ns0.reserve(n - 1);   ns1.reserve(n - 1);
    hash<Expr> hasher; vector<size_t> hv; hv.reserve(pow - 2);

    for (auto x = 1; x < pow/2; ++x) {
        ns0.clear();    ns1.clear();    auto i = 0;
        for (auto e: nums) if ((1 << i++) & x) ns0.push_back(e); else ns1.push_back(e);

        auto h0 = 0, h1 = 0;
        for (auto e: ns0) h0 = hash_combine(h0, hasher(*e));
        for (auto e: ns1) h1 = hash_combine(h1, hasher(*e));
            if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                continue; else hv.push_back(h0);
        if (h1 != h0) {
            if (std::find(hv.begin(), hv.end(), h1) != hv.end())
                continue; else hv.push_back(h1);
        }

        //for (auto e: ns0) std::cerr << ' ' << *e; std::cerr << ';';
        //for (auto e: ns1) std::cerr << ' ' << *e; std::cerr << std::endl; //continue;

        if (1 < ns0.size()) ns0 = comp24_splitset(IR, ns0);
        if (1 < ns1.size()) ns1 = comp24_splitset(IR, ns1);

        for (auto ta: ns0) for (auto tb: ns1) {
             auto a = ta, b = tb; if (*b < *a) a = tb, b = ta;   // swap for ordering
            form_expr(a, b, [&](auto e) {
                if (&goal == &IR || e->v == goal) exps.push_back(e);
            });
        }
    }   return exps;
}

#include <unordered_set>
void comp24_construct(const Rational& goal, const size_t n,
    vector<PtrE>& nums, std::unordered_set<PtrE>& exps) {
    hash<Expr> hasher; vector<size_t> hv; hv.reserve(n * (n - 1) / 2);

    for (size_t i = 0; i < n; ++i) {
        const auto ta = nums[i];
        for (size_t j = i + 1; j < n; ++j) {
            const auto tb = nums[j];
            auto a = ta, b = tb; if (*b < *a) a = tb, b = ta;   // swap for ordering

            size_t h0 = hash_combine(hasher(*a), hasher(*b));
            if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                continue; else hv.push_back(h0);

            nums[j] = nums[n - 1];
            form_expr(a, b, [&](auto e) {
                if (n == 2) { if (e->v == goal) exps.insert(e); } else {
                    nums[i] = e;    comp24_construct(goal, n - 1, nums, exps); }
            });     nums[j] = tb;
        }           nums[i] = ta;
    }
}

list<PtrE> comp24_algo(const Rational& goal, list<PtrE>& nums, Comp24Algo algo) {
    list<PtrE> exps;
    if (nums.size() == 1) { auto e = nums.front();
         if (e->v == goal) exps.push_back(e);
        return exps;
    }

    switch (algo) {
        case DynProg:  exps = comp24_dynprog (goal, nums); break;
        case SplitSet: exps = comp24_splitset(goal, nums); break;

        //case Construct:
        case Inplace: {
            std::unordered_set<PtrE> eset;
            comp24_construct(goal, nums.size(), nums, eset);
            for (auto e: eset) exps.push_back(e);
        }   break;

        default: ;
    }   return exps;
}

void comp24_algo(Comp24* comp24) {
    /*assert(sizeof(comp24->algo == 1 && sizeof(bool) == 1);
    std::cerr << "algo: " << comp24->algo << ", ia: " << comp24->ia
            << ", goal: " << comp24->goal << ", nums: [";
    for (auto i = 0u; i < comp24->ncnt; ++i) std::cerr << comp24->nums[i] << ", ";
    std::cerr << "]\n"; */

    vector<PtrE> nums;
    for (auto i = 0u; i < comp24->ncnt; ++i)
        nums.push_back(std::make_shared<const Expr>(comp24->nums[i]));
    list<PtrE> exps = comp24_algo(comp24->goal, nums, comp24->algo);
    comp24->ecnt = exps.size();     // TODO:
}

#include <iomanip>

extern "C" void test_comp24() {
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
        { 24, { 0 }, { }, 0 },
        { 24, { 24 }, { "24" }, 0 },
        { 24, { 8, 8, 8, 8 }, { }, 0 },
        { 24, { 8, 8, 3, 3 }, { "8/(3-8/3)" }, 0 },
        { 24, { 5, 5, 5, 1 }, { "(5-1/5)*5" }, 0 },
        { 24, {10, 9, 7, 7 }, { "10+(9-7)*7" }, 0 },
        {  5, { 1, 2, 3 }, { "1*(2+3)", "(2+3)/1", "2*3-1",
                             "2+1*3", "2/1+3", "2+3/1", "1*2+3" }, 0 },
        { 24, { 1, 2, 3, 4 }, { "1*2*3*4", "2*3*4/1", "(1+3)*(2+4)", "4*(1+2+3)" }, 0 },
        {100, {13,14,15,16,17 }, { "16+(17-14)*(13+15)", "(17-13)*(14+15)-16" }, 0 },
        { 24, { 1, 2, 3, 4, 5 }, { }, 78 },
        {100, { 1, 2, 3, 4, 5, 6 }, { }, 299 },
        { 24, { 1, 2, 3, 4, 5, 6 }, { }, 1832 },
        //{100, { 1, 2, 3, 4, 5, 6, 7 }, { }, 5504 },
        //{ 24, { 1, 2, 3, 4, 5, 6, 7 }, { }, 34301 },
    };

    for (auto it: cases) {
        cout << "Test compute " << std::setw(3) << it.goal << " from [";
        for (auto n: it.nums) cout << std::setw(2) << n << ",";
        cout << "]" << endl;

        vector<PtrE> nums;
        Rational goal(it.goal);
        for (auto n: it.nums) nums.push_back(std::make_shared<const Expr>(n));

        auto assert_closure = [&](auto algo, auto algs) {
            list<PtrE> exps = comp24_algo(goal, nums, algo);

            for (auto e: exps) {
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
    test_comp24();
    return 0;
}
#endif

// vim:sts=4 ts=8 sw=4 noet