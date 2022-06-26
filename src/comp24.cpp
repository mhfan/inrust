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

#include <stdint.h>

#include <list>
#include <vector>
#include <string>
#include <sstream>
#include <cassert>
#include <iomanip>
#include <iostream>
#include <algorithm>
#include <unordered_set>

using std::ostream;//, std::istream;
using std::vector, std::list, std::hash;//, std::move;

struct Rational {
    int32_t n, d;

    Rational(auto n, int32_t d = 1): n(n), d(d) {}

    auto operator+(const auto& rhs) const {
        return Rational(n * rhs.d + d * rhs.n, d * rhs.d); }
    auto operator-(const auto& rhs) const {
        return Rational(n * rhs.d - d * rhs.n, d * rhs.d); }
    auto operator*(const auto& rhs) const { return Rational(n * rhs.n,  d * rhs.d); }
    auto operator/(const auto& rhs) const {
        return 0 == rhs.d ? Rational(0, 0) : Rational(n * rhs.d,  d * rhs.n); }

    auto operator<(const auto& rhs) const {    return n * rhs.d < d * rhs.n; }

    auto operator==(const auto& rhs) const {
        return d != 0 && rhs.d != 0 && n * rhs.d == d * rhs.n;
    }

    friend ostream& operator<<(ostream& os, const Rational& r) {
        if (1 == r.d && 0 <= r.n) return os << r.n;
        return os << '(' <<  r.n << '/' << r.d << ')';
    }

    //friend istream& operator>>(istream& is, Rational& r) { return is >> r.n >> r.d; }
};

//typedef char Oper;
enum Oper { Num, Add = '+', Sub = '-', Mul = '*', Div = '/' };

struct Expr {
    Rational v;
    struct { Oper op; const Expr *a, *b; }; // anonymous structure

    Expr(auto n): Expr(Rational(n)) {}   // Constructor delegation
    Expr(const Rational& r, Oper op = Num, const Expr *a = 0, const Expr *b = 0):
        v(r), op(op), a(a), b(b) {}
    //Expr(): Expr(Rational(0, 0)) {}
    //Expr(const Expr&) = delete;

    Expr(auto a, auto op, auto b): v(0), op(op), a(a), b(b) {
        switch (op) {
            case '+': v = a->v + b->v; break;
            case '-': v = a->v - b->v; break;
            case '*': v = a->v * b->v; break;
            case '/': v = a->v / b->v; break;
            default: ;
        }
    }

    //~Expr() { std::cerr << "Destruct: " << *this << std::endl; }

    //auto operator+(const auto& rhs) const { return Expr(v + rhs.v, Add, this, &rhs); }
    //auto operator-(const auto& rhs) const { return Expr(v - rhs.v, Sub, this, &rhs); }
    //auto operator*(const auto& rhs) const { return Expr(v * rhs.v, Mul, this, &rhs); }
    //auto operator/(const auto& rhs) const { return Expr(v / rhs.v, Div, this, &rhs); }

    friend ostream& operator<<(ostream& os, const auto& e) {
        if (e.op == Num) return os << e.v;  //assert(e.a && e.b);

        if ((e.a->op == '+' || e.a->op == '-') && (e.op == '*' || e.op == '/'))
            os << '(' << *e.a << ')'; else os << *e.a;  os << char(e.op);

        if (e.op == '/' && (e.b->op == '*' || e.b->op == '/') ||
            e.op != '+' && (e.b->op == '+' || e.b->op == '-'))
            os << '(' << *e.b << ')'; else os << *e.b;  return os;
    }
};

vector<const Expr*> coll;

bool is_subn_expr(const auto& e) {
    if (e->op == '*' || e->op == '/') return is_subn_expr(e->a) || is_subn_expr(e->b);
    return e->op == '-' && e->a->v < e->b->v;
}

void form_expr_exec(const auto a, const auto b, auto func) {
    const Oper OPS[] = { Add, Sub, Mul, Div };
    for (auto op: OPS) {
        // ((a . b) . B) => (a . (b . B)
        if (a->op == op) continue;

        // ((a - b) + B) => ((a + B) - b)
        // ((a / b) * B) => ((a * B) / b)
        if (a->op == '-' && op == '+' || a->op == '/' && op == '*') continue;

        // (A + (a + b)) => (a + (A + b)) if a < A
        // (A * (a * b)) => (a * (A * b)) if a < A
        if (b->a && op == b->op && (op == '+' || op == '*') && b->a->v < a->v) continue;

        // (A + (a - b)) => ((A + a) - b)
        // (A * (a / b)) => ((A * a) / b)
        // (A - (a - b)) => ((A + b) - a)
        // (A / (a / b)) => ((A * b) / a)
        if (op == '+' && b->op == '-' || op == '*' && b->op == '/' ||
            op == b->op && (op == '-' || op == '/')) continue;

        // swap sub-expr. for order mattered (different values) operators
        if (op == '/' && a->v.n != 0 || op == '-'/* && !is_subn_expr(a)*/) {
            auto e = new Expr(b, op, a); func(e); coll.push_back(e);
        }

        if (op == '/' && b->v.n == 0 || op == '-'/* &&  is_subn_expr(b)*/) continue;
            auto e = new Expr(a, op, b); func(e); coll.push_back(e);
    }
}

typedef std::pair<const Expr*, const Expr*> EPT;
bool operator==(const EPT& e1, const EPT& e2) {
    return e1.first->v == e2.first->v && e1.second->v == e2.second->v;
}

inline size_t hash_combine(size_t lhs, size_t rhs) {
  return lhs ^ (rhs + 0x9e3779b9 + (lhs << 6) + (lhs >> 2));
}

template <> struct hash<Expr> {
    size_t operator()(Expr const& e) const noexcept {  hash<Expr> hasher;
        if (e.op == Num) return hash_combine(hash<int32_t>{}(e.v.n), hash<int32_t>{}(e.v.d));
        return hash_combine(hasher(*e.a), hasher(*e.b)) ^ (hash<char>{}(char(e.op)) << 16);
    }
};

template <> struct hash<EPT> {
    size_t operator()(EPT const& ep) const noexcept {  hash<Expr> hasher;
        return hash_combine(hasher(*ep.first), hasher(*ep.second));
    }
};

template <> struct hash<list<const Expr*>> {
    size_t operator()(const auto& exps) const noexcept {
        size_t hs = 0; for (auto e: exps) hs = hash_combine(hs, hash<Expr>{}(*e)); return hs;
    }
};

list<const Expr*> comp24_dynprog(const auto& goal, const list<const Expr*>& nums) {
    vector<list<const Expr*>> vexp;
    auto cnt = nums.size();
    auto pow = 1 << cnt;
    vexp.reserve(pow);

    for (auto i = 0; i < pow; ++i) vexp.push_back(list<const Expr*>());
    auto i = 0; for (auto e: nums) vexp[1 << i++].push_back(e);

    for (auto x = 3; x < pow; ++x) {
        //vector<size_t> hv; hash<EPT> hasher;
        std::unordered_set<EPT> hs;
        auto& exps = vexp[x];

        for (auto i = 1; i < (x+1)/2; ++i) {
            if ((x & i) != i) continue;  auto j = x - i;

            for (auto a: vexp[i]) for (auto b: vexp[j]) {
                auto ea = a, eb = b; if (b->v < a->v) ea = b, eb = a;   // swap for ordering
                if (!hs.insert(std::make_pair(ea, eb)).second) continue;
                /* auto h0 = hasher(std::make_pair(ea, eb));
                if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                    continue; else hv.push_back(h0); */

                form_expr_exec(ea, eb, [&](const auto* e) { exps.push_back(e); });
            }
        }
    }

    auto& exps = vexp[pow - 1];
    for (auto it = exps.begin(); it != exps.end(); )
        if ((*it)->v == goal) ++it; else it = exps.erase(it);
    return exps;
}

list<const Expr*> comp24_splitset(const list<const Expr*>& nums) {
    auto cnt = nums.size();
    if  (cnt == 1) return nums;
    auto pow =  1 << cnt;

    vector<size_t> hv;
    hv.reserve(pow - 2);
    list<const Expr*> exps;
    hash<list<const Expr*>> hasher;
    for (auto mask = 1; mask < pow/2; ++mask) {
        list<const Expr*> ns0, ns1; auto i = 0;
        for (auto e: nums) if ((1 << i++) & mask) ns0.push_back(e); else ns1.push_back(e);

        auto h0 = hasher(ns0), h1 = hasher(ns1);
            if (std::find(hv.begin(), hv.end(), h0) != hv.end())
                continue; else hv.push_back(h0);
        if (h1 != h0) {
            if (std::find(hv.begin(), hv.end(), h1) != hv.end())
                continue; else hv.push_back(h1);
        }

        //for (auto e: ns0) std::cerr << ' ' << *e; std::cerr << ';';
        //for (auto e: ns1) std::cerr << ' ' << *e; std::cerr << std::endl; //continue;

        if (1 < ns0.size()) ns0 = comp24_splitset(ns0);
        if (1 < ns1.size()) ns1 = comp24_splitset(ns1);

        for (auto a: ns0) for (auto b: ns1) {
            auto ea = a, eb = b; if (b->v < a->v) ea = b, eb = a;   // swap for ordering
            form_expr_exec(ea, eb, [&](const auto* e) { exps.push_back(e); });
        }
    }

    return exps;
}

int main(int argc, char* argv[]) {
    using std::cout, std::endl, std::string;

    auto a = Expr(5), b = Expr(6); //e = a * (b - a / b) + b;
    cout << "Test format rational/expression: "
         << "a: " << a << ", b: " << b /*<< ", expr.: " << e*/ << endl;

    std::stringstream ss;   // test Rational/Expr output
    ss.str(""); ss << a; assert(ss.str() == "5");
    ss.str(""); ss << b; assert(ss.str() == "6");
    //ss.str(""); ss << e; assert(ss.str() == "1*(2-1/2)+2");

    struct CaseT { int32_t goal; vector<int32_t> nums; vector<string> exps; size_t cnt; };
    vector<CaseT> cases {
        //{100, { 1, 2, 3, 4, 5, 6, 7 }, { }, 1 },
        {  5, { 1, 2, 3 }, { "1*(2+3)", "(2+3)/1", "2*3-1",
                             "2+1*3", "2/1+3", "2+3/1", "1*2+3" }, 0 },
        { 24, { 1, 2, 3, 4 }, { "1*2*3*4", "2*3*4/1", "(1+3)*(2+4)", "4*(1+2+3)" }, 0 },
        { 24, { 0 }, { }, 0 },
        { 24, { 24 }, { "24" }, 0 },
        { 24, { 8, 8, 8, 8 }, { }, 0 },
        { 24, { 8, 8, 3, 3 }, { "8/(3-8/3)" }, 0 },
        { 24, { 5, 5, 5, 1 }, { "(5-1/5)*5" }, 0 },
        { 24, {10, 9, 7, 7 }, { "10+(9-7)*7" }, 0 },
        {100, {13,14,15,16,17 }, { "16+(17-14)*(13+15)", "(17-13)*(14+15)-16" }, 0 },
        { 24, { 1, 2, 3, 4, 5 }, { }, 78 },
        {100, { 1, 2, 3, 4, 5, 6 }, { }, 299 },
        { 24, { 1, 2, 3, 4, 5, 6 }, { }, 1832 },
    };

    for (auto it: cases) {
        cout << "Test compute " << std::setw(3) << it.goal << " from [";

        Rational goal(it.goal);
        list<const Expr*> nums;
        for (auto n: it.nums) {
            auto e = new Expr(n);
            coll.push_back(e);
            nums.push_back(e);
            cout << std::setw(2) << *e << ",";
        }   cout << "]" << endl;

        auto cnt = 0;
        list<const Expr*> exps;

        if (true) {
            exps = comp24_splitset(nums);
            for (auto it = exps.begin(); it != exps.end(); )
                if ((*it)->v == goal) { ++it; ++cnt; } else it = exps.erase(it);
        } else {
            exps = comp24_dynprog(goal, nums);
            cnt = exps.size();
        }

        for (auto e: exps) {
            //cout << *e << endl;
            ss.str(""); ss << *e;
            if (it.cnt < 1 && std::find(it.exps.begin(),
                it.exps.end(), ss.str()) == it.exps.end())
                cout << "Not expect expr.: " << ss.str() << endl;
        }

        if (it.cnt < 1) it.cnt = it.exps.size();
        if (cnt != it.cnt) cout << "Expr. count: " << it.cnt << " vs " << cnt << endl;

        for (auto it = coll.rbegin(); it != coll.rend(); ++it) delete *it;
        coll.clear();
//break;
    }

    return 0;
}

// vim:sts=4 ts=8 sw=4 noet