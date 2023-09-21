/****************************************************************
 * $ID: calc24.h         二, 21  6 2022 14:05:39 +0800  mhfan $ *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 * Copyright (c) 2022 M.H.Fan, All rights reserved.             *
 *                                                              *
 * Last modified: 四, 29  9 2022 14:42:33 +0800       by mhfan #
 ****************************************************************/

#ifndef CALC24_H
#define CALC24_H
//#pragma once

// XXX: this file is for cxx bridge only

//enum class Oper: char;
//struct Expr;

#include <vector>
using std::vector;

#include <string>
using std::string;

struct Rational;
#include <cstdint>
enum class Calc24Algo: uint8_t;

size_t calc24_print(const Rational& goal, const vector<Rational>& nums, Calc24Algo algo);
string calc24_first(const Rational& goal, const vector<Rational>& nums, Calc24Algo algo);
vector<string> calc24_coll(const Rational& goal,
    const vector<Rational>& nums, Calc24Algo algo);

#include "rust/cxx.h"
rust::Vec<rust::String> calc24_cxxffi(const Rational& goal,
          rust::Slice<const Rational> nums, Calc24Algo algo);

//#include "inrust/src/calc24.rs.h"

#endif//CALC24_H

