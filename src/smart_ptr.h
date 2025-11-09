/****************************************************************
 * $ID: shared_ptr.h  	Sun 09 Nov 2025 00:14:31+0800           *
 *                                                              *
 * Maintainer: 范美辉 (MeiHui FAN) <mhfan@ustc.edu>              *
 * Copyright (c) 2025 M.H.Fan, All rights reserved.             *
 ****************************************************************/

#ifndef SMART_PTR_H
#define SMART_PTR_H

#include <utility>  // for std::exchange, std::swap

template<typename T> class intrusive_ptr {
    T* px = nullptr;

    void add_ref() const { if (px) px->add_ref(); }
    void release() { if (px && px->release()) { delete px; } px = nullptr; }

public:
   ~intrusive_ptr() { release(); }
    intrusive_ptr() noexcept = delete; //default;
    intrusive_ptr(std::nullptr_t) noexcept {}
    explicit intrusive_ptr(T*  ptr): px(ptr)  { add_ref(); }
    intrusive_ptr(const intrusive_ptr& other): px(other.px) { add_ref(); }
    intrusive_ptr(intrusive_ptr&& other) noexcept: px(std::exchange(other.px, nullptr)) {}

    //explicit operator bool() const noexcept { return px != nullptr; }
    //intrusive_ptr& operator=(std::nullptr_t) { reset(); return *this; }
    //intrusive_ptr& operator=(T* ptr) { reset(ptr); return *this; }
    //explicit intrusive_ptr(T&& obj): px(&obj) { add_ref(); }

    intrusive_ptr& operator=(const intrusive_ptr& other) {
        if (this != &other) { release(); px = other.px; add_ref(); } return *this;
    }

    intrusive_ptr& operator=(intrusive_ptr&& other) noexcept {
        if (this != &other) { release(); px = std::exchange(other.px, nullptr); }
        return *this;
    }

    T& operator* () const noexcept { return *px; }
    T* operator->() const noexcept { return  px; }

    bool operator==(const intrusive_ptr& other) const noexcept { return px == other.px; }
    //bool operator!=(const intrusive_ptr& other) const noexcept { return px != other.px; }

    //void reset(T* ptr = nullptr) { if (px != ptr) { release(); px = ptr; add_ref(); } }
    //uint32_t use_count() const noexcept { return px ? px->use_count() : 0; }
    //void swap(intrusive_ptr& other) noexcept { std::swap(px, other.px); }
    //T* detach() noexcept { return std::exchange(px, nullptr); }
    //T* get() const noexcept { return px; }
};

//template<typename T>
//void swap(intrusive_ptr<T>& a, intrusive_ptr<T>& b) noexcept { a.swap(b); }

template<typename T, typename... Args> intrusive_ptr<T> make_intrusive(Args&&... args) {
    return intrusive_ptr<T>(new T(std::forward<Args>(args)...));
}

#endif//SMART_PTR_H
