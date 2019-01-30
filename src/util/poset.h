/*++
Copyright (c) 2019 Saint-Petersburg State University

Module Name:

    poset.h

Abstract:

    Effective implementation of partially ordered set.

Author:

    Dmitry Mordvinov (dvvrd) 2019-01-29

Revision History:

--*/
#ifndef POSET_H_
#define POSET_H_

#include "util/map.h"
#include "util/obj_hashtable.h"
#include "util/queue.h"

enum class comparison_result {
    equal = 0,
    lt = 1,
    gt = 2,
    incomparable = 3
};

template<typename T, typename Comparator>
class poset {
public:
    typedef hashtable<T*, ptr_hash<T>, ptr_eq<T>> item_set;

private:
    typedef map<T*, item_set, ptr_hash<T>, ptr_eq<T>> porder;
    typedef map<T*, comparison_result, ptr_hash<T>, ptr_eq<T>> cache;

    Comparator m_comparator;
    item_set m_tops;
    item_set m_bottoms;
    porder m_lt_order;       // m_lt_order[x] contains elements immediately less than x
    porder m_gt_order;       // m_gt_order[x] contains elements immediately greater than x

    item_set &init_children(porder &ord, T *element) {
        SASSERT(element);
        auto *e = ord.find_core(element);
        if (e) return e->get_data().m_value;
        ord.insert(element, item_set());
        e = ord.find_core(element);
        SASSERT(e);
        return e->get_data().m_value;
    }

    /// @returns false if element is already inserted into the poset
    bool insert_into_children(T &element, T *parent, item_set &children,
            porder &ord, comparison_result less, cache &visited,
            item_set &lt_res, item_set &gt_res) {
        bool comparable_with_child = false;
        bool greater_than_child = false;
        item_set to_remove;
        for (T *child : children) {
            auto *e = visited.find_core(child);
            comparison_result res = e ? e->get_data().m_value : m_comparator(element, *child);
            if (res == comparison_result::equal) return false;
            if (res == comparison_result::incomparable) continue;
            if (res != less) greater_than_child = true;
            comparable_with_child = true;
            if (e) continue;
            visited.insert(child, res);
            if (res == less) {
                // we have parent > child > element, so pushing the element below the child
                if (!insert_into_children(element, child, init_children(ord, child), ord, less, visited, lt_res, gt_res)) {
                    return false;
                }
            } else {
                to_remove.insert(child);
                // we have parent > element > child, inserting the element between parent and child
                lt_res.insert(child);
            }
        }
        for (T *child : to_remove) {
            children.remove(child);
        }
        if (!comparable_with_child || greater_than_child) {
            children.insert(&element);
            if (parent) {
                gt_res.insert(parent);
            }
        }
        return true;
    }

public:
    poset() {}
    poset(const ptr_vector<T> &incomparable_elements)
    {
        for (T *elem : incomparable_elements) {
            m_tops.insert(elem);
            m_bottoms.insert(elem);
        }
    }

    void insert(T &element) {
        cache visited;
        item_set lt, gt;
        if (insert_into_children(element, nullptr, m_tops, m_lt_order, comparison_result::lt, visited, lt, gt)) {
            visited.reset();
            insert_into_children(element, nullptr, m_bottoms, m_gt_order, comparison_result::gt, visited, gt, lt);
            m_lt_order.insert(&element, lt);
            m_gt_order.insert(&element, gt);
        }
    }

    const item_set &tops() const {return m_tops;}
    const item_set &bottoms() const {return m_bottoms;}

    class queued_iterator {
        const porder *m_ord;
        queue<T*> m_queue;
        item_set m_visited;

    public:
        queued_iterator() : m_ord(nullptr) {}
        queued_iterator(const porder &ord, T &begin) : m_ord(&ord) {
            if (auto *e = ord.find_core(&begin)) {
                for (T *child : e->get_data().m_value) {
                    m_queue.push(child);
                    m_visited.insert(child);
                }
            }
        }

        T * operator*() { return m_queue.top(); }
        const T * operator*() const { return m_queue.top(); }
        queued_iterator & operator++() {
            SASSERT(m_ord);
            SASSERT(!m_queue.empty());
            T *curr = m_queue.pop_front();
            if (auto *e = m_ord->find_core(curr)) {
                for (T *child : e->get_data().m_value) {
                    if (!m_visited.contains(child)) {
                        m_queue.push(child);
                        m_visited.insert(child);
                    }
                }
            }
            return *this;
        }
        bool operator!=(queued_iterator const &it) const {
            return (!m_queue.empty() && it.m_queue.empty()) ||
                    (m_queue.empty() && !it.m_queue.empty()) ||
                    (!m_queue.empty() && !it.m_queue.empty() && m_queue.top() == it.m_queue.top());
        }
        bool operator==(queued_iterator const &it) const { return !(*this != it); }
    };

    class comparable_item_collection {
        queued_iterator m_begin;
        queued_iterator m_end;
    public:
        comparable_item_collection(const porder &ord, T &begin) : m_begin(ord, begin) {}
        const queued_iterator &begin() const { return m_begin; }
        const queued_iterator &end() const { return m_end; }
    };

    comparable_item_collection greater_elements(T &elem) {return comparable_item_collection(m_gt_order, elem);}
    comparable_item_collection smaller_elements(T &elem) {return comparable_item_collection(m_lt_order, elem);}
};

#endif /* POSET_H_ */
