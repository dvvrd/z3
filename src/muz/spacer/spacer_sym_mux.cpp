/*++
Copyright (c) 2018 Arie Gurfinkel and Microsoft Corporation

Module Name:

    sym_mux.cpp

Abstract:

    A symbol multiplexer that helps with having multiple versions of
    each of a set of symbols.

Author:

    Arie Gurfinkel
    Krystof Hoder (t-khoder) 2011-9-8.

Revision History:

--*/

#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"

#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_sym_mux.h"

using namespace spacer;

sym_mux::sym_mux(ast_manager & m) : m(m) {}
sym_mux::~sym_mux() {
    for (auto &entry : m_entries) {
        dealloc(entry.m_value);
    }
}

func_decl_ref sym_mux::mk_variant(func_decl *fdecl, unsigned i) const {
    func_decl_ref v(m);
    std::string name = fdecl->get_name().str();
    std::string suffix = "_";
    suffix += i == 0 ? "n" : std::to_string(i - 1);
    name += suffix;
    v =  m.mk_func_decl(symbol(name.c_str()), fdecl->get_arity(),
                        fdecl->get_domain(), fdecl->get_range());
    return v;
}

void sym_mux::register_decl(func_decl *fdecl) {
    sym_mux_entry *entry = alloc(sym_mux_entry, m);
    entry->m_main = fdecl;
    entry->m_variants.push_back(mk_variant(fdecl, 0));
    entry->m_variants.push_back(mk_variant(fdecl, 1));

    m_entries.insert(fdecl, entry);
    m_muxes.insert(entry->m_variants.get(0), std::make_tuple(entry, 0, 0));
    m_muxes.insert(entry->m_variants.get(1), std::make_tuple(entry, 1, 0));
}

void sym_mux::ensure_capacity(sym_mux_entry &entry, unsigned sz, unsigned versions_sz) const {
    while (entry.m_variants.size() < sz) {
        unsigned idx = entry.m_variants.size();
        entry.m_variants.push_back (mk_variant(entry.m_main, idx));
        func_decl *v = entry.m_variants.back();
        m_muxes.insert(v, std::make_tuple(&entry, idx, 0));
        for (unsigned i = 0; i < entry.m_versions_of_variants.size(); ++i) {
            entry.m_versions_of_variants[i].push_back(mk_variant(v, i + 1));
        }
    }
    clone_variants(entry, versions_sz);
}

void sym_mux::clone_variants(sym_mux::sym_mux_entry &entry, unsigned sz) const
{
    if (sz < 2) {return;}
    while (entry.m_versions_of_variants.size() < sz - 1) {
        unsigned idx = entry.m_versions_of_variants.size();
        func_decl_ref_vector variants(m);
        for (unsigned i = 0; i < entry.m_variants.size(); ++i) {
            variants.push_back(mk_variant(entry.m_variants.get(i), idx + 1));
            m_muxes.insert(variants.back(), {&entry, i, idx + 1});
        }
        entry.m_versions_of_variants.push_back(variants);
    }
}

bool sym_mux::find_idx(func_decl * sym, unsigned & idx,
                       unsigned &version, func_decl *&associated) const {
    std::tuple<sym_mux_entry *, unsigned, unsigned> entry;
    if (m_muxes.find(sym, entry)) {
        idx = std::get<1>(entry);
        version = std::get<2>(entry);
        associated = std::get<0>(entry)->m_associated;
        return true;
    }
    return false;
}

void sym_mux::associate(func_decl *fdecl, func_decl *associated)
{
    sym_mux_entry *entry;
    if (m_entries.find(fdecl, entry)) {entry->m_associated = associated;}
}

func_decl * sym_mux::find_by_decl(func_decl* fdecl, unsigned idx) const {
    sym_mux_entry *entry = nullptr;
    if (m_entries.find(fdecl, entry)) {
        ensure_capacity(*entry, idx+1, 0);
        return entry->m_variants.get(idx);
    }
    return nullptr;
}

func_decl * sym_mux::shift_decl(func_decl * decl, unsigned src_idx,
                                unsigned tgt_idx) const {
    std::tuple<sym_mux_entry*,unsigned,unsigned> entry;
    if (m_muxes.find(decl, entry)) {
        SASSERT(std::get<1>(entry) == src_idx);
        unsigned version = std::get<2>(entry);
        ensure_capacity(*std::get<0>(entry), tgt_idx + 1, version + 1);
        return version == 0
                ? std::get<0>(entry)->m_variants.get(tgt_idx)
                : std::get<0>(entry)->m_versions_of_variants[version - 1].get(tgt_idx);
    }
    UNREACHABLE();
    return nullptr;
}

func_decl *sym_mux::shift_decl(func_decl *sym, unsigned src_idx,
                               const sym_mux::idx_subst &tgt_idcs) const
{
    std::tuple<sym_mux_entry*,unsigned,unsigned> entry;
    if (m_muxes.find(sym, entry)) {
        SASSERT(std::get<1>(entry) == src_idx);
        unsigned version = std::get<2>(entry);
        versioned_func id{std::get<0>(entry)->m_associated, version};
        auto &tgt = tgt_idcs.find(id);
        unsigned tgt_idx = tgt.first;
        unsigned tgt_version = tgt.second;
        ensure_capacity(*std::get<0>(entry), tgt_idx + 1, tgt_version + 1);
        return tgt_version == 0
                ? std::get<0>(entry)->m_variants.get(tgt_idx)
                : std::get<0>(entry)->m_versions_of_variants[tgt_version - 1].get(tgt_idx);
    }
    UNREACHABLE();
    return nullptr;
}

func_decl * sym_mux::shift_version(func_decl * decl, unsigned src_version,
                                   unsigned tgt_version) const {
    if (src_version == tgt_version) {
        return decl;
    }
    std::tuple<sym_mux_entry*,unsigned,unsigned> entry;
    if (m_muxes.find(decl, entry)) {
        SASSERT(std::get<2>(entry) == src_version);
        unsigned idx = std::get<1>(entry);
        ensure_capacity(*std::get<0>(entry), idx + 1, tgt_version + 1);
        return tgt_version == 0
                ? std::get<0>(entry)->m_variants.get(idx)
                : std::get<0>(entry)->m_versions_of_variants[tgt_version - 1].get(idx);
    }
    UNREACHABLE();
    return nullptr;
}

namespace {
struct formula_checker {
    formula_checker(const sym_mux & parent, unsigned idx) :
        m_parent(parent), m_idx(idx), m_found(false) {}

    void operator()(expr * e) {
        if (m_found || !is_app(e)) { return; }

        func_decl * sym = to_app(e)->get_decl();
        func_decl * tmp = nullptr;
        unsigned version;
        unsigned sym_idx;
        if (!m_parent.find_idx(sym, sym_idx, version, tmp)) { return; }

        bool have_idx = sym_idx == m_idx;
        m_found = !have_idx;
    }

    bool all_have_idx() const {return !m_found;}

private:
    const sym_mux & m_parent;
    unsigned m_idx;
    bool m_found;
};
}

bool sym_mux::is_homogenous_formula(expr * e, unsigned idx) const {
    expr_mark visited;
    formula_checker fck(*this, idx);
    for_each_expr(fck, visited, e);
    return fck.all_have_idx();
}

namespace {
struct conv_rewriter_cfg : public default_rewriter_cfg {
private:
    ast_manager & m;
    const sym_mux & m_parent;
    bool m_subst_version;
    const sym_mux::source_subst *m_from_subst;
    const sym_mux::idx_subst *m_to_subst;
    unsigned m_from_idx;
    unsigned m_to_idx;
    unsigned m_from_version;
    unsigned m_to_version;
    bool m_homogenous;
    expr_ref_vector m_pinned;
public:
    conv_rewriter_cfg(const sym_mux & parent, unsigned from_idx,
                      unsigned to_idx, bool homogenous)
        : m(parent.get_manager()),
          m_parent(parent),
          m_subst_version(false),
          m_from_subst(nullptr),
          m_to_subst(nullptr),
          m_from_idx(from_idx),
          m_to_idx(to_idx),
          m_from_version(0),
          m_to_version(0),
          m_homogenous(homogenous), m_pinned(m) {(void) m_homogenous;}

    conv_rewriter_cfg(const sym_mux & parent, const sym_mux::source_subst &from_idcs,
                      unsigned to_idx, bool homogenous)
        : m(parent.get_manager()),
          m_parent(parent),
          m_subst_version(false),
          m_from_subst(&from_idcs),
          m_to_subst(nullptr),
          m_from_idx(0),
          m_to_idx(to_idx),
          m_from_version(0),
          m_to_version(0),
          m_homogenous(homogenous), m_pinned(m) {(void) m_homogenous;}

    conv_rewriter_cfg(const sym_mux & parent, unsigned from_idx,
                      const sym_mux::idx_subst &tgt_idcs, bool homogenous)
        : m(parent.get_manager()),
          m_parent(parent),
          m_subst_version(false),
          m_from_subst(nullptr),
          m_to_subst(&tgt_idcs),
          m_from_idx(from_idx),
          m_to_idx(0),
          m_from_version(0),
          m_to_version(0),
          m_homogenous(homogenous), m_pinned(m) {(void) m_homogenous;}

    conv_rewriter_cfg(const sym_mux & parent, unsigned from_version, unsigned to_version)
        : m(parent.get_manager()),
          m_parent(parent),
          m_subst_version(true),
          m_from_subst(nullptr),
          m_to_subst(nullptr),
          m_from_idx(0),
          m_to_idx(0),
          m_from_version(from_version),
          m_to_version(to_version),
          m_homogenous(true), m_pinned(m) {(void) m_homogenous;}

    bool get_subst(expr * s, expr * & t, proof * &)
    {
        if (!is_app(s)) { return false; }
        app * a = to_app(s);
        func_decl * sym = a->get_decl();
        func_decl * tgt = nullptr;
        unsigned version = 0;
        func_decl * associated = nullptr;
        unsigned from_idx = 0;
        if (!m_parent.find_idx(sym, from_idx, version, associated)) {
            SASSERT(!m_parent.is_muxed(sym));
            return false;
        }

        if (m_subst_version) {
            SASSERT(version == m_from_version);
            tgt = m_parent.shift_version(sym, m_from_version, m_to_version);
        } else {
            SASSERT((!m_from_subst && !m_to_subst) || associated);
            unsigned tgt_idx = m_to_idx;
            unsigned tgt_version = version;
            if ((!m_from_subst && from_idx != m_from_idx) ||
                (m_from_subst && !m_from_subst->find({associated, version, from_idx}, tgt_version))) {
                    SASSERT(!m_homogenous);
                    return false;
            }
            if (m_to_subst) {
                auto &tgt = m_to_subst->find({associated, version});
                tgt_idx = tgt.first;
                tgt_version = tgt.second;
            }
            tgt = m_parent.shift_decl(sym, from_idx, tgt_idx);
            tgt = m_parent.shift_version(tgt, version, tgt_version);
        }

        t = m.mk_app(tgt, a->get_args());
        m_pinned.push_back(t);
        return true;
    }
};
}

void sym_mux::shift_expr(expr * f, unsigned src_idx, unsigned tgt_idx,
                         expr_ref & res, bool homogenous) const {
    if (src_idx == tgt_idx) {res = f;}
    else {
        conv_rewriter_cfg r_cfg(*this, src_idx, tgt_idx, homogenous);
        rewriter_tpl<conv_rewriter_cfg> rwr(m, false, r_cfg);
        rwr(f, res);
    }
}

void sym_mux::shift_expr(expr * f, const source_subst & src_idcs, unsigned tgt_idx,
                         expr_ref & res, bool homogenous) const {
    conv_rewriter_cfg r_cfg(*this, src_idcs, tgt_idx, homogenous);
    rewriter_tpl<conv_rewriter_cfg> rwr(m, false, r_cfg);
    rwr(f, res);
}

void sym_mux::shift_expr(expr * f, unsigned src_idx, const idx_subst & tgt_idcs,
                         expr_ref & res, bool homogenous) const {
    conv_rewriter_cfg r_cfg(*this, src_idx, tgt_idcs, homogenous);
    rewriter_tpl<conv_rewriter_cfg> rwr(m, false, r_cfg);
    rwr(f, res);
}

void sym_mux::shift_version(expr * f, unsigned src_version, unsigned tgt_version,
                            expr_ref & res) const {
    if (src_version == tgt_version) {
        res = f;
        return;
    }
    conv_rewriter_cfg r_cfg(*this, src_version, tgt_version);
    rewriter_tpl<conv_rewriter_cfg> rwr(m, false, r_cfg);
    rwr(f, res);
}

void sym_mux::shift_version(const expr_ref_vector &in, expr_ref_vector &out,
                            unsigned src_version, unsigned tgt_version) const
{
    out.reset();
    for (expr * f : in) {
        expr_ref shifted(m);
        shift_version(f, src_version, tgt_version, shifted);
        out.push_back(shifted);
    }
}
