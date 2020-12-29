/*++
Copyright (c) 2018 Arie Gurfinkel and Microsoft Corporation

Module Name:

    sym_mux.h

Abstract:

    A symbol multiplexer that helps with having multiple versions of
    each of a set of symbols.

Author:

    Arie Gurfinkel
    Krystof Hoder (t-khoder) 2011-9-8.

Revision History:

--*/

#ifndef _SYM_MUX_H_
#define _SYM_MUX_H_

#include <string>
#include <map>

#include "ast/ast.h"
#include "util/map.h"
#include "util/vector.h"
#include "muz/spacer/spacer_util.h"

namespace spacer {
class sym_mux {
private:
    class sym_mux_entry {
    public:
        func_decl_ref m_main;
        func_decl_ref_vector m_variants;
        func_decl_ref m_associated;
        sym_mux_entry(ast_manager &m) : m_main(m), m_variants(m), m_associated(m) {}
    };

    typedef obj_map<func_decl, sym_mux_entry*> decl2entry_map;
    typedef obj_map<func_decl, std::pair<sym_mux_entry*, unsigned> > mux2entry_map;

    ast_manager &m;
    mutable decl2entry_map m_entries;
    mutable mux2entry_map m_muxes;

    func_decl_ref mk_variant(func_decl *fdecl, unsigned i) const;
    void ensure_capacity(sym_mux_entry &entry, unsigned sz) const;

public:
    typedef obj_map<func_decl, unsigned> idx_subst;
    typedef std::pair<func_decl*,unsigned> idx_key;
    typedef map<idx_key, func_decl*, pair_hash<ptr_hash<func_decl>, unsigned_hash>, default_eq<idx_key>> ext_idx_subst;
    typedef obj_map<func_decl, func_decl*> subst;

    sym_mux(ast_manager & m);
    ~sym_mux();
    ast_manager & get_manager() const { return m; }

    void register_decl(func_decl *fdecl);
    bool find_idx(func_decl * sym, unsigned & idx, func_decl *&associated) const;
    bool has_index(func_decl * sym, unsigned idx, func_decl *&associated) const
    {unsigned v; return find_idx(sym, v, associated) && idx == v;}

    bool is_muxed(func_decl *fdecl) const {return m_muxes.contains(fdecl);}

    void associate(func_decl *fdecl, func_decl *associated);

    /**
       \brief Return symbol created from prefix, or 0 if the prefix
        was never used.
    */
    func_decl * find_by_decl(func_decl* fdecl, unsigned idx) const;

    /**
       \brief Return true if the only multiplexed symbols which e contains are
       of index idx.
    */
    bool is_homogenous_formula(expr * e, unsigned idx) const;


    /**
      \brief Convert symbol sym which has to be of src_idx variant
      into variant tgt_idx.
    */
    func_decl * shift_decl(func_decl * sym, unsigned src_idx, unsigned tgt_idx) const;

    /**
      \brief Convert symbol sym which has to be of src_idx variant
      into variant tgt_idcs[A], where A is associated with sym.
    */
    func_decl * shift_decl(func_decl * sym, unsigned src_idx,
                           const idx_subst &tgt_idcs) const;

    /**
      \brief Convert src_idx symbols in formula f variant into
      tgt_idx.  If homogenous is true, formula cannot contain symbols
      of other variants.
    */
    void shift_expr(expr * f, unsigned src_idx, unsigned tgt_idx,
                    expr_ref & res, bool homogenous = true) const;

    /**
      \brief Convert symbols of variant idx associated with A in formula f into
      src_idcs[(A, idx)].
      If homogenous is true, formula cannot contain symbols of other variants.
    */
    void shift_expr(expr * f, const ext_idx_subst & src_idcs,
                             expr_ref & res, bool homogenous) const;

    /**
      \brief Convert src_idx symbols in formula f variant into
      tgt_idcs[A], where A is associated with sym.
      If homogenous is true, formula cannot contain symbols of other variants.
    */
    void shift_expr(expr * f, unsigned src_idx, const idx_subst & tgt_idcs,
                    expr_ref & res, bool homogenous = true) const;

    /**
      \brief Performs substitution into f.
      If homogenous is true, formula contains only symbols mapped by subst.
    */
    void substitute(expr * f, const subst & subst,
                    expr_ref & res, bool homogenous = true) const;
};
}

#endif
