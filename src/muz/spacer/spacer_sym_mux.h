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
        vector<func_decl_ref_vector> m_versions_of_variants;
        func_decl_ref m_associated;
        sym_mux_entry(ast_manager &m) : m_main(m), m_variants(m), m_associated(m) {}
    };

    typedef obj_map<func_decl, sym_mux_entry*> decl2entry_map;
    typedef obj_map<func_decl, std::tuple<sym_mux_entry*, unsigned, unsigned> > mux2entry_map;

    ast_manager &m;
    mutable decl2entry_map m_entries;
    mutable mux2entry_map m_muxes;

    func_decl_ref mk_variant(func_decl *fdecl, unsigned i) const;
    void ensure_capacity(sym_mux_entry &entry, unsigned sz, unsigned versions_sz) const;
    void clone_variants(sym_mux_entry &entry, unsigned sz) const;

public:
    typedef versioned_func_map<std::pair<unsigned, unsigned>> idx_subst;
    typedef triple<func_decl*,unsigned,unsigned> version_idx_key;
    typedef map<version_idx_key, unsigned, triple_hash<ptr_hash<func_decl>, unsigned_hash, unsigned_hash>, default_eq<version_idx_key>> source_subst;

    sym_mux(ast_manager & m);
    ~sym_mux();
    ast_manager & get_manager() const { return m; }

    void register_decl(func_decl *fdecl);
    bool find_idx(func_decl * sym, unsigned & idx,
                  unsigned &version, func_decl *&associated) const;
    bool has_index(func_decl * sym, unsigned idx,
                   unsigned &version, func_decl *&associated) const
    {unsigned v; return find_idx(sym, v, version, associated) && idx == v;}

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

//    /**
//      \brief Convert symbol sym which has to be of src_idx variant
//      into variant tgt_idx. Validates and converts version of the symbol.
//    */
//    func_decl * shift_decl(func_decl * sym, unsigned src_idx, unsigned src_version,
//                           unsigned tgt_idx, unsigned tgt_version) const;

    /**
      \brief Convert symbol sym which has to be of src_idx variant
      into variant tgt_idcs[A], where A is associated with sym.
    */
    func_decl * shift_decl(func_decl * sym, unsigned src_idx,
                           const idx_subst &tgt_idcs) const;

    /**
      \brief Convert symbol sym which has to be of src_version into tgt_version.
    */
    func_decl * shift_version(func_decl * sym, unsigned src_version,
                              unsigned tgt_version) const;

    /**
      \brief Convert src_idx symbols in formula f variant into
      tgt_idx.  If homogenous is true, formula cannot contain symbols
      of other variants.
    */
    void shift_expr(expr * f, unsigned src_idx, unsigned tgt_idx,
                    expr_ref & res, bool homogenous = true) const;

    /**
      \brief Convert src_idcs[A] symbols in formula f variant into
      tgt_idx, where A is associated with sym.
      If homogenous is true, formula cannot contain symbols of other variants.
    */
    void shift_expr(expr * f, const source_subst & src_idcs, unsigned tgt_idx,
                             expr_ref & res, bool homogenous) const;

    /**
      \brief Convert src_idx symbols in formula f variant into
      tgt_idcs[A], where A is associated with sym.
      If homogenous is true, formula cannot contain symbols of other variants.
    */
    void shift_expr(expr * f, unsigned src_idx, const idx_subst & tgt_idcs,
                    expr_ref & res, bool homogenous = true) const;

    /**
      \brief Convert src_version symbols in formula f into
      tgt_version. Formula cannot contain symbols of other versions.
    */
    void shift_version(expr * f, unsigned src_version, unsigned tgt_version,
                       expr_ref & res) const;

    /**
      \brief Convert input symbols of src_version to tgt_version.
       Formulas cannot contain symbols of other versions.
    */
    void shift_version(const expr_ref_vector & input, expr_ref_vector & output,
                       unsigned src_version, unsigned tgt_version) const;

};
}

#endif
