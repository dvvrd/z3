/*++
Copyright (c) 2017 Saint-Petersburg State University

Module Name:

    dl_mk_synchronize.h

Abstract:

    Rule transformer that attempts to merge recursive iterations
    relaxing the shape of the inductive invariant.

Author:

    Dmitry Mordvinov (dvvrd) 2017-05-24

Revision History:

--*/
#ifndef DL_MK_SYNCHRONIZE_H_
#define DL_MK_SYNCHRONIZE_H_

#include"dl_context.h"
#include"dl_rule_set.h"
#include"uint_set.h"
#include"dl_rule_transformer.h"
#include"dl_mk_rule_inliner.h"

namespace datalog {

    /**
       \brief Implements a synchronous product transformation.
    */
    class mk_synchronize : public rule_transformer::plugin {
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;

        bool is_recursive_app(rule & r, app * app) const;
        void replace_applications(rule & r, rule_set & rules, ptr_vector<app> & apps, func_decl * pred);

        rule * rename_bound_vars_in_rule(rule * r, unsigned & var_idx);
        vector<rule_vector> rename_bound_vars(ptr_vector<func_decl> const & heads, rule_set & rules);

        app* product_application(ptr_vector<app> const & apps, func_decl * pred);
        rule_ref product_rule(rule_vector const & rules, func_decl * pred);

        void merge_rules(unsigned idx, ptr_vector<func_decl> const & decls, rule_vector &buf,
            vector<rule_vector> const & merged_rules, rule_set & all_rules, func_decl * pred);
        void merge_applications(rule & r, rule_set & rules);

    public:
        /**
           \brief Create synchronous product transformer.
         */
        mk_synchronize(context & ctx, unsigned priority = 22500);

        rule_set * operator()(rule_set const & source);
    };

};

#endif /* DL_MK_SYNCHRONIZE_H_ */

