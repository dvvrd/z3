/**
Copyright (c) 2017 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_context.cpp

Abstract:

    SPACER predicate transformers and search context.

Author:

    Arie Gurfinkel
    Anvesh Komuravelli

    Based on muz/pdr/pdr_context.cpp by Nikolaj Bjorner (nbjorner)

Notes:

--*/

#define ENABLE_ASSERTS false
//#define LOG_STREAM std::cout
#define LOG_STREAM tout

#include <sstream>
#include <iomanip>

#include "muz/base/dl_util.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"
#include "util/util.h"
#include "muz/spacer/spacer_prop_solver.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "ast/for_each_expr.h"
#include "muz/base/dl_rule_set.h"
#include "smt/tactic/unit_subsumption_tactic.h"
#include "model/model_smt2_pp.h"
#include "muz/transforms/dl_mk_rule_inliner.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_util.h"
#include "ast/proofs/proof_checker.h"
#include "smt/smt_value_sort.h"
#include "ast/scoped_proof.h"
#include "muz/spacer/spacer_qe_project.h"
#include "tactic/core/blast_term_ite_tactic.h"

#include "util/timeit.h"
#include "util/luby.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/expr_abstract.h"

#include "smt/smt_solver.h"

#include "muz/spacer/spacer_sat_answer.h"

#define WEAKNESS_MAX 65535

namespace spacer {

/// pob -- proof obligation
pob::pob (pob* parent, pred_transformer& pt,
          unsigned level, unsigned depth, bool add_to_parent):
    m_ref_count (0),
    m_parent (parent), m_pt (pt),
    m_post (m_pt.get_ast_manager ()),
    m_binding(m_pt.get_ast_manager()),
    m_new_post (m_pt.get_ast_manager ()),
    m_level (level), m_depth (depth),
    m_open (true), m_use_farkas (true), m_in_queue(false),
    m_weakness(0), m_blocked_lvl(0) {
    if (add_to_parent && m_parent) {
        m_parent->add_child(*this);
    }
}

void pob::set_post(expr* post) {
    app_ref_vector empty_binding(get_ast_manager());
    set_post(post, empty_binding);
}

void pob::set_post(expr* post, app_ref_vector const &binding) {
    SASSERT(!is_in_queue());
    normalize(post, m_post,
              m_pt.get_context().simplify_pob(),
              m_pt.get_context().use_euf_gen());

    m_binding.reset();
    if (!binding.empty()) {m_binding.append(binding);}
}

void pob::inherit(pob const &p) {
    LOG_STREAM << "POB::INHERIT " << this->pt().name() << " lvl " << this->level() << " from lvl " << p.level() << "\n";
    SASSERT(!is_in_queue());
    SASSERT(m_parent == p.m_parent);
    SASSERT(&m_pt == &p.m_pt);
    SASSERT(m_post == p.m_post);
    SASSERT(!m_new_post);

    m_binding.reset();
    m_binding.append(p.m_binding);

    m_level = p.m_level;
    m_depth = p.m_depth;
    m_open = p.m_open;
    m_use_farkas = p.m_use_farkas;
    m_weakness = p.m_weakness;

    m_derivation = nullptr;
}

void pob::close () {
    if (!m_open) { return; }

    m_derivation = nullptr;
    m_open = false;
    for (unsigned i = 0, sz = m_kids.size (); i < sz; ++i)
    { m_kids [i]->close(); }
}

void pob::get_skolems(app_ref_vector &v) {
    for (unsigned i = 0, sz = m_binding.size(); i < sz; ++i) {
        expr* e;
        e = m_binding.get(i);
        v.push_back (mk_zk_const (get_ast_manager(), i, get_sort(e)));
    }
}

    std::ostream &pob::display(std::ostream &out, bool full) const {
        out << pt().name()
            << " level: " << level()
            << " depth: " << depth()
            << " post_id: " << post()->get_id()
            << (is_in_queue() ? " in_queue" : "");
        if (full) out << "\n" << m_post;
        return out;
    }

// ----------------
// pob_queue

pob* pob_queue::top ()
{
    /// nothing in the queue
    if (m_data.empty()) { return nullptr; }
    /// top queue element is above max level
    if (m_data.top()->level() > m_max_level) { return nullptr; }
    /// top queue element is at the max level, but at a higher than base depth
    if (m_data.top ()->level () == m_max_level &&
        m_data.top()->depth() > m_min_depth) { return nullptr; }

    /// there is something good in the queue
    return m_data.top ();
}

void pob_queue::pop() {
    pob *p = m_data.top();
    p->set_in_queue(false);
    m_data.pop();
}


void pob_queue::set_root(pob& root)
{
    m_root = &root;
    m_max_level = root.level ();
    m_min_depth = root.depth ();
    reset();
}

void pob_queue::reset()
{
    while (!m_data.empty()) {
        pob *p = m_data.top();
        m_data.pop();
        p->set_in_queue(false);
    }
    if (m_root) {
        SASSERT(!m_root->is_in_queue());
        m_root->set_in_queue(true);
        m_data.push(m_root.get());
    }
}

void pob_queue::push(pob &n) {
    if (!n.is_in_queue()) {
        TRACE("pob_queue",
              tout << "pob_queue::push(" << n.post()->get_id() << ")\n";);
        n.set_in_queue(true);
        m_data.push (&n);
        n.get_context().new_pob_eh(&n);
    }
}

// ----------------
// derivation

derivation::derivation (pob& parent, expr *trans,
                        app_ref_vector const &evars) :
    m_parent (parent),
    m_premises (),
    m_active (0),
    m_trans (trans, m_parent.get_ast_manager ()),
    m_evars (evars) {}



void derivation::add_reachability_premise (pred_transformer &pt,
                              func_decl *decl, unsigned oidx,
                              unsigned version, expr *summary,
                              const ptr_vector<app> *aux_vars)
{m_premises.push_back (premise (pt, decl, oidx, version, summary, aux_vars));}

void derivation::add_summary_premise (pred_transformer &pt,
                                      const manager::ext_idx_subst &subst,
                                      const manager::idx_subst &oidcs,
                                      expr *summary)
{m_premises.push_back (premise (pt, subst, oidcs, summary));}


pob *derivation::create_first_child (model &mdl) {
    if (m_premises.empty()) { return nullptr; }
    m_active = 0;
    return create_next_child(mdl);
}

void derivation::exist_skolemize(expr* fml, app_ref_vector &vars, expr_ref &res) {
    ast_manager &m = get_ast_manager();
    if (vars.empty()) {res = fml; return;}
    if (m.is_true(fml) || m.is_false(fml)) {res = fml; return;}

    {
        std::stable_sort (vars.c_ptr(), vars.c_ptr() + vars.size(), sk_lt_proc());
        unsigned i, j, end;
        app_ref v(m);
        for (i = 1, j = 1, end = vars.size(); i < end; ++i) {
            if (vars.get(j-1) != vars.get(i)) {
                v = vars.get(i);   // keep ref
                vars.set(j++, v);
            }
        }
        vars.shrink(j);
    }

    TRACE("spacer", tout << "Skolemizing: ";
          for (auto v : vars) tout << " " << mk_pp(v, m) << " ";
          tout << "\nfrom " << mk_pp(fml, m) << "\n";
        );

    app_ref_vector pinned(m);

    expr_safe_replace sub(m);
    for (unsigned i = 0, sz = vars.size(); i < sz; ++i) {
        expr* e;
        e = vars.get(i);
        pinned.push_back (mk_zk_const (m, i, get_sort(e)));
        sub.insert (e, pinned.back());
    }
    sub(fml, res);
}

pob *derivation::create_next_child(model &mdl)
{
    timeit _timer (is_trace_enabled("spacer_timeit"),
                   "spacer::derivation::create_next_child",
                   verbose_stream ());
    LOG_STREAM << "create_next_child...\n";

    ast_manager &m = get_ast_manager ();
    expr_ref_vector summaries (m);
    app_ref_vector vars(m);

    // -- find first may premise
    while (m_active < m_premises.size() && m_premises[m_active].is_must()) {
//        STRACE("spacer",
//               tout << "[dvvrd] Adding summary into m_trans (m_premises): " << mk_pp(m_premises[m_active].get_summary (), m) << "\n";);
        summaries.push_back (m_premises[m_active].get_summary ());
        vars.append (m_premises[m_active].get_ovars ());
        ++m_active;
    }
    if (m_active >= m_premises.size()) { LOG_STREAM << "  the end!\n";return nullptr; }
    LOG_STREAM << "   " << m_premises[m_active].pt().name() << " (m_active = " << m_active << ")" << "\n";

    // -- update m_trans with the pre-image of m_trans over the must summaries
    summaries.push_back (m_trans);
    STRACE("spacer",
           tout << "[dvvrd] Adding summary into m_trans (m_trans): " << mk_pp(m_trans, m) << "\n";);
    m_trans = mk_and (summaries);
    summaries.reset ();

    LOG_STREAM << "create_next_child(mdl): m_trans before MBP: " << mk_pp(m_trans, m) << "\n";
    LOG_STREAM << "create_next_child(mdl): vars before MBP: " << vars << std::endl;

    if (!vars.empty()) {
        timeit _timer1 (is_trace_enabled("spacer_timeit"),
                        "create_next_child::qproject1",
                        verbose_stream ());
        vars.append(m_evars);
        m_evars.reset();
        pt().mbp(vars, m_trans, mdl,
                 true, pt().get_context().use_ground_pob());
        CTRACE("spacer", !vars.empty(),
               tout << "Failed to eliminate: " << vars << "\n";);
        m_evars.append (vars);
        vars.reset();
    }
    STRACE("spacer",
           tout << "[dvvrd] m_trans after MBP: " << mk_pp(m_trans, m) << "\n";);
    LOG_STREAM << "[dvvrd] m_trans after MBP: " << mk_pp(m_trans, m) << "\n";

//    if (!mdl.is_true(m_premises[m_active].get_summary())) {
//        IF_VERBOSE(1, verbose_stream() << "Summary unexpectendly not true\n";);
//        return nullptr;
//    }


    // create the post-condition by computing a post-image over summaries
    // that precede currently active premise
    for (unsigned i = m_active + 1; i < m_premises.size(); ++i) {
//        STRACE("spacer",
//               tout << "[dvvrd] Adding summary into POST (m_premises): " << "[" << m_premises [i].pt().name() << "]; " << mk_pp(m_premises [i].get_summary (), m) << "; vars: " << m_premises[i].get_ovars() << "\n";);
        summaries.push_back (m_premises [i].get_summary ());
        LOG_STREAM << i  << ": pushing premise " << mk_pp(m_premises[i].get_summary(), m) << " of " << m_premises[i].pt().name() << "\n";
        vars.append (m_premises [i].get_ovars ());
    }
    summaries.push_back (m_trans);
    LOG_STREAM << "summaries before mbp: " << summaries << "\n";
    LOG_STREAM << "vars: " << vars << "\n";
    expr_ref post(m);
    post = mk_and(summaries);
    summaries.reset ();

    STRACE("spacer",
           tout << "[dvvrd] POST before MBP: " << mk_pp(post, m) << "; vars: " << vars << "\n";);
    if (!vars.empty()) {
        timeit _timer2(is_trace_enabled("spacer_timeit"),
                       "create_next_child::qproject2",
                       verbose_stream ());
        // include m_evars in case they can eliminated now as well
        vars.append(m_evars);
        pt().mbp(vars, post, mdl,
                 true, pt().get_context().use_ground_pob());
        CTRACE("spacer", !vars.empty(),
               tout << "Failed to eliminate: " << vars << "\n";);
        //qe::reduce_array_selects (*mev.get_model (), post);
    }
    else {
        // if no variables to eliminate, don't forget about m_evars
        // that occur in m_trans
        vars.append(m_evars);
    }
    STRACE("spacer",
           tout << "[dvvrd] POST after MBP: " << mk_pp(post, m) << "\n";);

    if (!vars.empty()) {
        // existentially quantify out vars from post and skolemize the result
        exist_skolemize(post.get(), vars, post);
    }
    STRACE("spacer",
           tout << "[dvvrd] POST after skolemization: " << mk_pp(post, m) << "\n";);
    LOG_STREAM << "[dvvrd] POST after skolemization: " << mk_pp(post, m) << "\n";

    const manager::ext_idx_subst &subst = m_premises [m_active].get_subst();
    LOG_STREAM << m_parent.pt().name() << ": RENAMING (" << vars << ") "
            << " " << mk_pp(post.get(), m) << "; Idcs:" << std::endl;
    for (auto &p : subst) {
        LOG_STREAM << "{" << p.m_key.first->get_name() << ", " << p.m_key.second  << "} |-> " << p.m_value << std::endl;
    }
    get_manager ().formula_o2tgt (post.get (), post, subst, vars.empty() && subst.size() == 1);
    LOG_STREAM << m_parent.pt().name() << ": RENAMED (" << vars << ") "
            << "INTO " << mk_pp(post.get(), m) << std::endl;


    /* The level and depth are taken from the parent, not the sibling.
       The reasoning is that the sibling has not been checked before,
       and lower level is a better starting point. */
    pob *n = m_premises[m_active].pt().mk_pob(&m_parent,
                                              prev_level (m_parent.level ()),
                                              m_parent.depth (), post, vars);
    IF_VERBOSE (1, verbose_stream ()
                << "\n\tcreate_child: " << n->pt().name ()
                << " (" << n->level () << ", " << n->depth () << ") "
                << (n->use_farkas_generalizer () ? "FAR " : "SUB ")
                << n->post ()->get_id ();
                verbose_stream().flush (););
    return n;
}

pob *derivation::create_next_child ()
{
    if (m_active + 1 >= m_premises.size()) { return nullptr; }
    LOG_STREAM << "parameterless create_next_child (" << m_premises[m_active].pt().name() << ")\n";

    // update the summary of the active node to some must summary

    // construct a new model consistent with the must summary of m_active premise
    pred_transformer &pt = m_premises[m_active].pt ();

    ast_manager &m = get_ast_manager ();
    manager &pm = get_manager ();

    expr_ref_vector summaries (m);

    for (unsigned i = m_active + 1; i < m_premises.size (); ++i)
    { summaries.push_back(m_premises [i].get_summary()); }
//    LOG_STREAM << "summaries before adding trans: " << summaries << "\n";

    // -- orient transition relation towards m_active premise
    expr_ref active_trans (m_trans, m);
    pm.formula_o2n (active_trans.get(), active_trans,
                    m_premises[m_active].get_oidcs (), false);
    summaries.push_back (active_trans);

    // if not true, bail out, the must summary of m_active is not strong enough
    // this is possible if m_post was weakened for some reason
    model_ref mdl;
//    LOG_STREAM << this->pt().name() <<" create_next_child: before\n";
    if (!pt.is_must_reachable(mk_and(summaries), &mdl)) { return nullptr; }

//    LOG_STREAM << this->pt().name() <<" create_next_child: after\n";
    mdl->set_model_completion(false);

    // get an implicant of the summary
    expr_ref_vector u(m), lits(m);
    ptr_vector<app> aux_vars;
    unsigned real_version = 0;
    for (auto &cfunc : pt.heads()) {
        func_decl *h = cfunc.func;
        unsigned count = cfunc.count;
        pred_transformer &pt = get_context().get_pred_transformer(h);
        for (unsigned version = 0; version < count; ++version) {
            // find must summary used
            reach_fact *rf = pt.get_used_rf (*mdl, real_version, true);
            expr_ref renamed(m);
            pm.formula_v2v(rf->get (), renamed, 0, real_version);
            u.push_back (renamed);
            for (app *var : rf->aux_vars()) {
                pm.formula_v2v(var, renamed, 0, real_version);
                aux_vars.push_back(to_app(renamed));
            }
            ++real_version;
        }
    }
    compute_implicant_literals (*mdl, u, lits);
    expr_ref v(m);
    v = mk_and (lits);

    // dvvrd: TODO: uncomment it back?
//    // XXX The summary is not used by anyone after this point
//    m_premises[m_active].set_summary (v, true, &aux_vars);


    /** HACK: needs a rewrite
     * compute post over the new must summary this must be done here
     * because the must summary is currently described over new
     * variables. However, we store it over old-variables, but we do
     * not update the model. So we must get rid of all of the
     * new-variables at this point.
     */
    {
        pred_transformer &pt = m_premises[m_active].pt ();
        app_ref_vector vars (m);

        summaries.reset ();
        summaries.push_back (v);
        summaries.push_back (active_trans);
        m_trans = mk_and (summaries);

        // variables to eliminate
        vars.append (aux_vars.size (), aux_vars.c_ptr ());
        for (unsigned i = 0, sz = pt.sig_size(); i < sz; ++i)
        { vars.push_back(m.mk_const(pm.o2n(pt.sig(i), 0))); }

        if (!vars.empty ()) {
            vars.append(m_evars);
            m_evars.reset();
            LOG_STREAM << "trans before mbp (vars " << vars << "): " << mk_pp(m_trans, m) << "\n";
            this->pt().mbp(vars, m_trans, *mdl,
                           true, this->pt().get_context().use_ground_pob());
            LOG_STREAM << "trans after mbp (vars " << vars << "): " << mk_pp(m_trans, m) << "\n";
            // keep track of implicitly quantified variables
            CTRACE("spacer", !vars.empty(),
                   tout << "Failed to eliminate: " << vars << "\n";);
            m_evars.append (vars);
            vars.reset();
        }
        LOG_STREAM << this->pt().name() <<"create_next_child: m_trans: " << mk_pp(m_trans, m) << "\n";
    }

    m_active++;

    return create_next_child (*mdl);
}

/// derivation::premise

derivation::premise::premise (pred_transformer &pt, func_decl *decl, unsigned o_idx,
                              unsigned version, expr *summary,
                              const ptr_vector<app> *aux_vars) :
    m_pt (pt),
    m_summary (summary, pt.get_ast_manager ()), m_must (true),
    m_ovars (pt.get_ast_manager ())
{

    ast_manager &m = m_pt.get_ast_manager ();
    manager &sm = m_pt.get_manager ();

    sm.add_source_subst(m_oidcs, decl, 0, o_idx, version);

    for (unsigned i = 0; i < m_pt.sig_size(); ++i) {
        func_decl *ovar = sm.o2o(pt.sig(i), 0, o_idx);
        ovar = sm.get_version_pred(ovar, 0, version);
        m_ovars.push_back(m.mk_const(ovar));
    }

    if (aux_vars)
        for (unsigned i = 0, sz = aux_vars->size (); i < sz; ++i)
        { m_ovars.push_back(m.mk_const(sm.n2o(aux_vars->get(i)->get_decl(), o_idx))); }
}

derivation::premise::premise (pred_transformer &pt, const manager::ext_idx_subst &subst,
                              const manager::idx_subst &oidcs, expr *summary) :
    m_pt (pt), m_subst (subst),
    m_summary (summary, pt.get_ast_manager ()), m_must (false),
    m_ovars (pt.get_ast_manager ())
{
    ast_manager &m = m_pt.get_ast_manager ();
    manager &sm = m_pt.get_manager ();

    for (unsigned i = 0; i < m_pt.sig_size(); ++i)
    { m_ovars.push_back(m.mk_const(sm.o2o(pt.sig(i), 0, oidcs))); }
}

derivation::premise::premise (const derivation::premise &p) :
    m_pt (p.m_pt), m_subst (p.m_subst), m_summary (p.m_summary), m_must (p.m_must),
    m_ovars (p.m_ovars) {}

///// \brief Updated the summary.
///// The new summary is over n-variables.
//void derivation::premise::set_summary (expr * summary, bool must,
//                                       const ptr_vector<app> *aux_vars)
//{
//    ast_manager &m = m_pt.get_ast_manager ();
//    manager &sm = m_pt.get_manager ();

//    m_must = must;
//    sm.formula_n2o (summary, m_summary, m_oidcs);

//    m_ovars.reset ();
//    for (unsigned i = 0; i < m_pt.sig_size(); ++i)
//    { m_ovars.push_back(m.mk_const(sm.o2o(m_pt.sig(i), 0, m_oidcs))); }

//    if (aux_vars)
//        for (unsigned i = 0, sz = aux_vars->size (); i < sz; ++i)
//            m_ovars.push_back (m.mk_const (sm.n2o (aux_vars->get (i)->get_decl (),
//                                                   m_oidcs)));
//}


/// Lemma

lemma::lemma (ast_manager &manager, expr * body, unsigned lvl) :
    m_ref_count(0), m(manager),
    m_body(body, m), m_cube(m),
    m_zks(m), m_bindings(m),
    m_pob(nullptr), m_ctp(nullptr),
    m_lvl(lvl), m_init_lvl(m_lvl),
    m_bumped(0), m_weakness(WEAKNESS_MAX),
    m_external(false), m_blocked(false),
    m_background(false) {
    SASSERT(m_body);
    normalize(m_body, m_body);
}

lemma::lemma(pob_ref const &p) :
    m_ref_count(0), m(p->get_ast_manager()),
    m_body(m), m_cube(m),
    m_zks(m), m_bindings(m),
    m_pob(p), m_ctp(nullptr),
    m_lvl(p->level()), m_init_lvl(m_lvl),
    m_bumped(0), m_weakness(p->weakness()),
    m_external(false), m_blocked(false),
    m_background(false) {
    SASSERT(m_pob);
    m_pob->get_skolems(m_zks);
    add_binding(m_pob->get_binding());
}

lemma::lemma(pob_ref const &p, expr_ref_vector &cube, unsigned lvl) :
    m_ref_count(0),
    m(p->get_ast_manager()),
    m_body(m), m_cube(m),
    m_zks(m), m_bindings(m),
    m_pob(p), m_ctp(nullptr),
    m_lvl(p->level()), m_init_lvl(m_lvl),
    m_bumped(0), m_weakness(p->weakness()),
    m_external(false), m_blocked(false),
    m_background(false) {
    if (m_pob) {
        m_pob->get_skolems(m_zks);
        add_binding(m_pob->get_binding());
    }
    update_cube(p, cube);
    set_level(lvl);
}

void lemma::add_skolem(app *zk, app *b) {
    SASSERT(m_bindings.size() == m_zks.size());
    // extend bindings
    m_bindings.push_back(b);
    // extend skolems
    m_zks.push_back(zk);
}


void lemma::mk_expr_core() {
    if (m_body) {return;}

    if (m_pob) {mk_cube_core();}

    SASSERT(!m_cube.empty());
    m_body = ::mk_and(m_cube);
    // normalize works better with a cube
    normalize(m_body, m_body, false /* no simplify bounds */, false /* term_graph */);

    m_body = ::push_not(m_body);

    if (!m_zks.empty() && has_zk_const(m_body)) {
            app_ref_vector zks(m);
            zks.append(m_zks);
            zks.reverse();
            expr_abstract(m, 0,
                          zks.size(), (expr* const*)zks.c_ptr(), m_body,
                          m_body);
            ptr_buffer<sort> sorts;
            svector<symbol> names;
            for (unsigned i=0, sz=zks.size(); i < sz; ++i) {
                sorts.push_back(get_sort(zks.get(i)));
                names.push_back(zks.get(i)->get_decl()->get_name());
            }
            m_body = m.mk_quantifier(forall_k, zks.size(),
                                     sorts.c_ptr(),
                                     names.c_ptr(),
                                     m_body, 15, symbol(m_body->get_id()));
    }
    SASSERT(m_body);
}
void lemma::mk_cube_core() {
    if (!m_cube.empty()) {return;}
    expr_ref cube(m);
    if (m_pob || m_body) {
        if (m_pob) {cube = m_pob->post();}
        else if (m_body) {
            // no quantifiers for now
            SASSERT(!is_quantifier(m_body));
            cube = m_body;
            cube = ::push_not(cube);
        }
        flatten_and(cube, m_cube);
        if (m_cube.empty()) {
            m_cube.push_back(m.mk_true());
        }
        else {
            std::sort(m_cube.c_ptr(), m_cube.c_ptr() + m_cube.size(), ast_lt_proc());
        }
    }
    else {
        UNREACHABLE();
    }
}
bool lemma::is_false() {
    // a lemma is false if
    // 1. it is defined by a cube, and the cube contains a single literal 'true'
    // 2. it is defined by a body, and the body is a single literal false
    // 3. it is defined by a pob, and the pob post is false
    if (m_cube.size() == 1) {return m.is_true(m_cube.get(0));}
    else if (m_body) {return m.is_false(m_body);}
    else if (m_pob) {return m.is_true(m_pob->post());}

    return false;
}
expr* lemma::get_expr() {
    mk_expr_core();
    return m_body;
}
expr_ref_vector const &lemma::get_cube() {
    mk_cube_core();
    return m_cube;
}

void lemma::update_cube (pob_ref const &p, expr_ref_vector &cube) {
    SASSERT(m_pob);
    SASSERT(m_pob.get() == p.get());
    m_cube.reset();
    m_body.reset();
    m_cube.append(cube);
    if (m_cube.empty()) {m_cube.push_back(m.mk_true());}

    // after the cube is updated, if there are no skolems,
    // convert the lemma to quantifier-free
    bool is_quant = false;
    for (unsigned i = 0, sz = cube.size(); !is_quant && i < sz; ++i) {
        is_quant = has_zk_const(cube.get(i));
    }

    if (!is_quant) {
        m_zks.reset();
        m_bindings.reset();
    }
}

bool lemma::has_binding(app_ref_vector const &binding) {
    unsigned num_decls = m_zks.size();

    SASSERT(binding.size() == num_decls);

    if (num_decls == 0) return true;

    for (unsigned off = 0, sz = m_bindings.size(); off < sz; off += num_decls) {
        unsigned i = 0;
        for (; i < num_decls; ++i) {
            if (m_bindings.get(off + i) != binding.get(i)) {
                break;
            }
        }
        if (i == num_decls) return true;
    }
    return false;
}
void lemma::add_binding(app_ref_vector const &binding) {
    if (!has_binding(binding)) {
        m_bindings.append(binding);

        TRACE("spacer",
              tout << "new binding: ";
              for (unsigned i = 0; i < binding.size(); i++)
                  tout << mk_pp(binding.get(i), m) <<  " ";
              tout << "\n";);
    }
}
void lemma::instantiate(expr * const * exprs, expr_ref &result, expr *e) {
    expr *lem = e == nullptr ? get_expr() : e;
    if (!is_quantifier (lem) || m_bindings.empty()) {return;}

    expr *body = to_quantifier(lem)->get_expr();
    unsigned num_decls = to_quantifier(lem)->get_num_decls();
    var_subst vs(m, false);
    result = vs(body, num_decls, exprs);
}

void lemma::set_level (unsigned lvl) {
    if (m_pob){m_pob->blocked_at(lvl);}
    m_lvl = lvl;
}


void lemma::mk_insts(expr_ref_vector &out, expr* e)
{
    expr *lem = e == nullptr ? get_expr() : e;
    if (!is_quantifier (lem) || m_bindings.empty()) {return;}

    unsigned num_decls = to_quantifier(lem)->get_num_decls();
    expr_ref inst(m);
    for (unsigned off = 0, sz = m_bindings.size(); off < sz; off += num_decls) {
        instantiate((expr * const *) m_bindings.c_ptr() + off, inst, e);
        out.push_back(inst);
        inst.reset();
    }
}

// ----------------
// pred_tansformer
pred_transformer::pt_rule &pred_transformer::pt_rules::mk_rule(const pred_transformer::pt_rule &v) {
    pt_rule *p = nullptr;
    if (find_by_rule(v.rule(), p))
        return *p;

    p = alloc(pt_rule, v);
    m_rules.insert(&p->rule(), p);
    if (p->tag()) m_tags.insert(p->tag(), p);
    return *p;
}

const app_ref_vector &pred_transformer::pt_rules::mk_app_tags(manager &pm, pred_transformer::pt_rule &v)
{
    const datalog::rule &r = v.rule();
    unsigned sz = r.get_uninterpreted_tail_size();
    ast_manager &m = pm.get_manager();
    app_ref_vector app_tags(m);
    app_tags.resize(sz);
    for (unsigned i = 0; i < sz; ++i) {
        func_decl *decl = r.get_tail(i)->get_decl();
        std::string name = v.rule().get_decl()->get_name().str() + "__app_" + decl->get_name().str() + std::to_string(i);
        func_decl *tag_decl = m.mk_const_decl(symbol(name.c_str()), m.mk_bool_sort());
        tag_decl = pm.get_n_pred(tag_decl);
        app_tags.set(i, m.mk_const(tag_decl));
    }
    v.set_app_tags(app_tags);
    return v.app_tags();
}


void pred_transformer::occurrence_cache::init(const vector<std::pair<pt_rules&, unsigned>> &crules)
{
    unsigned rule_index = 0;
    unsigned app_delta = 0;
    for (auto &pair : crules) {
        const class pt_rules &rules = pair.first;
        unsigned count = pair.second;
        unsigned max_tail_size = 0;
        for (auto &kv : rules) {
            const datalog::rule &r = kv.get_value()->rule();
            unsigned tail_size = r.get_uninterpreted_tail_size();
            if (max_tail_size < tail_size) {max_tail_size = tail_size;}
            for (unsigned i = 0; i < count; ++i) {
                for (unsigned j = 0; j < tail_size; ++j) {
                    func_decl *f = r.get_tail(j)->get_decl();
                    insert_multiset(m_body_multiset, f);
                    occurrence occ { &r, app_delta + j, rule_index, kv.get_value()->app_tag(j) };
                    auto *e = m_occurrences.insert_if_not_there2(f, vector<occurrence>());
                    e->get_data().m_value.push_back(occ);
                }
            }
            ++rule_index;
        }
        app_delta += max_tail_size;
    }
}

void pred_transformer::occurrence_cache::insert_multiset(func_decl_multiset &set, func_decl *f) {
    auto *e = set.find_core(f);
    if (e) {
        ++e->get_data().m_value;
    } else {
        set.insert(f, 1);
    }
}

bool pred_transformer::occurrence_cache::multiset_contains(const func_decl_multiset &body,
                                                           func_decl *elem, unsigned count) const
{
    auto *e = body.find_core(elem);
    return e ? e->get_data().m_value >= count : count == 0;
}

bool pred_transformer::occurrence_cache::covers(const func_decl_multiset &body,
                                                const func_decl_multivector &sorted_decls) const
{
    for (auto &cfunc : sorted_decls) {
        if (!multiset_contains(body, cfunc.func, cfunc.count)) {
            return false;
        }
    }
    return true;
}

pred_transformer::occurrence_cache::occurrence_cache(manager &pm)
    : pm(pm)
{
}

bool pred_transformer::occurrence_cache::approximately_uses(const func_decl_multivector &head) const
{
    return covers(m_body_multiset, head);
}

bool pred_transformer::occurrence_cache::occurrence_matcher::shift_from(
        unsigned occ_index) {
    const occurrence &from_occ = m_occs[occ_index];
    func_decl *from_head = from_occ.rule->get_decl();
    indexed_rule &from_entry = m_used_rules.find({from_head, from_occ.rule_index});
    SASSERT(from_occ.rule == from_entry.first && from_entry.second > 0);
    --from_entry.second;
    return true;
}

bool pred_transformer::occurrence_cache::occurrence_matcher::shift_to(unsigned index, unsigned occ_index) {
    const occurrence &to_occ = m_occs[occ_index];
    func_decl *to_head = to_occ.rule->get_decl();
    indexed_rule &to_entry = m_used_rules.insert_if_not_there2({to_head, to_occ.rule_index}, {nullptr, 0})->get_data().m_value;
    if (to_entry.first == to_occ.rule || to_entry.second == 0) {
        to_entry.first = to_occ.rule;
        ++to_entry.second;
    } else {
        return false;
    }

    pm.add_o_subst(m_subst, m_head, m_app_tags_base + index, to_occ.idx, to_occ.version);
    func_decl *vtag = pm.get_version_pred(to_occ.app_tag->get_decl(), 0, to_occ.version);
    m_app_tags.set(m_app_tags_base + index, pm.get_manager().mk_const(vtag));
    return true;
}

bool pred_transformer::occurrence_cache::occurrence_matcher::shift_to_next(unsigned index) {
    if (index >= m_count) {return true;}
    unsigned &ptr = m_pointers.get(index);
    unsigned max = m_occs.size();
    if (ptr >= max) {ptr = 0;}
    do {
        while (ptr < max && !shift_to(index, ptr)) ++ptr;
    } while (ptr < max && !shift_to_next(index + 1) && shift_from(ptr));
    return ptr < max;
}

bool pred_transformer::occurrence_cache::occurrence_matcher::match_next() {
    if (!m_initialized) {
        m_initialized = true;
        return shift_to_next(0);
    }
    unsigned index = m_count;
    unsigned max = m_occs.size();
    SASSERT(m_pointers[0] < max);
    while (index > 0) {
        --index;
        unsigned &ptr = m_pointers.get(index);
        SASSERT(ptr < max);
        shift_from(ptr);
        ++ptr;
        if (ptr < max && shift_to_next(index)) {
            break;
        }
    }
    return (m_pointers[0] < max);
}

bool pred_transformer::occurrence_cache::increasing_occurrence_matcher::shift_from(
        unsigned occ_index) {
    const occurrence &from_occ = m_occs[occ_index];
    func_decl *from_head = from_occ.rule->get_decl();
    versioned_rule &from_entry = m_used_rules.find({from_head, from_occ.version});
    SASSERT(from_occ.rule == from_entry.first && from_entry.second > 0);
    --from_entry.second;
    return true;
}

bool pred_transformer::occurrence_cache::increasing_occurrence_matcher::shift_to(unsigned index, unsigned occ_index) {
    const occurrence &to_occ = m_occs[occ_index];
    func_decl *to_head = to_occ.rule->get_decl();
    versioned_rule &to_entry = m_used_rules.insert_if_not_there2({to_head, to_occ.version}, {nullptr, 0})->get_data().m_value;
    if (to_entry.first == to_occ.rule || to_entry.second == 0) {
        to_entry.first = to_occ.rule;
        ++to_entry.second;
    } else {
        return false;
    }

    pm.add_o_subst(m_subst, m_head, m_app_tags_base + index, to_occ.idx, to_occ.version);
    func_decl *vtag = pm.get_version_pred(to_occ.app_tag->get_decl(), 0, to_occ.version);
    m_app_tags.set(m_app_tags_base + index, pm.get_manager().mk_const(vtag));
    return true;
}

bool pred_transformer::occurrence_cache::increasing_occurrence_matcher::shift_to_next(unsigned index) {
    if (index >= m_count) {return true;}
    unsigned &ptr = m_pointers.get(index);
    unsigned max = m_occs.size();
    if (ptr >= max) {ptr = 0;}
    do {
        while (ptr < max && ((index == 0 && !shift_to(index, ptr)) || (index > 0 && ptr <= m_pointers.get(index-1)) || (index > 0 && ptr > m_pointers.get(index-1) && !shift_to(index, ptr)))) ++ptr;
    } while (ptr < max && !shift_to_next(index + 1) && shift_from(ptr++));
    return ptr < max;
}

bool pred_transformer::occurrence_cache::increasing_occurrence_matcher::match_next() {
    if (!m_initialized) {
        m_initialized = true;
        return shift_to_next(0);
    }
    unsigned index = m_count;
    unsigned max = m_occs.size();
    SASSERT(m_pointers[0] < max);
    while (index > 0) {
        --index;
        unsigned &ptr = m_pointers.get(index);
        SASSERT(ptr < max);
        shift_from(ptr);
        ++ptr;
        if (ptr < max && shift_to_next(index)) {
            break;
        }
    }
    return (m_pointers[0] < max);
}

void pred_transformer::occurrence_cache::mk_assumptions_rec(
        const func_decl_multivector &heads, unsigned idx,
        rules_cache &used_rules,
        manager::subst &subst, app_ref_vector &app_tags,
        expr *fml, expr_ref_vector &result)
{
    if (idx >= heads.size()) {
        ast_manager &m = pm.get_manager();
        expr_ref tag(m), tmp(m);
        tag = mk_and(app_tags);
        pm.substitute(fml, tmp, subst);
        result.push_back(m.mk_implies(tag, tmp));
        return;
    }
    auto &cfunc = heads.get(idx);
    func_decl *h = cfunc.func;
    unsigned count = cfunc.count;
    auto *e = m_occurrences.find_core(h);
    if (!e) {
        return;
    }

    const vector<occurrence> &occs = e->get_data().m_value;
    // TODO: choose optimal matching strategy
    // TODO: remove copy-paste!!
    if (occs.size() > 4) {
        increasing_occurrence_matcher matcher(pm, h, count, occs, used_rules, subst, app_tags);
        LOG_STREAM << "using increasing matcher" << std::endl;
        while (matcher.match_next()) {
            LOG_STREAM << "matched! app_tags: ";
            for (auto &tag : app_tags) {
                LOG_STREAM << mk_pp(tag, pm.get_manager()) << " ";
            }
            LOG_STREAM << std::endl;
            mk_assumptions_rec(heads, idx + 1, used_rules, subst, app_tags, fml, result);
        }
    } else {
        LOG_STREAM << "using complete matcher" << std::endl;
        occurrence_matcher matcher(pm, h, count, occs, used_rules, subst, app_tags);
        while (matcher.match_next()) {
            LOG_STREAM << "matched! app_tags: ";
            for (auto &tag : app_tags) {
                LOG_STREAM << mk_pp(tag, pm.get_manager()) << " ";
            }
            LOG_STREAM << std::endl;
            mk_assumptions_rec(heads, idx + 1, used_rules, subst, app_tags, fml, result);
        }
    }
}

void pred_transformer::occurrence_cache::mk_assumptions(const func_decl_multivector &heads,
                                                        expr *fml, expr_ref_vector &result)
{
    rules_cache used_rules;
    manager::idx_subst subst;
    app_ref_vector app_tags(pm.get_manager());
    LOG_STREAM << "mk_assumptions " << mk_pp(fml, pm.get_manager()) << std::endl;
    mk_assumptions_rec(heads, 0, used_rules, subst, app_tags, fml, result);
}


pred_transformer::pred_transformer(context& ctx, manager& pm, func_decl_multivector const& heads):
    pm(pm), m(pm.get_manager()),
    ctx(ctx), m_heads(heads),
    m_name(mk_name()),
    m_sig_idcs(heads.size()),
    m_merged_head(m),
    m_occurrences(pm),
    m_reach_solver (ctx.mk_solver2()),
    m_pobs(*this),
    m_frames(*this),
    m_reach_facts(),
    m_reach_fmls(m),
    m_transition(m), m_init(m),
    m_extend_lit0(m), m_extend_lit(m),
    m_all_init(false)
{
    LOG_STREAM << m_name << "'s reach_solver: " << (long)(m_reach_solver.get()) << std::endl;
    m_solver = alloc(prop_solver, m, ctx.mk_solver0(), ctx.mk_solver1(),
                     ctx.get_params(), m_name);
    init_sig();

    if (heads.size() == 1 && heads[0].count == 1) {
        m_extend_lit = mk_extend_lit();
        m_extend_lit0 = m_extend_lit;
    }
}


symbol pred_transformer::mk_name() const
{
    string_buffer<> buffer;
    for (unsigned i = 0; i < m_heads.size(); ++i) {
        if (i > 0) {buffer << "|><|";}
        buffer << m_heads[i].func->get_name();
        unsigned count = m_heads[i].count;
        if (count > 1) {
            buffer << "^" << count;
        }
    }
    return symbol(buffer.c_str());
}

app_ref pred_transformer::mk_extend_lit() const {
    SASSERT(m_heads.size() == 1 && m_heads[0].count == 1);
    app_ref v(m);
    std::stringstream name;

    func_decl *head = m_heads[0].func;
    name << head->get_name () << "_ext0";
    v = m.mk_const (symbol(name.str().c_str()), m.mk_bool_sort());
    return app_ref(m.mk_not (m.mk_const (pm.get_n_pred (v->get_decl ()))), m);
}


std::ostream& pred_transformer::display(std::ostream& out) const
{
    if (!rules().empty()) { out << "rules\n"; }
    datalog::rule_manager& rm = ctx.get_datalog_context().get_rule_manager();
    for (unsigned i = 0; i < rules().size(); ++i) {
        rm.display_smt2(*rules()[i], out) << "\n";
    }
    out << "transition\n" << mk_pp(transition(), m) << "\n";
    return out;
}

void pred_transformer::collect_statistics(statistics& st) const
{
    m_solver->collect_statistics(st);

    // -- number of times a lemma has been propagated to a higher level
    // -- during push
    st.update("SPACER num propagations", m_stats.m_num_propagations);
    // -- number of lemmas in all current frames
    st.update("SPACER num active lemmas", m_frames.lemma_size ());
    // -- number of lemmas that are inductive invariants
    st.update("SPACER num invariants", m_stats.m_num_invariants);
    // -- number of proof obligations (0 if pobs are not reused)
    st.update("SPACER num pobs", m_pobs.size());

    // -- number of reach facts created
    st.update("SPACER num reach queries", m_stats.m_num_reach_queries);

    st.update("SPACER num ctp blocked", m_stats.m_num_ctp_blocked);
    st.update("SPACER num is_invariant", m_stats.m_num_is_invariant);
    st.update("SPACER num lemma jumped", m_stats.m_num_lemma_level_jump);

    // -- time in rule initialization
    st.update ("time.spacer.init_rules.pt.init", m_initialize_watch.get_seconds ());
    // -- time is must_reachable()
    st.update ("time.spacer.solve.pt.must_reachable",
               m_must_reachable_watch.get_seconds ());
    st.update("time.spacer.ctp", m_ctp_watch.get_seconds());
    st.update("time.spacer.mbp", m_mbp_watch.get_seconds());
}

void pred_transformer::reset_statistics()
{
    m_solver->reset_statistics();
    //m_reachable.reset_statistics();
    m_stats.reset();
    m_initialize_watch.reset ();
    m_must_reachable_watch.reset ();
    m_ctp_watch.reset();
    m_mbp_watch.reset();
}

void pred_transformer::init_sig()
{
    ptr_vector<sort> domain;
    unsigned idx = 0;
    unsigned args_count = 0;
    for (auto &cfunc : m_heads) {
        func_decl *head = cfunc.func;
        m_sig_idcs[idx] = args_count;
        args_count += head->get_arity();
        for (unsigned version = 0; version < cfunc.count; ++version) {
            for (unsigned i = 0; i < head->get_arity(); ++i) {
                sort * arg_sort = head->get_domain(i);
                domain.push_back(arg_sort);
                std::stringstream name_stm;
                name_stm << head->get_name() << '_' << idx++;
                func_decl_ref stm(m);
                stm = m.mk_func_decl(symbol(name_stm.str().c_str()), 0, (sort*const*)nullptr, arg_sort);
                m_sig.push_back(pm.get_o_pred(stm, 0));
                pm.associate(stm, head);
            }
        }
    }
    m_merged_head = (m_heads.size() == 1 && m_heads[0].count == 1)
            ? m_heads[0].func
            : m.mk_func_decl(m_name, domain.size(), domain.c_ptr(), m.mk_bool_sort());
}

void pred_transformer::ensure_level(unsigned level)
{
    if (is_infty_level(level)) { return; }

    while (m_frames.size() <= level) {
        m_frames.add_frame ();
        m_solver->add_level ();
    }
}

// MAKES QUERY
bool pred_transformer::is_must_reachable(expr* state, model_ref* model)
{
    LOG_STREAM << m_name << ": is_must_reachable " << mk_pp(state, m) << "\n";
    scoped_watch _t_(m_must_reachable_watch);
    SASSERT (state);
    solver::scoped_push _sp_(*m_reach_solver);

    bool all_reach_facts_empty = true;
    LOG_STREAM << m_name << "::m_reach_solver: assert (pushed) " << mk_pp(state, m) << std::endl;
    m_reach_solver->assert_expr (state);
    unsigned real_version = 0;
    for (auto &cfunc : heads()) {
        pred_transformer &pt = ctx.get_pred_transformer(cfunc.func);
        for (unsigned version = 0; version < cfunc.count; ++version) {
            if (!pt.m_reach_facts.empty()) {
                all_reach_facts_empty = false;
                expr_ref tag(pt.m_reach_facts.back()->tag(), m);
                pm.formula_v2v(tag, tag, 0, real_version++);
                LOG_STREAM << m_name << "::m_reach_solver: assert (pushed) " << mk_pp(m.mk_not(tag), m) << std::endl;
                m_reach_solver->assert_expr (m.mk_not(tag));
            }
        }
    }
    // XXX This seems to mis-handle the case when state is
    // reachable using the init rule of the current transformer
    if (all_reach_facts_empty) { return false; }
    lbool res = m_reach_solver->check_sat (0, nullptr);
    if (model) { m_reach_solver->get_model(*model); }
    return (res == l_true);
}

pt_collection pred_transformer::subsumers()
{
    return ctx.subsumers(*this);
}

pt_collection pred_transformer::subsumed()
{
    return ctx.subsumed(*this);
}



reach_fact* pred_transformer::get_used_rf (model& mdl, unsigned version, bool all) {
    SASSERT(heads().size() == 1 && heads()[0].count == 1);
    expr_ref v (m);
    model::scoped_model_completion _sc_(mdl, false);

    for (auto *rf : m_reach_facts) {
        if (!all && rf->is_init()) continue;
        expr_ref renamed(m);
        pm.formula_v2v(rf->tag(), renamed, 0, version);
        if (mdl.is_false(renamed)) return rf;
    }
    UNREACHABLE();
    return nullptr;
}

reach_fact *pred_transformer::get_used_origin_rf(model& mdl, unsigned oidx, unsigned version) {
    SASSERT(heads().size() == 1 && heads()[0].count == 1);
    expr_ref b(m), v(m);
    model::scoped_model_completion _sc_(mdl, false);
    for (auto *rf : m_reach_facts) {
        pm.formula_n2o (rf->tag(), v, oidx);
        pm.formula_v2v(v, v, 0, version);
        if (mdl.is_false(v)) return rf;
    }
    UNREACHABLE();
    return nullptr;
}

reach_fact *pred_transformer::get_used_origin_rf(model& mdl, const manager::idx_subst &oidcs) {
    SASSERT(heads().size() == 1 && heads()[0].count == 1);
    expr_ref b(m), v(m);
    model::scoped_model_completion _sc_(mdl, false);
    for (auto *rf : m_reach_facts) {
        pm.formula_n2o (rf->tag(), v, oidcs);
        if (mdl.is_false(v)) return rf;
    }
    UNREACHABLE();
    return nullptr;
}

void pred_transformer::find_rules(model &model, versioned_rule_vector& rules) {
    SASSERT(rules.empty());
    expr_ref val(m);

    func_decl_set processed_heads;
    unsigned rule_version = 0;
    for (auto &cfunc : m_heads) {
        pred_transformer &pt = ctx.get_pred_transformer(cfunc.func);
        for (unsigned version = 0; version < cfunc.count; ++version) {
            for (auto &kv : pt.m_pt_rules) {
                if (!processed_heads.contains(kv.m_value->rule().get_decl())) {
                    func_decl *tag = kv.m_value->tag()->get_decl();
                    tag = pm.get_version_pred(tag, 0, rule_version);
                    if (model.is_true_decl(tag)) {
                        rules.push_back({&kv.m_value->rule(), rule_version++});
                        processed_heads.insert(kv.m_value->rule().get_decl());
                    }
                }
            }
        }
    }
}

void pred_transformer::find_rules(model &model,
                                  vector<bool>& is_concrete,
                                  vector<bool>& reach_pred_used,
                                  unsigned& num_reuse_reach,
                                  versioned_rule_vector& rules)
{
    SASSERT(rules.empty());
    SASSERT(is_concrete.empty());
    versioned_func_map<const datalog::rule*> best_rules;
    versioned_func_map<vector<bool>> reach_pred_used_map;
    versioned_func_map<bool> concrete_heads;

    // find a rule whose tag is true in the model;
    // prefer a rule where the model intersects with reach facts of all predecessors;
    // also find how many predecessors' reach facts are true in the model
    expr_ref vl(m);
    unsigned rule_version = 0;
    for (auto &cfunc : m_heads) {
        class pt_rules &pt_rules = ctx.get_pred_transformer(cfunc.func).m_pt_rules;
        for (unsigned version = 0; version < cfunc.count; ++version) {
            versioned_func id{cfunc.func, version};
            for (auto &kv : pt_rules) {
                func_decl *tag = kv.m_value->tag()->get_decl();
                tag = pm.get_version_pred(tag, 0, rule_version);

                // dvvrd: TODO: something should be done to repeating heads!
                if (!concrete_heads.contains(id) &&
                        model.eval(tag, vl) && m.is_true(vl)) {
                    const datalog::rule *r = &kv.m_value->rule();
                    best_rules.insert(id, r);
                    bool intersects_with_all_rfs = true;
                    num_reuse_reach = 0;
                    unsigned tail_sz = r->get_uninterpreted_tail_size();
                    vector<bool> rpu;
                    for (unsigned i = 0; i < tail_sz; i++) {
                        bool used = false;
                        func_decl* d = r->get_tail(i)->get_decl();
                        const pred_transformer &pt = ctx.get_pred_transformer(d);
                        if (!pt.has_rfs()) {intersects_with_all_rfs = false;}
                        else {
                            expr_ref v(m);
                            pm.formula_n2o(pt.get_last_rf_tag (), v, i);
                            pm.formula_v2v(v, v, 0, rule_version);
                            model.eval(to_app (v.get ())->get_decl (), vl);
                            used = m.is_false (vl);
                            if (!used) {
                                LOG_STREAM << rule_version << ": app of " << d->get_name() << " in rule for " << r->get_decl()->get_name() << " UNUSED" << std::endl;
                            } else {
                                LOG_STREAM << rule_version << ": app of " << mk_pp(v, m) << " in rule for " << r->get_decl()->get_name() << " IS USED" << std::endl;
                            }
                            intersects_with_all_rfs &= used;
                        }

                        rpu.insert(used);
                        if (used) {num_reuse_reach++;}
                    }
                    reach_pred_used_map.insert(id, rpu);
                    if (intersects_with_all_rfs) {
                        concrete_heads.insert(id, true);
                    }
                }
            }
            ++rule_version;
        }
    }
    // SASSERT (r);
    rule_version = 0;
    for (auto &cfunc : m_heads) {
        for (unsigned version = 0; version < cfunc.count; ++version) {
            func_decl *key = cfunc.func;
            versioned_func id{key, version};
            if (best_rules.contains(id)) {
                is_concrete.push_back(concrete_heads.contains(id));
                rules.push_back({best_rules[id], rule_version});
                reach_pred_used.append(reach_pred_used_map.find(id));
            }
            ++rule_version;
        }
    }
}

void pred_transformer::get_transitions(versioned_rule_vector const& rules,
                                       expr_ref_vector &transitions)
{
   for (auto &pair : rules) {
       const datalog::rule *r = pair.first;
       unsigned version = pair.second;
       pred_transformer &pt = ctx.get_pred_transformer(r->get_decl());
       pt_rule *p;
       if (pt.m_pt_rules.find_by_rule(*r, p)) {
           expr_ref trans(m);
           pm.formula_v2v(p->trans(), trans, 0, version);
           transitions.push_back(trans);
       }
   }
}

void pred_transformer::get_initials(const versioned_rule_vector &rules, model &mdl,
                                    expr_ref_vector &initials)
{
    versioned_func_map<bool> used_heads;
    for (auto &vr : rules) {
        used_heads.insert({vr.first->get_decl(), vr.second}, true);
    }
    unsigned real_version = 0;
    for (auto &chead : m_heads) {
        for (unsigned version = 0; version < chead.count; ++version) {
            if (!used_heads.contains({chead.func, real_version})) {
                pred_transformer &pt = ctx.get_pred_transformer(chead.func);
                initials.push_back(pt.get_used_rf(mdl, real_version, true)->get());
            }
            ++real_version;
        }
    }
}

void pred_transformer::get_aux_vars(versioned_rule_vector const& rules,
                                    app_ref_vector& vars)
{
    for (auto &pair : rules) {
        const datalog::rule *r = pair.first;
        unsigned version = pair.second;
        pred_transformer &pt = ctx.get_pred_transformer(r->get_decl());
        pt_rule *p = nullptr;
        VERIFY(pt.m_pt_rules.find_by_rule(*r, p));
        for (app *aux : p->auxs()) {
            expr_ref renamed(m);
            pm.formula_v2v(aux, renamed, 0, version);
            vars.push_back(to_app(renamed));
        }
    }
}

void pred_transformer::find_predecessors(datalog::rule const& r,
                                         ptr_vector<func_decl>& preds) const
{
    preds.reset();
    unsigned tail_sz = r.get_uninterpreted_tail_size();
    for (unsigned ti = 0; ti < tail_sz; ti++) {
        preds.push_back(r.get_tail(ti)->get_decl());
    }
}

void pred_transformer::find_predecessors(indexed_rule_vector const& rules,
                                         vector<indexed_func>& preds) const
{
    preds.reset();
    for (auto &pair : rules) {
        const datalog::rule *r = pair.first;
        unsigned tail_sz = r->get_uninterpreted_tail_size();
        for (unsigned ti = 0; ti < tail_sz; ti++) {
            preds.push_back({r->get_tail(ti)->get_decl(), pair.second});
        }
    }
}

void pred_transformer::simplify_formulas()
{m_frames.simplify_formulas ();}


expr_ref pred_transformer::get_formulas(unsigned level, bool bg)
{
    expr_ref_vector res(m);
    m_frames.get_frame_geq_lemmas (level, res, bg);
//    for (pred_transformer *pt : subsumed())
//        pt->m_frames.get_frame_geq_lemmas (level, res, bg);
    return mk_and(res);
}

bool pred_transformer::propagate_to_next_level (unsigned src_level)
{return m_frames.propagate_to_next_level (src_level);}


/// \brief adds a lemma to the solver and to child solvers
void pred_transformer::add_lemma_core(lemma* lemma, bool ground_only)
{
    SASSERT(!lemma->is_background());
    unsigned lvl = lemma->level();
    expr* l = lemma->get_expr();
    SASSERT(!lemma->is_ground() || is_clause(m, l));
    SASSERT(!is_quantifier(l) || is_clause(m, to_quantifier(l)->get_expr()));

    TRACE("spacer", tout << "add-lemma-core: " << pp_level (lvl)
          << " " << m_name
          << " " << mk_pp (l, m) << "\n";);

    TRACE("core_array_eq", tout << "add-lemma-core: " << pp_level (lvl)
          << " " << m_name
          << " " << mk_pp (l, m) << "\n";);

    STRACE ("spacer_progress",
            tout << "** add-lemma: " << pp_level (lvl) << " "
            << m_name << " "
            << mk_epp (l, m) << "\n";

            if (!lemma->is_ground()) {
                tout << "Bindings: " << lemma->get_bindings() << "\n";
            }
            tout << "\n";
        );


    if (is_infty_level(lvl)) { m_stats.m_num_invariants++; }

    // dvvrd: TODO: merging pts should reuse this code somehow!
    if (lemma->is_ground()) {
        if (is_infty_level(lvl)) {
            m_solver->assert_expr(l);
            for (pred_transformer *pt : subsumers()) {
                LOG_STREAM << "feeding inifinite-level lemma to " << pt->name() << "\n";
                pt->m_solver->assert_expr(l);
            }
        } else {
            ensure_level (lvl);
            m_solver->assert_expr (l, lvl);
            for (pred_transformer *pt : subsumers()) {
                LOG_STREAM << "feeding level " << lvl << " lemma to " << pt->name() << "\n";
                //TODOOODOODOODDOODODODODDODOODOD: implement generic multiplexing a-la mk_assumptions
                if (heads().size() == 1 && heads()[0].count == 1 && pt->heads().size() == 1) {
                    pt->ensure_level (lvl);
                    for (unsigned version = 0; version < pt->heads()[0].count; ++version) {
                        expr_ref renamed(m);
                        pm.formula_v2v(l, renamed, 0, version);
                        pt->m_solver->assert_expr (renamed, lvl);
                    }
                } else {
                pt->ensure_level (lvl);
                pt->m_solver->assert_expr (l, lvl);
                }
            }
        }
    }

    for (unsigned i = 0, sz = m_use.size (); i < sz; ++i)
    { m_use [i]->add_lemma_from_child(*this, lemma,
                                      next_level(lvl), ground_only); }
}

bool pred_transformer::add_lemma (expr *e, unsigned lvl, bool bg) {
    lemma_ref lem = alloc(lemma, m, e, lvl);
    lem->set_background(bg);
    return m_frames.add_lemma(lem.get());
}

void pred_transformer::add_lemma_from_child (pred_transformer& child,
                                             lemma* lemma, unsigned lvl,
                                             bool ground_only)
{
    ensure_level(lvl);
    expr_ref_vector fmls(m);
    mk_assumptions(child.heads(), lemma->get_expr(), fmls);

    for (unsigned i = 0; i < fmls.size(); ++i) {
        expr_ref_vector inst(m);
        expr* a = to_app(fmls.get(i))->get_arg(0);
        if (!lemma->is_ground() && get_context().use_instantiate()) {
            expr* l = to_app(fmls.get(i))->get_arg(1);
            expr_ref grnd_lemma(m);
            app_ref_vector tmp(m);
            lemma->mk_insts(inst, l);
            // -- take ground instance of the current lemma
            ground_expr(to_quantifier(l)->get_expr(), grnd_lemma, tmp);
            inst.push_back(grnd_lemma);
        }
        for (unsigned j=0; j < inst.size(); j++) {
            inst.set(j, m.mk_implies(a, inst.get(j)));
        }
        if (lemma->is_ground() || (get_context().use_qlemmas() && !ground_only)) {
            inst.push_back(fmls.get(i));
        }
        SASSERT (!inst.empty ());
        for (unsigned j = 0; j < inst.size(); ++j) {
            TRACE("spacer_detail", tout << "child property: "
                  << mk_pp(inst.get (j), m) << "\n";);
            if (is_infty_level(lvl)) {
                STRACE("spacer", tout << "[dvvrd] SOLVER [" << m_name << "]: asserting ground infinite level *child* lemma " << mk_pp(inst.get(j), m) << "\n";);
                m_solver->assert_expr(inst.get(j));
            }
            else {
                STRACE("spacer", tout << "[dvvrd] SOLVER [" << m_name << "]: asserting ground level " << lvl << " *child* lemma " << mk_pp(inst.get(j), m) << "\n";);
                m_solver->assert_expr(inst.get(j), lvl);
            }
        }
    }

}

app_ref pred_transformer::mk_fresh_rf_tag (func_decl* head)
{
    SASSERT(heads().size() == 1);
    SASSERT(head);
    std::stringstream name;
    func_decl_ref decl(m);

    name << head->get_name () << "#reach_tag_" << m_reach_facts.size ();
    decl = m.mk_func_decl (symbol (name.str ().c_str ()), 0,
                           (sort*const*)nullptr, m.mk_bool_sort ());
    func_decl *n_decl = pm.get_n_pred (decl);
    pm.associate(decl, head);
    return app_ref(m.mk_const (n_decl), m);
}

void pred_transformer::add_rf (reach_fact *rf)
{
    SASSERT(heads().size() == 1 && heads()[0].count == 1);
    timeit _timer (is_trace_enabled("spacer_timeit"),
                   "spacer::pred_transformer::add_rf",
                   verbose_stream ());

    LOG_STREAM << "[" << m_name << "] add_rf: " << rf->get_rule().get_head()->get_name() << " "
           << (rf->is_init () ? "INIT " : "")
           << mk_pp(rf->get (), m) << std::endl;

    TRACE ("spacer",
           tout << "[" << m_name << "] add_rf: " << rf->get_rule().get_head()->get_name() << " "
           << (rf->is_init () ? "INIT " : "")
           << mk_pp(rf->get (), m) << "\n";);

    // -- avoid duplicates
    if (!rf || get_rf(rf->get())) {return;}

    // all initial facts are grouped together
    SASSERT (!rf->is_init () || m_reach_facts.empty () ||
             m_reach_facts.back ()->is_init ());

    // create tags
    app_ref last_tag(m);
    app_ref new_tag(m);
    expr_ref fml(m);

    if (!m_reach_facts.empty()) {last_tag = m_reach_facts.back()->tag();}
    if (rf->is_init ())
        new_tag = mk_fresh_rf_tag(rf->get_rule().get_decl());
    else
        // side-effect: updates m_solver with rf
        new_tag = to_app(extend_initial(rf->get())->get_arg(0));
    rf->set_tag(new_tag);

    LOG_STREAM << m_name << ": adding " << mk_pp(rf->tag(), m) << "to reach facts" << std::endl;
    // add to m_reach_facts
    m_reach_facts.push_back (rf);

    // update m_reach_solver
    if (last_tag) {fml = m.mk_or(m.mk_not(last_tag), rf->get(), rf->tag());}
    else {fml = m.mk_or(rf->get(), rf->tag());}
    LOG_STREAM << m_name << "::m_reach_solver: assert " << mk_pp(fml, m) << std::endl;
    m_reach_solver->assert_expr (fml);
    for (pred_transformer *pt : subsumers()) {
        unsigned real_version = 0;
        for (auto &p : pt->heads()) {
            if (p.func == m_heads[0].func) {
                for (unsigned version = 0; version < p.count; ++version) {
                    expr_ref renamed(m);
                    pm.formula_v2v(fml, renamed, 0, real_version++);
                    LOG_STREAM << pt->name() << "::m_reach_solver: assert " << mk_pp(renamed, m) << std::endl;
                    pt->m_reach_solver->assert_expr(renamed);
                }
                break;
            } else {real_version += p.count;}
        }
    }
    m_reach_fmls.push_back(fml);
    TRACE ("spacer", tout << "updating reach ctx: " << fml << "\n";);

    // update solvers of other pred_transformers
    // XXX wrap rf into a lemma to fit the API
    lemma fake_lemma(m, fml, infty_level());
    // update users; reach facts are independent of levels
    for (auto use : m_use)
        use->add_lemma_from_child (*this, &fake_lemma, infty_level());
}

expr_ref pred_transformer::get_reachable()
{
    SASSERT(heads().size() == 1 && heads()[0].count == 1);
    expr_ref res(m);
    res = m.mk_false();

    if (!m_reach_facts.empty()) {
        expr_substitution sub(m);
        expr_ref c(m), v(m);
        for (unsigned i = 0, sz = sig_size(); i < sz; ++i) {
            c = m.mk_const(pm.o2n(sig(i), 0));
            v = m.mk_var(i, sig(i)->get_range());
            sub.insert(c, v);
        }
        scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer(m);
        rep->set_substitution(&sub);

        expr_ref_vector args(m);
        for (unsigned i = 0, sz = m_reach_facts.size (); i < sz; ++i) {
            reach_fact *f;
            f = m_reach_facts.get(i);
            expr_ref r(m);
            r = f->get();
            const ptr_vector<app> &aux = f->aux_vars();
            if (!aux.empty()) {
                // -- existentially quantify auxiliary variables
                r = mk_exists (m, aux.size(), aux.c_ptr(), r);
                // XXX not sure how this interacts with variable renaming later on.
                // XXX For now, simply dissallow existentially quantified auxiliaries
                NOT_IMPLEMENTED_YET();
            }
            (*rep)(r);

            args.push_back (r);
        }
        res = mk_or(args);
    }
    return res;
}

expr* pred_transformer::get_last_rf_tag () const
{
    SASSERT(heads().size() == 1);
    return m_reach_facts.empty() ? nullptr : m_reach_facts.back()->tag();
}

expr_ref pred_transformer::get_cover_delta(func_decl* p_orig, int level)
{
    expr_ref result(m.mk_true(), m), v(m), c(m);

    expr_ref_vector lemmas (m);
    m_frames.get_frame_lemmas (level == -1 ? infty_level() : level, lemmas);
    if (!lemmas.empty()) { result = mk_and(lemmas); }

    // replace local constants by bound variables.
    expr_substitution sub(m);
    for (unsigned i = 0; i < sig_size(); ++i) {
        c = m.mk_const(pm.o2n(sig(i), 0));
        v = m.mk_var(i, sig(i)->get_range());
        sub.insert(c, v);
    }
    scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
    rep->set_substitution(&sub);
    (*rep)(result);

    // adjust result according to model converter.
    unsigned arity = sig_size();
    model_ref md = alloc(model, m);
    if (arity == 0) {
        md->register_decl(m_merged_head, result);
    } else {
        func_interp* fi = alloc(func_interp, m, arity);
        fi->set_else(result);
        md->register_decl(m_merged_head, fi);
    }
    model_converter_ref mc = ctx.get_model_converter();
    apply(mc, md);
    if (p_orig->get_arity() == 0) {
        result = md->get_const_interp(p_orig);
    } else {
        result = md->get_func_interp(p_orig)->get_interp();
    }
    return result;
}

/**
 * get an origin summary used by this transformer in the given model
 * level is the level at which may summaries are obtained
 * oidx is the origin index of this predicate in the model
 * must indicates whether a must or a may summary is requested
 *
 * returns an implicant of the summary
 */
expr_ref pred_transformer::get_origin_summary (model &mdl,
                                               unsigned level,
                                               const manager::idx_subst &oidcs,
                                               bool must,
                                               const ptr_vector<app> **aux)
{
    // TODO: what about version in must and may cases?
    model::scoped_model_completion _sc_(mdl, false);
    expr_ref_vector summary (m);
    expr_ref v(m);

    if (!must) { // use may summary
        LOG_STREAM << "get_origin_summary " << level << ": adding " << mk_pp(get_formulas(level), m) << "\n";
        summary.push_back (get_formulas(level));
        // -- no auxiliary variables in lemmas
        *aux = nullptr;
    } else { // find must summary to use
        SASSERT(oidcs.size() == 1);
        LOG_STREAM << "get_origin_summary (must lvl" << level << "): adding " << mk_pp(get_used_origin_rf(mdl, oidcs)->get(), m) << "\n";
        reach_fact *f = get_used_origin_rf(mdl, oidcs);
        summary.push_back (f->get ());
        *aux = &f->aux_vars ();
    }

    SASSERT (!summary.empty ());

    // -- convert to origin
    for (unsigned i = 0; i < summary.size(); ++i) {
        pm.formula_n2o (summary.get (i), v, oidcs);
        summary[i] = v;
    }
    LOG_STREAM << "get_origin_summary " << level << ": after renaming " << summary << "\n";

    // bail out of if the model is insufficient
    // (skip quantified lemmas cause we can't validate them in the model)
    // TBD: for quantified lemmas use current instances
    flatten_and(summary);
    for (auto *s : summary) {
        if (!is_quantifier(s) && !mdl.is_true(s)) {
            LOG_STREAM << "Summary not true in the model: "
                  << mk_pp(s, m) << "\n";
            TRACE("spacer", tout << "Summary not true in the model: "
                  << mk_pp(s, m) << "\n";);
            // return expr_ref(m);
        }
    }

    LOG_STREAM << "get_origin_summary " << level << ": before picking" << summary << "\n";
    // -- pick an implicant
    expr_ref_vector lits(m);
    compute_implicant_literals (mdl, summary, lits);
    LOG_STREAM << "get_origin_summary " << level << ": after picking" << lits << "\n";
    return mk_and(lits);
}


void pred_transformer::add_cover(unsigned level, expr* property, bool bg)
{
    SASSERT(!bg || is_infty_level(level));
    // replace bound variables by local constants.
    expr_ref result(property, m), v(m), c(m);
    expr_substitution sub(m);
    proof_ref pr(m);
    pr = m.mk_asserted(m.mk_true());
    for (unsigned i = 0; i < sig_size(); ++i) {
        c = m.mk_const(pm.o2n(sig(i), 0));
        v = m.mk_var(i, sig(i)->get_range());
        sub.insert(v, c, pr);
    }
    scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
    rep->set_substitution(&sub);
    (*rep)(result);
    TRACE("spacer", tout << "cover:\n" << mk_pp(result, m) << "\n";);

    // add the property.
    expr_ref_vector lemmas(m);
    flatten_and(result, lemmas);
    for (unsigned i = 0, sz = lemmas.size(); i < sz; ++i) {
        add_lemma(lemmas.get(i), level, bg);
    }
}

void pred_transformer::propagate_to_infinity (unsigned level)
{m_frames.propagate_to_infinity (level);}

// compute a conjunction of all background facts
void pred_transformer::get_pred_bg_invs(expr_ref_vector& out) {
    expr_ref inv(m), tmp1(m), tmp2(m);
    ptr_vector<func_decl> preds;
    for (auto &cfunc : m_heads) {
        pred_transformer &hpt = ctx.get_pred_transformer(cfunc.func);
        for (auto &kv : hpt.m_pt_rules) {
            expr_ref tag(m);
            datalog::rule const &r = kv.m_value->rule();
            find_predecessors (r, preds);

            for (unsigned i = 0, preds_sz = preds.size(); i < preds_sz; i++) {
                func_decl* pre = preds[i];
                pred_transformer &pt = ctx.get_pred_transformer(pre);
                // TODO: subsumed_bg_invs?
                const lemma_ref_vector &invs = pt.get_bg_invs();
                CTRACE("spacer", !invs.empty(),
                       tout << "add-bg-invariant: " << mk_pp (pre, m) << "\n";);
                // TODO: real version!
                for (auto inv : invs) {
                    for (unsigned version = 0; version < cfunc.count; ++version) {
                        pm.formula_v2v(kv.m_value->tag(), tag, 0, version);
                        // tag -> inv1 ...  tag -> invn
                        tmp1 = m.mk_implies(tag, inv->get_expr());
                        pm.formula_n2o(tmp1, tmp2, i);
                        pm.formula_v2v(tmp2, tmp2, 0, version);
                        out.push_back(tmp2);
                        TRACE("spacer", tout << tmp2 << "\n";);
                    }
                }
            }
        }
    }
}

void pred_transformer::get_ext_lits(expr_ref_vector &out) const {
    unsigned real_version = 0;
    for (auto &cfunc : m_heads) {
        for (unsigned version = 0; version < cfunc.count; ++version) {
            expr *ext_lit = ctx.get_pred_transformer(cfunc.func).m_extend_lit;
            expr_ref renamed(m);
            pm.formula_v2v(ext_lit, renamed, 0, real_version++);
            out.push_back(renamed);
        }
    }
}


/// \brief Returns true if the obligation is already blocked by current lemmas
// MAKES QUERY
bool pred_transformer::is_blocked (pob &n, unsigned &uses_level)
{
    LOG_STREAM << "pred_transformer::is_blocked\n";
    ensure_level (n.level ());
    prop_solver::scoped_level _sl (*m_solver, n.level ());
    m_solver->set_core (nullptr);
    m_solver->set_model (nullptr);

    expr_ref_vector post(m), _aux(m);
    post.push_back (n.post ());
    // this only uses the lemmas at the current level
    // transition relation is irrelevant
    // XXX quic3: not all lemmas are asserted at the post-condition
    STRACE("spacer", tout << "[dvvrd] SOLVER [" << m_name << "] [is_blocked]: checking " << post.size() << " assumptions for " << mk_pp(n.post(), m) << "\n";);
    lbool res = m_solver->check_assumptions (post, _aux, vector<expr_ref_vector>(),
                                            0, nullptr, 0);
    if (res == l_false) { uses_level = m_solver->uses_level(); }
    return res == l_false;
}


// MAKES QUERY
// DISABLED (QUANTIFIED VERSION OF is_bocked)
bool pred_transformer::is_qblocked (pob &n) {
    // XXX currently disabled
    return false;
    params_ref p;
    p.set_bool("arith.ignore_int", true);
    p.set_bool("array.weak", true);
    p.set_bool("mbqi", false);
    scoped_ptr<solver> s;
    s = mk_smt_solver(m, p, symbol::null);
    s->updt_params(p);
    // XXX force parameters to be set
    s->push();
    s->pop(1);

    expr_ref_vector frame_lemmas(m);
    m_frames.get_frame_geq_lemmas (n.level (), frame_lemmas);

    // assert all lemmas
    bool has_quant = false;
    for (unsigned i = 0, sz = frame_lemmas.size (); i < sz; ++i)
    {
        has_quant = has_quant || is_quantifier(frame_lemmas.get(i));
        s->assert_expr(frame_lemmas.get(i));
    }
    if (!has_quant) return false;

    // assert cti
    s->assert_expr(n.post());
    lbool res = s->check_sat(0, nullptr);

    // if (res == l_false) {
    //     expr_ref_vector core(m);
    //     solver->get_itp_core(core);
    //     expr_ref c(m);
    //     c = mk_and(core);
    //     STRACE("spacer_progress", tout << "core: " << mk_epp(c,m) << "\n";);
    // }
    return res == l_false;
}


void pred_transformer::mbp(app_ref_vector &vars, expr_ref &fml, model &mdl,
                           bool reduce_all_selects, bool force) {
    scoped_watch _t_(m_mbp_watch);
    qe_project(m, vars, fml, mdl, reduce_all_selects, use_native_mbp(), !force);
}

//
// check if predicate transformer has a satisfiable predecessor state.
// returns either a satisfiable predecessor state or
// return a property that blocks state and is implied by the
// predicate transformer (or some unfolding of it).
//
/// MAKES QUERY
lbool pred_transformer::is_reachable(pob& n, expr_ref_vector* core,
                                     model_ref* model, unsigned& uses_level,
                                     vector<bool>& is_concrete,
                                     versioned_rule_vector& rules,
                                     vector<bool>& reach_pred_used,
                                     unsigned& num_reuse_reach)
{
    LOG_STREAM << "==================================================\n";
    LOG_STREAM << "is-reachable: " << m_name << " level: "
          << n.level() << " depth: " << n.depth () << "\n";
          LOG_STREAM << mk_pp(n.post(), m) << "\n";
    TRACE("spacer",
          tout << "is-reachable: " << m_name << " level: "
          << n.level() << " depth: " << n.depth () << "\n";
          tout << mk_pp(n.post(), m) << "\n";);
    timeit _timer (is_trace_enabled("spacer_timeit"),
                   "spacer::pred_transformer::is_reachable",
                   verbose_stream ());
    LOG_STREAM << "pob: " << (long)&n << std::endl;

    ensure_level(n.level());

    // prepare the solver
    prop_solver::scoped_level _sl(*m_solver, n.level());
    prop_solver::scoped_subset_core _sc (*m_solver, !n.use_farkas_generalizer ());
    prop_solver::scoped_weakness _sw(*m_solver, 0,
                                     ctx.weak_abs() ? n.weakness() : UINT_MAX);
    m_solver->set_core(core);
    m_solver->set_model(model);

    expr_ref_vector post (m), reach_assumps (m);
    post.push_back (n.post ());
    flatten_and(post);

    // if equality propagation is disabled in arithmetic, expand
    // equality literals into two inequalities to increase the space
    // for interpolation
    if (!ctx.use_eq_prop()) {
        expand_literals(m, post);
    }

    // populate reach_assumps
    if (n.level () > 0 && !m_all_init) {
        unsigned real_version = 0;
        for (auto &cfunc : m_heads) {
            pred_transformer &hpt = ctx.get_pred_transformer(cfunc.func);
            for (unsigned version = 0; version < cfunc.count; ++version) {
                for (auto &kv : hpt.m_pt_rules) {
                    find_predecessors(kv.m_value->rule(), m_predicates);
                    if (m_predicates.empty()) {continue;}
                    for (unsigned i = 0; i < m_predicates.size(); i++) {
                        const pred_transformer &pt = ctx.get_pred_transformer(m_predicates[i]);
                        if (pt.has_rfs()) {
                            LOG_STREAM << pt.name() << " has rfs" << std::endl;
                            expr_ref a(m);
                            pm.formula_n2o(pt.get_last_rf_tag(), a, i);
                            pm.formula_v2v(a, a, 0, real_version);
                            reach_assumps.push_back(m.mk_not (a));
                        } else {
                            LOG_STREAM << pt.name() << " doesn't have rfs" << std::endl;
                            expr_ref tag(m);
                            pm.formula_v2v(kv.m_value->tag(), tag, 0, real_version);
                            reach_assumps.push_back(m.mk_not (tag));
                            break;
                        }
                    }
                }
                ++real_version;
            }
        }
    }

    TRACE ("spacer",
           if (!reach_assumps.empty ()) {
               tout << "reach assumptions\n";
               for (unsigned i = 0; i < reach_assumps.size (); i++) {
                   tout << mk_pp (reach_assumps.get (i), m) << "\n";
               }
           }
        );

    // check local reachability;
    // result is either sat (with some reach assumps) or
    // unsat (even with no reach assumps)
    expr_ref_vector bg(m);
    get_ext_lits(bg);

    LOG_STREAM << "reach assumps: " << reach_assumps << std::endl;
    LOG_STREAM << "bg: " << bg << std::endl;
    lbool is_sat = m_solver->check_assumptions(post, reach_assumps,
                                               m_transition_clauses,
                                               bg.size(), bg.c_ptr(), 0);
    LOG_STREAM << is_sat << "\n";

    TRACE ("spacer",
           if (!reach_assumps.empty ()) {
               tout << "reach assumptions used\n";
               for (unsigned i = 0; i < reach_assumps.size (); i++) {
                   tout << mk_pp (reach_assumps.get (i), m) << "\n";
               }
           }
        );

    if (is_sat == l_true || is_sat == l_undef) {
        if (core) { core->reset(); }
        if (model && model->get()) {
            find_rules(**model, is_concrete, reach_pred_used, num_reuse_reach, rules);
            LOG_STREAM << "------------------------------------------\n";
            LOG_STREAM << "reachable "
                   << "rules cout: " << rules.size() << "; "
                   << "is_concrete [ ";
                   for (bool concr : is_concrete)
                       LOG_STREAM << concr << " ";
                   LOG_STREAM << "] rused: ";
                   for (unsigned i = 0, sz = reach_pred_used.size (); i < sz; ++i)
                       LOG_STREAM << reach_pred_used [i];
                   LOG_STREAM << "\n";
            LOG_STREAM << "model: ";
            model_smt2_pp(LOG_STREAM, m, **model, 0);

            TRACE ("spacer", tout << "reachable "
                   << "is_concrete [ ";
                   for (bool concr : is_concrete)
                       tout << concr << " ";
                   tout << "] rused: ";
                   for (unsigned i = 0, sz = reach_pred_used.size (); i < sz; ++i)
                       tout << reach_pred_used [i];
                   tout << "\n";);
        }

        return is_sat;
    }
    if (is_sat == l_false) {
        SASSERT (reach_assumps.empty ());
        TRACE ("spacer", tout << "unreachable with lemmas\n";
               if (core) {
                   tout << "Core:\n";
                   for (unsigned i = 0; i < core->size (); i++) {
                       tout << mk_pp (core->get(i), m) << "\n";
                   }
               }
            );
               if (core) {
                   LOG_STREAM << "Core:\n";
                   for (unsigned i = 0; i < core->size (); i++) {
                       LOG_STREAM << mk_pp (core->get(i), m) << "\n";
                   }
               }
        uses_level = m_solver->uses_level();
        return l_false;
    }
    UNREACHABLE();
    return l_undef;
}

/// returns true if lemma is blocked by an existing model
bool pred_transformer::is_ctp_blocked(lemma *lem) {
    if (!ctx.use_ctp() || !lem->has_ctp()) {return false;}

    scoped_watch _t_(m_ctp_watch);

    model_ref &ctp = lem->get_ctp();

    // -- find rule of the ctp
    versioned_rule_vector rules;
    find_rules(*ctp, rules);
    if (rules.empty()) {
        // no rules means lemma is blocked forever because
        // it does not satisfy some derived facts
        lem->set_blocked(true);
        return true;
    }

    vector<versioned_func> preds;
    // -- find predicates along the rule
    find_predecessors(rules, preds);

    // check if any lemma blocks the ctp model
    for (unsigned i = 0, sz = preds.size(); i < sz; ++i) {
        versioned_func &vf = preds.get(i);
        pred_transformer &pt = ctx.get_pred_transformer(vf.func);
        expr_ref lemmas(m), val(m);
        lemmas = pt.get_formulas(lem->level());
        pm.formula_n2o(lemmas.get(), lemmas, i);
        pm.formula_v2v(lemmas.get(), lemmas, 0, vf.version);
        if (ctp->is_false(lemmas)) return false;
    }
// dvvrd: AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA TODO!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
// dvvrd: TODO: should we check the lemmas for single predicates or for the merged symbols?
//    func_decl_ptr_vector preds(m);
//    for (auto *pred : m_predicates) {
//        preds.push_back(pred);
//    }
//    pred_transformer &pt = ctx.get_pred_transformer(preds);
//    expr_ref lemmas(m), val(m);
//    lemmas = pt.get_formulas(lem->level());
//    pm.formula_n2o(lemmas.get(), lemmas, 0);
//    if (ctp->is_false(lemmas)) return false;

    LOG_STREAM << "BLOCKED!\n";
    // lem is blocked by ctp since none of the lemmas at the previous
    // level block ctp
    return true;
}

// MAKES QUERY
bool pred_transformer::is_invariant(unsigned level, lemma* lem,
                                    unsigned& solver_level,
                                    expr_ref_vector* core)
{
    LOG_STREAM << m_name << ": is_invariant " << level << " " << mk_pp(lem->get_expr(), m) << (lem->is_blocked() ? " [blocked]" : "") << "\n";
    if (lem->is_blocked()) return false;

    m_stats.m_num_is_invariant++;
    if (is_ctp_blocked(lem)) {
        m_stats.m_num_ctp_blocked++;
        LOG_STREAM << "ctp blocked! not invariant\n";
        return false;
    }

    expr_ref lemma_expr(m);
    lemma_expr = lem->get_expr();

    expr_ref_vector cand(m), aux(m), conj(m);
    expr_ref gnd_lemma(m);


    if (!get_context().use_qlemmas() && !lem->is_ground()) {
        app_ref_vector tmp(m);
        ground_expr(to_quantifier(lemma_expr)->get_expr (), gnd_lemma, tmp);
        lemma_expr = gnd_lemma.get();
    }

    cand.push_back(mk_not(m, lemma_expr));
    flatten_and (cand);

    prop_solver::scoped_level _sl(*m_solver, level);
    prop_solver::scoped_subset_core _sc (*m_solver, true);
    prop_solver::scoped_weakness _sw (*m_solver, 1,
                                      ctx.weak_abs() ? lem->weakness() : UINT_MAX);
    model_ref mdl;
    model_ref *mdl_ref_ptr = nullptr;
    if (ctx.use_ctp()) {mdl_ref_ptr = &mdl;}
    m_solver->set_core(core);
    m_solver->set_model(mdl_ref_ptr);

    get_ext_lits(conj);
    if (ctx.use_bg_invs()) get_pred_bg_invs(conj);

    STRACE("spacer", tout << "[dvvrd] SOLVER [" << m_name << "] [is_invariant]: checking " << cand.size() << " assumptions for ";);
    for (auto &p : cand) {
        STRACE("spacer", tout << mk_pp(p, m) << "\n";);
    }
    STRACE("spacer", tout << "\n";);
    lbool r = m_solver->check_assumptions (cand, aux, m_transition_clauses,
                                           conj.size(), conj.c_ptr(), 1);
    if (r == l_false) {
        solver_level = m_solver->uses_level ();
        lem->reset_ctp();
        if (level < m_solver->uses_level()) {m_stats.m_num_lemma_level_jump++;}
        SASSERT (level <= solver_level);
    }
    else if (r == l_true) {
//        LOG_STREAM << "CTI: ";
//        model_smt2_pp(LOG_STREAM, m, **mdl_ref_ptr, 0);
//        LOG_STREAM << "\n";
//        LOG_STREAM.flush();
        // TBD: optionally remove unused symbols from the model
        if (mdl_ref_ptr) {lem->set_ctp(*mdl_ref_ptr);}
    }
    else {lem->reset_ctp();}

    LOG_STREAM << "returning " << (r == l_false) << "\n";
    return r == l_false;
}

// MAKES QUERY
// USED BY GENERALIZERS
bool pred_transformer::check_inductive(unsigned level, expr_ref_vector& state,
                                       unsigned& uses_level, unsigned weakness)
{
    expr_ref_vector conj(m), core(m);
    expr_ref states(m);
    states = mk_and(state);
    states = m.mk_not(states);
    mk_assumptions(heads(), states, conj);
    prop_solver::scoped_level _sl(*m_solver, level);
    prop_solver::scoped_subset_core _sc (*m_solver, true);
    prop_solver::scoped_weakness _sw (*m_solver, 1,
                                      ctx.weak_abs() ? weakness : UINT_MAX);
    m_solver->set_core(&core);
    m_solver->set_model (nullptr);
    expr_ref_vector aux (m);
    if (ctx.use_bg_invs()) get_pred_bg_invs(conj);
    get_ext_lits(conj);

    STRACE("spacer", tout << "[dvvrd] SOLVER [" << m_name << "] [check_inductive]: checking " << state.size() << " assumptions for ";);
    for (auto &p : state) {
        STRACE("spacer", tout << mk_pp(p, m) << "\n";);
    }
    STRACE("spacer", tout << "\n";);
    lbool res = m_solver->check_assumptions (state, aux,
                                            m_transition_clauses,
                                            conj.size (), conj.c_ptr (), 1);
    if (res == l_false) {
        state.reset();
        state.append(core);
        uses_level = m_solver->uses_level();
    }
    TRACE ("core_array_eq",
           tout << "check_inductive: "
           << "states: " << mk_pp (states, m)
           << " is: " << res << "\n"
           << "with transition: " << mk_pp (m_transition, m) << "\n";);
    return res == l_false;
}

void pred_transformer::mk_assumptions(func_decl_multivector const& heads, expr* fml,
                                      expr_ref_vector& result)
{
    m_occurrences.mk_assumptions(heads, fml, result);
}

void pred_transformer::initialize(decls2rel const& pts)
{
    m_init = m.mk_false();
    m_transition = m.mk_true();
    init_rules(pts);
    th_rewriter rw(m);
    rw(m_transition);
    rw(m_init);

    STRACE("spacer", tout << "[dvvrd] SOLVER [" << m_name << "] [initialize]: asserting transition " << mk_pp(m_transition, m) << " and initial state " << mk_pp(m_init, m) << "\n";);
    m_solver->assert_expr (m_transition);
    m_solver->assert_expr (m_init, 0);
    TRACE("spacer",
          tout << "Initial state: " << mk_pp(m_init, m) << "\n";
          tout << "Transition:    " << mk_pp(m_transition,  m) << "\n";);
    SASSERT(is_app(m_init));
    //m_reachable.add_init(to_app(m_init));


}

void pred_transformer::subsume_lemmas(const pt_collection &subsumed_pts)
{
    for (pred_transformer *subsumed_pt : subsumed_pts) {
        for (lemma *lemma : subsumed_pt->m_frames.lemmas()) {
            if (lemma->is_ground()) {
                // TODODODODODODODODODODODODODODO
                // dvvrd: TODO: remove copy/paste from add_lemma_core
                unsigned lvl = lemma->level();
                if (is_infty_level(lvl)) {
                    m_solver->assert_expr(lemma->get_expr());
                } else {
                    LOG_STREAM << m_name << ": subsuming level " << lvl << " lemma from " << subsumed_pt->name() << "\n";
                    ensure_level (lvl);
                    m_solver->assert_expr (lemma->get_expr(), lvl);
                }
            }
        }
    }
}

void pred_transformer::merge(const vector<std::pair<pred_transformer*, unsigned>> &pts)
{
    LOG_STREAM << "MERGING! " << m_name << "\n";
    LOG_STREAM.flush();
    // dvvrd: TODO: trace it baby
    expr_ref_vector transition(m);
    expr_ref_vector init(m);
    m_all_init = true;
    unsigned real_version = 0;
    for (auto &pair : pts) {
        pred_transformer *pt = pair.first;
        unsigned count = pair.second;
        for (unsigned version = 0; version < count; ++version) {
            expr_ref tmp(m);
            pm.formula_v2v(pt->m_transition, tmp, 0, real_version);
            transition.push_back(tmp);
            pm.formula_v2v(pt->m_init, tmp, 0, real_version);
            init.push_back(tmp);
            for (const expr_ref_vector &tc : pt->m_transition_clauses) {
                expr_ref_vector renamed_tc(m);
                pm.formulas_v2v(tc, renamed_tc, 0, real_version);
                m_transition_clauses.push_back(renamed_tc);
            }
            m_all_init &= pt->m_all_init;
            ++real_version;
        }
    }
    flatten_and(transition);
    flatten_and(init);
    m_transition = mk_and(transition);
    m_init = mk_and(init);

    m_solver->assert_expr (m_transition);
    m_solver->assert_expr (m_init, 0);
}

void pred_transformer::merge_child_lemmas(const decls2rel &rels)
{
    vector<std::pair<class pt_rules &, unsigned>> rules;
    func_decl_set processed_predecessors;
    for (multifunc &cfunc : m_heads) {
        pred_transformer &pt = ctx.get_pred_transformer(cfunc.func);
        rules.push_back({pt.m_pt_rules, cfunc.count});
    }
    m_occurrences.init(rules);
    unsigned real_version = 0;
    for (multifunc &cfunc : m_heads) {
        pred_transformer &pt = ctx.get_pred_transformer(cfunc.func);
        for (const datalog::rule *rule : pt.m_rules) {
            for (unsigned i = 0; i < rule->get_uninterpreted_tail_size(); ++i) {
                func_decl *decl = rule->get_tail(i)->get_decl();
                if (!processed_predecessors.contains(decl)) {
                    processed_predecessors.insert(decl);
                    pred_transformer &pred_pt = ctx.get_pred_transformer(decl);
                    // XXX this is an entirely hacky way to obtain child reachability facts!
                    for (expr *fml : pred_pt.m_reach_fmls) {
//                        for (unsigned version = 0; version < cfunc.count; ++version) {
//                            expr_ref renamed(m);
//                            pm.formula_v2v(fml, renamed, 0, version);
//                            lemma fake_lemma(m, renamed, infty_level());
                            lemma fake_lemma(m, fml, infty_level());
                            add_lemma_from_child (pred_pt, &fake_lemma, infty_level());
                            // TODO: wat? maybe assert only rfs of subsumer relations?
//                            m_reach_solver->assert_expr(renamed);
//                        }
                    }
                }
            }
        }
        for (expr *fml : pt.m_reach_fmls) {
            for (unsigned version = 0; version < cfunc.count; ++version) {
                expr_ref renamed(m);
                pm.formula_v2v(fml, renamed, 0, real_version++);
                LOG_STREAM << m_name << "::m_reach_solver: merge: assert " << mk_pp(renamed, m) << std::endl;
                m_reach_solver->assert_expr(renamed);
            }
        }
    }
    for (auto &entry : rels) {
        pred_transformer *other = entry.m_value;
        if (m_occurrences.approximately_uses(entry.m_key)) {
            other->add_use(this);
            if (this != other) {
                for (lemma *l: other->m_frames.lemmas()) {
                    add_lemma_from_child(*other, l, next_level(l->level()));
                }
            }
        }
        if (this == other) {
            continue;
        }
        if (other->m_occurrences.approximately_uses(m_heads)) {
            add_use(other);
        }
    }
}

void pred_transformer::init_rfs ()
{
    expr_ref_vector v(m);
    reach_fact_ref fact;

    for (auto &kv : m_pt_rules) {
        pt_rule &ptr = *kv.m_value;
        const datalog::rule& r = ptr.rule();
        if (ptr.is_init()) {
            fact = alloc(reach_fact, m, r, ptr.trans(), ptr.auxs(), true);
            add_rf(fact.get());
        }
    }
}

void pred_transformer::init_rules(decls2rel const& pts) {
    enable_trace("spacer");
    expr_ref_vector transitions(m), not_inits(m);
    app_ref tag(m);
    for (auto r : m_rules) {
        init_rule(pts, *r);
    }

    if (m_pt_rules.empty()) {
        m_transition = m.mk_false();
        m_transition_clauses.reset();
    }
    else {
        SASSERT(m_heads.size() == 1 && m_heads[0].count == 1);
        unsigned i = 0;
        expr_ref_vector transitions(m);
        expr_ref_vector transition_clause(m);
        transition_clause.push_back (m_extend_lit->get_arg(0));
        func_decl *head = m_heads[0].func;
        for (auto &kv : m_pt_rules) {
            pt_rule &r = *kv.m_value;
            std::string name = head->get_name().str() + "__tr" + std::to_string(i);
            func_decl *tag_decl = m.mk_const_decl(symbol(name.c_str()), m.mk_bool_sort());
            tag_decl = pm.get_n_pred(tag_decl);
            tag = m.mk_const(tag_decl);
            m_pt_rules.set_tag(tag, r);
            transition_clause.push_back(tag);
            transitions.push_back(m.mk_implies(r.tag(), r.trans()));
            if (!r.is_init()) {not_inits.push_back(m.mk_not(tag));}
            const app_ref_vector &app_tags = m_pt_rules.mk_app_tags(pm, r);
            transitions.push_back(m.mk_implies(tag, mk_and(app_tags)));
            ++i;
        }

//        if (ctx.use_inc_clause()) {
//            m_transition_clauses.push_back(transition_clause);
//        } else {
            transitions.push_back(mk_or(transition_clause));
//        }
        m_transition = mk_and(transitions);
    }
    // mk init condition -- disables all non-initial transitions
    m_init = mk_and(not_inits);
    // no rule has uninterpreted tail
    if (not_inits.empty ()) {m_all_init = true;}
    vector<std::pair<pt_rules &, unsigned>> pt_rules;
    pt_rules.push_back({m_pt_rules, 1});
    m_occurrences.init(pt_rules);
}

#ifdef Z3DEBUG
static bool is_all_non_null(app_ref_vector const& apps) {
    for (auto *a : apps) if (!a) return false;
    return true;
}
#endif

void pred_transformer::init_rule(decls2rel const& pts, datalog::rule const& rule) {
    scoped_watch _t_(m_initialize_watch);

    // Predicates that are variable representatives. Other predicates at
    // positions the variables occur are made equivalent with these.
    expr_ref_vector side(m);
    app_ref_vector var_reprs(m);
    ptr_vector<app> aux_vars;

    unsigned ut_size = rule.get_uninterpreted_tail_size();
    unsigned t_size  = rule.get_tail_size();
    SASSERT(ut_size <= t_size);
    init_atom(pts, rule.get_head(), var_reprs, side, UINT_MAX);
    for (unsigned i = 0; i < ut_size; ++i) {
        if (rule.is_neg_tail(i)) {
            throw default_exception("SPACER does not support "
                                    "negated predicates in rule tails");
        }
        init_atom(pts, rule.get_tail(i), var_reprs, side, i);
    }
    // -- substitute free variables
    expr_ref trans(m);
    {
        expr_ref_vector tail(m);
        for (unsigned i = ut_size; i < t_size; ++i)
            tail.push_back(rule.get_tail(i));
        trans= mk_and (tail);

        ground_free_vars(trans, var_reprs, aux_vars, ut_size == 0);
        SASSERT(is_all_non_null(var_reprs));

        expr_ref tmp = var_subst(m, false)(trans, var_reprs.size (), (expr*const*)var_reprs.c_ptr());
        flatten_and (tmp, side);
        trans = mk_and(side);
        side.reset ();
    }

    // rewrite and simplify
    th_rewriter rw(m);
    rw(trans);
    if (ctx.blast_term_ite_inflation() > 0) {
        blast_term_ite(trans, ctx.blast_term_ite_inflation());
        rw(trans);
    }
    TRACE("spacer_init_rule", tout << mk_pp(trans, m) << "\n";);

    // allow quantifiers in init rule
    SASSERT(ut_size == 0 || is_ground(trans));
    if (!m.is_false(trans)) {
        pt_rule &ptr = m_pt_rules.mk_rule(m, rule);
        ptr.set_trans(trans);
        ptr.set_auxs(aux_vars);
        ptr.set_reps(var_reprs);
    }

    // TRACE("spacer",
    //       tout << rule.get_decl()->get_name() << "\n";
    //       tout << var_reprs << "\n";);
}


// create constants for free variables in tail.
void pred_transformer::ground_free_vars(expr* e, app_ref_vector& vars,
                                        ptr_vector<app>& aux_vars, bool is_init) {
    expr_free_vars fv;
    fv(e);

    while (vars.size() < fv.size()) {vars.push_back(nullptr);}

    for (unsigned i = 0; i < fv.size(); ++i) {
        if (fv[i] && !vars[i].get()) {
            // AG: is it useful to make names unique across rules?
            app_ref v(m);
            v = m.mk_fresh_const("aux", fv[i]);
            app_ref o(m);
            o = m.mk_const (pm.get_n_pred(v->get_decl ()));
            pm.associate(v->get_decl(), m_heads[0].func);
            vars[i] = o;
            aux_vars.push_back(o);
        }
    }

}

// create names for variables used in relations.
void pred_transformer::init_atom(decls2rel const &pts, app *atom,
                                 app_ref_vector &var_reprs,
                                 expr_ref_vector &side, unsigned tail_idx) {
    unsigned arity = atom->get_num_args();
    func_decl_multivector head;
    head.push_back({atom->get_decl(), 1});
    pred_transformer& pt = *pts.find(head);
    for (unsigned i = 0; i < arity; i++) {
        app_ref rep(m);

        if (tail_idx == UINT_MAX) {
            rep = m.mk_const(pm.o2n(pt.sig(i), 0));
        } else {
            rep = m.mk_const(pm.o2o(pt.sig(i), 0, tail_idx));
        }

        expr * arg = atom->get_arg(i);
        if (is_var(arg)) {
            var * v = to_var(arg);
            unsigned var_idx = v->get_idx();
            if (var_idx >= var_reprs.size()) {
                var_reprs.resize(var_idx+1);
            }
            expr * repr = var_reprs[var_idx].get();
            if (repr) {
                side.push_back(m.mk_eq(rep, repr));
            } else {
                var_reprs[var_idx] = rep;
            }
        } else {
            SASSERT(is_app(arg));
            side.push_back(m.mk_eq(rep, arg));
        }
    }
}

// Adds premises from pts into r.
void pred_transformer::add_premises(decls2rel const& pts, unsigned lvl, expr_ref_vector& r)
{
    if (lvl == 0) {r.push_back(m_init);}
    else {
        r.push_back(m_transition);
        for (auto &tc : m_transition_clauses) {
            if (!tc.empty()) {
                expr_ref c(m);
                c = mk_or(tc);
                r.push_back(c);
            }
        }
    }
    for (unsigned i = 0; i < rules().size(); ++i) {
        add_premises(pts, lvl, *rules()[i], r);
    }
}

void pred_transformer::add_premises(decls2rel const& pts, unsigned lvl,
                                    datalog::rule& rule, expr_ref_vector& r)
{
    find_predecessors(rule, m_predicates);
    for (unsigned i = 0; i < m_predicates.size(); ++i) {
        expr_ref tmp(m);
        func_decl_multivector head;
        head.push_back({m_predicates[i], 1});
        pred_transformer& pt = *pts.find(head);
        expr_ref inv = pt.get_formulas(lvl);
        if (!m.is_true(inv)) {
            pm.formula_n2o(inv, tmp, i, true);
            r.push_back(tmp);
        }
    }
}

void pred_transformer::inherit_lemmas(pred_transformer& other)
{m_frames.inherit_frames (other.m_frames);}

app* pred_transformer::extend_initial (expr *e)
{
    SASSERT(m_heads.size() == 1 && m_heads[0].count == 1);
    // create fresh extend literal
    std::stringstream name;
    name << m_name << "_ext";
    app_ref o(m);
    o = m.mk_fresh_const (name.str ().c_str (),
                          m.mk_bool_sort ());
    app_ref v(m);
    v = m.mk_const (pm.get_n_pred (o->get_decl ()));
    pm.associate(o->get_decl(), m_heads[0].func);

    expr_ref ic(m);

    // -- extend the initial condition
    ic = m.mk_or (m_extend_lit, e, v);
    m_solver->assert_expr (ic);
    for (pred_transformer *pt : subsumers()) {
        unsigned real_version = 0;
        for (auto cfunc : pt->heads()) {
            if (cfunc.func == m_heads[0].func) {
                for (unsigned version = 0; version < cfunc.count; ++version) {
                    expr_ref renamed(m);
                    pm.formula_v2v(ic, renamed, 0, real_version++);
                    pt->m_solver->assert_expr (renamed);
                }
                break;
            }
        }
    }

    // -- remember the new extend literal
    m_extend_lit = m.mk_not (v);

    LOG_STREAM << "[" << m_name << "]: extend_initial " << mk_pp(ic, m) << " to " << mk_pp(m_extend_lit, m) << std::endl;
    return m_extend_lit;
}



/// pred_transformer::frames
bool pred_transformer::frames::add_lemma(lemma *new_lemma)
{
    LOG_STREAM << "add-lemma: " << pp_level(new_lemma->level()) << " "
          << m_pt.name() << " "
          << mk_pp(new_lemma->get_expr(), m_pt.get_ast_manager()) << "\n";
    TRACE("spacer", tout << "add-lemma: " << pp_level(new_lemma->level()) << " "
          << m_pt.name() << " "
          << mk_pp(new_lemma->get_expr(), m_pt.get_ast_manager()) << "\n";);

    if (new_lemma->is_background()) {
        SASSERT (is_infty_level(new_lemma->level()));

        for (auto &l : m_bg_invs) {
            if (l->get_expr() == new_lemma->get_expr()) return false;
        }
        TRACE("spacer", tout << "add-external-lemma: "
              << pp_level(new_lemma->level()) << " "
              << m_pt.name() << " "
              << mk_pp(new_lemma->get_expr(), m_pt.get_ast_manager()) << "\n";);

        m_bg_invs.push_back(new_lemma);
        return true;
    }

    unsigned i = 0;
    for (auto *old_lemma : m_lemmas) {
        if (old_lemma->get_expr() == new_lemma->get_expr()) {
            m_pt.get_context().new_lemma_eh(m_pt, new_lemma);

            // register existing lemma with the pob
            if (new_lemma->has_pob()) {
                pob_ref &pob = new_lemma->get_pob();
                if (!pob->lemmas().contains(old_lemma))
                    pob->add_lemma(old_lemma);
            }

            // extend bindings if needed
            if (!new_lemma->get_bindings().empty()) {
                old_lemma->add_binding(new_lemma->get_bindings());
            }
            // if the lemma is at a higher level, skip it,
            if (old_lemma->level() >= new_lemma->level()) {
                TRACE("spacer", tout << "Already at a higher level: "
                      << pp_level(old_lemma->level()) << "\n";);
                // but, since the instances might be new, assert the
                // instances that have been copied into m_lemmas[i]
                if (!new_lemma->get_bindings().empty()) {
                    m_pt.add_lemma_core(old_lemma, true);
                }
                if (is_infty_level(old_lemma->level())) {
                    old_lemma->bump();
                    if (old_lemma->get_bumped() >= 100) {
                        IF_VERBOSE(1, verbose_stream() << "Adding lemma to oo "
                                   << old_lemma->get_bumped() << " "
                                   << mk_pp(old_lemma->get_expr(),
                                            m_pt.get_ast_manager()) << "\n";);
                        throw default_exception("Stuck on a lemma");
                    }
                }
                // no new lemma added
                return false;
            }

            // update level of the existing lemma
            old_lemma->set_level(new_lemma->level());
            // assert lemma in the solver
            m_pt.add_lemma_core(old_lemma, false);
            // move the lemma to its new place to maintain sortedness
            unsigned sz = m_lemmas.size();
            for (unsigned j = i;
                 (j + 1) < sz && m_lt(m_lemmas[j + 1], m_lemmas[j]); ++j) {
                m_lemmas.swap (j, j+1);
            }
            return true;
        }
        i++;
    }

    LOG_STREAM << "ADDING LEMMA " << mk_pp(new_lemma->get_expr(), m_pt.get_ast_manager()) << " IN FACT\n";
    // new_lemma is really new
    m_lemmas.push_back(new_lemma);
    // XXX because m_lemmas is reduced, keep secondary vector of all lemmas
    // XXX so that pob can refer to its lemmas without creating reference cycles
    m_pinned_lemmas.push_back(new_lemma);
    m_sorted = false;
    m_pt.add_lemma_core(new_lemma);

    if (new_lemma->has_pob()) {new_lemma->get_pob()->add_lemma(new_lemma);}

    if (!new_lemma->external()) {
        m_pt.get_context().new_lemma_eh(m_pt, new_lemma);
    }
    return true;
}


// adds lemma core to m_pt
void pred_transformer::frames::propagate_to_infinity (unsigned level)
{
    LOG_STREAM << m_pt.name() << " propagate_to_infinity " << level << "\n";
    for (unsigned i = 0, sz = m_lemmas.size (); i < sz; ++i)
        if (m_lemmas[i]->level() >= level && !is_infty_level(m_lemmas [i]->level())) {
            LOG_STREAM << m_pt.name() << ": SETTING LEVEL 'INF' for " << mk_pp(m_lemmas[i]->get_expr(), m_pt.get_ast_manager()) << "\n";
            m_lemmas [i]->set_level (infty_level ());
            m_pt.add_lemma_core (m_lemmas [i]);
            m_sorted = false;
        }
}

void pred_transformer::frames::sort ()
{
    if (m_sorted) { return; }

    m_sorted = true;
    std::sort(m_lemmas.c_ptr(), m_lemmas.c_ptr() + m_lemmas.size (), m_lt);
}

bool pred_transformer::frames::propagate_to_next_level (unsigned level)
{
    LOG_STREAM << m_pt.name() << " propagate_to_next_level " << level << "\n";
    sort ();
    bool all = true;


    if (m_lemmas.empty()) { return all; }

    unsigned tgt_level = next_level (level);
    m_pt.ensure_level (tgt_level);

    for (unsigned i = 0, sz = m_lemmas.size(); i < sz && m_lemmas [i]->level() <= level;) {
        if (m_lemmas [i]->level () < level) {++i; continue;}

        unsigned solver_level;
        if (m_pt.is_invariant(tgt_level, m_lemmas.get(i), solver_level)) {
            LOG_STREAM << m_pt.name() << ": SETTING LEVEL " << solver_level << " for " << mk_pp(m_lemmas[i]->get_expr(), m_pt.get_ast_manager()) << "\n";
            m_lemmas [i]->set_level (solver_level);
            m_pt.add_lemma_core (m_lemmas.get(i));

            // percolate the lemma up to its new place
            for (unsigned j = i; (j+1) < sz && m_lt (m_lemmas[j+1], m_lemmas[j]); ++j) {
                m_lemmas.swap(j, j + 1);
            }
            ++m_pt.m_stats.m_num_propagations;
        } else {
            all = false;
            ++i;
        }
    }

    return all;
}

void pred_transformer::frames::simplify_formulas ()
{
    // number of subsumed lemmas
    unsigned num_sumbsumed = 0;

    // ensure that the lemmas are sorted
    sort();
    ast_manager &m = m_pt.get_ast_manager();

    tactic_ref simplifier = mk_unit_subsumption_tactic(m);
    lemma_ref_vector new_lemmas;

    unsigned lemmas_size = m_lemmas.size();
    goal_ref g(alloc (goal, m, false, false, false));

    unsigned j = 0;
    // for every frame + infinity frame
    for (unsigned i = 0; i <= m_size; ++i) {
        g->reset_all ();
        // normalize level
        unsigned level = i < m_size ? i : infty_level ();

        goal_ref_buffer result;

        // simplify lemmas of the current level
        // XXX lemmas of higher levels can be assumed in background
        // XXX decide what to do with non-ground lemmas!
        unsigned begin = j;
        for (; j < lemmas_size && m_lemmas[j]->level() <= level; ++j) {
            if (m_lemmas[j]->level() == level) {
                g->assert_expr(m_lemmas[j]->get_expr());
            }
        }
        unsigned end = j;

        unsigned sz = end - begin;
        // no lemmas at current level, move to next level
        if (sz <= 0) {continue;}

        // exactly one lemma at current level, nothing to
        // simplify. move to next level
        if (sz == 1) {
            new_lemmas.push_back(m_lemmas[begin]);
            continue;
        }

        // more than one lemma at current level. simplify.
        (*simplifier)(g, result);
        SASSERT(result.size () == 1);
        goal *r = result[0];

        // no simplification happened, copy all the lemmas
        if (r->size () == sz) {
            for (unsigned n = begin; n < end; ++n) {
                new_lemmas.push_back (m_lemmas[n]);
            }
        }
        // something got simplified, find out which lemmas remain
        else {
            num_sumbsumed += (sz - r->size());
            // For every expression in the result, copy corresponding
            // lemma into new_lemmas
            // XXX linear search. optimize if needed.
            for (unsigned k = 0; k < r->size(); ++k) {
                bool found = false;
                for (unsigned n = begin; n < end; ++n) {
                    if (m_lemmas[n]->get_expr() == r->form(k)) {
                        new_lemmas.push_back(m_lemmas[n]);
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    verbose_stream() << "Failed to find a lemma for: "
                                     << mk_pp(r->form(k), m) << "\n";
                    verbose_stream() << "Available lemmas are: ";
                    for (unsigned n = begin; n < end; ++n) {
                        verbose_stream() << n << ": "
                                         << mk_pp(m_lemmas[n]->get_expr(), m)
                                         << "\n";
                    }

                    verbose_stream() << "Simplified goal is:\n";
                    for (unsigned k = 0; k < r->size(); ++k)
                        verbose_stream() << k << ": "
                                         << mk_pp(r->form(k), m) << "\n";
                }
                ENSURE(found);
                SASSERT(found);
            }
        }
    }

    SASSERT(new_lemmas.size() + num_sumbsumed == m_lemmas.size());
    ENSURE(new_lemmas.size() + num_sumbsumed == m_lemmas.size());
    if (new_lemmas.size() < m_lemmas.size()) {
        m_lemmas.reset();
        m_lemmas.append(new_lemmas);
        m_sorted = false;
        sort();
    }
}

/// pred_transformer::pobs

pob* pred_transformer::pob_manager::mk_pob(pob *parent,
                                           unsigned level, unsigned depth,
                                           expr *post,
                                           app_ref_vector const &b)
{
    // create a new pob and set its post to normalize it
    pob p(parent, m_pt, level, depth, false);
    p.set_post(post, b);

    if (m_pobs.contains(p.post())) {
        for (auto *f : m_pobs[p.post()]) {
            if (f->parent() == parent && !f->is_in_queue()) {
                f->inherit(p);
                return f;
            }
        }
    }

    pob* n = alloc(pob, parent, m_pt, level, depth);
    n->set_post(post, b);
    m_pinned.push_back(n);

    if (m_pobs.contains(n->post())) {
        m_pobs[n->post()].push_back(n);
    }
    else {
        pob_buffer buf;
        buf.push_back(n);
        m_pobs.insert(n->post(), buf);
    }
    return n;
}

pob* pred_transformer::pob_manager::find_pob(pob* parent, expr *post) {
    pob p(parent, m_pt, 0, 0, false);
    p.set_post(post);
    pob *res = nullptr;
    if (m_pobs.contains(p.post())) {
        for (auto *f : m_pobs[p.post()]) {
            if (f->parent() == parent) {
                // try to find pob not already in queue
                if (!f->is_in_queue()) return f;
                res = f;
            }
        }
    }
    return res;
}


// ----------------
// context

comparison_result pt_subsumption_comparator::operator()(const pred_transformer &pt1, const pred_transformer &pt2) {
    return compare_func_multivectors(pt1.heads(), pt2.heads());
}

context::context(fp_params const& params, ast_manager& m) :
    m_params(params),
    m(m),
    m_context(nullptr),
    m_pm(m),
    m_query_pred(m),
    m_query(nullptr),
    m_pob_queue(),
    m_last_result(l_undef),
    m_inductive_lvl(0),
    m_expanded_lvl(0),
    m_json_marshaller(this) {
    ref<solver> pool0_base =
        mk_smt_solver(m, params_ref::get_empty(), symbol::null);
    ref<solver> pool1_base =
        mk_smt_solver(m, params_ref::get_empty(), symbol::null);
    ref<solver> pool2_base =
        mk_smt_solver(m, params_ref::get_empty(), symbol::null);

    unsigned max_num_contexts = params.spacer_max_num_contexts();
    m_pool0 = alloc(solver_pool, pool0_base.get(), max_num_contexts);
    m_pool1 = alloc(solver_pool, pool1_base.get(), max_num_contexts);
    m_pool2 = alloc(solver_pool, pool2_base.get(), max_num_contexts);

    updt_params();
}

context::~context()
{
    reset_lemma_generalizers();
    reset();
}

void context::updt_params() {
    m_random.set_seed(m_params.spacer_random_seed());
    m_children_order = static_cast<spacer_children_order>(m_params.spacer_order_children());
    m_simplify_pob = m_params.spacer_simplify_pob();
    m_use_euf_gen = m_params.spacer_use_euf_gen();
    m_use_ctp = m_params.spacer_ctp();
    m_use_inc_clause = m_params.spacer_use_inc_clause();
    m_blast_term_ite_inflation = m_params.spacer_blast_term_ite_inflation();
    m_use_ind_gen = m_params.spacer_use_inductive_generalizer();
    m_use_array_eq_gen = m_params.spacer_use_array_eq_generalizer();
    m_validate_lemmas = m_params.spacer_validate_lemmas();
    m_max_level = m_params.spacer_max_level ();
    m_use_propagate = m_params.spacer_propagate ();
    m_reset_obligation_queue = m_params.spacer_reset_pob_queue();
    m_push_pob = m_params.spacer_push_pob();
    m_push_pob_max_depth = m_params.spacer_push_pob_max_depth();
    m_use_lemma_as_pob = m_params.spacer_use_lemma_as_cti();
    m_elim_aux = m_params.spacer_elim_aux();
    m_reach_dnf = m_params.spacer_reach_dnf();
    m_use_derivations = m_params.spacer_use_derivations();
    m_validate_result = m_params.validate();
    m_use_eq_prop = m_params.spacer_eq_prop();
    m_ground_pob = m_params.spacer_ground_pobs();
    m_q3_qgen = m_params.spacer_q3_use_qgen();
    m_use_gpdr = m_params.spacer_gpdr();
    m_simplify_formulas_pre = m_params.spacer_simplify_lemmas_pre();
    m_simplify_formulas_post = m_params.spacer_simplify_lemmas_post();
    m_use_native_mbp = m_params.spacer_native_mbp ();
    m_instantiate = m_params.spacer_q3_instantiate ();
    m_use_qlemmas = m_params.spacer_q3();
    m_weak_abs = m_params.spacer_weak_abs();
    m_use_restarts = m_params.spacer_restarts();
    m_restart_initial_threshold = m_params.spacer_restart_initial_threshold();
    m_pdr_bfs = m_params.spacer_gpdr_bfs();
    m_use_bg_invs = m_params.spacer_use_bg_invs();

    if (m_use_gpdr) {
        // set options to be compatible with GPDR
        m_weak_abs = false;
        m_push_pob = false;
        m_use_qlemmas = false;
        m_ground_pob = true;
        m_reset_obligation_queue = false;
        m_use_derivations = false;
        m_use_lemma_as_pob = false;
    }
}

void context::reset()
{
    TRACE("spacer", tout << "\n";);
    m_pob_queue.reset();
    for (auto &entry: m_rels) {dealloc(entry.m_value);}
    m_rels.reset();
    m_query = nullptr;
    m_last_result = l_undef;
    m_inductive_lvl = 0;
}

struct func_decl_lt_proc : public std::binary_function<lemma*, lemma *, bool> {
    bool operator() (func_decl *a, func_decl *b) {
        return !a || !b || lt(a->get_name(), b->get_name());
    }
};

pred_transformer& context::get_pred_transformer(func_decl* p) const
{
    func_decl_multivector key;
    key.push_back({p, 1});
    return *m_rels.find(key);
}

pred_transformer& context::get_pred_transformer(ptr_vector<func_decl> & p)
{
    SASSERT(!p.empty());
    if (p.size() > 1) {
        std::sort(p.begin(), p.end(), func_decl_lt_proc());
    }
    func_decl_multivector mv;
    func_decl *prev = nullptr;
    unsigned counter = 0;
    for (func_decl * curr : p) {
        if (curr != prev) {
            if (prev) {mv.push_back({prev, counter});}
            counter = 1;
            prev = curr;
        } else {
            ++counter;
        }
    }
    SASSERT(prev && (counter > 0));
    mv.push_back({prev, counter});
    auto *e = m_rels.find_core(mv);
    return e ? *e->get_data().m_value : init_merged_pred_transformer(mv);
}

pt_collection context::subsumers(pred_transformer &pt)
{
    return m_pt_subsumptions.greater_elements(pt);
}

pt_collection context::subsumed(pred_transformer &pt)
{
    return m_pt_subsumptions.smaller_elements(pt);
}

void context::init_rules(const datalog::rule_set& rules, decls2rel& rels)
{
    scoped_watch _t_(m_init_rules_watch);
    m_context = &rules.get_context();

    // Allocate collection of predicate transformers
    for (auto dit = rules.begin_grouped_rules(),
             dend = rules.end_grouped_rules(); dit != dend; ++dit) {
        func_decl* pred = dit->m_key;
        TRACE("spacer", tout << mk_pp(pred, m) << "\n";);
        func_decl_multivector preds;
        preds.push_back({pred, 1});
        SASSERT(!rels.contains(preds));
        auto *e = rels.insert_if_not_there2(preds, alloc(pred_transformer, *this,
                                                        get_manager(), preds));
        datalog::rule_vector const& pred_rules = *dit->m_value;
        for (auto rule : pred_rules) {e->get_data().m_value->add_rule(rule);}
    }

    // Allocate predicate transformers for predicates that are used
    // but don't have rules
    for (auto *r : rules) {
        pred_transformer* pt;
        unsigned utz = r->get_uninterpreted_tail_size();
        for (unsigned i = 0; i < utz; ++i) {
            func_decl* pred = r->get_decl(i);
            func_decl_multivector preds;
            preds.push_back({pred, 1});
            if (!rels.find(preds, pt)) {
                pt = alloc(pred_transformer, *this, get_manager(), preds);
                rels.insert(preds, pt);
            }
        }
    }

    // Initialize use list dependencies
    for (auto &entry : rels) {
        m_pt_subsumptions.insert(*entry.m_value);
        func_decl_multivector& preds = entry.m_key;
        SASSERT(preds.size() == 1 && preds[0].count == 1);
        func_decl* pred = preds[0].func;
        pred_transformer* pt = entry.m_value, *pt_user = nullptr;
        for (auto dep : rules.get_dependencies().get_deps(pred)) {
            TRACE("spacer", tout << mk_pp(pred, m) << " " << mk_pp(dep, m) << "\n";);
            func_decl_multivector dep_key;
            dep_key.push_back({dep, 1});
            rels.find(dep_key, pt_user);
            pt_user->add_use(pt);
        }
    }

    // Initialize the predicate transformers.
    for (auto &entry : rels) {
        pred_transformer* rel = entry.m_value;
        rel->initialize(rels);
        TRACE("spacer", rel->display(tout); );
    }

    // initialize reach facts
    for (auto &entry : rels) {entry.m_value->init_rfs();}
}


pred_transformer &context::init_merged_pred_transformer(const func_decl_multivector &preds)
{
    pred_transformer *pt = alloc(pred_transformer, *this, get_manager(), preds);
    vector<std::pair<pred_transformer*, unsigned>> pts;
    for (auto &pair : preds) {
        pts.push_back({&get_pred_transformer(pair.func), pair.count});
    }
    m_pt_subsumptions.insert(*pt);
    pt->merge(pts);
    pt_collection subsumed_pts = m_pt_subsumptions.smaller_elements(*pt);
    pt->subsume_lemmas(subsumed_pts);
    m_rels.insert(preds, pt);
    pt->merge_child_lemmas(m_rels);
    return *pt;
}

void context::inherit_lemmas(const decls2rel &rels) {
    for (auto &entry : rels) {
        pred_transformer *pt = nullptr;
        if (m_rels.find(entry.m_key, pt)) {
            entry.m_value->inherit_lemmas(*pt);
        }
    }
}

void context::update_rules(datalog::rule_set& rules)
{
    decls2rel rels;
    // SMT params must be set before any expression is asserted to any
    // solver
    init_global_smt_params();
    // constructs new pred transformers and asserts trans and init
    init_rules(rules, rels);
    // inherits lemmas from m_rels into rels
    // dvvrd: TODO: lemmas would be lost! not all lemmas would be inherited!
    // dvvrd: m_rels are going to be resetted after this, but combined transformers are not yet discovered!
    inherit_lemmas(rels);
    // switch context to new rels
    init(rels);
    // re-initialize lemma generalizers
    init_lemma_generalizers();
}

void context::init(const decls2rel &rels) {
    // reset context. Current state is all stored in rels
    reset();
    // re-initialize context
    for (auto &entry : rels) {
        m_rels.insert(entry.m_key, entry.m_value);
    }
}

unsigned context::get_num_levels(func_decl* p)
{
    pred_transformer* pt = nullptr;
    func_decl_multivector key;
    key.push_back({p, 1});
    if (m_rels.find(key, pt)) {
        return pt->get_num_levels();
    } else {
        IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
        return 0;
    }
}

expr_ref context::get_cover_delta(int level, func_decl* p_orig, func_decl* p)
{
    pred_transformer* pt = nullptr;
    func_decl_multivector key;
    // dvvrd: TODO: extract information from all pts containing p!
    key.push_back({p, 1});
    if (m_rels.find(key, pt)) {
        return pt->get_cover_delta(p_orig, level);
    } else {
        IF_VERBOSE(10, verbose_stream() << "did not find predicate "
                   << p->get_name() << "\n";);
        return expr_ref(m.mk_true(), m);
    }
}

void context::add_cover(int level, func_decl* p, expr* property, bool bg)
{
    scoped_proof _pf_(m);

    pred_transformer* pt = nullptr;
    // dvvrd: TODO: add information for all pts containing p!
    func_decl_multivector key;
    key.push_back({p, 1});
    if (!m_rels.find(key, pt)) {
        pt = alloc(pred_transformer, *this, get_manager(), key);
        m_rels.insert(key, pt);
        IF_VERBOSE(10, verbose_stream() << "did not find predicate "
                   << p->get_name() << "\n";);
    }
    unsigned lvl = (level == -1)?infty_level():(static_cast<unsigned>(level));
    pt->add_cover(lvl, property, bg);
}

void context::add_invariant (func_decl *p, expr *property)
{add_cover (static_cast<int>(infty_level()), p, property, use_bg_invs());}

expr_ref context::get_reachable(func_decl *p)
{
    // dvvrd: TODO: extract information from all pts containing p!
    pred_transformer* pt = nullptr;
    func_decl_multivector key;
    key.push_back({p, 1});
    if (!m_rels.find(key, pt))
    { return expr_ref(m.mk_false(), m); }
    return pt->get_reachable();
}

// MAKES QUERY
// ONLY FOR VALIDATION
bool context::validate() {
    if (!m_validate_result) { return true; }

    std::stringstream msg;

    switch(m_last_result) {
    case l_true: {
#if 0
        expr_ref cex(m);
        cex = get_ground_sat_answer();
        if (!cex.get()) {
            IF_VERBOSE(0, verbose_stream() << "Cex validation failed\n";);
            throw default_exception("Cex validation failed\n");
            return false;
        }
#endif
        proof_ref cex(m);
        cex = get_ground_refutation();
        if (!cex.get()) {
            IF_VERBOSE(0, verbose_stream() << "Cex validation failed\n";);
            throw default_exception("Cex validation failed\n");
            return false;
        }
        break;
    }
    case l_false: {
        expr_ref_vector refs(m);
        expr_ref tmp(m);
        model_ref model;
        vector<relation_info> rs;
        model_converter_ref mc;
        get_level_property(m_inductive_lvl, refs, rs, use_bg_invs());
        inductive_property ex(m, mc, rs);
        ex.to_model(model);
        var_subst vs(m, false);
        for (auto& kv : m_rels) {
            ptr_vector<datalog::rule> const& rules = kv.m_value->rules();
            TRACE ("spacer", tout << "PT: " << kv.m_value->name().str()
                   << "\n";);
            for (auto* rp : rules) {
                datalog::rule& r = *rp;

                TRACE ("spacer",
                       get_datalog_context ().
                       get_rule_manager ().
                       display_smt2(r, tout) << "\n";);

                tmp = (*model)(r.get_head());
                expr_ref_vector fmls(m);
                fmls.push_back(m.mk_not(tmp));
                unsigned utsz = r.get_uninterpreted_tail_size();
                unsigned tsz  = r.get_tail_size();
                for (unsigned j = 0; j < utsz; ++j) {
                    tmp = (*model)(r.get_tail(j));
                    fmls.push_back(tmp);
                }
                for (unsigned j = utsz; j < tsz; ++j) {
                    fmls.push_back(r.get_tail(j));
                }
                tmp = m.mk_and(fmls.size(), fmls.c_ptr());
                svector<symbol> names;
                expr_free_vars fv;
                fv (tmp);
                fv.set_default_sort (m.mk_bool_sort ());

                for (unsigned i = 0; i < fv.size(); ++i) {
                    names.push_back(symbol(fv.size () - i - 1));
                }
                if (!fv.empty()) {
                    fv.reverse ();
                    tmp = m.mk_exists(fv.size(), fv.c_ptr(), names.c_ptr(), tmp);
                }
                ref<solver> sol =
                    mk_smt_solver(m, params_ref::get_empty(), symbol::null);
                sol->assert_expr(tmp);
                lbool res = sol->check_sat(0, nullptr);
                if (res != l_false) {
                    msg << "rule validation failed when checking: "
                        << mk_pp(tmp, m);
                    IF_VERBOSE(0, verbose_stream() << msg.str() << "\n";);
                    throw default_exception(msg.str());
                    return false;
                }
            }
        }
        TRACE ("spacer", tout << "Validation Succeeded\n";);
        break;
    }
    default:
        break;
    }
    return true;
}


void context::reset_lemma_generalizers()
{
    std::for_each(m_lemma_generalizers.begin(), m_lemma_generalizers.end(),
                  delete_proc<lemma_generalizer>());
    m_lemma_generalizers.reset();
}

// initialize global SMT parameters shared by all solvers
void context::init_global_smt_params() {
    m.toggle_proof_mode(PGM_ENABLED);
    params_ref p;
    if (!m_use_eq_prop) {
        p.set_uint("arith.propagation_mode", BP_NONE);
        p.set_bool("arith.auto_config_simplex", true);
        p.set_bool("arith.propagate_eqs", false);
        p.set_bool("arith.eager_eq_axioms", false);
    }
    p.set_uint("random_seed", m_params.spacer_random_seed());

    p.set_bool("dump_benchmarks", m_params.spacer_dump_benchmarks());
    p.set_double("dump_threshold", m_params.spacer_dump_threshold());

    // mbqi
    p.set_bool("mbqi", m_params.spacer_mbqi());

    if (!m_ground_pob) {
        p.set_uint("phase_selection", PS_CACHING_CONSERVATIVE2);
        p.set_uint("restart_strategy", RS_GEOMETRIC);
        p.set_double("restart_factor", 1.5);
        p.set_uint("qi.quick_checker", MC_UNSAT);
        p.set_double("qi.eager_threshold", 10.0);
        p.set_double("qi.lazy_threshold", 20.0);

        // options that we used to set, but are not user visible and
        // possibly not very useful
        // fparams.m_ng_lift_ite = LI_FULL;
        // fparams.m_eliminate_bounds = true;
        // fparams.m_pi_use_database = true;
    }

    m_pool0->updt_params(p);
    m_pool1->updt_params(p);
    m_pool2->updt_params(p);
}
void context::init_lemma_generalizers()
{
    reset_lemma_generalizers();
    LOG_STREAM << "m_q3_qgen: " << m_q3_qgen << ", m_use_euf_gen " << m_use_euf_gen
              << ", m_use_ind_gen " << m_use_ind_gen << ", m_use_array_eq_gen " << m_use_array_eq_gen
              << ", m_validate_lemmas " << m_validate_lemmas << "\n";

    if (m_q3_qgen) {
        m_lemma_generalizers.push_back(alloc(lemma_bool_inductive_generalizer,
                                             *this, 0, true));
        m_lemma_generalizers.push_back(alloc(lemma_quantifier_generalizer, *this,
                                             m_params.spacer_q3_qgen_normalize()));
    }

    if (m_use_euf_gen) {
        m_lemma_generalizers.push_back (alloc(lemma_eq_generalizer, *this));
    }

    // -- AG: commented out because it is causing performance issues at the moment
    //m_lemma_generalizers.push_back (alloc (unsat_core_generalizer, *this));

    if (m_use_ind_gen) {
        m_lemma_generalizers.push_back(alloc(lemma_bool_inductive_generalizer, *this, 0));
    }

    if (m_use_array_eq_gen) {
        m_lemma_generalizers.push_back(alloc(lemma_array_eq_generalizer, *this));
    }

    if (m_validate_lemmas) {
        m_lemma_generalizers.push_back(alloc(lemma_sanity_checker, *this));
    }

}

void context::get_level_property(unsigned lvl, expr_ref_vector& res,
                                 vector<relation_info>& rs, bool with_bg) const {
    for (auto const& kv : m_rels) {
        pred_transformer* r = kv.m_value;
        if (r->merged_head() == m_query_pred) {
            continue;
        }
        expr_ref conj = r->get_formulas(lvl, with_bg);
        m_pm.formula_n2o(0, false, conj);
        res.push_back(conj);
        ptr_vector<func_decl> sig(r->merged_head()->get_arity(), r->sig());
        rs.push_back(relation_info(m, r->merged_head(), sig, conj));
    }
}

void context::simplify_formulas() {
    for (auto& kv : m_rels) {
        kv.m_value->simplify_formulas();
    }
}

lbool context::solve(unsigned from_lvl)
{
    enable_trace("spacer");
    enable_trace("spacer_init_rule");
    enable_assertions(ENABLE_ASSERTS);
    m_last_result = l_undef;
    try {
        if (m_use_gpdr) {
            SASSERT(from_lvl == 0);
            m_last_result = gpdr_solve_core();
        }
        else {
            m_last_result = solve_core (from_lvl);
        }
        LOG_STREAM << "SOLVE CORE FINISHED!!!!\n";
        LOG_STREAM << m_last_result << "\n";
        LOG_STREAM.flush();LOG_STREAM.flush();LOG_STREAM.flush();

        if (m_last_result == l_false) {
            LOG_STREAM << "m_last_result == l_false\n";
            LOG_STREAM << mk_pp(mk_unsat_answer(), m);
            LOG_STREAM.flush();LOG_STREAM.flush();LOG_STREAM.flush();
            simplify_formulas();
            m_last_result = l_false;
            IF_VERBOSE(1, {
                    expr_ref_vector refs(m);
                    vector<relation_info> rs;
                    get_level_property(m_inductive_lvl, refs, rs, use_bg_invs());
                    model_converter_ref mc;
                    inductive_property ex(m, mc, rs);
                    verbose_stream() << ex.to_string();
                });
            // upgrade invariants that are known to be inductive.
            // decl2rel::iterator it = m_rels.begin (), end = m_rels.end ();
            // for (; m_inductive_lvl > 0 && it != end; ++it) {
            //   if (it->m_value->head() != m_query_pred) {
            //     it->m_value->propagate_to_infinity (m_inductive_lvl);
            //   }
            // }
        }
        VERIFY (validate ());
    } catch (const unknown_exception &)
    {}

    if (m_last_result == l_true) {
        m_stats.m_cex_depth = get_cex_depth ();
    }

    if (m_params.print_statistics ()) {
        statistics st;
        collect_statistics (st);
        st.display_smt2 (verbose_stream ());
    }

    return m_last_result;
}


void context::checkpoint()
{
    if (m.canceled ()) {
        throw default_exception("spacer canceled");
    }
}

unsigned context::get_cex_depth()
{
    if (m_last_result != l_true) {
        IF_VERBOSE(1,
                   verbose_stream ()
                   << "Trace unavailable when result is false\n";);
        return 0;
    }

    // treat the following as queues: read from left to right and insert at right
    ptr_vector<func_decl> preds;
    ptr_vector<pred_transformer> pts;
    reach_fact_ref_vector facts;

    // temporary
    reach_fact* fact;
    datalog::rule const* r;
    pred_transformer* pt;

    // get and discard query rule
    fact = m_query->get_last_rf ();
    r = &fact->get_rule ();

    unsigned cex_depth = 0;

    // initialize queues
    // assume that the query is only on a single predicate
    // (i.e. disallow fancy queries for now)
    facts.append (fact->get_justifications ());
    if (facts.size() != 1) {
        // XXX AG: Escape if an assertion is about to fail
        IF_VERBOSE(1,
                   verbose_stream () <<
                   "Warning: counterexample is trivial or non-existent\n";);
        return cex_depth;
    }
    SASSERT (facts.size () == 1);
    m_query->find_predecessors (*r, preds);
    SASSERT (preds.size () == 1);
    pts.push_back (&(get_pred_transformer (preds)));

    pts.push_back (NULL); // cex depth marker

    // bfs traversal of the query derivation tree
    for (unsigned curr = 0; curr < pts.size (); curr++) {
        // get current pt and fact
        pt = pts.get (curr);
        // check for depth marker
        if (pt == nullptr) {
            ++cex_depth;
            // insert new marker if there are pts at higher depth
            if (curr + 1 < pts.size()) { pts.push_back(NULL); }
            continue;
        }
        fact = facts.get (curr - cex_depth); // discount the number of markers
        // get rule justifying the derivation of fact at pt
        r = &fact->get_rule ();
        TRACE ("spacer",
               tout << "next rule: " << r->name ().str () << "\n";
            );
        // add child facts and pts
        facts.append (fact->get_justifications ());
        pt->find_predecessors (*r, preds);
        for (unsigned j = 0; j < preds.size (); j++) {
            pts.push_back (&(get_pred_transformer (preds.get(j))));
        }
    }

    return cex_depth;
}

/**
   \brief retrieve answer.
*/

void context::get_rules_along_trace(datalog::rule_ref_vector& rules)
{
    if (m_last_result != l_true) {
        IF_VERBOSE(1,
                   verbose_stream ()
                   << "Trace unavailable when result is false\n";);
        return;
    }

    // treat the following as queues: read from left to right and insert at right
    ptr_vector<func_decl> preds;
    ptr_vector<pred_transformer> pts;
    reach_fact_ref_vector facts;

    // temporary
    reach_fact* fact;
    datalog::rule const* r;
    pred_transformer* pt;

    // get query rule
    fact = m_query->get_last_rf ();
    r = &fact->get_rule ();
    rules.push_back (const_cast<datalog::rule *> (r));
    TRACE ("spacer",
           tout << "Initial rule: " << r->name().str() << "\n";
        );

    // initialize queues
    // assume that the query is only on a single predicate
    // (i.e. disallow fancy queries for now)
    facts.append (fact->get_justifications ());
    if (facts.size() != 1) {
        // XXX AG: Escape if an assertion is about to fail
        IF_VERBOSE(1,
                   verbose_stream () <<
                   "Warning: counterexample is trivial or non-existent\n";);
        return;
    }
    SASSERT (facts.size () == 1);
    m_query->find_predecessors (*r, preds);
    SASSERT (preds.size () == 1);
    pts.push_back (&(get_pred_transformer (preds)));

    // populate rules according to a preorder traversal of the query derivation tree
    for (unsigned curr = 0; curr < pts.size (); curr++) {
        // get current pt and fact
        pt = pts.get (curr);
        fact = facts.get (curr);
        // get rule justifying the derivation of fact at pt
        r = &fact->get_rule ();
        rules.push_back (const_cast<datalog::rule *> (r));
        TRACE ("spacer",
               tout << "next rule: " << r->name ().str () << "\n";
            );
        // add child facts and pts
        facts.append (fact->get_justifications ());
        pt->find_predecessors (*r, preds);
        for (unsigned j = 0; j < preds.size (); j++) {
            pts.push_back (&(get_pred_transformer (preds.get(j))));
        }
    }
}

model_ref context::get_model()
{
    model_ref model;
    expr_ref_vector refs(m);
    vector<relation_info> rs;
    get_level_property(m_inductive_lvl, refs, rs, use_bg_invs());
    inductive_property ex(m, const_cast<model_converter_ref&>(m_mc), rs);
    ex.to_model (model);
    return model;
}

proof_ref context::get_proof() const
{
    return proof_ref (m);
}

expr_ref context::get_answer()
{
    switch(m_last_result) {
    case l_true:
        return mk_sat_answer();
    case l_false:
        return mk_unsat_answer();
    default:
        return expr_ref(m.mk_true(), m);
    }
}



expr_ref context::mk_unsat_answer() const
{
    expr_ref_vector refs(m);
    vector<relation_info> rs;
    get_level_property(m_inductive_lvl, refs, rs, use_bg_invs());
    inductive_property ex(m, const_cast<model_converter_ref&>(m_mc), rs);
    return ex.to_expr();
}


proof_ref context::get_ground_refutation() {
    if (m_last_result != l_true) {
        IF_VERBOSE(0, verbose_stream()
                   << "Sat answer unavailable when result is false\n";);
        return proof_ref(m);
    }

    ground_sat_answer_op op(*this);
    return op(*m_query);
}
// MAKES QUERY
expr_ref context::get_ground_sat_answer() const {
    if (m_last_result != l_true) {
        IF_VERBOSE(0, verbose_stream()
                   << "Sat answer unavailable when result is false\n";);
        return expr_ref(m);
    }

    // treat the following as queues: read from left to right and insert at the right
    reach_fact_ref_vector reach_facts;
    ptr_vector<func_decl> preds;
    ptr_vector<pred_transformer> pts;
    expr_ref_vector cex (m); // pre-order list of ground instances of predicates
    expr_ref_vector cex_facts (m); // equalities for the ground cex using signature constants

    // temporary
    reach_fact *reach_fact;
    pred_transformer* pt;
    expr_ref cex_fact (m);
    datalog::rule const* r;

    // get and discard query rule
    reach_fact = m_query->get_last_rf ();
    r = &reach_fact->get_rule ();

    // initialize queues
    reach_facts.append (reach_fact->get_justifications ());
    if (reach_facts.size() != 1) {
        // XXX Escape if an assertion is about to fail
        IF_VERBOSE(1,
                   verbose_stream () <<
                   "Warning: counterexample is trivial or non-existent\n";);
        return expr_ref(m.mk_true(), m);
    }
    m_query->find_predecessors (*r, preds);
    SASSERT (preds.size () == 1);
    pts.push_back (&(get_pred_transformer (preds.get(0))));
    cex_facts.push_back (m.mk_true ());

    // XXX a hack to avoid assertion when query predicate is not nullary
    if (preds[0]->get_arity () == 0)
    { cex.push_back(m.mk_const(preds[0])); }

    // smt context to obtain local cexes
    ref<solver> cex_ctx =
        mk_smt_solver(m, params_ref::get_empty(), symbol::null);

    // preorder traversal of the query derivation tree
    for (unsigned curr = 0; curr < pts.size (); curr++) {
        // pick next pt, fact, and cex_fact
        pt = pts.get (curr);
        reach_fact = reach_facts[curr];

        cex_fact = cex_facts.get (curr);

        ptr_vector<pred_transformer> child_pts;

        // get justifying rule and child facts for the derivation of reach_fact at pt
        r = &reach_fact->get_rule ();
        const reach_fact_ref_vector &child_reach_facts =
            reach_fact->get_justifications ();
        // get child pts
        preds.reset();
        pt->find_predecessors(*r, preds);

        for (unsigned j = 0; j < preds.size (); j++) {
            child_pts.push_back (&get_pred_transformer (preds.get(j)));
        }
        // update the queues
        reach_facts.append (child_reach_facts);
        pts.append (child_pts);

        // update cex and cex_facts by making a local sat check:
        // check consistency of reach facts of children, rule body, and cex_fact
        cex_ctx->push ();
        cex_ctx->assert_expr (cex_fact);
        unsigned u_tail_sz = r->get_uninterpreted_tail_size ();
        SASSERT (child_reach_facts.size () == u_tail_sz);
        for (unsigned i = 0; i < u_tail_sz; i++) {
            expr_ref ofml (m);
            m_pm.formula_n2o(child_reach_facts[i]->get(), ofml, i);
            cex_ctx->assert_expr (ofml);
        }
        cex_ctx->assert_expr(pt->transition());
        cex_ctx->assert_expr(pt->rule2tag(r));
        lbool res = cex_ctx->check_sat(0, nullptr);
        CTRACE("cex", res == l_false,
               tout << "Cex fact: " << mk_pp(cex_fact, m) << "\n";
               for (unsigned i = 0; i < u_tail_sz; i++)
                   tout << "Pre" << i << " "
                        << mk_pp(child_reach_facts[i]->get(), m) << "\n";
               tout << "Rule: ";
               get_datalog_context().get_rule_manager().display_smt2(*r, tout) << "\n";
            );
        VERIFY (res == l_true);
        model_ref local_mdl;
        cex_ctx->get_model (local_mdl);
        cex_ctx->pop (1);
        local_mdl->set_model_completion(true);
        for (unsigned i = 0; i < child_pts.size(); i++) {
            pred_transformer& ch_pt = *(child_pts.get(i));
            unsigned sig_size = ch_pt.sig_size();
            expr_ref_vector ground_fact_conjs(m);
            expr_ref_vector ground_arg_vals(m);
            for (unsigned j = 0; j < sig_size; j++) {
                expr_ref sig_arg(m), sig_val(m);
                sig_arg = m.mk_const (m_pm.o2o(ch_pt.sig(j), 0, i));
                sig_val = (*local_mdl)(sig_arg);
                ground_fact_conjs.push_back(m.mk_eq(sig_arg, sig_val));
                ground_arg_vals.push_back(sig_val);
            }
            if (!ground_fact_conjs.empty()) {
                expr_ref ground_fact(m);
                ground_fact = mk_and(ground_fact_conjs);
                m_pm.formula_o2n(ground_fact, ground_fact, i);
                cex_facts.push_back (ground_fact);
            } else {
                cex_facts.push_back (m.mk_true ());
            }
            cex.push_back(m.mk_app(ch_pt.merged_head(),
                                   sig_size, ground_arg_vals.c_ptr()));
        }
    }

    TRACE ("spacer", tout << "ground cex\n" << cex << "\n";);

    return expr_ref(m.mk_and(cex.size(), cex.c_ptr()), m);
}

void context::display_certificate(std::ostream &out) const {
    switch(m_last_result) {
    case l_false:
        out << mk_pp(mk_unsat_answer(), m);
        break;
    case l_true:
        out << mk_pp(mk_sat_answer(), m);
        break;
    case l_undef:
        out << "unknown";
        break;
    }
}

///this is where everything starts
lbool context::solve_core (unsigned from_lvl)
{
    scoped_watch _w_(m_solve_watch);
    //if there is no query predicate, abort
    func_decl_multivector query_key;
    query_key.push_back({m_query_pred, 1});
    if (!m_rels.find(query_key, m_query)) { return l_false; }

    unsigned lvl = from_lvl;

    pob *root = m_query->mk_pob(nullptr,from_lvl,0,m.mk_true());
    m_pob_queue.set_root (*root);

    unsigned max_level = m_max_level;

    for (unsigned i = from_lvl; i < max_level; ++i) {
        LOG_STREAM << "\n\n\nEntering level " << i << std::endl;
        checkpoint();
        m_expanded_lvl = infty_level ();
        m_stats.m_max_query_lvl = lvl;

        if (check_reachability()) { return l_true; }

        if (lvl > 0 && m_use_propagate)
            if (propagate(m_expanded_lvl, lvl, UINT_MAX)) { dump_json(); return l_false; }

        dump_json();

        if (is_inductive()){
            return l_false;
        }

        for (unsigned i = 0; i < m_callbacks.size(); i++){
            if (m_callbacks[i]->unfold())
                m_callbacks[i]->unfold_eh();
        }

        m_pob_queue.inc_level ();
        lvl = m_pob_queue.max_level ();
        m_stats.m_max_depth = std::max(m_stats.m_max_depth, lvl);
        IF_VERBOSE(1,verbose_stream() << "Entering level "<< lvl << "\n";);

        STRACE("spacer_progress", tout << "\n* LEVEL " << lvl << "\n";);
        IF_VERBOSE(1,
                   if (m_params.print_statistics ()) {
                       statistics st;
                       collect_statistics (st);
                   };
            );

    }
    // communicate failure to datalog::context
    if (m_context) { m_context->set_status(datalog::BOUNDED); }
    return l_undef;
}


// dvvrd: some sort of entry point for each level
bool context::check_reachability ()
{
    scoped_watch _w_(m_reach_watch);

    timeit _timer (get_verbosity_level () >= 1,
                   "spacer::context::check_reachability",
                   verbose_stream ());

    pob_ref last_reachable;

    pob_ref_buffer new_pobs;

    if (m_reset_obligation_queue) { m_pob_queue.reset(); }

    unsigned initial_size = m_stats.m_num_lemmas;
    unsigned threshold = m_restart_initial_threshold;
    unsigned luby_idx = 1;

    while (m_pob_queue.top()) {
        pob_ref node;
        checkpoint ();

        while (last_reachable) {
            checkpoint ();
            node = last_reachable;
            last_reachable = nullptr;
            if (m_pob_queue.is_root(*node)) { return true; }
            if (is_reachable (*node->parent())) {
                last_reachable = node->parent ();
                SASSERT(last_reachable->is_closed());
                last_reachable->close ();
            } else if (!node->parent()->is_closed()) {
                /* bump node->parent */
                node->parent ()->bump_weakness();
            }
        }

        SASSERT (m_pob_queue.top ());
        // -- remove all closed nodes
        // -- this is necessary because there is no easy way to
        // -- remove nodes from the priority queue.
        while (m_pob_queue.top ()->is_closed ()) {
            pob_ref n = m_pob_queue.top();
            m_pob_queue.pop();
            IF_VERBOSE (1,
                        verbose_stream () << "Deleting closed node: "
                        << n->pt ().name ()
                        << "(" << n->level () << ", " << n->depth () << ")"
                        << " " << n->post ()->get_id () << "\n";);
            if (m_pob_queue.is_root(*n)) {return true;}
            SASSERT (m_pob_queue.top ());
        }

        SASSERT (m_pob_queue.top ());

        if (m_use_restarts && m_stats.m_num_lemmas - initial_size > threshold) {
            luby_idx++;
            m_stats.m_num_restarts++;
            threshold =
                static_cast<unsigned>(get_luby(luby_idx)) * m_restart_initial_threshold;
            IF_VERBOSE (1, verbose_stream ()
                        << "(restarting :lemmas " << m_stats.m_num_lemmas
                        << " :restart_threshold " << threshold
                        << ")\n";);
            // -- clear obligation queue up to the root
            while (!m_pob_queue.is_root(*m_pob_queue.top())) { m_pob_queue.pop(); }
            initial_size = m_stats.m_num_lemmas;
        }

        node = m_pob_queue.top ();
        m_pob_queue.pop();
        size_t old_sz = m_pob_queue.size();
        (void)old_sz;
        SASSERT (node->level () <= m_pob_queue.max_level ());
        switch (expand_pob(*node, new_pobs)) {
        case l_true:
            SASSERT(m_pob_queue.size() == old_sz);
            SASSERT(new_pobs.empty());
            last_reachable = node;
            last_reachable->close ();
            if (m_pob_queue.is_root(*node)) {return true;}
            break;
        case l_false:
            SASSERT(m_pob_queue.size() == old_sz);
            for (auto pob : new_pobs) {
                if (is_requeue(*pob)) {m_pob_queue.push(*pob);}
            }

            if (m_pob_queue.is_root(*node)) {return false;}
            break;
        case l_undef:
            SASSERT(m_pob_queue.size() == old_sz);
            for (auto pob : new_pobs) {m_pob_queue.push(*pob);}
            break;
        }
        new_pobs.reset();
    }

    UNREACHABLE();
    return false;
}

/// returns true if the given pob can be re-scheduled
bool context::is_requeue(pob &n) {
    if (!m_push_pob) {return false;}
    unsigned max_depth = m_push_pob_max_depth;
    return (n.level() >= m_pob_queue.max_level() ||
            m_pob_queue.max_level() - n.level() <= max_depth);
}

/// check whether node n is concretely reachable
// dvvrd: used only in check_reachability. happens before expand_pob
bool context::is_reachable(pob &n)
{
    scoped_watch _w_(m_is_reach_watch);
    // XXX hold a reference for n during this call.
    // XXX Should convert is_reachable() to accept pob_ref as argument
    pob_ref nref(&n);

    TRACE ("spacer",
           tout << "is-reachable: " << n.pt().name()
           << " level: " << n.level()
           << " depth: " << (n.depth () - m_pob_queue.min_depth ()) << "\n"
           << mk_pp(n.post(), m) << "\n";);
    LOG_STREAM << "small-is-reachable: " << n.pt().name()
           << " level: " << n.level()
           << " depth: " << (n.depth () - m_pob_queue.min_depth ()) << "\n"
           << mk_pp(n.post(), m) << "\n";

    stopwatch watch;
    IF_VERBOSE (1, verbose_stream () << "is-reachable: " << n.pt ().name ()
                << " (" << n.level () << ", "
                << (n.depth () - m_pob_queue.min_depth ()) << ") "
                << (n.use_farkas_generalizer () ? "FAR " : "SUB ")
                << n.post ()->get_id ();
                verbose_stream().flush ();
                watch.start (););

    // used in case n is unreachable
    unsigned uses_level = infty_level ();
    model_ref mdl;

    // used in case n is reachable
    vector<bool> is_concrete;
    versioned_rule_vector rules;
    // denotes which predecessor's (along r) reach facts are used
    vector<bool> reach_pred_used;
    unsigned num_reuse_reach = 0;

    unsigned saved = n.level ();
    // TBD: don't expose private field
    n.m_level = infty_level ();
    lbool res = n.pt().is_reachable(n, nullptr, &mdl,
                                    uses_level, is_concrete, rules,
                                    reach_pred_used, num_reuse_reach);
    n.m_level = saved;

//    bool is_concretely_reachable = true;
//    for (unsigned i = 0; i < rules.size(); ++i) {
//        bool concr = is_concrete[i];
//        is_concretely_reachable &= concr;
//        const datalog::rule *r = rules[i].first;
//        if (concr && r && r->get_uninterpreted_tail_size () > 0) {
//            // -- update must summary
//            pred_transformer &rf_pt = get_pred_transformer(r->get_decl());
//            reach_fact_ref rf = rf_pt.mk_rf (n, *mdl, *r, rules[i].second);
//            rf_pt.add_rf (rf.get ());
//        }
//    }

    bool is_concretely_reachable = true;
    for (unsigned i = 0; i < rules.size(); ++i) {
        is_concretely_reachable &= is_concrete[i];
    }
    if (is_concretely_reachable) {
        for (unsigned i = 0; i < rules.size(); ++i) {
            const datalog::rule *r = rules[i].first;
            if (is_concrete[i] && r && r->get_uninterpreted_tail_size () > 0) {
                // -- update must summary
                pred_transformer &rf_pt = get_pred_transformer(r->get_decl());
                reach_fact_ref rf = rf_pt.mk_rf (n, *mdl, *r, rules[i].second);
                rf_pt.add_rf (rf.get ());
            }
        }
    }


    if (res != l_true || !is_concretely_reachable) {
        IF_VERBOSE(1, verbose_stream () << " F "
                   << std::fixed << std::setprecision(2)
                   << watch.get_seconds () << "\n";);
        return false;
    }
    SASSERT(res == l_true);
    SASSERT(is_concretely_reachable);

    // if n has a derivation, create a new child and report l_undef
    // otherwise if n has no derivation or no new children, report l_true
    pob *next = nullptr;
    scoped_ptr<derivation> deriv;
    if (n.has_derivation()) {deriv = n.detach_derivation();}

    // -- close n, it is reachable
    // -- don't worry about removing n from the obligation queue
    n.close ();

    if (deriv) {
        STRACE("spacer",
               tout << "[dvvrd] before create_next_child in is_reachable\n";);
        next = deriv->create_next_child ();
        if (next) {
            SASSERT(!next->is_closed());
            // move derivation over to the next obligation
            next->set_derivation(deriv.detach());

            // remove the current node from the queue if it is at the top
            if (m_pob_queue.top() == &n) { m_pob_queue.pop(); }

            m_pob_queue.push(*next);
        }
    }

    // either deriv was a nullptr or it was moved into next
    SASSERT(!next || !deriv);


    IF_VERBOSE(1, verbose_stream () << (next ? " X " : " T ")
               << std::fixed << std::setprecision(2)
               << watch.get_seconds () << "\n";);

    // recurse on the new proof obligation
    return next ? is_reachable(*next) : true;
}

void context::dump_json()
{
    if (m_params.spacer_print_json().size()) {
        std::ofstream of;
        of.open(m_params.spacer_print_json().bare_str());
        m_json_marshaller.marshal(of);
        of.close();
    }
}

void context::predecessor_eh()
{
    for (unsigned i = 0; i < m_callbacks.size(); i++) {
        if (m_callbacks[i]->predecessor())
            m_callbacks[i]->predecessor_eh();
    }
}

/// Checks whether the given pob is reachable
/// returns l_true if reachable, l_false if unreachable
/// returns l_undef if reachability cannot be decided
/// out contains new pobs to add to the queue in case the result is l_undef
lbool context::expand_pob(pob& n, pob_ref_buffer &out)
{
    SASSERT(out.empty());
    pob::on_expand_event _evt(n);
    TRACE ("spacer",
           tout << "expand-pob: " << n.pt().name()
           << " level: " << n.level()
           << " depth: " << (n.depth () - m_pob_queue.min_depth ())
           << " fvsz: " << n.get_free_vars_size() << "\n"
           << mk_pp(n.post(), m) << "\n";);

    STRACE ("spacer_progress",
            tout << "** expand-pob: " << n.pt().name()
            << " level: " << n.level()
            << " depth: " << (n.depth () - m_pob_queue.min_depth ()) << "\n"
            << mk_epp(n.post(), m) << "\n\n";);

    TRACE ("core_array_eq",
           tout << "expand-pob: " << n.pt().name()
           << " level: " << n.level()
           << " depth: " << (n.depth () - m_pob_queue.min_depth ()) << "\n"
           << mk_pp(n.post(), m) << "\n";);

    stopwatch watch;
    IF_VERBOSE (1, verbose_stream () << "expand: " << n.pt ().name ()
                << " (" << n.level () << ", "
                << (n.depth () - m_pob_queue.min_depth ()) << ") "
                << (n.use_farkas_generalizer () ? "FAR " : "SUB ")
                << " w(" << n.weakness() << ") "
                << n.post ()->get_id ();
                verbose_stream().flush ();
                watch.start (););

    // used in case n is unreachable
    unsigned uses_level = infty_level ();
    expr_ref_vector cube(m);
    model_ref model;

    // used in case n is reachable
    vector<bool> is_concrete;
    versioned_rule_vector rules;
    // denotes which predecessor's (along r) reach facts are used
    vector<bool> reach_pred_used;
    unsigned num_reuse_reach = 0;


    if (m_push_pob && n.pt().is_blocked(n, uses_level)) {
        // if (!m_pob_queue.is_root (n)) n.close ();
        IF_VERBOSE (1, verbose_stream () << " K "
                    << std::fixed << std::setprecision(2)
                    << watch.get_seconds () << "\n";);
        n.inc_level();
        LOG_STREAM << "IS BLOCKED SUKA\n";
        out.push_back(&n);
        return l_false;
    }

    if (/* XXX noop */ n.pt().is_qblocked(n)) {
        STRACE("spacer_progress",
               tout << "This pob can be blocked by instantiation\n";);
    }

    predecessor_eh();

    lbool res = n.pt ().is_reachable (n, &cube, &model, uses_level, is_concrete, rules,
                                      reach_pred_used, num_reuse_reach);
    if (model) model->set_model_completion(false);
    checkpoint ();
    IF_VERBOSE (1, verbose_stream () << "." << std::flush;);
    switch (res) {
        //reachable but don't know if this is purely using UA
    case l_true: {
        // update stats
        m_stats.m_num_reuse_reach += num_reuse_reach;

        bool all_rules_covered = rules.size() == n.pt().heads().size();
        bool is_concretely_reachable = true;
//        for (unsigned i = 0; i < rules.size(); ++i) {
//            const datalog::rule *r = rules[i].first;
//            is_concretely_reachable &= is_concrete[i];
//            if (is_concrete[i] && r && r->get_uninterpreted_tail_size() > 0) {
//                // -- update must summary
//                pred_transformer &rf_pt = get_pred_transformer(r->get_decl());
//                reach_fact_ref rf = rf_pt.mk_rf (n, *model, *r, rules[i].second);
//                checkpoint ();
//                rf_pt.add_rf (rf.get ());
//                checkpoint ();
//            }
//        }
        for (unsigned i = 0; i < rules.size(); ++i) {
            is_concretely_reachable &= is_concrete[i];
        }

        if (is_concretely_reachable) {
            for (unsigned i = 0; i < rules.size(); ++i) {
                const datalog::rule *r = rules[i].first;
                if (r && r->get_uninterpreted_tail_size() > 0) {
                    // -- update must summary
                    pred_transformer &rf_pt = get_pred_transformer(r->get_decl());
                    reach_fact_ref rf = rf_pt.mk_rf (n, *model, *r, rules[i].second);
                    checkpoint ();
                    rf_pt.add_rf (rf.get ());
                    checkpoint ();
                }
            }
        }

        // must-reachable
        if (is_concretely_reachable && all_rules_covered) {
            LOG_STREAM << "is_concretely_reachable && all_rules_covered\n";
//            LOG_STREAM << "concrete model:\n";
//            model_smt2_pp(LOG_STREAM, m, *model, 0);
//            LOG_STREAM << "\n";
            // if n has a derivation, create a new child and report l_undef
            // otherwise if n has no derivation or no new children, report l_true
            pob *next = nullptr;
            scoped_ptr<derivation> deriv;
            if (n.has_derivation()) {deriv = n.detach_derivation();}

            // -- close n, it is reachable
            // -- don't worry about removing n from the obligation queue
            n.close ();

            if (deriv) {
                next = deriv->create_next_child ();
                checkpoint ();
                if (next) {
                    // move derivation over to the next obligation
                    next->set_derivation (deriv.detach());

                    // this is the new node to add
                    STRACE("spacer",
                            tout << "[dvvrd] PUSHING NEXT POB: [" << (long)next << "] [parent: "
                                      << (long)(next->parent()) <<  "] (" << next->pt().name() << ") "
                                      << mk_pp(next->post(), m) << "\n";);
                    LOG_STREAM << "[dvvrd] PUSHING NEXT POB: [" << (long)next << "] [parent: "
                              << (long)(next->parent()) <<  "] (" << next->pt().name() << ", lvl " << next->level() << ") "
                              << mk_pp(next->post(), m) << "\n";
                    out.push_back (next);
                }
            }


            IF_VERBOSE(1, verbose_stream () << (next ? " X " : " T ")
                       << std::fixed << std::setprecision(2)
                       << watch.get_seconds () << "\n";);
            if (next) {
                LOG_STREAM << "next is " << next->pt().name() << " " << mk_pp(next->post(), m) << "\n";
            }
            LOG_STREAM << "expand-pob: " << (next ? l_undef : l_true) << "\n";
            return next ? l_undef : l_true;
        }

        if (!is_concretely_reachable) {
            // create a child of n
            STRACE("spacer",
                    tout << "[dvvrd] RE-PUSHING POB: [" << (long)(&n) << "] [parent: " << (long)(n.parent())
                         <<  "] (" << n.pt().name() << ") "
                         << mk_pp(n.post(), m) << "\n";);
            LOG_STREAM << "[dvvrd] RE-PUSHING POB: [" << (long)(&n) << "] [parent: " << (long)(n.parent())
                      <<  "] (" << n.pt().name() << ", lvl " << n.level() << ") "
                         << mk_pp(n.post(), m) << "\n";
            out.push_back(&n);
//        if (!is_concretely_reachable) {
            VERIFY(create_children (n, rules, *model, reach_pred_used, out));
            IF_VERBOSE(1, verbose_stream () << " U "
                       << std::fixed << std::setprecision(2)
                       << watch.get_seconds () << "\n";);
        }
        return l_undef;

    }
    case l_false:
        // n is unreachable, create new summary facts
    {
        timeit _timer (is_trace_enabled("spacer_timeit"),
                       "spacer::expand_pob::false",
                       verbose_stream ());

        // -- only update expanded level when new lemmas are generated at it.
        if (n.level() < m_expanded_lvl) { m_expanded_lvl = n.level(); }

        TRACE("spacer", tout << "cube:\n";
              for (unsigned j = 0; j < cube.size(); ++j)
                  tout << mk_pp(cube[j].get(), m) << "\n";);


        pob_ref nref(&n);
        // -- create lemma from a pob and last unsat core
        lemma_ref lemma = alloc(class lemma, pob_ref(&n), cube, uses_level);
        LOG_STREAM << n.pt().name() << ": lemma before generalization: " << cube << "\n";

        // -- run all lemma generalizers
        for (unsigned i = 0;
             // -- only generalize if lemma was constructed using farkas
             n.use_farkas_generalizer () && !lemma->is_false() &&
                 i < m_lemma_generalizers.size(); ++i) {
            checkpoint ();
            (*m_lemma_generalizers[i])(lemma);
        }
        DEBUG_CODE(
            lemma_sanity_checker sanity_checker(*this);
            sanity_checker(lemma);
            );


        LOG_STREAM << "invariant state: "
              << (is_infty_level(lemma->level())?"(inductive)":"")
              <<  mk_pp(lemma->get_expr(), m) << "\n";
        LOG_STREAM << "lemma cube: " << lemma->get_cube() << "\n";

        TRACE("spacer", tout << "invariant state: "
              << (is_infty_level(lemma->level())?"(inductive)":"")
              <<  mk_pp(lemma->get_expr(), m) << "\n";);

        bool v = n.pt().add_lemma (lemma.get());
        if (v) { m_stats.m_num_lemmas++; }

        // Optionally update the node to be the negation of the lemma
        if (v && m_use_lemma_as_pob) {
            expr_ref c(m);
            c = mk_and(lemma->get_cube());
            // check that the post condition is different
            if (c  != n.post()) {
                pob *f = n.pt().find_pob(n.parent(), c);
                // skip if a similar pob is already in the queue
                if (f != &n && (!f || !f->is_in_queue())) {
                    f = n.pt().mk_pob(n.parent(), n.level(),
                                      n.depth(), c, n.get_binding());
                    SASSERT(!f->is_in_queue());
                    f->inc_level();
                    //f->set_farkas_generalizer(false);
                    LOG_STREAM << "[dvvrd] PUSHING POB IN STRANGE CASE: [" << (long)f << "] [parent: "
                              << (long)(f->parent()) <<  "] (" << f->pt().name() << ", lvl " << f->level() << ") "
                              << mk_pp(f->post(), m) << "\n";
                    out.push_back(f);
                }
            }
        }

        // schedule the node to be placed back in the queue
        n.inc_level();
        LOG_STREAM << "[dvvrd] PUSHING POB AFTER GENERALIZATION: [" << (long)(&n) << "] [parent: " << (long)(n.parent())
                  <<  "] (" << n.pt().name() << ", lvl " << n.level() << ") "
                     << mk_pp(n.post(), m) << "\n";
        out.push_back(&n);

        CASSERT("spacer", n.level() == 0 || check_invariant(n.level()-1));


        IF_VERBOSE(1, verbose_stream () << " F "
                   << std::fixed << std::setprecision(2)
                   << watch.get_seconds () << "\n";);

        return l_false;
    }
    case l_undef:
        // something went wrong
        if (n.weakness() < 10 /* MAX_WEAKENSS */) {
            bool has_new_child = false;
            SASSERT(m_weak_abs);
            m_stats.m_expand_pob_undef++;
            bool has_uninterpreted_atoms = false;
            for (auto &r : rules) {
                if (r.first->get_uninterpreted_tail_size() > 0) {
                    has_uninterpreted_atoms = true;
                    break;
                }
            }
            if (has_uninterpreted_atoms) {
                // do not trust reach_pred_used
                for (unsigned i = 0, sz = reach_pred_used.size(); i < sz; ++i)
                { reach_pred_used[i] = false; }
                has_new_child = create_children(n, rules, *model, reach_pred_used, out);
            }
            IF_VERBOSE(1, verbose_stream() << " UNDEF "
                       << std::fixed << std::setprecision(2)
                       << watch.get_seconds () << "\n";);
            if (has_new_child) {
                // ensure that n is placed back in the queue
                out.push_back(&n);
                return l_undef;
            }

            // -- failed to create a child, bump weakness and repeat
            // -- the recursion is bounded by the levels of weakness supported
            SASSERT(out.empty());
            n.bump_weakness();
            return expand_pob(n, out);
        }
        TRACE("spacer", tout << "unknown state: " << mk_and(cube) << "\n";);
        throw unknown_exception();
    }
    UNREACHABLE();
    throw unknown_exception();
}

//
// check if predicate transformer has a satisfiable predecessor state.
// returns either a satisfiable predecessor state or
// return a property that blocks state and is implied by the
// predicate transformer (or some unfolding of it).
//

bool context::propagate(unsigned min_prop_lvl,
                        unsigned max_prop_lvl, unsigned full_prop_lvl)
{
    LOG_STREAM << "propagate " << min_prop_lvl << " " << max_prop_lvl << " " << full_prop_lvl << "\n";
    scoped_watch _w_(m_propagate_watch);

    if (min_prop_lvl == infty_level()) { return false; }

    timeit _timer (get_verbosity_level() >= 1,
                   "spacer::context::propagate",
                   verbose_stream ());

    if (full_prop_lvl < max_prop_lvl) { full_prop_lvl = max_prop_lvl; }

    if (m_simplify_formulas_pre) {
        simplify_formulas();
    }
    STRACE ("spacer_progress", tout << "Propagating\n";);

    IF_VERBOSE (1, verbose_stream () << "Propagating: " << std::flush;);

    for (unsigned lvl = min_prop_lvl; lvl <= full_prop_lvl; lvl++) {
        IF_VERBOSE (1,
                    if (lvl > max_prop_lvl && lvl == max_prop_lvl + 1)
                        verbose_stream () << " ! ";
                    verbose_stream () << lvl << " " << std::flush;);

        checkpoint();
        CTRACE ("spacer", lvl > max_prop_lvl && lvl == max_prop_lvl + 1,
                tout << "In full propagation\n";);

        bool all_propagated = true;
        for (auto & kv : m_rels) {
            checkpoint();
            pred_transformer& r = *kv.m_value;
            all_propagated &= r.propagate_to_next_level(lvl);
        }
        //CASSERT("spacer", check_invariant(lvl));

        if (all_propagated) {
            for (auto& kv : m_rels) {
                checkpoint ();
                pred_transformer& r = *kv.m_value;
                r.propagate_to_infinity (lvl);
            }
            if (lvl <= max_prop_lvl) {
                m_inductive_lvl = lvl;
                IF_VERBOSE(1, verbose_stream () << "\n";);
                return true;
            }
            break;
        }

        if (all_propagated && lvl == max_prop_lvl) {
            m_inductive_lvl = lvl;
            return true;
        } else if (all_propagated && lvl > max_prop_lvl) { break; }
    }
    if (m_simplify_formulas_post) {
        simplify_formulas();
    }

    IF_VERBOSE(1, verbose_stream () << "\n";);
    return false;
}

reach_fact *pred_transformer::mk_rf(pob& n, model &mdl, const datalog::rule& r, unsigned version)
{
//    SASSERT(&n.pt() == this);
    timeit _timer1 (is_trace_enabled("spacer_timeit"),
                    "mk_rf",
                    verbose_stream ());
    expr_ref res(m);
    reach_fact_ref_vector child_reach_facts;

    ptr_vector<func_decl> preds;
    find_predecessors (r, preds);

    expr_ref_vector path_cons (m);
    expr_ref trans(get_transition (r), m);
    pm.formula_v2v(trans, trans, 0, version);
    path_cons.push_back (trans);
    app_ref_vector vars (m);

    for (unsigned i = 0; i < preds.size (); i++) {
        func_decl* pred = preds[i];
        pred_transformer& ch_pt = ctx.get_pred_transformer (pred);
        // get a reach fact of body preds used in the model
        expr_ref o_ch_reach (m);
        reach_fact *kid = ch_pt.get_used_origin_rf(mdl, i, version);
        child_reach_facts.push_back (kid);
        pm.formula_n2o (kid->get (), o_ch_reach, i);
        pm.formula_v2v (o_ch_reach, o_ch_reach, 0, version);
        path_cons.push_back (o_ch_reach);
        // collect o-vars to eliminate
        for (unsigned j = 0; j < pred->get_arity (); j++)
        { vars.push_back(m.mk_const(pm.get_version_pred(pm.o2o(ch_pt.sig(j), 0, i), 0, version))); }

        const ptr_vector<app> &v = kid->aux_vars ();
        for (unsigned j = 0, sz = v.size (); j < sz; ++j)
        { vars.push_back(m.mk_const(pm.get_version_pred(pm.n2o(v [j]->get_decl(), i), 0, version))); }
    }
    // collect aux vars to eliminate
    ptr_vector<app>& aux_vars = get_aux_vars (r);
    bool elim_aux = ctx.elim_aux();
    if (elim_aux) { vars.append(aux_vars.size(), aux_vars.c_ptr()); }

    res = mk_and (path_cons);

    // -- pick an implicant from the path condition
    if (ctx.reach_dnf()) {
        expr_ref_vector u(m), lits(m);
        u.push_back (res);
        compute_implicant_literals (mdl, u, lits);
        res = mk_and (lits);
    }

    TRACE ("spacer",
           tout << "Reach fact, before QE:\n";
           tout << mk_pp (res, m) << "\n";
           tout << "Vars:\n";
           for (unsigned i = 0; i < vars.size(); ++i) {
               tout << mk_pp(vars.get (i), m) << "\n";
           }
        );

    {
        timeit _timer1 (is_trace_enabled("spacer_timeit"),
                        "mk_rf::qe_project",
                        verbose_stream ());
        mbp(vars, res, mdl, false, true /* force or skolemize */);
    }


    TRACE ("spacer",
           tout << "Reach fact, after QE project:\n";
           tout << mk_pp (res, m) << "\n";
           tout << "Vars:\n";
           for (unsigned i = 0; i < vars.size(); ++i) {
               tout << mk_pp(vars.get (i), m) << "\n";
           }
        );

    SASSERT (vars.empty ());

    m_stats.m_num_reach_queries++;
    ptr_vector<app> empty;
    pm.formula_v2v(res, res, version, 0);
    reach_fact *f = alloc(reach_fact, m, r, res, elim_aux ? empty : aux_vars);
    for (unsigned i = 0, sz = child_reach_facts.size (); i < sz; ++i)
    { f->add_justification(child_reach_facts.get(i)); }
    return f;
}

struct func_decl_triple_lt_proc : public std::binary_function<triple<func_decl*,unsigned,unsigned>, triple<func_decl*,unsigned,unsigned>, bool> {
    bool operator() (const triple<func_decl*,unsigned,unsigned> &a, const triple<func_decl*,unsigned,unsigned> &b) {
        return !a.first || !b.first || lt(a.first->get_name(), b.first->get_name()) || a.second < b.second || a.third < b.third;
    }
};


/**
   \brief create children states from model cube.
*/
bool context::create_children(pob& n,
                              versioned_rule_vector &rules,
                              model &mdl,
                              const vector<bool> &reach_pred_used,
                              pob_ref_buffer &out)
{
    LOG_STREAM << "create-children " << n.pt().name() << "\n";
    LOG_STREAM << "versions of rules: ";
    for (auto &p : rules) { LOG_STREAM << p.first->get_head()->get_name() << " " << p.second << "; "; }
    LOG_STREAM << std::endl;
    scoped_watch _w_ (m_create_children_watch);
    pred_transformer& pt = n.pt();

    // obtain all formulas to consider for model generalization
    expr_ref_vector forms(m), lits(m);
    pt.get_transitions(rules, forms);
    pt.get_initials(rules, mdl, forms);
    forms.push_back(n.post());
    LOG_STREAM << "forms: " << forms << std::endl;

    TRACE("spacer",
          tout << "Model:\n";
          model_smt2_pp(tout, m, mdl, 0);
          tout << "\n";
          tout << "Transition:\n" << forms << "\n";
          tout << "Pob:\n" << mk_pp(n.post(), m) << "\n";);

    compute_implicant_literals (mdl, forms, lits);
    expr_ref phi = mk_and (lits);

    // primed variables of the head
    app_ref_vector vars(m);
    for (unsigned i = 0, sz = pt.sig_size(); i < sz; ++i) {
        vars.push_back(m.mk_const(m_pm.o2n(pt.sig(i), 0)));
    }
    // local variables of the rule
    pt.get_aux_vars(rules, vars);

    // skolems of the pob
    n.get_skolems(vars);

    LOG_STREAM << "after picking: " << mk_pp(phi, m) << std::endl;
    LOG_STREAM << "vars: " << vars << std::endl;
    n.pt().mbp(vars, phi, mdl, true, use_ground_pob());
    //qe::reduce_array_selects (*mev.get_model (), phi1);
    SASSERT (!m_ground_pob || vars.empty ());

    TRACE ("spacer",
           tout << "Implicant:\n";
           tout << lits << "\n";
           tout << "After MBP:\n" << phi << "\n";
           if (!vars.empty())
               tout << "Failed to eliminate: " << vars << "\n";
        );

    if (m_use_gpdr) {
        vector<versioned_func> preds;
        pt.find_predecessors(rules, preds);
        if (preds.size() > 1) {
            SASSERT(vars.empty());
            return gpdr_create_split_children(n, preds, phi, mdl, out);
        }
    }

    LOG_STREAM << "alloc derivation with phi: " << mk_pp(phi, m) << std::endl;
    derivation *deriv = alloc(derivation, n, phi, vars);

/////// ----- begin of old code -------
//    // pick an order to process children
//    unsigned_vector kid_order;
//    kid_order.resize(preds.size(), 0);
//    for (unsigned i = 0, sz = preds.size(); i < sz; ++i) kid_order[i] = i;
//    if (m_children_order == CO_REV_RULE) {
//        kid_order.reverse();
//    }
//    else if (m_children_order == CO_RANDOM) {
//        shuffle(kid_order.size(), kid_order.c_ptr(), m_random);
//    }

//    LOG_STREAM << "------------------------------\n";
//    for (unsigned i = 0, sz = preds.size(); i < sz; ++i) {
//        unsigned j = kid_order[i];

//        pred_transformer &pt = get_pred_transformer(preds.get(j));
//        LOG_STREAM << "CREATE_CHILDREN (LEVEL" << n.level() << "): " << pt.name() << " is " << (reach_pred_used[j] ? "rf" : "sum") << "\n";

//        const ptr_vector<app> *aux = nullptr;
//        expr_ref sum(m);
//        sum = pt.get_origin_summary (mdl, prev_level(n.level()),
//                                     j, reach_pred_used[j], &aux);
//        if (!sum) {
//            dealloc(deriv);
//            return false;
//        }
//        STRACE("spacer",
//               tout << "[dvvrd] Adding premise[" << j << "]: " << reach_pred_used[j] << ";;; " << mk_pp(sum, m) << "\n";);
//        deriv->add_premise (pt, j, sum, reach_pred_used[j], aux);
//    }
/////// ----- end of old code -------

    ptr_vector<func_decl> rec_heads;
    manager::idx_subst rec_oidcs;
    ptr_vector<func_decl> nonrec_heads;
    vector<triple<func_decl*, unsigned, unsigned>> rec_metaheads;
    vector<triple<func_decl*, unsigned, unsigned>> nonrec_metaheads;
    manager::source_subst nonrec_source_subst;
    manager::idx_subst nonrec_oidcs;
    manager::source_subst rec_source_subst;
    unsigned recidx = 0;
    unsigned nonrecidx = 0;
    unsigned idx = 0;
    for (auto &pair : rules) {
        const datalog::rule *r = pair.first;
        unsigned version = pair.second;
        for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i, ++idx) {
            if (reach_pred_used[idx]) {
                func_decl *h = r->get_tail(i)->get_decl();
                pred_transformer &pt = get_pred_transformer(h);
                const ptr_vector<app> *aux = nullptr;
                expr_ref sum(m);
                manager::idx_subst oidcs;
                m_pm.add_o_subst(oidcs, h, 0, i, version);
                sum = pt.get_origin_summary (mdl, prev_level(n.level()), oidcs, true, &aux);
                if (!sum) {
                    dealloc(deriv);
                    return false;
                }
                LOG_STREAM << "adding reachability premise " << h->get_name() << " " << version << "\n";
                deriv->add_reachability_premise(pt, h, i, version, sum, aux);
            } else {
                // dvvrd: TODO: remove copy-paste!
                func_decl *h = r->get_tail(i)->get_decl();
                bool is_recursive = false;
                for (auto &pair : pt.heads()) {
                    if (pair.func == h) {
                        is_recursive = version < pair.count;  // TODO: assume that version is a general one
                        break;
                    }
                }
                if (is_recursive) {
                    rec_metaheads.push_back({h, version, i});
                } else {
                    nonrec_metaheads.push_back({h,version,i});
                }
//                if (is_recursive) {
//                    LOG_STREAM << "adding recursive summary premise " << h->get_name() << " " << version << std::endl;
//                    rec_heads.push_back(h);
////                    unsigned v = 0;
////                    while (rec_oidcs.contains({h, v})) ++v;
//                    ++recidx;
//                    m_pm.add_source_subst(rec_source_subst, h, version, i, recidx);
//                    m_pm.add_o_subst(rec_oidcs, h, recidx, i, version);
//                } else {
//                    LOG_STREAM << "adding non-recursive summary premise " << h->get_name() << " " << version << std::endl;
//                    nonrec_heads.push_back(h);
////                    unsigned v = 0;
////                    while (nonrec_oidcs.contains({h, v})) ++v;
//                    ++nonrecidx;
//                    m_pm.add_source_subst(nonrec_source_subst, h, version, i, nonrecidx);
//                    m_pm.add_o_subst(nonrec_oidcs, h, nonrecidx, i, version);
//                }
            }
        }
    }
    std::sort(rec_metaheads.begin(), rec_metaheads.end(), func_decl_triple_lt_proc());
    std::sort(nonrec_metaheads.begin(), nonrec_metaheads.end(), func_decl_triple_lt_proc());
    for (auto &t : rec_metaheads) {
        LOG_STREAM << "adding recursive summary premise " << t.first->get_name() << " " << recidx << std::endl;
        rec_heads.push_back(t.first);
        m_pm.add_source_subst(rec_source_subst, t.first, t.second, t.third, recidx);
        m_pm.add_o_subst(rec_oidcs, t.first, recidx, t.third, t.second);
        ++recidx;
    }
    for (auto &t : nonrec_metaheads) {
        // dvvrd: For me in the future: the triple stores <func, version, i>
        LOG_STREAM << "adding non-recursive summary premise " << t.first->get_name() << " " << nonrecidx << std::endl;
        nonrec_heads.push_back(t.first);
        m_pm.add_source_subst(nonrec_source_subst, t.first, t.second, t.third, nonrecidx);
        m_pm.add_o_subst(nonrec_oidcs, t.first, nonrecidx, t.third, t.second);
        ++nonrecidx;
    }

    SASSERT(!rec_heads.empty() || !nonrec_heads.empty());

    // TODO: rec_heads should not have more heads of each func/version than heads!
    // The more precise grouping should be implemented!

    LOG_STREAM << "rules count: " << rules.size() << "\n";
    if (!rec_heads.empty()) {
        pred_transformer &premise_pt = get_pred_transformer(rec_heads);
        // dvvrd: TODO: remove copy-paste!
        // dvvrd: TODO: separate reasoning for ambiguous coverage (like in case of fib)
        const ptr_vector<app> *aux = nullptr;
        expr_ref sum(m);
        sum = premise_pt.get_origin_summary (mdl, prev_level(n.level()), rec_oidcs, false, &aux);
        if (!sum) {
            LOG_STREAM << "BAILING OUT REC\n";
            dealloc(deriv);
            return false;
        }
        LOG_STREAM << "creating recursive child " << premise_pt.name() << "\n";
        deriv->add_summary_premise(premise_pt, rec_source_subst, rec_oidcs, sum);
    }
    if (!nonrec_heads.empty()) {
        pred_transformer &premise_pt = get_pred_transformer(nonrec_heads);
        const ptr_vector<app> *aux = nullptr;
        expr_ref sum(m);
        sum = premise_pt.get_origin_summary (mdl, prev_level(n.level()), nonrec_oidcs, false, &aux);
        LOG_STREAM << "NON_REC OR SUM FOR " << premise_pt.name() << " RETURNED " << mk_pp(sum, m) << std::endl;
        if (!sum) {
            LOG_STREAM << "BAILING OUT NONREC" << std::endl;
            dealloc(deriv);
            return false;
        }
        LOG_STREAM << "creating non-recursive child " << premise_pt.name() << std::endl;
        deriv->add_summary_premise(premise_pt, nonrec_source_subst, nonrec_oidcs, sum);
    }

    // create post for the first child and add to queue
    pob* kid = deriv->create_first_child (mdl);

    // -- failed to create derivation, cleanup and bail out
    if (!kid) {
        dealloc(deriv);
        return false;
    }
    SASSERT (kid);
    kid->set_derivation (deriv);

    // Optionally disable derivation optimization
    if (!m_use_derivations) { kid->reset_derivation(); }

    bool is_true = mdl.is_true(n.post());
    for (auto &trans : forms) {
        if (!is_true) { break; }
        is_true &= mdl.is_true(trans);
    }
    // -- deriviation is abstract if the current weak model does
    // -- not satisfy 'T && phi'. It is possible to recover from
    // -- that more gracefully. For now, we just remove the
    // -- derivation completely forcing it to be recomputed
    if (m_weak_abs && !is_true)
    { kid->reset_derivation(); }

    LOG_STREAM << "[dvvrd] PUSHING KID POB: [" << (long)kid << "] [parent: "
              << (long)(kid->parent()) <<  "] (" << kid->pt().name() << ", lvl " << kid->level() << ") "
              << mk_pp(kid->post(), m) << "\n";
    out.push_back(kid);
    m_stats.m_num_queries++;
    return true;
}




void context::collect_statistics(statistics& st) const
{
    m_pool0->collect_statistics(st);
    m_pool1->collect_statistics(st);
    m_pool2->collect_statistics(st);

    for (auto const& kv : m_rels) {
        kv.m_value->collect_statistics(st);
    }

    // -- number of times a pob for some predicate transformer has
    // -- been created
    st.update("SPACER num queries", m_stats.m_num_queries);
    // -- number of times a reach fact was true in some model
    st.update("SPACER num reuse reach facts", m_stats.m_num_reuse_reach);
    // -- maximum level at which any query was asked
    st.update("SPACER max query lvl", m_stats.m_max_query_lvl);
    // -- maximum depth
    st.update("SPACER max depth", m_stats.m_max_depth);
    // -- level at which safe inductive invariant was found
    st.update("SPACER inductive level", m_inductive_lvl);
    // -- length of the counterexample
    st.update("SPACER cex depth", m_stats.m_cex_depth);
    // -- number of times expand_pobresulted in undef
    st.update("SPACER expand pob undef", m_stats.m_expand_pob_undef);
    // -- number of distinct lemmas constructed
    st.update("SPACER num lemmas", m_stats.m_num_lemmas);
    // -- number of restarts taken
    st.update("SPACER restarts", m_stats.m_num_restarts);

    // -- time to initialize the rules
    st.update ("time.spacer.init_rules", m_init_rules_watch.get_seconds ());
    // -- time in the main solve loop
    st.update ("time.spacer.solve", m_solve_watch.get_seconds ());
    // -- time in lemma propagation (i.e., pushing)
    st.update ("time.spacer.solve.propagate", m_propagate_watch.get_seconds ());
    // -- time in reachability (i.e., blocking)
    st.update ("time.spacer.solve.reach", m_reach_watch.get_seconds ());
    // -- time in deciding whether a pob is must-reachable
    st.update ("time.spacer.solve.reach.is-reach", m_is_reach_watch.get_seconds ());
    // -- time in creating new predecessors
    st.update ("time.spacer.solve.reach.children",
               m_create_children_watch.get_seconds ());
    st.update("spacer.random_seed", m_params.spacer_random_seed());
    st.update("spacer.lemmas_imported", m_stats.m_num_lemmas_imported);
    st.update("spacer.lemmas_discarded", m_stats.m_num_lemmas_discarded);

    for (unsigned i = 0; i < m_lemma_generalizers.size(); ++i) {
        m_lemma_generalizers[i]->collect_statistics(st);
    }
}

void context::reset_statistics()
{
    m_pool0->reset_statistics();
    m_pool1->reset_statistics();
    m_pool2->reset_statistics();

    for (auto & kv : m_rels) {
        kv.m_value->reset_statistics();
    }
    m_stats.reset();

    for (unsigned i = 0; i < m_lemma_generalizers.size(); ++i) {
        m_lemma_generalizers[i]->reset_statistics();
    }

    m_init_rules_watch.reset ();
    m_solve_watch.reset ();
    m_propagate_watch.reset ();
    m_reach_watch.reset ();
    m_is_reach_watch.reset ();
    m_create_children_watch.reset ();
}

bool context::check_invariant(unsigned lvl)
{
    for (auto &entry : m_rels) {
        checkpoint();
        if (!check_invariant(lvl, *entry.m_value)) {
            return false;
        }
    }
    return true;
}

// MAKES QUERY
// USED ONLY FOR VALIDATION?
bool context::check_invariant(unsigned lvl, pred_transformer& pt)
{
    ref<solver> ctx = mk_smt_solver(m, params_ref::get_empty(), symbol::null);
    expr_ref_vector conj(m);
    expr_ref inv = pt.get_formulas(next_level(lvl));
    if (m.is_true(inv)) { return true; }
    pt.add_premises(m_rels, lvl, conj);
    conj.push_back(m.mk_not(inv));
    expr_ref fml(m.mk_and(conj.size(), conj.c_ptr()), m);
    ctx->assert_expr(fml);
    lbool result = ctx->check_sat(0, nullptr);
    TRACE("spacer", tout << "Check invariant level: " << lvl << " " << result
          << "\n" << mk_pp(fml, m) << "\n";);
    return result == l_false;
}

void context::add_constraint (expr *c, unsigned level)
{
    if (!c) { return; }
    if (m.is_true(c)) { return; }

        expr *e1, *e2;
        if (m.is_implies(c, e1, e2)) {
            SASSERT (is_app (e1));
            // dvvrd: TODO: add information for all pts containing this decl!
            func_decl_multivector key;
            key.push_back({to_app (e1)->get_decl (), 1});
            pred_transformer * r = nullptr;
            if (m_rels.find(key, r)) {
                lemma_ref lem = alloc(lemma, m, e2, level);
                lem.get()->set_external(true);
                if (r->add_lemma(lem.get())) {
                    this->m_stats.m_num_lemmas_imported++;
                }
                else{
                    this->m_stats.m_num_lemmas_discarded++;
            }
        }
    }
}

void context::new_lemma_eh(pred_transformer &pt, lemma *lem) {
    if (m_params.spacer_print_json().size())
        m_json_marshaller.register_lemma(lem);
    bool handle=false;
    for (unsigned i = 0; i < m_callbacks.size(); i++) {
        handle|=m_callbacks[i]->new_lemma();
    }
    if (!handle)
        return;
    if ((is_infty_level(lem->level()) && m_params.spacer_p3_share_invariants()) ||
        (!is_infty_level(lem->level()) && m_params.spacer_p3_share_lemmas())) {
        expr_ref_vector args(m);
        for (unsigned i = 0; i < pt.sig_size(); ++i) {
            args.push_back(m.mk_const(pt.get_manager().o2n(pt.sig(i), 0)));
        }
        // dvvrd: TODO: rly merged_head?
        expr *app = m.mk_app(pt.merged_head(), pt.sig_size(), args.c_ptr());
        expr *lemma = m.mk_implies(app, lem->get_expr());
        for (unsigned i = 0; i < m_callbacks.size(); i++) {
            if (m_callbacks[i]->new_lemma())
                m_callbacks[i]->new_lemma_eh(lemma, lem->level());
        }
    }
}

void context::new_pob_eh(pob *p) {
    if (m_params.spacer_print_json().size())
        m_json_marshaller.register_pob(p);
}

bool context::is_inductive() {
    // check that inductive level (F infinity) of the query predicate
    // contains a constant false

    return false;
}

/// pob_lt operator
inline bool pob_lt_proc::operator() (const pob *pn1, const pob *pn2) const
{
    SASSERT (pn1);
    SASSERT (pn2);
    const pob& n1 = *pn1;
    const pob& n2 = *pn2;

    if (n1.level() != n2.level()) { return n1.level() < n2.level(); }

    if (n1.depth() != n2.depth()) { return n1.depth() < n2.depth(); }

    // -- a more deterministic order of proof obligations in a queue
    // if (!n1.get_context ().get_params ().spacer_nondet_tie_break ())
    {
        const expr* p1 = n1.post ();
        const expr* p2 = n2.post ();
        ast_manager &m = n1.get_ast_manager ();


        // -- order by size. Less conjunctions is a proxy for
        // -- generality.  Currently, this takes precedence over
        // -- predicates which might not be the best choice
        unsigned sz1 = 1;
        unsigned sz2 = 1;

        if (m.is_and(p1)) { sz1 = to_app(p1)->get_num_args(); }
        if (m.is_and(p2)) { sz2 = to_app(p2)->get_num_args(); }
        if (sz1 != sz2) { return sz1 < sz2; }

        // -- when all else fails, order by identifiers of the
        // -- expressions.  This roughly means that expressions created
        // -- earlier are preferred.  Note that variables in post are
        // -- based on names of the predicates. Hence this guarantees an
        // -- order over predicates as well. That is, two expressions
        // -- are equal if and only if they correspond to the same proof
        // -- obligation of the same predicate.
        if (p1->get_id() != p2->get_id()) { return p1->get_id() < p2->get_id(); }

        if (n1.pt().heads().size() != n1.pt().heads().size())
        { return n1.pt().heads().size() < n1.pt().heads().size(); }

        for (unsigned i = 0, sz = n1.pt().heads().size(); i < sz; ++i) {
            // XXX see comment below on identical nodes
            // SASSERT (n1.pt ().head ()->get_id () != n2.pt ().head ()->get_id ());
            // -- if expression comparison fails, compare by predicate id
            auto &p1 = n1.pt().heads ()[i];
            auto &p2 = n2.pt().heads ()[i];
            if (p1.func->get_id () != p2.func->get_id ()) {
                return p1.func->get_id() < p2.func->get_id();
            } else if (p1.count != p2.count) {
                return p1.count < p2.count;
            }
        }

        IF_VERBOSE (1,
                    verbose_stream ()
                    << "dup: " << n1.pt ().name ()
                    << "(" << n1.level () << ", " << n1.depth () << ") "
                    << p1->get_id () << "\n";
                    //<< " p1: " << mk_pp (const_cast<expr*>(p1), m) << "\n"
            );

        /** XXX Identical nodes. This should not happen. However,
         * currently, when propagating reachability, we might call
         * expand_pob() twice on the same node, causing it to generate
         * the same proof obligation multiple times */
        return &n1 < &n2;
    }
    // else
    //   return &n1 < &n2;
}



}
