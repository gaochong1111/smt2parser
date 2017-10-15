#include "csltp_sat.h"
#include<sstream>
#include<iostream>


/**
 * csltp context construct function
 */

csltp_context::csltp_context() :delta_ge1_predicates(ctx), new_bool_vars(ctx), pure_abs(ctx), space_abs(ctx), phi_star(ctx){
        this->lvars = NULL;
        this->index_processing = -1;

        this->pure_abs = this->ctx.bool_val(true);
        this->space_abs = this->ctx.bool_val(true);
        this->phi_star = this->ctx.bool_val(true);
}


/**
 *@return 1, if sat
 0, if unsat
 3,if undef
*/
int csltp_sat_check(noll_form_t * form) {
        //TODO: check the formula sat

        // for all atom, compute abstraction(ai)

        csltp_context ctx;
        // z3::context ctx;
        ctx.lvars = form->lvars;

        // compute the delta_pd
        compute_all_delta_ge1_p(ctx);

        // translate formula to abstraction
        noll_pure_t* pure = form->pure;

        abs_pure(pure, ctx);

        // cout<< "\npure abstraction:\n";
        // cout<< ctx.pure_abs << endl;

        noll_space_t* space = form->space;
        abs_space(space, ctx);

        // cout<<"\nspace abstraction:\n";
        // cout<< ctx.space_abs << endl;

        abs_phi_star(ctx);

        // cout << "\nphi_star:\n";
        // cout << ctx.phi_star<<endl;

        z3::expr abs = ctx.pure_abs && ctx.space_abs && ctx.phi_star;

        // cout<<"\n abs:\n";
        // cout<< abs <<endl;
        // slove

        z3::solver s(ctx.ctx);
        s.add(abs);
        int res = -1;

        switch (s.check()) {
        case z3::unsat:   res = 0; break;
        case z3::sat:     res = 1; break;
        case z3::unknown: res = 3; break;
        }

        return res;
}


/**
 * compute all predicate delta_ge1_p
 * @param ctx : csltp context
 */
void compute_all_delta_ge1_p(csltp_context& ctx) {
        uid_t size_pred = noll_vector_size(preds_array);

        for (uid_t i=0; i<size_pred; i++) {
                noll_pred_t* pred = noll_vector_at(preds_array, i);
                uid_t fargs = pred->def->fargs;
                z3::expr phi_pd_abs = compute_delta_phi_pd(pred, ctx.ctx);
                // compute delta_ge1_p
                z3::expr delta_ge1_p_abs =  ctx.ctx.bool_val(false);
                // for all recursive rules
                noll_pred_rule_array* rec_rules = pred->def->rec_rules;

                uid_t length_rules = noll_vector_size(rec_rules);

                for (uid_t k=0; k<length_rules; k++) {
                        // for each rule
                        noll_pred_rule_t* rule = noll_vector_at(rec_rules, k);

                        z3::expr delta_ge1_r = compute_delta_ge1_r(rule, pred, phi_pd_abs, ctx);

                        delta_ge1_p_abs = delta_ge1_p_abs || delta_ge1_r;
                }

                ctx.delta_ge1_predicates.push_back(delta_ge1_p_abs);
        }
}




/**
 * compute delta_ge1_r
 * @param rule : the rule R
 * @param fargs : the recursive call predicate arguments number
 * @param ctx : csltp context
 * @return expr
 */
z3::expr compute_delta_ge1_r(noll_pred_rule_t* rule, noll_pred_t* pred, z3::expr& phi_pd_abs, csltp_context& ctx) {

        uid_t fargs = pred->def->fargs;

        // compute delta_ge1_r
        z3::expr_vector x_vars(ctx.ctx); // exists x f
        for (uid_t i=1+fargs; i<noll_vector_size(rule->vars); i++) {
                if (noll_vector_at(rule->vars, i)->vty->kind == NOLL_TYP_RAT) {
                        z3::expr x_var = ctx.ctx.real_const(noll_vector_at(rule->vars, i)->vname);
                        x_vars.push_back(x_var);
                }
        }

        // compute exists formula
        OrderGraph g_delta;
        pure2graph(rule, g_delta);
        z3::expr formula = graph2expr(g_delta, ctx.ctx);

        // compute delta, gamma, epsilon, alpha, beta
        z3::expr_vector alpha(ctx.ctx);
        z3::expr_vector delta(ctx.ctx);
        z3::expr_vector gamma(ctx.ctx);

        noll_space_array* sep = rule->rec->m.sep;
        noll_space_t* phi = noll_vector_at(sep, 0);
        noll_space_t* phi_delta = NULL;
        if (noll_vector_at (phi->m.ls.args, fargs/2) == 0) { // nil
                phi_delta =  noll_vector_at(sep, 1);
        } else {
                phi_delta = phi;
                phi = noll_vector_at(sep, 1);
        }
        // compute alpha, delta, gamma

        for (uid_t i=1; i<=fargs/2; i++) {
                noll_var_t* alpha_v = noll_vector_at(pred->def->vars, i);
                alpha.push_back(ctx.ctx.real_const(alpha_v->vname));

                z3::expr delta_v = create_expr_args(rule->vars, noll_vector_at(phi_delta->m.ls.args, i-1), ctx.ctx);
                delta.push_back(delta_v);
                z3::expr gamma_v = create_expr_args(rule->vars, noll_vector_at(phi->m.ls.args, i-1), ctx.ctx);
                gamma.push_back(gamma_v);

        }

        // substitute 1
        formula = formula && phi_pd_abs.substitute(alpha, delta);


        // add beta and epsilon
        for (uid_t i=fargs/2+2; i<=fargs; i++) {
                noll_var_t* beta_v = noll_vector_at(pred->def->vars, i);
                alpha.push_back(ctx.ctx.real_const(beta_v->vname));

                z3::expr epsilon_v =  create_expr_args(rule->vars, noll_vector_at(phi->m.ls.args, i-1), ctx.ctx);
                gamma.push_back(epsilon_v);
        }
        // substitute2
        formula = formula && phi_pd_abs.substitute(alpha, gamma);

        z3::expr delta_ge1_r = exists(x_vars, formula);
        return delta_ge1_r;
}


/**
 * compute the delta_phi_pd
 * @param pred : predicate
 * @param ctx : z3 context
 * @return expr
 */
z3::expr compute_delta_phi_pd(noll_pred_t* pred, z3::context& ctx) {

        if (pred->typ->p.treekind == NOLL_PRED_TREE_ONLY_DATA) {
                z3::expr phi_pd_abs = ctx.bool_val(false);
                // if pred->typing only data constraint
                OrderGraphSet ogset = lfp(pred);
                print_order_graph_set(ogset, pred->pname);
                for (int j=0; j<ogset.size(); j++) {
                        OrderGraph og = ogset.at(j);
                        z3::expr og_expr = graph2expr(og, ctx);
                        phi_pd_abs = phi_pd_abs || og_expr;
                }
                return phi_pd_abs;
        } else if (pred->typ->p.treekind == NOLL_PRED_TREE_NONE_DATA) {
                return ctx.bool_val(true);
        } else if (pred->typ->p.treekind == NOLL_PRED_TREE_ONLY_SIZE) {
                return ctx.bool_val(true);
        } else {
                return ctx.bool_val(true);
        }
}


/**
 * abstraction of pure part
 * @param pure : pure part of formula
 * @param ctx : csltp ontext
 */
void abs_pure(noll_pure_t* pure, csltp_context& ctx) {
        if (pure == NULL) return ;
        for (uid_t l = 0; l < pure->size; l++)
        {
                for (uid_t c = l+1; c < pure->size; c++)
                {
                        noll_var_t* var1 = noll_vector_at(ctx.lvars, l);
                        noll_var_t* var2 = noll_vector_at(ctx.lvars, c);
                        z3::expr expr1 = var2expr(var1, ctx);
                        z3::expr expr2 = var2expr(var2, ctx);
                        switch (noll_pure_matrix_at (pure, l, c))
                        {
                        case NOLL_PURE_EQ:
                                ctx.pure_abs = ctx.pure_abs && (expr1 == expr2);
                                break;
                        case NOLL_PURE_NEQ:
                                ctx.pure_abs = ctx.pure_abs && (expr1 != expr2);
                                break;
                        default:
                                break;
                        }
                }
        }

        // data formula

        noll_dform_array* dfs = pure->data;

        if (dfs == NULL) return ;

        for (uint_t i = 0; i < noll_vector_size (dfs); i++)
        {
                noll_dform_t* df = noll_vector_at(dfs, i);
                z3::expr df_abs = dform2expr(df, ctx);
                ctx.pure_abs = ctx.pure_abs && df_abs;
        }
}

/**
 * abstraction of space part
 * @param space : the spatial part
 * @param ctx : csltp_context
 */
void abs_space(noll_space_t* space, csltp_context& ctx) {

        if (space->kind == NOLL_SPACE_PTO) {
                ctx.index_processing++;
                // pto atom
                noll_var_t* pto_source = noll_vector_at(ctx.lvars, space->m.pto.sid);
                ctx.space_abs = ctx.space_abs && var2expr(pto_source, ctx)>0;
                ctx.space_abs = ctx.space_abs && introduce_bool_var(pto_source, ctx);
        } else if (space->kind == NOLL_SPACE_LS) {
                ctx.index_processing++;
                // predicate atom
                uid_t pid = space->m.ls.pid;
                noll_pred_t* pred =  noll_vector_at (preds_array, pid);
                uid_t fargs = pred->def->fargs;
                uid_t z1_id =  noll_vector_at(space->m.ls.args, 0);
                noll_var_t* z1 = noll_vector_at(ctx.lvars, z1_id);
                uid_t z2_id =  noll_vector_at(space->m.ls.args, fargs/2);
                noll_var_t* z2 = noll_vector_at(ctx.lvars, z2_id);
                z3::expr z1_bool = introduce_bool_var(z1, ctx);
                z3::expr z1_abs = var2expr(z1, ctx);
                z3::expr z2_abs = var2expr(z2, ctx);

                z3::expr ufld0 = (!z1_bool && (z1_abs==z2_abs));

                z3::expr_vector to(ctx.ctx); // \mu \nu
                for (uid_t i=1; i<fargs/2; i++) {
                        uid_t mu_id =  noll_vector_at(space->m.ls.args, i);
                        noll_var_t* mu = noll_vector_at(ctx.lvars, mu_id);
                        uid_t nu_id =  noll_vector_at(space->m.ls.args, i+fargs/2);
                        noll_var_t* nu = noll_vector_at(ctx.lvars, nu_id);
                        z3::expr mu_abs = var2expr(mu, ctx);
                        z3::expr nu_abs = var2expr(nu, ctx);
                        ufld0 = ufld0 && (mu_abs == nu_abs);
                        to.push_back(mu_abs);
                        to.push_back(nu_abs);
                }

                z3::expr delta_p = ctx.delta_ge1_predicates[pid];
                z3::expr_vector from(ctx.ctx); // \alpha \beta

                for (uid_t i=2; i<=fargs/2; i++) {
                        noll_var_t* alpha = noll_vector_at(pred->def->vars, i);
                        noll_var_t* beta = noll_vector_at(pred->def->vars, i+fargs/2);
                        from.push_back(var2expr(alpha, ctx));
                        from.push_back(var2expr(beta, ctx));
                }

                delta_p.substitute(from, to);

                z3::expr ufld_ge1 = (z1_bool && (z1_abs != 0) && delta_p);

                z3::expr pi_abs = (ufld0 || ufld_ge1);

                ctx.space_abs = ctx.space_abs && pi_abs;
        } else if (space->kind == NOLL_SPACE_SSEP) {
                for (uid_t i=0; i<noll_vector_size(space->m.sep); i++) {
                        abs_space(noll_vector_at(space->m.sep, i), ctx);
                }
        }
}

/**
 * compute phi_star
 * @param ctx : csltp_context
 */
void abs_phi_star(csltp_context& ctx) {
        z3::expr_vector bool_vars(ctx.ctx);
        // the new bool vars may be repeated
        int size = ctx.new_bool_vars.size();
        for (int i=0; i<size; i++) {
                int size_b = bool_vars.size();
                bool insert_flag = true;
                for(int j=0; j<size_b; j++) {
                        if (ctx.new_bool_vars[i].hash() == bool_vars[j].hash()) {
                                insert_flag = false;
                                break;
                        }
                }

                if (insert_flag) {
                        bool_vars.push_back(ctx.new_bool_vars[i]);
                }
        }

        // compute phi_star

        size = bool_vars.size();
        for (int i=0; i<size; i++) {
                for (int j=i+1; j<size; j++) {
                        string str1 = bool_vars[i].to_string();
                        string str2 = bool_vars[j].to_string();

                        // string: |[z1,1]|
                        if (str1[str1.length()-3] != str2[str2.length()-3]) {
                                // i != j, add implied formula
                                string z1_str = str1.substr(2, str1.length() - 6);
                                string z2_str = str2.substr(2, str2.length() - 6);

                                z3::expr z1_abs = ctx.ctx.int_const(z1_str.c_str());
                                z3::expr z2_abs = ctx.ctx.int_const(z2_str.c_str());
                                z3::expr P = (z1_abs==z2_abs) && bool_vars[i];
                                z3::expr Q = !bool_vars[j];
                                // P => Q
                                z3::expr imp_f = implies(P, Q);
                                ctx.phi_star = ctx.phi_star && imp_f;
                        }
                }
        }
}





/**
 * compute lfp(pred)
 * @param pred: the predicate definition
 * @return ogset: the least fixed point: order graph set
 */
OrderGraphSet lfp(noll_pred_t* pred) {
        // init: construct G0 by base rule
        noll_pred_rule_t* base_rule = noll_vector_at (pred->def->base_rules, 0);
        uid_t fargs = pred->def->fargs;

        // compute alpha, beta
        vector<Vertex> alpha;
        vector<Vertex> beta;
        extractAlphaBeta(pred, alpha, beta);

        OrderGraph g0;
        pure2graph(base_rule, g0);

        // standard iteratiron:
        OrderGraphSet ogset_new;
        OrderGraphSet ogset;
        ogset.addOrderGraph(g0);

        while(!(ogset==ogset_new)) {
                ogset_new = ogset;

                // for all recursive rules
                noll_pred_rule_array* rec_rules = pred->def->rec_rules;

                uid_t length_rules = noll_vector_size(rec_rules);

                for (uid_t k=0; k<length_rules; k++) {
                        noll_pred_rule_t* rule = noll_vector_at(rec_rules, k);

                        // extract constant -> set
                        set<Vertex> constant_set;
                        extract_constant_from_rule_pure(rule, constant_set);

                        // compute delta, gamma_epsilon
                        vector<Vertex> delta;
                        vector<Vertex> gamma_epsilon;

                        extractRecCallDataPara(rule, fargs, delta, gamma_epsilon, constant_set);

                        OrderGraph og_cons; // constant order graph
                        create_constant_order_graph(constant_set, og_cons);

                        // print_vertex(delta, "delta:");
                        // print_vertex(gamma_epsilon, "epsilon:");

                        // T_R(G)
                        for (int i=0; i<ogset.size(); i++) {
                                for (int j=0; j<ogset.size(); j++) {
                                        OrderGraph og1 = ogset.at(i);
                                        OrderGraph og2 = ogset.at(j);

                                        // g_delta constructed by recursive rule (data constraint)
                                        OrderGraph g_delta = og_cons;
                                        pure2graph(rule, g_delta);
                                        // substitution1
                                        og1.substitution(alpha, delta);

                                        vector<Vertex> old_vs2 = alpha;
                                        old_vs2.insert(old_vs2.end(), beta.begin(), beta.end());
                                        vector<Vertex> new_vs2 = gamma_epsilon;

                                        // substitution2
                                        og2.substitution(old_vs2, new_vs2);

                                        //union
                                        g_delta.unionGraph(og1);
                                        g_delta.unionGraph(og2);

                                        //saturate
                                        g_delta.saturate();

                                        if (g_delta.isConsistent()) {
                                                // restriction
                                                set<Vertex> v_set;
                                                old_vs2.insert(old_vs2.end(), constant_set.begin(), constant_set.end()); // add constant_set
                                                vec2set(old_vs2, v_set);

                                                ogset.addOrderGraph(g_delta);
                                        }
                                }
                        }
                }
        }

        return ogset;
}


/**
 * create expr by name
 * @param str : name or constant
 * @param ctx : z3 context
 * @return expr
 */
z3::expr create_expr_by_name(string str, z3::context& ctx) {
        locale loc;
        if (isdigit(str[0] , loc)) {
                return ctx.int_val(atoi(str.c_str()));
        } else {
                return ctx.real_const(str.c_str());
        }
}



/**
 * create expr by vid for args
 * @param lvars : var environment
 * @param vid : the varid or constant
 * @param ctx : z3 context
 * @return expr
 */
z3::expr create_expr_args(noll_var_array* lvars, uid_t vid, z3::context& ctx) {
        if (vid >= noll_vector_size(lvars)) {
                return ctx.real_val(vid - noll_vector_size(lvars));
        } else {
                return ctx.real_const(noll_vector_at(lvars, vid)->vname);
        }
}


/**
 * order graph to z3 expr
 * @param og : order graph
 * @param ctx : z3 context
 * @return expr : expr
 */
z3::expr graph2expr(OrderGraph& og, z3::context& ctx) {
        set<Edge> edges = og.getEdges();
        z3::expr res = ctx.bool_val(true);
        for (auto edge : edges) {
                z3::expr expr1 = create_expr_by_name(edge.getSource().getName(), ctx);
                z3::expr expr2 = create_expr_by_name(edge.getDest().getName(), ctx);
                if (edge.getLabel() == LABEL_LE) {
                        res = res && (expr1 <= expr2);
                } else {
                        res = res && (expr1 < expr2);
                }
        }
        return res;
}




/**
 * var to z3 expr
 * @param var : var
 * @param ctx : z3context
 * @return expr : expr
 */
z3::expr var2expr(noll_var_t* var, csltp_context& ctx) {
        if (var->vid == 0) {
                // nil
                return ctx.ctx.int_val(0);
        }
        if (var->vty->kind == NOLL_TYP_INT) {
                return ctx.ctx.int_const(var->vname);
        }
        if (var->vty->kind == NOLL_TYP_RAT) {
                return ctx.ctx.real_const(var->vname);
        }
        if (var->vty->kind == NOLL_TYP_RECORD) {
                return ctx.ctx.int_const(var->vname) ;
        }
        return ctx.ctx.bool_val(true);
}
/**
 * introduce a new boolean var
 * @param var : var
 * @param ctx : context
 * @return res : bool var of z3
 */
z3::expr introduce_bool_var(noll_var_t* var, csltp_context& ctx) {
        string s = var->vname;
        stringstream sstream;
        sstream<<"["<<s<<","<<ctx.index_processing<<"]"; // may repeat!
        z3::expr res = ctx.ctx.bool_const(sstream.str().c_str());
        ctx.new_bool_vars.push_back(res);
        return res;
}




/**
 * data term to expr
 * @param lvars : var array
 * @param dt : data term
 * @param ctx : z3 context
 * @return expr: expr
 */
z3::expr dterm2expr(noll_dterm_t* dt, csltp_context& ctx) {
        if (dt->kind == NOLL_DATA_VAR) {
                return var2expr(noll_vector_at(ctx.lvars, dt->p.sid), ctx);
        } else if (dt->kind == NOLL_DATA_RAT) {
                return ctx.ctx.real_val((int)dt->p.value);
        } else if (dt->kind == NOLL_DATA_INT) {
                return ctx.ctx.int_val((int)dt->p.value);
        } else if (dt->kind == NOLL_DATA_PLUS) {
                return dterm2expr(noll_vector_at(dt->args, 0), ctx) + dterm2expr(noll_vector_at(dt->args, 1), ctx);
        }
        return ctx.ctx.bool_val(true);
}

/**
 * dform to expr
 * @param df : data formula
 * @param ctx : csltp_context
 * @return expr
 */
z3::expr dform2expr(noll_dform_t* df, csltp_context& ctx) {
        z3::expr res(ctx.ctx);
        noll_dterm_t* term1 = noll_vector_at(df->p.targs, 0);
        noll_dterm_t* term2 = noll_vector_at(df->p.targs, 1);
        z3::expr expr1 = dterm2expr(term1, ctx);
        z3::expr expr2 = dterm2expr(term2, ctx);

        if (df->kind == NOLL_DATA_EQ) {
                res = (expr1 == expr2);
        } else if (df->kind == NOLL_DATA_LT) {
                res = (expr1 < expr2);
        } else if (df->kind == NOLL_DATA_GT) {
                res = (expr1 > expr2);
        } else if (df->kind == NOLL_DATA_LE) {
                res =  (expr1 <= expr2);
        } else if (df->kind == NOLL_DATA_GE) {
                res =  (expr1 >= expr2);
        }
        return res;
}



/**
 * @param rule : predicate rule definition
 * @param og: output order graph related data graph (Rat)
 */
void pure2graph(noll_pred_rule_t* rule, OrderGraph& og) {
        noll_var_array * vars = rule->vars;
        // add vertex
        uid_t length_vars = noll_vector_size (vars);
        for (uid_t i = 0; i < length_vars; i++)
        {
                noll_var_t *vi = noll_vector_at (vars, i);
                noll_type_t *ti = vi->vty;
                if (ti->kind == NOLL_TYP_RAT) {
                        // add vertex
                        string name(vi->vname);
                        Vertex vertex(name);
                        og.addVertex(vertex);
                }
        }

        //add edge
        noll_pure_t* phi = rule->pure;

        for (uid_t l = 0; l < phi->size; l++)
        {
                for (uid_t c = l+1; c < phi->size; c++)
                {
                        noll_var_t* var1 = noll_vector_at (vars, l);
                        noll_var_t* var2 = noll_vector_at(vars, c);

                        if (var1->vty->kind == NOLL_TYP_RAT
                            && var2->vty->kind == NOLL_TYP_RAT
                            && noll_pure_matrix_at (phi, l, c) == NOLL_PURE_EQ) {
                                Vertex v1(var1->vname);
                                Vertex v2(var2->vname);
                                Edge e1(v1, LABEL_LE, v2);
                                Edge e2(v2, LABEL_LE, v1);
                                og.addEdge(e1);
                                og.addEdge(e2);
                        }
                }
        }

        // data formula

        noll_dform_array* dfs = phi->data;

        if (dfs == NULL) return;

        for (uint_t i = 0; i < noll_vector_size (dfs); i++)
        {
                noll_dform_t* df = noll_vector_at(dfs, i);

                noll_var_t* v1 = NULL;
                noll_var_t* v2 = NULL;

                if (df->p.targs != NULL && noll_vector_size (df->p.targs) == 2) {
                        noll_dterm_t* term1 = noll_vector_at (df->p.targs, 0);
                        noll_dterm_t* term2 = noll_vector_at (df->p.targs, 1);

                        if (term1->kind == NOLL_DATA_VAR) {
                                v1 =  noll_vector_at (vars, term1->p.sid);
                                if (v1->vty->kind == NOLL_TYP_RAT) {
                                        if (term2->kind == NOLL_DATA_VAR) {
                                                v2 =  noll_vector_at (vars, term2->p.sid);
                                        } else if (term2->kind == NOLL_DATA_INT) {
                                                string con_str = to_string(term2->p.value);
                                                v2 = noll_var_new(con_str.c_str(), noll_mk_type_int(), NOLL_SCOPE_LOCAL);
                                                Vertex v_con(con_str);
                                                // og.addVertex(v_con);
                                        }
                                }
                        }
                }

                if (v1 != NULL && v2 != NULL) {
                        Vertex vertex1(v1->vname);
                        Vertex vertex2(v2->vname);

                        if (df->kind == NOLL_DATA_EQ) {
                                Edge eq_e1(vertex1, LABEL_LE, vertex2);
                                Edge eq_e2(vertex2, LABEL_LE, vertex1);
                                og.addEdge(eq_e1);
                                og.addEdge(eq_e2);
                        } else if (df->kind == NOLL_DATA_LT) {
                                Edge lt_e(vertex1, LABEL_LT, vertex2);
                                // cout<<lt_e.getSource().getName()<<"->"<<lt_e.getDest().getName()<<endl;
                                og.addEdge(lt_e);
                        } else if (df->kind == NOLL_DATA_GT) {
                                Edge gt_e(vertex2, LABEL_LT, vertex1);
                                og.addEdge(gt_e);
                        } else if (df->kind == NOLL_DATA_LE) {
                                Edge le_e(vertex1, LABEL_LE, vertex2);
                                og.addEdge(le_e);
                        } else if (df->kind == NOLL_DATA_GE) {
                                Edge ge_e(vertex2, LABEL_LE, vertex1);
                                og.addEdge(ge_e);
                        }
                }
        }
}

/**
 * extract alpha and beta from predicate definition
 * @param pred : predicate definition
 * @param alpha : output alpha
 * @param beta : output beta
 */
void extractAlphaBeta(noll_pred_t* pred, vector<Vertex>& alpha, vector<Vertex>& beta) {
        uid_t fargs = pred->def->fargs;
        noll_var_array* vars = pred->def->vars;
        noll_var_t *vi = NULL;
        for (uid_t i=2; i<= fargs/2; i++) {
                vi = noll_vector_at (vars, i);
                if (vi->vty->kind == NOLL_TYP_RAT) {
                        Vertex v(vi->vname);
                        alpha.push_back(v);
                }
        }
        for (uid_t i=fargs/2+2; i<=fargs; i++) {
                vi = noll_vector_at (vars, i);
                if (vi->vty->kind == NOLL_TYP_RAT) {
                        Vertex v(vi->vname);
                        beta.push_back(v);
                }
        }
}

/**
 * extract delta, gamma, epsilon
 * @param rule: recursive rule
 * @param fargs: the predicate argument number
 * @param delta_gamma, epsilon : output
 */
void extractRecCallDataPara(noll_pred_rule_t* rule, uid_t fargs, vector<Vertex>& delta, vector<Vertex>& gamma_epsilon, set<Vertex>& constant_set) {
        noll_var_array* lvars = rule->vars;

        noll_space_array* sep = rule->rec->m.sep;
        noll_space_t* phi = noll_vector_at(sep, 0);

        noll_space_t* phi_delta = NULL;

        if (noll_vector_at (phi->m.ls.args, fargs/2) == 0) { // nil
                phi_delta =  noll_vector_at(sep, 1);
        } else {
                phi_delta = phi;
                phi = noll_vector_at(sep, 1);
        }


        // delta gamma
        for (uid_t i = 1; i < fargs/2; i++)
        {
                uint_t vid = noll_vector_at (phi_delta->m.ls.args, i);

                if (vid >= noll_vector_size(lvars)) {
                        Vertex v_con_delta(to_string((vid-noll_vector_size(lvars))));
                        delta.push_back(v_con_delta);
                        constant_set.insert(v_con_delta);
                } else {
                        noll_var_t *vi = noll_vector_at (lvars, vid);
                        Vertex v_delta(vi->vname);
                        delta.push_back(v_delta);
                }

                vid = noll_vector_at (phi->m.ls.args, i);
                if (vid >= noll_vector_size(lvars)) {
                        Vertex v_con_gamma(to_string((vid-noll_vector_size(lvars))));
                        gamma_epsilon.push_back(v_con_gamma);
                        constant_set.insert(v_con_gamma);
                } else {
                        noll_var_t *vi = noll_vector_at (lvars, vid);
                        Vertex v_gamma(vi->vname);
                        gamma_epsilon.push_back(v_gamma);
                }
        }

        // epsilon
        for (uid_t i = fargs/2+1; i < fargs; i++)
        {
                uint_t vid = noll_vector_at (phi->m.ls.args, i);
                if (vid >= noll_vector_size(lvars)) {
                        Vertex v_con_epsilon(to_string((vid-noll_vector_size(lvars))));
                        gamma_epsilon.push_back(v_con_epsilon);
                        constant_set.insert(v_con_epsilon);
                } else {
                        noll_var_t *vi = noll_vector_at (lvars, vid);
                        Vertex v_epsilon(vi->vname);
                        gamma_epsilon.push_back(v_epsilon);
                }
        }
}





/**
 * vector (no same elements) to set
 * @param vec : vector
 * @param v_set : output
 */
void vec2set(vector<Vertex>& vec, set<Vertex>& v_set) {
        for (uid_t i=0; i<vec.size(); i++) {
                v_set.insert(vec[i]);
        }
}

/**
 * extract constant from the inductive rule
 * @param rule : the inductive rule
 * @param constant_set : constant vertex set
 */
void extract_constant_from_rule_pure(noll_pred_rule_t* rule, set<Vertex>& constant_set) {
        // from pure data formula
        noll_dform_array* dfs = rule->pure->data;
        noll_var_array* vars = rule->vars;

        if (dfs == NULL) return;

        for (uint_t i = 0; i < noll_vector_size (dfs); i++)
        {
                noll_dform_t* df = noll_vector_at(dfs, i);

                noll_var_t* v1 = NULL;
                noll_var_t* v2 = NULL;

                if (df->p.targs != NULL && noll_vector_size (df->p.targs) == 2) {
                        noll_dterm_t* term1 = noll_vector_at (df->p.targs, 0);
                        noll_dterm_t* term2 = noll_vector_at (df->p.targs, 1);

                        if (term1->kind == NOLL_DATA_VAR) {
                                v1 =  noll_vector_at (vars, term1->p.sid);
                                if (v1->vty->kind == NOLL_TYP_RAT) {
                                        if (term2->kind == NOLL_DATA_VAR) {
                                                v2 =  noll_vector_at (vars, term2->p.sid);
                                        } else if (term2->kind == NOLL_DATA_INT) {
                                                Vertex v_con(to_string(term2->p.value));
                                                constant_set.insert(v_con);
                                        }
                                }
                        }
                }
        }
}

/**
 * create constant graph
 * @param constant_set : the set of constant
 * @param og_cons : the output graph
 */
void create_constant_order_graph(set<Vertex>& constant_set, OrderGraph& og_cons) {
        for (auto cons : constant_set) {
                og_cons.addVertex(cons);
        }
        for (auto cons1 : constant_set) {
                for (auto cons2: constant_set) {
                        int cons_v1 = atoi(cons1.getName().c_str());
                        int cons_v2 = atoi(cons2.getName().c_str());
                        if (cons_v1 < cons_v2) {
                                Edge e_con_lt(cons1, LABEL_LT, cons2);
                                og_cons.addEdge(e_con_lt);
                        } else if (cons_v1 > cons_v2){
                                Edge e_con_lt(cons2, LABEL_LT, cons1);
                                og_cons.addEdge(e_con_lt);
                        }
                }
        }
}


/*******************************
 ***  print functions        ***
 ******************************/

void print_vertex(vector<Vertex> vec, string msg) {
        cout<<msg<<endl;
        for (uid_t i=0; i<vec.size(); i++) {
                cout<<vec[i]<<endl;
        }
        cout<<endl;
}

/**
 * print the order graph lfp for $prefix_G_$i.dot
 * @param ogset : order graph set
 * @param prefix : the file prefix
 */
void print_order_graph_set(OrderGraphSet& ogset, string prefix) {
        for (int i=0; i<ogset.size(); i++) {
                stringstream ss;
                ss << prefix << "_G_"<<i<<".dot";
                ogset.at(i).printAsDot(ss.str());
        }
}
