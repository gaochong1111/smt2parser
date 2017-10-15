#include "solver.h"

/**
 *###################### treechecker ####################################3
 */

bool treechecker::is_repeat(z3::expr_vector vec) {
        std::set<z3::expr, exprcomp> args_set;
        for (int i=0; i<vec.size(); i++) {
                args_set.insert(vec[i]);
        }
        if (args_set.size() != vec.size()) {
                return true;
        }
        return false;
}

bool treechecker::is_repeat(std::vector<z3::expr> vec) {
        std::set<z3::expr, exprcomp> args_set;
        for (int i=0; i<vec.size(); i++) {
                args_set.insert(vec[i]);
        }
        if (args_set.size() != vec.size()) {
                return true;
        }
        return false;
}

bool treechecker::is_data_var(z3::expr x) {
        if(x.get_sort().to_string() == "Real" && x.to_string().find("(:var")==0) return true;
        return false;
}

bool treechecker::is_size_var(z3::expr x) {
        if(x.get_sort().to_string() == "Int" && x.to_string().find("(:var")==0) return true;
        return false;
}

bool treechecker::is_numeral(z3::expr x) {
        if (x.is_numeral()) return true;
        if (x.is_app()
            && (x.decl().name().str() == "to_real" || x.decl().name().str() == "to_int")
            && is_numeral(x.arg(0))) return true;
        return false;
}



std::set<z3::expr, exprcomp> treechecker::union_set(std::set<z3::expr, exprcomp> s1, std::set<z3::expr, exprcomp> s2) {
        for (auto item : s2) {
                s1.insert(item);
        }
        return s1;
}

/**
 * check args
 */
void treechecker::check_args() {
        z3::expr_vector args = m_pred.get_pars();
        // 1. number
        int num_of_args = args.size();
        if ((num_of_args&1) != 0) {
                throw smt2exception("the number of parameters of tree predicate must be even number. \n");
        }

        assert(num_of_args > 0);
        // 2. first parameter
        z3::expr first_arg = args[0];
        if (first_arg.get_sort().sort_kind() != Z3_UNINTERPRETED_SORT) {
                throw smt2exception("the first parameter of tree predicate must be record type. \n");
        }

        // 3. source and dest paramters type match
        for (int i=0; i<num_of_args/2; i++) {
                if (args[i].get_sort().sort_kind() != args[i+num_of_args/2].get_sort().sort_kind()) {
                        throw smt2exception("the source parameters and destination parameters of tree predicate must be matched in types. \n");
                }
        }

        // 4. data parameters include Rat and Int
        int size_count = 0;
        for (int i=1; i<num_of_args/2; i++) {
                std::string sort_name = args[i].get_sort().to_string();
                if (sort_name != "Real" && sort_name != "Int") {
                        throw smt2exception("the only data and size parameters in the alpha source parameters. \n");
                }

                if (sort_name == "Real" && size_count>0) {
                        throw smt2exception("the data parameters must be before size parameters in the source parameters. \n");
                }

                if (sort_name == "Int") {
                        size_count++;
                        if (size_count > 1) {
                                throw smt2exception("the number of size parameters in the alpha source parameters must be less than 2. \n");
                        }
                }
        }

        // 5. no repeat
        if (is_repeat(args)) {
                throw smt2exception("the parameters of tree predicate must be different from each other. \n");
        }
}

/**
 * check recursive rules
 */
void treechecker::check_rec_rules() {
        for (int i=0; i<m_pred.rec_rule_size(); i++) {
                pred_rule rule = m_pred.get_rule(i);
                check_rec_rule(rule);
        }
}

/**
 * check recursive rule
 */
void treechecker::check_rec_rule(pred_rule &rule) {
        z3::expr data = rule.get_data();
        z3::expr pto = rule.get_pto();
        z3::expr_vector rec_apps = rule.get_rec_apps();
        // 1. data
        bool size_flag = false;
        for (unsigned int i=0; i<data.num_args(); i++) {
                z3::expr data_item = data.arg(i);
                if (data_item.num_args() == 2) {
                        // 1.1 first must be variable
                        if ((data_item.arg(0).is_app() && !data_item.arg(0).is_const()) || data_item.arg(0).is_numeral()) {
                                throw smt2exception("the data constraints in each inductive rule must start with one variable, like x < x1. \n");
                        }
                        // 1.2 data type
                        if (data_item.arg(0).get_sort().to_string() == "Real") {
                                // data constraint
                                if (size_flag) {
                                        throw smt2exception("the data type constraints must be before the size type constraints in data constraints in the inductive rule. \n");
                                }
                                if (!data_item.arg(1).is_numeral() && data_item.arg(1).is_app() && !data_item.arg(1).is_const()) {
                                        if (data_item.arg(1).decl().name().str() != "to_real"
                                            && data_item.arg(1).decl().name().str() != "to_int") {
                                                throw smt2exception("the data type must include like x op d or x op x1 in data constraints in the inductive rule. \n");
                                        }
                                }
                        } else {
                                // 1.3 size type constraint
                                size_flag = true;
                                if (data_item.arg(1).is_app() && !data_item.arg(1).is_const()) {
                                        z3::expr plus = data_item.arg(1);
                                        if (plus.num_args() == 2
                                            || plus.decl().name().str() != "+"
                                            || !plus.arg(1).is_numeral()) {
                                                throw smt2exception("the size type must include like h op n or h op h+n in data constraints in the inductive rule. \n");
                                        }
                                } else if (!data_item.arg(1).is_numeral()){
                                        throw smt2exception("the size type must include like h op n or h op h+n in data constraints in the inductive rule. \n");
                                }
                        }
                }
        }

        // 2. pto
        // 2.1 source
        if (!(pto.arg(0).hash() == m_pred.get_pars()[0].hash())) {
                throw smt2exception("the source of pto must be the first predicate parameter of tree predicate  in the inductive rule. \n");
        }
        // 2.2 left , right
        if ((pto.arg(1).num_args()<2)) {
                throw smt2exception("the fields of pto atom must include (left, right) in the tree predicate. \n");
        } else {
                std::string left = pto.arg(1).arg(0).arg(0).to_string();
                std::string right = pto.arg(1).arg(1).arg(0).to_string();
                if (left != "left") {
                        throw smt2exception("the first field of pto atom must be left in the tree predicate. \n");
                }
                if (right != "right") {
                        throw smt2exception("the second field of pto atom must be left in the tree predicate. \n");
                }
        }

        // 3. rec app

        // 3.1 nil
        z3::expr first_app = rule.get_rec_apps()[0];
        z3::expr second_app = rule.get_rec_apps()[1];
        z3::expr_vector args = m_pred.get_pars();
        int num_of_args = args.size();

        bool is_nil1 = first_app.arg(num_of_args/2).to_string() == "nil";
        bool is_nil2 = second_app.arg(num_of_args/2).to_string() == "nil";
        if (!(is_nil1 ^ is_nil2)) {
                throw smt2exception("the only one of recursive call must include one nil parameter in the inductive rule. \n");
        }

        // 3.2 gamma, delta, epsilon
        std::set<z3::expr, exprcomp> alpha;
        std::set<z3::expr, exprcomp> beta;
        std::set<z3::expr, exprcomp> gamma;
        std::set<z3::expr, exprcomp> delta;
        std::set<z3::expr, exprcomp> epsilon;
        // 3.2.1 alpha, beta
        for (int i=1; i<num_of_args/2; i++) {
                alpha.insert(args[i]);
                beta.insert(args[i+num_of_args/2]);
        }
        // 3.2.2 gamma, delta, epsilon
        if (is_nil1) {
                for(int i=1; i<num_of_args/2; i++) {
                        gamma.insert(first_app.arg(i));
                        delta.insert(second_app.arg(i));
                        epsilon.insert(first_app.arg(i+num_of_args/2));
                }
        } else {
                for(int i=1; i<num_of_args/2; i++) {
                        gamma.insert(second_app.arg(i));
                        delta.insert(first_app.arg(i));
                        epsilon.insert(second_app.arg(i+num_of_args/2));
                }
        }

        std::set<z3::expr, exprcomp> gamma_delta = union_set(gamma, delta);

        // 3.2.3 gamma, delta subset alpha + x + h + constant
        for (auto exp : gamma_delta) {
                if (!is_numeral(exp) && !is_data_var(exp) && !is_size_var(exp) && alpha.find(exp) == alpha.end()) {
                        throw smt2exception("the parameters of Gamma and Delta must be subset of the parameters of Alpha and x and h and constant in the inductive rule. \n");
                }
        }

        // 3.2.4 gamma
        if (gamma.size() != num_of_args/2-1) {
                throw smt2exception("the parameters of Gamma must be different from eacher. \n");
        }
        // 3.2.5 delta
        if (delta.size() != num_of_args/2-1) {
                throw smt2exception("the parameters of Delta must be different from eacher. \n");
        }
        // 3.2.6 epsilon
        for (auto exp : epsilon) {
                if (!is_numeral(exp) && alpha.find(exp) == alpha.end()) {
                        throw smt2exception("the parameters of Epsilon must be subset of the parameters of Alpha and constants in the inductive rule. \n");
                }
        }

        //3.3 size type constraint
        int size_i = num_of_args/2 - 1;
        if (args[size_i].get_sort().to_string() == "Int") {
                // 3.3.1 delta_i, gamma_i \in h, epsilon_i \in N
                std::string info = "when size type occur in Alph(i), the Delta(i) and Gamma(i) must be in h and Epsilon(i) is constant and the Alpha(i) = Delta(i) + n or Alpha(i) = Gamma(i) + n must ouccur in data constraint in the inductive rule. \n";
                if (first_app.arg(size_i).get_sort().to_string() != "Int"
                    || second_app.arg(size_i).get_sort().to_string() != "Int") {
                        throw smt2exception(info);
                }
                if (is_nil1 && !first_app.arg(size_i+num_of_args/2).is_numeral()) {
                        throw smt2exception(info);
                }
                if (is_nil2 && !second_app.arg(size_i+num_of_args/2).is_numeral()) {
                        throw smt2exception(info);
                }
                // 3.3.2 alpha_i = delta_i + n or alpha_i = gamma_i + n in data
                z3::expr data = rule.get_data();
                bool find = false;
                for (int i=0; i<data.num_args(); i++) {
                        if (data.arg(i).arg(0).hash() == args[size_i].hash()
                            && data.arg(i).arg(1).is_app()
                            && data.arg(i).arg(1).decl().name().str() == "+"
                            && is_numeral(data.arg(i).arg(1).arg(1))) {
                                if (data.arg(i).arg(1).arg(0).hash() == first_app.arg(size_i).hash()
                                    ||data.arg(i).arg(1).arg(0).hash() == second_app.arg(size_i).hash()) {
                                        find = true;
                                }
                        }
                }
                if (!find) {
                        throw smt2exception(info);
                }
        }
}

/**
 *###################### solver ####################################3
 */


bool treesolver::check_sat() {
        // 1. check_preds
        // m_ctx.logger() << "check preds" << std::endl;
        check_preds();
        // 2. check_sat
        m_ctx.logger() << "check sat" << std::endl;
        std::set<z3::expr, exprcomp> vec;
        predicate pred = m_ctx.get_pred(0);
        get_constants(pred, vec);
        std::cout << "constant size: " << vec.size() << std::endl;
        for (auto con : vec) {
                std::cout << con << std::endl;
        }

        return true;
}

/**
 * check whether all predicate definitions are corresponding to userdef constraints
 */
bool treesolver::check_preds() {
        for (int i=0; i<m_ctx.pred_size(); i++) {
                predicate pred = m_ctx.get_pred(i);
                if (pred.is_tree()) {
                        treechecker tc(pred);
                        tc.check_args();
                        tc.check_rec_rules();
                }
        }

        return true;
}

/**
 * compute all predicate delta_ge1_p (delta_ge1_predicates)
 */
void treesolver::compute_all_delta_ge1_p() {
        for (int i=0; i<m_ctx.pred_size(); i++) {
                predicate pred = m_ctx.get_pred(i);
                // 1. compute phi_pd_abs
                z3::expr phi_pd_abs = compute_delta_phi_pd(pred);
                // 2. compute delta_ge1_p
                z3::expr delta_ge1_p_abs = z3_ctx().bool_val(false);

                // 2.1 for all rec rules
                for (int i=0; i<pred.rec_rule_size(); i++) {
                        pred_rule rule = pred.get_rule(i);
                        z3::expr delta_ge1_r_abs = compute_delta_ge1_rule(rule, pred, phi_pd_abs);
                        delta_ge1_p_abs = delta_ge1_p_abs || delta_ge1_r_abs;
                }
                delta_ge1_predicates.push_back(delta_ge1_p_abs);
        }
}

/**
 * compute delta_ge1_r
 * @param rule : the rule R
 * @param pred : the predicate
 * @param delta_ge1_p_abs : the formula used
 * @return expr
 */
z3::expr treesolver::compute_delta_ge1_rule(pred_rule &rule, predicate &pred, z3::expr &delta_ge1_p_abs) {
        // compute exists expr_vector formula
        // 1. expr_vector by rule
        z3::expr_vector x_h(z3_ctx());
        // 2. formula
        z3::expr formula = rule.get_data();
        // 2.1 alpha, beta by pred
        // 2.2 gamma, delta, epsilon by rule
        // 2.3 substitute alpha by delta

        // 2.4 substitute alpha, beta by gamma,epsilon



        return exists(x_h, formula);
}


/**
 * compute the delta_phi_pd
 * @param pred : predicate
 * @return expr
 */
z3::expr treesolver::compute_delta_phi_pd(predicate &pred) {
        z3::expr_vector args = pred.get_pars();
        int num_of_args = args.size();
        if (num_of_args == 2) {
                // P(E,F)
                return z3_ctx().bool_val(true);
        } else if (args[num_of_args/2-1].get_sort().to_string() == "Int") {
                if (num_of_args > 4) {
                        // TODO data and size type
                        return z3_ctx().bool_val(true);

                } else {
                        // TODO only size type
                        return z3_ctx().bool_val(true);
                }
        } else {
                // only data type
                z3::expr phi_pd_abs = z3_ctx().bool_val(false);
                // 1. compute least fixed point (Order Graph)

                // 2. Graph to expr

                return phi_pd_abs;
        }

}

/**
 * get constants from expr
 * @param exp : the expression
 * @param constants : the set of constant expr
 */
void treesolver::get_constants(const z3::expr &exp, std::set<z3::expr, exprcomp> &constants) {
        if (exp.is_app()) {
                if (exp.is_numeral()) {
                        constants.insert(exp);
                } if((exp.decl().name().str() == "to_real" || exp.decl().name().str() == "to_int")){
                        constants.insert(exp.arg(0));
                }else {
                        for (unsigned i=0; i<exp.num_args(); i++) {
                                get_constants(exp.arg(i), constants);
                        }
                }
        } else if(exp.is_quantifier()) {
                get_constants(exp.body(), constants);
        }
}

/**
 * get constants from pred
 * @param pred : the predicate
 * @param constants : the set of constant expr
 */
void treesolver::get_constants(predicate& pred, std::set<z3::expr, exprcomp> &constants) {
        int size = pred.rec_rule_size();
        for (int i=0; i<size; i++) {
                z3::expr data = pred.get_rule(i).get_data();

                get_constants(data, constants);
                z3::expr_vector rec_apps = pred.get_rule(i).get_rec_apps();
                for (int i=0; i<rec_apps.size(); i++) {
                        z3::expr app = rec_apps[i];
                        get_constants(app, constants);
                }
        }
}
