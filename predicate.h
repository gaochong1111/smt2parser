#ifndef PREDICATE_H
#define PREDICATE_H

#include <z3++.h>
#include <iostream>
#include <string>
/**
 * pred_rule
 * data, pto, rec_app
 *
 */
class pred_rule {
private:
        z3::expr m_data;
        z3::expr m_pto;
        z3::expr_vector m_rec_apps;
public:
pred_rule(z3::expr data, z3::expr pto, z3::expr_vector rec_apps)
        :m_data(data), m_pto(pto), m_rec_apps(rec_apps) {
        }

        z3::expr get_data() {return m_data;}
        z3::expr get_pto() {return m_pto;}
        z3::expr_vector get_rec_apps() {return m_rec_apps;}

        bool is_tree_rule() {
                return m_rec_apps.size() == 2;
        }

        friend std::ostream& operator<<(std::ostream& out, pred_rule& pr) {
                out << "data: " << pr.m_data << std::endl;
                out << "pto: " << pr.m_pto << std::endl;
                out << "m_rec_apps: " << pr.m_rec_apps << std::endl;
                return out;
        }
};

/**
 * tree pred binding info
 */
class tree_binding {
public:
        z3::expr_vector m_constants;
        z3::expr_vector m_alpha;
        z3::expr_vector m_beta;
        z3::expr_vector m_gamma;
        z3::expr_vector m_delta;
        z3::expr_vector m_epsilon;
tree_binding(z3::expr_vector constants, z3::expr_vector alpha,  z3::expr_vector beta,  z3::expr_vector gamma, z3::expr_vector delta, z3::expr_vector epsilon):m_constants(constants),
                m_alpha(alpha),
                m_beta(beta),
                m_gamma(gamma),
                m_delta(delta),
                m_epsilon(epsilon){}
};


/**
 * the recursive definition
 * binding arguments (var env)
 * base_rule, rec_rules
 *
 */
class predicate {
private:
        z3::func_decl m_fun;
        z3::expr_vector m_pars;
        z3::expr m_base_rule;
        std::vector<pred_rule> m_rec_rules; // exists
public:
        z3::expr_vector& get_pars() {return m_pars;}
predicate(z3::func_decl fun, z3::expr_vector pars, z3::expr base_rule)
        :m_fun(fun), m_pars(pars), m_base_rule(base_rule) {
        }

        void add_base_rule(z3::expr base_rule) {
                m_base_rule = base_rule;
        }

        void add_rec_rule(pred_rule pr) {
                m_rec_rules.push_back(pr);
        }

        int rec_rule_size() {return m_rec_rules.size();}

        pred_rule get_rule(int i) {
                assert(i < m_rec_rules.size());
                return m_rec_rules[i];
        }

        z3::func_decl get_fun() {
                return m_fun;
        }

        std::string get_pred_name() {
                return m_fun.name().str();
        }

        bool is_tree() {
                for (int i=0; i<m_rec_rules.size(); i++) {
                        if (!m_rec_rules[i].is_tree_rule()) return false;
                }
                return true;
        }

        friend std::ostream& operator<<(std::ostream& out, predicate& p) {
                out << "pars: \n" << p.m_pars << std::endl;
                out << "base rule: \n" << p.m_base_rule << std::endl;
                out << "m_rec_rules: \n";
                for (int i=0; i<p.m_rec_rules.size(); i++) {
                        out << "index: " << i << " :\n" << p.m_rec_rules[i] << std::endl;
                }
                return out;
        }
};






#endif /* PREDICATE_H */
