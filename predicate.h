#ifndef PREDICATE_H
#define PREDICATE_H

#include <z3++.h>
#include <iostream>
#include <string>
#include <set>
#include <vector>

/**
 * the expr comparator
 */
class exprcomp {
public:
        bool operator() (const z3::expr& lhs, const z3::expr& rhs) const {
                return lhs.hash() < rhs.hash();
        }
};

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
        void get_x_h(z3::expr exp, std::set<z3::expr, exprcomp>& x_h) {
                if (exp.is_app()) {
                        for (int i=0; i<exp.num_args(); i++) {
                                get_x_h(exp.arg(i), x_h);
                        }
                } else {
                        if (exp.is_var()) {
                                x_h.insert(exp);
                        }
                }
        }

public:
pred_rule(z3::expr data, z3::expr pto, z3::expr_vector rec_apps)
        :m_data(data), m_pto(pto), m_rec_apps(rec_apps) {
        }

        z3::expr get_data() {return m_data;}
        z3::expr get_pto() {return m_pto;}
        z3::expr_vector get_rec_apps() {return m_rec_apps;}
        /**
         * get exists args (x, h)
         * @param x_h_vec : the result vector
         */
        void get_x_h(z3::expr_vector& x_h_vec) {
                std::set<z3::expr, exprcomp> x_h;
                get_x_h(m_data, x_h);
                get_x_h(m_pto, x_h);
                for (int i=0; i<m_rec_apps.size(); i++) {
                        get_x_h(m_rec_apps[i], x_h);
                }
                for (auto exp : x_h) {
                        x_h_vec.push_back(exp);
                }
        }



        bool is_tree_rule() {
                return m_rec_apps.size() == 2;
        }

        bool is_list_rule() {
                return m_rec_apps.size() == 1;
        }

        friend std::ostream& operator<<(std::ostream& out, pred_rule& pr) {
                out << "data: " << pr.m_data << std::endl;
                out << "pto: " << pr.m_pto << std::endl;
                out << "m_rec_apps: " << pr.m_rec_apps << std::endl;
                return out;
        }
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

        z3::expr get_base_rule(){return m_base_rule;}

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

        bool is_list() {
                for (int i=0; i<m_rec_rules.size(); i++) {
                        if (!m_rec_rules[i].is_list_rule()) return false;
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
