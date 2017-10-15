#ifndef SOLVER_H
#define SOLVER_H

#include <vector>
#include <set>
#include "smt2context.h"
#include "smt2exception.h"


class exprcomp {
public:
        bool operator() (const z3::expr& lhs, const z3::expr& rhs) const {
                return lhs.hash() < rhs.hash();
        }
};

class treechecker {
private:
        predicate m_pred;
        bool is_repeat(z3::expr_vector vec);
        bool is_repeat(std::vector<z3::expr> vec);
        bool is_data_var(z3::expr x);
        bool is_size_var(z3::expr x);
        bool is_numeral(z3::expr x);
        std::set<z3::expr, exprcomp> union_set(std::set<z3::expr, exprcomp> s1, std::set<z3::expr, exprcomp> s2);



public:
treechecker(predicate pred):m_pred(pred){}
        void check_args();
        void check_rec_rule(pred_rule& rule);
        void check_rec_rules();
};

/**
 * Solver
 */
class treesolver {
private:
        smt2context& m_ctx;
        z3::expr_vector delta_ge1_predicates; // phi^{>=1}_P(\alpha; \beta), corresponding to preds_array

private:
        void get_constants(z3::expr const& exp, std::set<z3::expr, exprcomp>& vec);
        void get_constants(predicate& pred, std::set<z3::expr, exprcomp>& vec);
public:
treesolver(smt2context& ctx):m_ctx(ctx), delta_ge1_predicates(ctx.z3_context()) {
        }

        smt2context& get_ctx() {return m_ctx;}
        z3::context& z3_ctx() {return m_ctx.z3_context();}

        bool check_preds();


        void compute_all_delta_ge1_p();

        z3::expr compute_delta_phi_pd(predicate& pred);
        z3::expr compute_delta_ge1_rule(pred_rule& rule, predicate& pred, z3::expr& delta_ge1_p_abs);

        bool check_sat();


};


#endif /* SOLVER_H */
