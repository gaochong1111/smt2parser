#ifndef SOLVER_H
#define SOLVER_H

#include "smt2context.h"
#include "smt2exception.h"
#include "csltp_order_graph.h"


/**
 * Checker
 */
class checker {
protected:
        predicate m_pred;
        bool is_numeral(z3::expr x);
        std::set<z3::expr, exprcomp> union_set(std::set<z3::expr, exprcomp> s1, std::set<z3::expr, exprcomp> s2);
public:
        checker(predicate pred):m_pred(pred){}
        virtual void check_args()=0;
        virtual void check_rec_rule(pred_rule& rule)=0;
        virtual void check_rec_rules()=0;
};

class treechecker :public checker {
private:
        bool is_repeat(z3::expr_vector vec);
        bool is_repeat(std::vector<z3::expr> vec);
        bool is_data_var(z3::expr x);
        bool is_size_var(z3::expr x);

public:
        treechecker(predicate pred):checker(pred){}
        void check_args();
        void check_rec_rule(pred_rule& rule);
        void check_rec_rules();
};

class listchecker :public checker {
public:
        listchecker(predicate pred):checker(pred){}
        void check_args();
        void check_rec_rule(pred_rule& rule);
        void check_rec_rules();
};



/**
 * Solver
 */
class solver {
protected:
	 smt2context& m_ctx;
     z3::expr_vector new_bools;
     z3::expr_vector delta_ge1_predicates; // phi^{>=1}_P(\alpha; \beta), corresponding to preds_array


protected:
	 void get_data_space(z3::expr& formula, z3::expr& data, z3::expr& space);
     int index_of_pred(std::string& pred_name);
     z3::expr abs_space(z3::expr& space);
     z3::expr abs_phi_star();

     smt2context& get_ctx() {return m_ctx;}
     z3::context& z3_ctx() {return m_ctx.z3_context();}
     Log& logger() {return m_ctx.logger();}
     virtual void check_preds()=0;
     virtual z3::check_result check_sat()=0;
     virtual z3::check_result check_entl()=0;
     virtual z3::expr pred2abs(z3::expr& atom, int i)=0;

 public:
solver(smt2context& ctx): m_ctx(ctx), new_bools(ctx.z3_context()), delta_ge1_predicates(ctx.z3_context()) {}
 	void solve();

};


class listsolver :public solver {
public:
        listsolver(smt2context& ctx) : solver(ctx){}
        void check_preds();
        z3::check_result check_sat();
        z3::check_result check_entl();
        z3::expr pred2abs(z3::expr& atom, int i);
};

/**
 * tree predicate solver
 */
class treesolver :public solver {
private:
        void get_constants(z3::expr const& exp, std::set<z3::expr, exprcomp>& vec);
        void get_constants(predicate& pred, std::set<z3::expr, exprcomp>& vec);
        void get_alpha_beta(predicate& pred, z3::expr_vector& alpha, z3::expr_vector& beta);
        void get_alpha_beta(predicate& pred, std::vector<Vertex>& alpha, std::vector<Vertex>& beta);
        void get_gamma_delta_epsilon(pred_rule& rule, z3::expr_vector& gamma, z3::expr_vector& delta, z3::expr_vector& epsilon);
        void get_gamma_delta_epsilon(pred_rule& rule, std::vector<Vertex>& gamma, std::vector<Vertex>& delta, std::vector<Vertex>& epsilon);
        z3::expr_vector get_x_h(pred_rule& rule);

        void expr2graph(z3::expr& exp, OrderGraph& og);
        void exp2vertex(z3::expr_vector& exp_vec, std::vector<Vertex>& ver_vec);
        void exp2vertex(std::set<z3::expr, exprcomp>& exp_set, std::vector<Vertex>& ver_vec);
        void vector2set(std::vector<Vertex>& ver_vec, std::set<Vertex>& ver_set);
        std::string get_exp_name(z3::expr exp);
        std::string simplify_var_name(std::string str);
        z3::expr vertex2exp(Vertex v);
        z3::expr edge2exp(Edge e);
        z3::expr graph2exp(OrderGraph& og);

        void compute_all_delta_ge1_p();

        z3::expr compute_delta_phi_pd(predicate& pred);
        z3::expr compute_delta_ge1_rule(pred_rule& rule, predicate& pred, z3::expr& delta_ge1_p_abs);

        OrderGraphSet lfp(predicate& pred);

public:
    treesolver(smt2context& ctx) : solver(ctx){}
        void check_preds();
        z3::check_result check_sat();
        z3::check_result check_entl();
        z3::expr pred2abs(z3::expr& atom, int i);
};

#endif /* SOLVER_H */
