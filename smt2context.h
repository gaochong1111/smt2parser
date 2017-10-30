#ifndef SMT2CONTEXT_H
#define SMT2CONTEXT_H

#include <iostream>
#include "log.h"
#include "predicate.h"


class smt2context {
private:
        bool m_exit_on_err;
        z3::context& m_ctx; // z3 context
        Log m_log; // logger

        // parse result
        std::vector<predicate> m_preds;
        z3::expr m_negf;
        z3::expr m_posf;

public:
        Log& logger() {return m_log;}
        z3::context& z3_context() {return m_ctx;}
        bool exit_on_error() {return m_exit_on_err;}

smt2context(z3::context& ctx, std::string log_file, bool exit_err=true):m_ctx(ctx), m_exit_on_err(exit_err), m_negf(ctx), m_posf(ctx){
                m_log.common_log_init(log_file);
        }

        void add_predicate(predicate pred) {
                m_preds.push_back(pred);
        }

        void set_negf(z3::expr f) {
                m_negf = f;
        }

        void set_posf(z3::expr f) {
                m_posf = f;
        }

        int pred_size() {return m_preds.size();}

        predicate get_pred(int index) {
                assert(index < m_preds.size());
                return m_preds[index];
        }

        z3::expr get_negf() {
                return m_negf;
        }

        z3::expr get_posf() {
                return m_posf;
        }

        bool is_tree() {
                // TODO
                for (int i=0; i<m_preds.size(); i++) {
                        if (!m_preds[i].is_tree()) return false;
                }
                return true;
        }

        bool is_list() {
                // TODO
                for (int i=0; i<m_preds.size(); i++) {
                        if (!m_preds[i].is_list()) return false;
                }
                return true;
        }



        bool is_no_formula() {
                return (Z3_ast(m_posf) == 0) && (Z3_ast(m_negf) == 0);
        }

        bool is_sat() {
                return Z3_ast(m_posf) == 0;
        }

        bool is_entl() {
                return (Z3_ast(m_negf) != 0) && (Z3_ast(m_posf) != 0);
        }

};

#endif /* SMT2CONTEXT_H */
