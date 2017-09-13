#ifndef SMT2CONTEXT_H
#define SMT2CONTEXT_H

#include <iostream>
#include "log.h"
// #include "sexpr.h"
#include <z3++.h>

class smt2context {
public:
        bool m_exit_on_err;
//        sexpr_manager m_sm;
        z3::context& m_ctx;
        // std::ostream& m_out;
        Log m_log;

public:
        Log& logger() {return m_log;}
//        sexpr_manager& sm() {return m_sm;}
        z3::context& z3_context() {return m_ctx;}
        bool exit_on_error() {return m_exit_on_err;}

// smt2context(z3::context& ctx,std::ostream& out, bool exit_err=true):m_ctx(ctx), m_out(out), m_exit_on_err(exit_err) { }
smt2context(z3::context& ctx, std::string log_file, bool exit_err=true):m_ctx(ctx), m_exit_on_err(exit_err) {
                m_log.common_log_init(log_file);
        }





};

#endif /* SMT2CONTEXT_H */
