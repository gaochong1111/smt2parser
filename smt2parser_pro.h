#ifndef SMT2PARSER_PRO_H
#define SMT2PARSER_PRO_H

#include <vector>
#include <map>
#include <z3++.h>
#include <sstream>

#include "smt2scanner.h"
// #include "sexpr.h"
/**
 * the recursive definition
 * func_decl
 * binding arguments (var env)
 * base_rule, rec_rules
 *
 */
class predicate {

};

/**
 * pred_rule
 * binding arguments (var env)
 * data, pto, rec_app
 *
 */
class pred_rule {

};

// fields: sort -> vars of fields [next]


class smt2parser {


public:
        enum logic{
                QF_SLRDI=0,
                OTHER
        };

        smt2scanner              m_scanner;
        smt2context& m_ctx;
        smt2scanner::token       m_curr;

        logic m_logic_name;

        class local {
        public:
                z3::expr           m_term;
                unsigned         m_level;
        local(z3::expr t, unsigned l):m_term(t), m_level(l) {}
        };

        // std::map<z3::symbol, local> m_symbol_var_table;
        // std::map<z3::symbol, z3::func_decl> m_symbol_func_table; //
        std::map<z3::symbol, std::vector<z3::expr>> m_sort_fields_table; // srot -> fields
        std::map<z3::symbol, z3::func_decl> m_builtin_func_table;
        std::map<z3::symbol, std::pair<z3::sort, unsigned> > m_builtin_sort_table;

        std::vector<z3::symbol> m_symbol_stack;
        std::vector<z3::expr> m_expr_stack;
        std::vector<unsigned> m_expr_frame_stack;

        std::vector<z3::expr> m_sorted_var_stack; // vars
        std::vector<unsigned> m_var_frame_stack;



        unsigned            m_cache_end;
        std::vector<std::string> m_cached_strings;
        int m_num_open_paren;
        unsigned m_num_bindings;


//        std::vector<sexpr*> m_sexpr_stack;
//        std::vector<int> m_sexpr_frame_stack;


        // z3::symbol               m_let;
        // z3::symbol               m_bang;
        // z3::symbol               m_forall;
        z3::symbol               m_exists;
        // z3::symbol               m_as;
        // z3::symbol               m_not;
        // z3::symbol               m_root_obj;

        // z3::symbol               m_named;
        // z3::symbol               m_weight;
        // z3::symbol               m_qid;
        // z3::symbol               m_skid;
        // z3::symbol               m_ex_act;
        // z3::symbol               m_pattern;
        // z3::symbol               m_nopattern;
        // z3::symbol               m_lblneg;
        // z3::symbol               m_lblpos;

        z3::symbol               m_assert;
        z3::symbol               m_check_sat;
        z3::symbol               m_define_fun;
        // z3::symbol               m_define_const;
        z3::symbol               m_declare_fun;
        // z3::symbol               m_declare_const;
        // z3::symbol               m_define_sort;
        z3::symbol               m_declare_sort;
        // z3::symbol               m_declare_datatypes;
        // z3::symbol               m_declare_datatype;
        // z3::symbol               m_par;
        // z3::symbol               m_push;
        // z3::symbol               m_pop;
        // z3::symbol               m_get_value;
        // z3::symbol               m_reset;
        // z3::symbol               m_check_sat_assuming;
        // z3::symbol               m_define_fun_rec;
        // z3::symbol               m_define_funs_rec;
        // z3::symbol               m_underscore;
        z3::symbol               m_set_logic;


        void scan_core();

        void scan(); // scan a symbol

        void next(); // next symbol

        smt2scanner::token curr() const { return m_curr; }

        void check_next(smt2scanner::token t, char const * msg);

        bool sync_after_error() ;

        void error(unsigned line, unsigned pos, char const * msg) ;

        void error(char const * msg) ;

        void error_wo_pos(char const * msg) ;

        z3::symbol const & curr_id() const { return m_scanner.get_id(); }
        z3::expr curr_numeral() const { return m_scanner.get_number(); }

        bool curr_is_lparen() const { return curr() == smt2scanner::LEFT_PAREN; }
        bool curr_is_rparen() const { return curr() == smt2scanner::RIGHT_PAREN; }
        bool curr_is_identifier() const { return curr() == smt2scanner::SYMBOL_TOKEN; }
        bool curr_is_int() const { return curr() == smt2scanner::INT_TOKEN; }
        bool curr_is_float() const { return curr() == smt2scanner::FLOAT_TOKEN; }

        bool curr_id_is_exists() const { assert(curr_is_identifier()); return curr_id() == m_exists; }

        void check_lparen_next(char const * msg) { check_next(smt2scanner::LEFT_PAREN, msg); }
        void check_rparen_next(char const * msg) { check_next(smt2scanner::RIGHT_PAREN, msg); }
        void check_rparen(char const * msg) { if (!curr_is_rparen()) throw smt2exception(msg, m_scanner.get_line(), m_scanner.get_pos()); }
        void check_identifier(char const * msg) { if (!curr_is_identifier()) throw smt2exception(msg, m_scanner.get_line(), m_scanner.get_pos()); }
        void check_int(char const * msg) { if (!curr_is_int()) throw smt2exception(msg, m_scanner.get_line(), m_scanner.get_pos()); }
        void check_int_or_float(char const * msg) { if (!curr_is_int() && !curr_is_float()) throw smt2exception(msg, m_scanner.get_line(), m_scanner.get_pos()); }

//        void parse_sexpr();

        bool check_args_bool(z3::expr_vector& args);
        bool check_args_numeral(z3::expr_vector& args); // int or real
        bool check_args_userdef(z3::expr_vector& args);
        z3::expr make_compare(Z3_decl_kind kind, z3::expr_vector& args);
        z3::expr make_eq(Z3_decl_kind kind, z3::expr_vector& args);
        z3::expr make_arith(Z3_decl_kind kind, z3::expr_vector& args);
        z3::expr make_logic(Z3_decl_kind kind, z3::expr_vector& args);
        z3::expr make_app(z3::symbol& func_sym, z3::expr_vector& args);


        bool check_var_exist(std::vector<z3::expr>& vec, z3::expr& var);

        void parse_expr();

        z3::sort parse_sort();

        bool parse_parameters();

        void parse_define_fun();

        void parse_set_logic();

        void parse_declare_sort();

        void parse_declare_fun();

        void parse_cmd();

        bool operator()();

        void init_theory();

        smt2parser(smt2context & ctx, std::istream & is);

};


#endif /* SMT2PARSER_PRO_H */
