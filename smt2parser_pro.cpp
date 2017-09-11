#include <cassert>

#include "smt2parser_pro.h"
// #include "util.h"


void smt2parser::scan_core() {
        m_cache_end = m_scanner.cache_size();
        m_curr      = m_scanner.scan();
}

void smt2parser::scan() {
        switch (m_curr) {
        case smt2scanner::LEFT_PAREN: m_num_open_paren++; break;
        case smt2scanner::RIGHT_PAREN: m_num_open_paren--; break;
        default: break;
        }
        scan_core();
}

void smt2parser::next() {
        if (m_curr != smt2scanner::EOF_TOKEN)
                scan();
}


void smt2parser::check_next(smt2scanner::token t, const char *msg) {
        if (curr() == t) {
                next();
                return;
        }
        throw smt2exception(msg, m_scanner.get_line(), m_scanner.get_pos());
}

// consume garbage
// return true if managed to recover from the error...
bool smt2parser::sync_after_error() {
        while (true) {
                try {
                        while (curr_is_rparen())
                                next();
                        if (m_num_open_paren < 0)
                                m_num_open_paren = 0;
                        if (curr() == smt2scanner::EOF_TOKEN && m_num_open_paren == 0)
                                return true;
                        assert(m_num_open_paren >= 0);
                        while (m_num_open_paren > 0 || !curr_is_lparen()) {
                                if (curr() == smt2scanner::EOF_TOKEN) {
                                        return false;
                                }
                                assert(m_num_open_paren >= 0);
                                next();
                                assert(m_num_open_paren >= -1);
                                if (m_num_open_paren < 0)
                                        m_num_open_paren = 0;
                                assert(m_num_open_paren >= 0);
                        }
                        return true;
                }
                catch (smt2exception & ex) {
                        assert(ex.has_pos());
                        error(ex.line(), ex.pos(), ex.get_msg().c_str());
                }
        }
}

void smt2parser::error(unsigned line, unsigned pos, char const * msg) {
        m_ctx.logger().log_format("(error (line: %d, column: %d), %s) \n", line, pos, msg);

        if (m_ctx.exit_on_error()) {
                exit(1);
        }
}


void smt2parser::error(char const * msg) {
        error(m_scanner.get_line(), m_scanner.get_pos(), msg);
}

void smt2parser::error_wo_pos(char const * msg) {
        m_ctx.logger().log_format("(error: %s)", msg);
}

/*void smt2parser::parse_sexpr() {
  unsigned stack_pos  = m_sexpr_stack.size();
  unsigned num_frames = 0;
  do {
  unsigned line = m_scanner.get_line();
  unsigned pos  = m_scanner.get_pos();
  switch (curr()) {
  case smt2scanner::LEFT_PAREN: {
  m_sexpr_frame_stack.push_back(m_sexpr_stack.size());
  num_frames++;
  break;
  }
  case smt2scanner::RIGHT_PAREN: {
  if (num_frames == 0)
  throw smt2exception("invalid s-expression, unexpected ')'");
  num_frames--;
  unsigned spos = m_sexpr_frame_stack.back();
  unsigned epos = m_sexpr_stack.size();
  assert(epos >= spos);
  unsigned num  = epos - spos;
  if (num == 0)
  throw smt2exception("invalid empty s-expression");
  sexpr * r = m_ctx.sm().mk_composite(spos, m_sexpr_stack, m_scanner.get_line(), m_scanner.get_pos());

  m_sexpr_stack.erase(m_sexpr_stack.begin()+spos, m_sexpr_stack.end());

  m_sexpr_stack.push_back(r);
  m_sexpr_frame_stack.pop_back();
  break;
  }
  case smt2scanner::SYMBOL_TOKEN:
  m_sexpr_stack.push_back(m_ctx.sm().mk_symbol(curr_id(), line, pos));
  break;
  case smt2scanner::KEYWORD_TOKEN:
  m_sexpr_stack.push_back(m_ctx.sm().mk_keyword(curr_id(), line, pos));
  break;
  case smt2scanner::STRING_TOKEN:
  m_sexpr_stack.push_back(m_ctx.sm().mk_string(m_scanner.get_string(), line, pos));
  break;
  case smt2scanner::INT_TOKEN:
  m_sexpr_stack.push_back(m_ctx.sm().mk_int_numeral(curr_numeral(), line, pos));
  break;
  case smt2scanner::FLOAT_TOKEN:
  m_sexpr_stack.push_back(m_ctx.sm().mk_real_numeral(curr_numeral(), line, pos));
  break;
  case smt2scanner::BV_TOKEN:
  m_sexpr_stack.push_back(m_ctx.sm().mk_bv_numeral(curr_numeral(), m_scanner.get_bv_size(), line, pos));
  break;
  case smt2scanner::EOF_TOKEN:
  throw smt2exception("invalid s-expression, unexpected end of file");
  break;
  default:
  throw smt2exception("invalid s-expression, unexpected input");
  break;
  }
  next();
  } while (num_frames > 0);
  assert(m_sexpr_stack.size() == stack_pos + 1);

  std::cout << "size: "  << m_sexpr_stack.size() << std::endl;
  sexpr* sexp = m_sexpr_stack.back();
  sexp->display(std::cout);
delete sexp;
}*/


/**
 * check the args are all bool type
 * @param args : the parameters
 * @return true: if all of the parameters are bool type
 */
bool smt2parser::check_args_bool(z3::expr_vector& args) {
        for (unsigned i=0; i<args.size(); i++) {
                if (!args[i].is_bool()) {
                        return false;
                }
        }
        return true;
}
/**
 * check the args are all numeral type
 * @param args : the parameters
 * @return true: if all of the parameters are  arith type
 */
bool smt2parser::check_args_numeral(z3::expr_vector& args) {
        for (unsigned i=0; i<args.size(); i++) {
                if (!args[i].is_arith()) {
                        return false;
                }
        }
        return true;
}

/**
 * check the args are all user_def type
 * @param args : the parameters
 * @return true: if all of the parameters are $UNINTERPRETED_SORT
 */
bool smt2parser::check_args_userdef(z3::expr_vector& args) {
        for (unsigned i=0; i<args.size(); i++) {
                if (args[i].get_sort().sort_kind() != Z3_UNINTERPRETED_SORT) {
                        return false;
                }
        }
        return true;
}

/**
 * check whether the $var is in $vec
 * @param vec : var list
 * @param var : var
 * @return true: if $var in $vec, otherwise false
 */
bool smt2parser::check_var_exist(std::vector<z3::expr> &vec, z3::expr& var) {
        for (int i=0; i<vec.size(); i++) {
                if (vec[i].hash() == var.hash()) {
                        return true;
                }
        }
        return false;
}


/**
 * make eq or ne expr according to kind
 * @param kind : the kind ==, !=
 * @param args : the args
 * @param line, pos: the expr position
 */
z3::expr smt2parser::make_eq(Z3_decl_kind kind, z3::expr_vector& args) {
        if (!check_args_bool(args) && !check_args_numeral(args) && !check_args_userdef(args))
                throw smt2exception("invalid s-expression, unexpected args type", m_scanner.get_line(), m_scanner.get_pos());
        if (args.size() != 2)
                throw smt2exception("invalid s-expression, expected 2 args", m_scanner.get_line(), m_scanner.get_pos());
        switch(kind) {
        case Z3_OP_EQ:
                return args[0] == args[1];
        case Z3_OP_DISTINCT:
                return args[0] != args[1];
        default: break;
        }
        throw smt2exception("invalid s-expression, expected = or distinct", m_scanner.get_line(), m_scanner.get_pos());
}
/**
 * make compare expr according to kind
 * @param kind : the kind >=, <=, >, <
 * @param args : the args
 * @param line, pos: the expr position
 */
z3::expr smt2parser::make_compare(Z3_decl_kind kind, z3::expr_vector& args) {
        if (!check_args_numeral(args))
                throw smt2exception("invalid s-expression, unexpected args type", m_scanner.get_line(), m_scanner.get_pos());
        if (args.size() != 2)
                throw smt2exception("invalid s-expression, expected 2 args", m_scanner.get_line(), m_scanner.get_pos());
        switch(kind) {
        case Z3_OP_LE:
                return args[0] <= args[1];
        case Z3_OP_GE:
                return args[0] >= args[1];
        case Z3_OP_LT:
                return args[0] < args[1];
        case Z3_OP_GT:
                return args[0] > args[1];
        default: break;
        }
        throw smt2exception("invalid s-expression, expected <, <= , >, >=", m_scanner.get_line(), m_scanner.get_pos());
}

/**
 * make arith expr according to kind
 * @param kind : the kind -, +, *
 * @param args : the args
 * @param line, pos: the expr position
 */
z3::expr smt2parser::make_arith(Z3_decl_kind kind, z3::expr_vector& args) {
        if (!check_args_numeral(args))
                throw smt2exception("invalid s-expression, unexpected args type", m_scanner.get_line(), m_scanner.get_pos());

        z3::expr res = args[0];
        switch(kind) {
        case Z3_OP_SUB:
                if (args.size() == 1) {
                        // (- 1)
                        res = -args[0];
                } else {
                        // (- 1 1)
                        for (unsigned i=1; i<args.size(); i++) {
                                res = res - args[i];
                        }
                }
                return res;
        case Z3_OP_ADD:
                return sum(args);
        case Z3_OP_MUL:
                for (unsigned i=1; i<args.size(); i++) {
                        res = res * args[i];
                }
                return res;
        default: break;
        }
        throw smt2exception("invalid s-expression, expected +, -, *", m_scanner.get_line(), m_scanner.get_pos());
}
/**
 * make logic expr according to kind
 * @param kind : the kind and , or , not , =>
 * @param args : the args
 * @param line, pos: the expr position
 */
z3::expr smt2parser::make_logic(Z3_decl_kind kind, z3::expr_vector& args){
        if (!check_args_bool(args))
                throw smt2exception("invalid s-expression, unexpected args type", m_scanner.get_line(), m_scanner.get_pos());
        switch(kind) {
        case Z3_OP_NOT:
                if (args.size() > 1)
                        throw smt2exception("invalid s-expression, expected 1 arg", m_scanner.get_line(), m_scanner.get_pos());
                return !args[0];
        case Z3_OP_IMPLIES:
                if (args.size() != 2)
                        throw smt2exception("invalid s-expression, expected 2 args", m_scanner.get_line(), m_scanner.get_pos());
                return implies(args[0], args[1]);
        case Z3_OP_AND:
                return mk_and(args);
        case Z3_OP_OR:
                return mk_or(args);
        default: break;
        }
        throw smt2exception("invalid s-expression, expected and, or, not, =>", m_scanner.get_line(), m_scanner.get_pos());
}


/**
 * make expr according to the $func_sym
 * @param func_sym : function name
 * @param args : actual args
 * @param line, pos: current position
 */
z3::expr smt2parser::make_app(z3::symbol& func_sym, z3::expr_vector& args){

        //
        std::string func = func_sym.str();
        std::map<std::string, Z3_decl_kind> name_kind_table;

        name_kind_table["true"] = Z3_OP_TRUE;
        name_kind_table["false"] = Z3_OP_FALSE;
        name_kind_table["="] = Z3_OP_EQ;
        name_kind_table["distinct"] = Z3_OP_DISTINCT;
        name_kind_table["and"] = Z3_OP_AND;
        name_kind_table["or"] = Z3_OP_OR;
        name_kind_table["not"] = Z3_OP_NOT;
        name_kind_table["=>"] = Z3_OP_IMPLIES;
        name_kind_table["<="] = Z3_OP_LE;
        name_kind_table[">="] = Z3_OP_GE;
        name_kind_table["<"] = Z3_OP_LT;
        name_kind_table[">"] = Z3_OP_GT;
        name_kind_table["+"] = Z3_OP_ADD;
        name_kind_table["-"] = Z3_OP_SUB;
        name_kind_table["*"] = Z3_OP_MUL;

        if (name_kind_table.find(func) == name_kind_table.end()) {
                std::string info = m_ctx.logger().string_format("invalid s-expression, '%s' unexpected func name", func);
                throw smt2exception(info, m_scanner.get_line(), m_scanner.get_pos());
        }

        // std::cout << "app: " << func << std::endl;

        Z3_decl_kind kind = name_kind_table[func];

        switch(kind) {
        case Z3_OP_TRUE:
                return m_ctx.z3_context().bool_val(true);
        case Z3_OP_FALSE:
                return m_ctx.z3_context().bool_val(false);

        case Z3_OP_AND:
        case Z3_OP_OR:
        case Z3_OP_NOT:
        case Z3_OP_IMPLIES:
                return make_logic(kind, args);
        case Z3_OP_EQ:
        case Z3_OP_DISTINCT:
                return make_eq(kind, args);
        case Z3_OP_GE:
        case Z3_OP_LE:
        case Z3_OP_GT:
        case Z3_OP_LT:
                return make_compare(kind, args);
        case Z3_OP_ADD:
        case Z3_OP_SUB:
        case Z3_OP_MUL:
                return make_arith(kind, args);
        default: {
                std::string info = m_ctx.logger().string_format("invalid s-expression, '%s' unexpected func name", func);
                throw smt2exception(info, m_scanner.get_line(), m_scanner.get_pos());
        }
        }
}

/**
 * parse expr (app_name args)
 */
void smt2parser::parse_expr() {
        m_ctx.logger().log_out_ln("parse expr start.");
        unsigned stack_pos  = m_expr_stack.size();
        unsigned num_frames = 0;
        do {
                unsigned line = m_scanner.get_line();
                unsigned pos  = m_scanner.get_pos();
                switch (curr()) {
                case smt2scanner::LEFT_PAREN: {
                        m_expr_frame_stack.push_back(m_expr_stack.size());
                        num_frames++;
                        break;
                }
                case smt2scanner::RIGHT_PAREN: {
                        if (num_frames == 0)
                                throw smt2exception("invalid s-expression, unexpected ')'", m_scanner.get_line(), m_scanner.get_pos());
                        num_frames--;
                        unsigned spos = m_expr_frame_stack.back();
                        unsigned epos = m_expr_stack.size();
                        assert(epos >= spos);
                        unsigned num  = epos - spos;
                        z3::expr exp = m_ctx.z3_context().int_val(1);

                        // make apply
                        // 1. get fun_declare
                        if(m_symbol_stack.size()<=0) {
                                throw smt2exception("invalid empty s-expression", m_scanner.get_line(), m_scanner.get_pos());
                        }
                        z3::symbol func_sym = m_symbol_stack.back();

                        if (num == 0) {
                                std::string info = m_ctx.logger().string_format("invalid s-expression, for %s arguments missing", func_sym.str());
                                throw smt2exception(info, m_scanner.get_line(), m_scanner.get_pos());
                        }
                        // 2. get arguments
                        z3::expr_vector args(m_ctx.z3_context());

                        for (int i=spos; i<epos; i++) {
                                args.push_back(m_expr_stack[i]);
                        }

                        if ( m_symbol_func_table.find(func_sym) != m_symbol_func_table.end()) {
                                z3::func_decl fun = m_symbol_func_table.find(func_sym)->second;
                                for (int i=0; i<num; i++) {
                                        if (fun.domain(i).name() == args[i].get_sort().name()) {
                                                std::string info = m_ctx.logger().string_format("invalid s-expression, for %s argument %d mismatch", func_sym.str(), i);
                                                throw smt2exception(info, m_scanner.get_line(), m_scanner.get_pos());
                                        }
                                }
                                // make user-def app
                                exp = fun(args);
                        } else {
                                // make built-in app
                                exp = make_app(func_sym, args);
                        }

                        m_symbol_stack.pop_back();

                        m_expr_stack.erase(m_expr_stack.begin()+spos, m_expr_stack.end());

                        m_expr_stack.push_back(exp);


                        m_expr_frame_stack.pop_back();
                        break;
                }
                case smt2scanner::SYMBOL_TOKEN:{
                        z3::symbol sym = curr_id();

                        if (m_symbol_var_table.find(sym) != m_symbol_var_table.end()) {
                                // variable or 0-arity func
                                z3::expr var = m_symbol_var_table.find(sym)->second.m_term;
                                m_expr_stack.push_back(var);
                        } else if(m_builtin_func_table.find(sym) != m_builtin_func_table.end()){
                                // app
                                z3::func_decl f = m_builtin_func_table.find(sym)->second;
                                if (f.arity()==0) {
                                        z3::expr_vector args(m_ctx.z3_context());
                                        z3::expr val = make_app(sym, args);
                                        m_expr_stack.push_back(val);
                                }
                        } else {
                                m_symbol_stack.push_back(sym);
                        }
                        // std::cout << " \nsymbol:"  << sym;
                        break;
                }
                case smt2scanner::KEYWORD_TOKEN:
                        // std::cout << "\n keyword ";
                        // :sorts ...
                        break;
                case smt2scanner::STRING_TOKEN:
                        m_expr_stack.push_back(m_ctx.z3_context().string_val(m_scanner.get_string().c_str()));
                        // std::cout << "\n string: " << m_scanner.get_string();
                        break;
                case smt2scanner::INT_TOKEN:
                case smt2scanner::FLOAT_TOKEN:
                case smt2scanner::BV_TOKEN:
                        // std::cout << "\n number:" << curr_numeral();
                        m_expr_stack.push_back(curr_numeral());
                        break;
                case smt2scanner::EOF_TOKEN:
                        throw smt2exception("invalid s-expression, unexpected end of file", m_scanner.get_line(), m_scanner.get_pos());
                        break;
                default:
                        throw smt2exception("invalid s-expression, unexpected input", m_scanner.get_line(), m_scanner.get_pos());
                        break;
                }
                next();
        } while (num_frames > 0);
        assert(m_expr_stack.size() == stack_pos + 1);

        m_ctx.logger().log_format("expr stack size: %d\n", m_expr_stack.size());
        m_ctx.logger() << "ther last expr:\n" << m_expr_stack.back() << std::endl;
        m_ctx.logger().log_out_ln("parse expr end.");
}



/**
 * parse sort
 *     : (sort)  (Field 2)=>(Field Int Bool)
 * @return sort:
 */
z3::sort smt2parser::parse_sort() {
        unsigned line = m_scanner.get_line();
        unsigned pos = m_scanner.get_pos();
        if (curr_is_identifier()) {
                z3::symbol sort_s = curr_id();
                if (m_builtin_sort_table.find(sort_s) != m_builtin_sort_table.end()) {
                        return m_builtin_sort_table.find(sort_s)->second.first;
                } else {
                        throw smt2exception("invalid parametes, unexpected sort name", m_scanner.get_line(), m_scanner.get_pos());
                }
        }

        if (curr_is_lparen())  {
                next();
                check_identifier("invalid parametes, unsupported sort!");
                z3::symbol par_sort_s = curr_id();
                if (m_builtin_sort_table.find(par_sort_s) != m_builtin_sort_table.end()) {
                        unsigned num_par = m_builtin_sort_table.find(par_sort_s)->second.second;
                        z3::sort res_sort = m_ctx.z3_context().bool_sort();
                        if (num_par == 1) {
                                // set_ref
                                next();
                                check_identifier("invalid parametes, unsupported sort!");
                                z3::symbol domain_sy = curr_id();
                                if (m_builtin_sort_table.find(domain_sy) == m_builtin_sort_table.end()) {
                                        throw smt2exception("invalid parametes, unsupported sort", m_scanner.get_line(), m_scanner.get_pos());
                                }
                                z3::sort domain_sort = m_builtin_sort_table.find(domain_sy)->second.first;
                                z3::symbol void_sy = m_ctx.z3_context().str_symbol("Void");
                                z3::sort void_sort = m_builtin_sort_table.find(void_sy)->second.first;
                                z3::sort set_ref_sort = m_ctx.z3_context().array_sort(domain_sort, void_sort);
                                res_sort = set_ref_sort;
                                // return set_ref_sort;
                        } else if (num_par == 2) {
                                // field
                                next();
                                check_identifier("invalid parametes, unsupported sort!");
                                z3::symbol domain_sy = curr_id();
                                if (m_builtin_sort_table.find(domain_sy) == m_builtin_sort_table.end()) {
                                        throw smt2exception("invalid parametes, unsupported sort", m_scanner.get_line(), m_scanner.get_pos());
                                }
                                z3::sort domain_sort = m_builtin_sort_table.find(domain_sy)->second.first;
                                next();
                                check_identifier("invalid parametes, unsupported sort!");
                                z3::symbol range_sy = curr_id();
                                if (m_builtin_sort_table.find(range_sy) == m_builtin_sort_table.end()) {
                                        throw smt2exception("invalid parametes, unsupported sort", m_scanner.get_line(), m_scanner.get_pos());
                                }
                                z3::sort range_sort = m_builtin_sort_table.find(range_sy)->second.first;
                                z3::sort field_sort = m_ctx.z3_context().array_sort(domain_sort, range_sort);

                                res_sort = field_sort;
                                //return field_sort;
                        } else {
                                throw smt2exception("invalid parametes, unsupported sort", m_scanner.get_line(), m_scanner.get_pos());
                        }

                        next();
                        if (curr_is_rparen()) {
                                return res_sort;
                        }
                        throw smt2exception("invalid sort, expected ')'", m_scanner.get_line(), m_scanner.get_pos());
                }
                throw smt2exception("invalid parametes, unexpected sort name", m_scanner.get_line(), m_scanner.get_pos());
        }
}

/**
 * parse parameters ((var sort) ())
 *     the parameters as variables are pushed in the $m_sorted_var_stack
 *     the $m_var_frame_stack.back() stores the start position
 * @return empty : if empty, return true
 *                 otherwise, return false
 */
bool smt2parser::parse_parameters() {
        // std::cout << "parse parameter:\n";
        unsigned stack_pos  = m_sorted_var_stack.size();
        // m_var_frame_stack.push_back(m_sorted_var_stack.size());
        unsigned num_frames = 0;
        z3::expr var = m_ctx.z3_context().bool_val(true);
        bool empty = true;
        do {
                switch (curr()) {
                case smt2scanner::LEFT_PAREN: {
                        m_var_frame_stack.push_back(m_sorted_var_stack.size());
                        num_frames++;
                        break;
                }
                case smt2scanner::RIGHT_PAREN:{
                        // check empty
                        num_frames--;
                        if (!empty) {
                                // push var
                                if (num_frames > 0) {
                                        m_sorted_var_stack.push_back(var);
                                        m_var_frame_stack.pop_back();
                                }
                        } else {
                                m_var_frame_stack.pop_back();
                        }
                        break;
                }
                case smt2scanner::SYMBOL_TOKEN:{
                        empty = false;
                        z3::symbol var_s = curr_id();
                        next();
                        z3::sort var_sort = parse_sort();
                        var = m_ctx.z3_context().constant(var_s, var_sort);
                        break;
                }
                default:
                        throw smt2exception("invalid parametes, unexpected variable name", m_scanner.get_line(), m_scanner.get_pos());
                }
                next();
        }while(num_frames > 0);


        // std::cout <<"start pos: " <<m_var_frame_stack.back() << std::endl;
        // std::cout <<"parameter: " <<m_sorted_var_stack.size() << std::endl;
        return empty;

}



/**
 * parse cmd (set_logic LOGIC_NAME)
 * set the m_logic
 * do some init according to the logic
 */
void smt2parser::parse_set_logic() {
        m_ctx.logger() << "parse set logic start. \n";
        assert(curr_is_identifier());
        assert(m_set_logic ==  curr_id());
        next();
        check_identifier("invalid logic name, symbol expected");
        z3::symbol logic_id = curr_id();

        m_ctx.logger() << "parse logic :" << logic_id << std::endl;

        next();
        if (!curr_is_rparen())
                check_identifier("invalid set-logic, ')' expected");

        if (logic_id.str() == "QF_SLRDI") {
                m_logic_name = logic::QF_SLRDI;
                //TODO: do something else
                // std::cout << logic_name;
        }

        m_ctx.logger() << "parse set logic end. \n";

}

/**
 * parse cmd (declare-sort SORTNAE PARAMETER_NUM)
 * push the sort into $m_builtin_sort_table
 */
void smt2parser::parse_declare_sort() {
        m_ctx.logger() << "parse declare sort start. \n";
        assert(curr_is_identifier());
        assert(m_declare_sort ==  curr_id());
        next();
        check_identifier("invalid sort name, symbol expected");
        z3::symbol sort_name = curr_id();
        next();
        check_int("invalid declare-sort parameter, integer expcected");
        z3::expr num = curr_numeral();
        next();
        check_rparen("invalid declare-sort, ')' expcected");

        // insert new sort
        z3::sort sort_user = m_ctx.z3_context().uninterpreted_sort(sort_name);
        unsigned num_par = num.get_numeral_uint();

        m_ctx.logger() << "declare-sort: " << sort_user <<" " <<num_par << std::endl;
        if (m_builtin_sort_table.find(sort_name) != m_builtin_sort_table.end()) {
                std::string info = m_ctx.logger().string_format("redeclare sort for %s, unexpected sort name", m_ctx.logger().value_to_str(sort_name));
                throw smt2exception(info, m_scanner.get_line(), m_scanner.get_pos());
        }
        m_builtin_sort_table.insert(std::pair<z3::symbol, std::pair<z3::sort, unsigned> >(sort_name, std::pair<z3::sort, unsigned>(sort_user, num_par)));
        m_ctx.logger() << "parse declare sort end. \n";
}

/**
 * parse cmd (declare-fun FUN_NAME (parameters) SORT_NAME)
 * parse fields variable and variable, push them into $m_sort_fields_table and $m_sorted_var_stack respectively
 * TODO: process the fun_declare
 */
void smt2parser::parse_declare_fun() {

        m_ctx.logger() << "parse declare-fun start.\n";

        assert(curr_is_identifier());
        assert(m_declare_fun ==  curr_id());
        next(); // fun_name
        check_identifier("invalid function name, symbol expcected");

        z3::symbol fun_name = curr_id();

        m_ctx.logger() << "parse fun name: " << fun_name << std::endl;

        next(); // (
        bool empty = parse_parameters();

        m_ctx.logger() << "parser parameters, empty: " << empty << std::endl;

        z3::sort range = parse_sort();
        next(); // )
        check_rparen("invalid declare-fun, ')' expcected");

        if (empty) {
                // insert var
                z3::expr var_cons = m_ctx.z3_context().constant(fun_name, range);
                if (range.is_array()) {
                        // set_ref or field
                        if (range.array_range().to_string() == "Void") {
                                // set_ref NONE
                        } else {
                                z3::sort main_sort = range.array_domain();
                                if (main_sort.sort_kind() != Z3_UNINTERPRETED_SORT) {
                                        std::string info = m_ctx.logger().string_format("invalid field for sort '%s', unexpected sort name.", m_ctx.logger().value_to_str(main_sort));
                                        throw smt2exception(info, m_scanner.get_line(), m_scanner.get_pos());
                                }
                                z3::sort field_sort = range.array_range();

                                if (m_sort_fields_table.find(main_sort.name() ) == m_sort_fields_table.end()) {
                                        // insert
                                        std::vector<z3::expr> fields;
                                        fields.push_back(var_cons);
                                        m_sort_fields_table.insert(std::pair<z3::symbol, std::vector<z3::expr>>(main_sort.name(), fields));
                                } else {
                                        // find and insert
                                        std::vector<z3::expr>& fields = m_sort_fields_table.find(main_sort.name())->second;
                                        if (check_var_exist(fields, var_cons)) {
                                                std::string info = m_ctx.logger().string_format("redeclare field '%s' for sort '%s', unexpected sort name.", m_ctx.logger().value_to_str(var_cons), m_ctx.logger().value_to_str(main_sort));

                                                throw smt2exception(info, m_scanner.get_line(), m_scanner.get_pos());
                                        }
                                        fields.push_back(var_cons);
                                        // std::cout << "fields: " << fields.size() << std::endl;
                                }
                        }
                        m_ctx.logger() << "new filed: " << var_cons << std::endl;
                } else {
                        // var
                        if (check_var_exist(m_sorted_var_stack, var_cons)) {
                                std::string info = m_ctx.logger().string_format("redeclare variable '%s', unexpected sort name.", m_ctx.logger().value_to_str(var_cons));
                                throw smt2exception(info, m_scanner.get_line(), m_scanner.get_pos());
                        }
                        // insert
                        m_sorted_var_stack.push_back(var_cons);
                        m_ctx.logger() << "new variable: " << var_cons << std::endl;
                }
        } else {
                // fun-declare
        }

        m_ctx.logger() << "parse declare-fun end.\n";
}

/**
 * parse cmd (define-func FUN_NAME (parameters) SORT_NAME (body))
 * parse fun_declare, push it into $m_symbol_func_table [UNDO]
 * parse body, translate it into predicate define [UNDO]
 */
void smt2parser::parse_define_fun() {
        m_ctx.logger() << "parse define-fun start.\n";
        assert(curr_is_identifier());
        assert(m_define_fun ==  curr_id());
        next(); // fun_name
        check_identifier("invalid function/constant definition, symbol expected");
        z3::symbol fun_name = curr_id();
        next(); // (
        bool empty = parse_parameters();

        if (empty) {
                // error
                std::string info = m_ctx.logger().string_format("invalid define-fun for %s, unexpected empty parameter.", fun_name.str());
                throw smt2exception(info, m_scanner.get_line(), m_scanner.get_pos());
        } else {
                //
                unsigned spos = m_var_frame_stack.back();
                unsigned epos = m_sorted_var_stack.size();
                unsigned num = epos - spos;
                // std::cout << "the number of parameters : " << num << std::endl;
                m_ctx.logger()  << "the number of parameters : " << num << std::endl;

        }

        // unsigned sym_spos  = symbol_stack().size();
        // unsigned sort_spos = sort_stack().size();
        // unsigned expr_spos = expr_stack().size();
        // unsigned num_vars  = parse_sorted_vars();
        // parse_sort("Invalid function definition");
        // parse_expr();
        // if (m().get_sort(expr_stack().back()) != sort_stack().back())
        //         throw parser_exception("invalid function/constant definition, sort mismatch");
        // m_ctx.insert(id, num_vars, sort_stack().c_ptr() + sort_spos, expr_stack().back());
        // check_rparen("invalid function/constant definition, ')' expected");
        // // restore stacks & env
        // symbol_stack().shrink(sym_spos);
        // sort_stack().shrink(sort_spos);
        // expr_stack().shrink(expr_spos);
        // m_env.end_scope();
        // assert(num_vars == m_num_bindings);
        // m_num_bindings = 0;
        // m_ctx.print_success();
        // next();
}

void smt2parser::parse_cmd() {
        // std::cout <<"curr: " <<curr() << std::endl;

//        m_ctx.logger().log_format("parse: %s", "parse_cmd");

        assert(curr_is_lparen());
        int line = m_scanner.get_line();
        int pos  = m_scanner.get_pos();
        next();
        check_identifier("invalid command, symbol expected");
        z3::symbol s = curr_id();

        // std::cout << s;

        if (s == m_set_logic) {
                parse_set_logic();
                return;
        }

        if (s == m_declare_sort) {
                parse_declare_sort();
                return;
        }

        if (s == m_declare_fun) {
                parse_declare_fun();
                return;
        }

        ///////////////////////////////////

        if (s == m_define_fun) {
                parse_define_fun();
                return;
        }

        if (s == m_assert) {
                // parse_assert();
                std::cout << "assert \n ";
                return;
        }

        if (s == m_check_sat) {
                // parse_check_sat();
                return;
        }



}

bool smt2parser::operator()() {
        m_num_bindings    = 0;
        bool found_errors = false;

        try {
                scan_core();
        }
        catch (smt2exception & ex) {
                error(ex.get_msg().c_str());
                if (!sync_after_error())
                        return false;
                found_errors = true;
        }


        while (true) {
                try {
                        m_num_open_paren = 0;
                        while (true) {
                                switch (curr()) {
                                case smt2scanner::LEFT_PAREN:
                                        parse_cmd();
                                        break;
                                case smt2scanner::EOF_TOKEN:
                                        return !found_errors;
                                default:
                                        throw smt2exception("invalid command, '(' expected");
                                        break;
                                }
                        }
                }
                catch (smt2exception & ex) {
                        error(m_scanner.get_line(), m_scanner.get_pos(), ex.get_msg().c_str());
                }
        }
}


/**
 * init the theory, add some built-in sorts and funs
 */
void smt2parser::init_theory() {
        // built-in sorts

        z3::symbol bool_sym = m_ctx.z3_context().str_symbol("Bool");
        z3::sort B = m_ctx.z3_context().bool_sort();
        z3::symbol int_sym = m_ctx.z3_context().str_symbol("Int");
        z3::sort I = m_ctx.z3_context().int_sort();
        z3::symbol rat_sym = m_ctx.z3_context().str_symbol("Rat");
        z3::sort R = m_ctx.z3_context().real_sort();

        z3::symbol void_sym = m_ctx.z3_context().str_symbol("Void");
        z3::sort V = m_ctx.z3_context().uninterpreted_sort("Void");

        z3::symbol field_sym = m_ctx.z3_context().str_symbol("Field");
        z3::sort F =  m_ctx.z3_context().uninterpreted_sort("Field");

        z3::symbol set_ref_sym = m_ctx.z3_context().str_symbol("SetRef");
        z3::sort S =  m_ctx.z3_context().uninterpreted_sort("SetRef");

        z3::symbol space_sym = m_ctx.z3_context().str_symbol("Space");
        z3::sort SP =  m_ctx.z3_context().uninterpreted_sort("Space");

        // m_builtin_sort_table[bool_sym] = B; NO
        m_builtin_sort_table.insert(std::pair<z3::symbol, std::pair<z3::sort, unsigned> >(bool_sym, std::pair<z3::sort, unsigned>(B, 0)));
        m_builtin_sort_table.insert(std::pair<z3::symbol, std::pair<z3::sort, unsigned> >(int_sym, std::pair<z3::sort, unsigned>(I, 0)));
        m_builtin_sort_table.insert(std::pair<z3::symbol, std::pair<z3::sort, unsigned> >(rat_sym, std::pair<z3::sort, unsigned>(R, 0)));
        m_builtin_sort_table.insert(std::pair<z3::symbol, std::pair<z3::sort, unsigned> >(void_sym, std::pair<z3::sort, unsigned>(V, 0)));
        m_builtin_sort_table.insert(std::pair<z3::symbol, std::pair<z3::sort, unsigned> >(field_sym, std::pair<z3::sort, unsigned>(F, 2)));
        m_builtin_sort_table.insert(std::pair<z3::symbol, std::pair<z3::sort, unsigned> >(set_ref_sym, std::pair<z3::sort, unsigned>(S, 1)));
        m_builtin_sort_table.insert(std::pair<z3::symbol, std::pair<z3::sort, unsigned> >(space_sym, std::pair<z3::sort, unsigned>(SP, 0)));
        // m_builtin_sort_table.insert(std::pair<z3::symbol, z3::sort>(int_sym, I));
        // m_builtin_sort_table.insert(std::pair<z3::symbol, z3::sort>(rat_sym, R));
        // m_builtin_sort_table.insert(std::pair<z3::symbol, z3::sort>(void_sym, V));


        // built-in funs

//        z3::symbol bool_sym = m_ctx.z3_context().str_symbol("Bool");
        z3::func_decl true_f = m_ctx.z3_context().function("true", 0, 0, B);
        z3::symbol true_s =  m_ctx.z3_context().str_symbol("true");
        z3::func_decl false_f = m_ctx.z3_context().function("false", 0, 0, B);
        z3::symbol false_s =  m_ctx.z3_context().str_symbol("false");

        m_builtin_func_table.insert(std::pair<z3::symbol, z3::func_decl>(true_s, true_f));
        m_builtin_func_table.insert(std::pair<z3::symbol, z3::func_decl>(false_s, false_f));

}


smt2parser::smt2parser(smt2context & ctx, std::istream & is):
        m_ctx(ctx),
        m_scanner(ctx, is),
        m_curr(smt2scanner::NULL_TOKEN),
        //   m_curr_cmd(0),
        // m_num_bindings(0),
        // m_let(ctx.z3_context().str_symbol("let")),
        // m_bang(ctx.z3_context().str_symbol("!")),
        // m_forall(ctx.z3_context().str_symbol("forall")),
        m_exists(ctx.z3_context().str_symbol("exists")),
        // m_as(ctx.z3_context().str_symbol("as")),
        // m_not(ctx.z3_context().str_symbol("not")),
        // m_root_obj(ctx.z3_context().str_symbol("root-obj")),
        // m_named(ctx.z3_context().str_symbol(":named")),
        // m_weight(ctx.z3_context().str_symbol(":weight")),
        // m_qid(ctx.z3_context().str_symbol(":qid")),
        // m_skid(ctx.z3_context().str_symbol(":skolemid")),
        // m_ex_act(ctx.z3_context().str_symbol(":ex-act")),
        // m_pattern(ctx.z3_context().str_symbol(":pattern")),
        // m_nopattern(ctx.z3_context().str_symbol(":no-pattern")),
        // m_lblneg(ctx.z3_context().str_symbol(":lblneg")),
        // m_lblpos(ctx.z3_context().str_symbol(":lblpos")),
        m_assert(ctx.z3_context().str_symbol("assert")),
        m_check_sat(ctx.z3_context().str_symbol("check-sat")),
        m_define_fun(ctx.z3_context().str_symbol("define-fun")),
        // m_define_const(ctx.z3_context().str_symbol("define-const")),
        m_declare_fun(ctx.z3_context().str_symbol("declare-fun")),
        // m_declare_const(ctx.z3_context().str_symbol("declare-const")),
        // m_define_sort(ctx.z3_context().str_symbol("define-sort")),
        m_declare_sort(ctx.z3_context().str_symbol("declare-sort")),
        // m_declare_datatypes(ctx.z3_context().str_symbol("declare-datatypes")),
        // m_declare_datatype(ctx.z3_context().str_symbol("declare-datatype")),
        // m_par(ctx.z3_context().str_symbol("par")),
        // m_push(ctx.z3_context().str_symbol("push")),
        // m_pop(ctx.z3_context().str_symbol("pop")),
        // m_get_value(ctx.z3_context().str_symbol("get-value")),
        // m_reset(ctx.z3_context().str_symbol("reset")),
        // m_check_sat_assuming(ctx.z3_context().str_symbol("check-sat-assuming")),
        // m_define_fun_rec(ctx.z3_context().str_symbol("define-fun-rec")),
        // m_define_funs_rec(ctx.z3_context().str_symbol("define-funs-rec")),
        m_set_logic(ctx.z3_context().str_symbol("set-logic")),
        //m_underscore(ctx.z3_context().str_symbol("_")),
        m_num_open_paren(0)
{
        init_theory();

        // updt_params();
}
