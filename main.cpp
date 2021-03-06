#include <iostream>
#include <sstream>
#include <fstream>
#include "smt2scanner.h"
#include "smt2parser.h"
// #include "sexpr.h"

using namespace std;


string token_str[] = { "NULL_TOKEN",
                       "LEFT_PAREN",
                       "RIGHT_PAREN",
                       "KEYWORD_TOKEN",
                       "SYMBOL_TOKEN",
                       "STRING_TOKEN",
                       "INT_TOKEN",
                       "BV_TOKEN",
                       "FLOAT_TOKEN",
                       "EOF_TOKEN"};

std::string file_name = "test.smt";


void test_scanner() {
        try {
                fstream f("test.smt");

                // sexpr_manager sm;
                z3::context ctx;
                smt2context m_ctx(ctx, "log");

                smt2scanner scanner(m_ctx, f);

                smt2scanner::token t;
                while((t=scanner.scan()) != smt2scanner::token::EOF_TOKEN) {
                        cout << "type: " << token_str[t] << endl;
                        std::string str =  scanner.get_string();
                        // cout << "May word: " << str << endl;
                        if (t == smt2scanner::token::INT_TOKEN) {
                                cout << "int: " << scanner.get_number() << endl;
                        } else if (t == smt2scanner::token::SYMBOL_TOKEN) {
                                cout << "sym: " << scanner.get_id() << endl;
                        }
                }

        } catch(const smt2exception& e) {
                cout << e.get_msg() << endl;
        }


}

void test_parser() {
        try {
                fstream f(file_name);

                // sexpr_manager sm;
                z3::context ctx;
                smt2context m_ctx(ctx, "log");


                smt2parser parser(m_ctx, f);
                int N = 6;
                for (int i=0; i<N; i++) {
                        // parser.next();
                        parser.parse_cmd();
                }


                // z3::sort s = parser.parse_sort();
                // std::cout << s << std::endl;
                // parser.parse_expr();
                // parser.parse_parameters();

//                parser.next();
//                parser.parse_cmd();
//                std::cout << "curr: " << parser.curr() << std::endl;
//                parser.next();
//                parser.parse_cmd();

                // parser();

                /*
                  smt2scanner::token t;
                  while((t=scanner.scan()) != smt2scanner::token::EOF_TOKEN) {
                  cout << "type: " << token_str[t] << endl;
                  string token = scanner.get_string();
                  cout << "May word: " << token << endl;
                  }
                */
        } catch(const smt2exception& e) {
                cout << e.get_msg() << endl;
        }
}

void test() {
        try {
                fstream f(file_name);
                z3::context ctx;
                smt2context m_ctx(ctx, "log");
                smt2parser parser(m_ctx, f);
                parser();

                predicate pred = m_ctx.get_pred(0);

                // std::cout << pred << std::endl;

                z3::expr negf = m_ctx.get_negf();

                // std::cout << negf << std::endl;
        } catch(const smt2exception& e) {
                cout << e.get_msg() << endl;
        }
}

int main(int argc, char *argv[])
{
        if (argc>0) {
                int i=1;
                for (; i<argc; i++) {
                        std::string op = argv[i];
                        if (op == "-f" && i+1<argc) {
                                file_name = argv[i+1];
                                i++;
                        }
                        std::cout << "file_name: " << file_name << std::endl;
                        // std::cout << "arg" << i << " : " << op << std::endl;
                }
        }


        // test_scanner();
        // test_parser();
        test();




        return 0;
}
