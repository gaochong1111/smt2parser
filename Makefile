#---------------------------------------
# Flags
#---------------------------------------
CXX=g++

CXX_FLAGS= -std=c++11 -g

LIB_DIR=/usr/local/lib
Z3LIB_PATH=/usr/local/lib/libz3.so

DYN_LINK_LIB_FLAG = -rdynamic $(Z3LIB_PATH)
DYN_RUN_LIB_FLAG = -Wl,-R$(LIB_DIR)

#---------------------------------------
# Files
#---------------------------------------
SRC = main.cpp smt2scanner.cpp smt2parser.cpp log.cpp solver.cpp

INC = smt2scanner.h smt2exception.h  smt2context.h  smt2parser.h log.h predicate.h solver.h
#---------------------------------------
# Rules
#---------------------------------------
all: parser

parser:$(subst .cpp,.o,$(SRC))
	$(CXX) $(CXX_FLAGS)  -o $@ $^ \
	$(DYN_LINK_LIB_FLAG) \
	$(DYN_RUN_LIB_FLAG)

clean:
	rm -f parser *.o


#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .c .h .a .o .so .cpp



%.o: %.cpp $(INC)
	$(CXX)  $(CXX_FLAGS)  -c -o $@ $<
