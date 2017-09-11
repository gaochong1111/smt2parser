#---------------------------------------
# Flags
#---------------------------------------
CXX=g++

LIB_DIR=/usr/local/lib
Z3LIB_PATH=/usr/local/lib/libz3.so

DYN_LINK_LIB_FLAG = -rdynamic $(Z3LIB_PATH)
DYN_RUN_LIB_FLAG = -Wl,-R$(LIB_DIR)

#---------------------------------------
# Files
#---------------------------------------
SRC = main.cpp smt2scanner.cpp smt2parser_pro.cpp log.cpp

INC = smt2scanner.h smt2exception.h  smt2context.h  smt2parser_pro.h log.h
#---------------------------------------
# Rules
#---------------------------------------
all: scanner

scanner:$(subst .cpp,.o,$(SRC))
	$(CXX) -std=c++11 -o $@ $^ \
	$(DYN_LINK_LIB_FLAG) \
	$(DYN_RUN_LIB_FLAG)

clean:
	rm -f scanner *.o


#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .c .h .a .o .so .cpp



%.o: %.cpp $(INC)
	$(CXX) -std=c++11 -c -o $@ $<
