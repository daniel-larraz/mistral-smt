# (c) Isil Dillig (isil@cs.stanford.edu), Thomas Dillig (tdillig@cs.stanford.edu)

find_package(FLEX)
find_package(BISON)


FLEX_TARGET(SMTLexer smtlexer.l  ${CMAKE_CURRENT_BINARY_DIR}/smtlexer.cpp)
BISON_TARGET(SMTParser smtparser.y ${CMAKE_CURRENT_BINARY_DIR}/smtparser.cpp)
ADD_FLEX_BISON_DEPENDENCY(SMTLexer SMTParser)

include_directories(${CMAKE_CURRENT_BINARY_DIR})

file(GLOB PARSER_SRC "smt-parser.cpp")



add_library(smtparser ${FLEX_SMTLexer_OUTPUTS}  ${BISON_SMTParser_OUTPUTS} ${PARSER_SRC})

