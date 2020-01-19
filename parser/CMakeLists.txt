# (c) Isil Dillig (isil@cs.stanford.edu), Thomas Dillig (tdillig@cs.stanford.edu)

find_package(FLEX)
find_package(BISON)


FLEX_TARGET(MistralLexer lexer.l  ${CMAKE_CURRENT_BINARY_DIR}/lexer.cpp)
BISON_TARGET(MistralParser parser.y ${CMAKE_CURRENT_BINARY_DIR}/parser.cpp)
ADD_FLEX_BISON_DEPENDENCY(MistralLexer MistralParser)

include_directories(${CMAKE_CURRENT_BINARY_DIR})

file(GLOB PARSER_SRC "mistral-parser.cpp")



add_library(parser ${FLEX_MistralLexer_OUTPUTS}  ${BISON_MistralParser_OUTPUTS} ${PARSER_SRC})

#add_executable(Foo
#  ${FLEX_MistralLexer_OUTPUTS}
#  ${BISON_MistralParser_OUTPUTS}
# )