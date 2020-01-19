#!/bin/bash
g++ -g -static -I.. -I../cnode -I../solver -I../sat-solver/ -I../numeric-lib -I../term/ -I../smtparser/ -std=c++11 get-abduct-cli.cpp ../build/smtparser/libsmtparser.a ../build/libmistral.a ../build/parser/libparser.a -o get-abduct-cli -lgmp
