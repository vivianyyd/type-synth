package testutil.parser;

import java_cup.runtime.Symbol;

%%

%{
private Symbol symbol(int id) {
    return new Symbol(id, yyline + 1, yycolumn + 1);
}

private Symbol symbol(int id, Object value) {
    return new Symbol(id, yyline + 1, yycolumn + 1, value);
}
%}

%public
%class SExprLexer
%unicode
%line
%column
%cup
%function next_token
%type java_cup.runtime.Symbol

WHITESPACE = [ \t\r\n\f]+
ATOM = [^() \t\r\n\f]+

%%

{WHITESPACE}            { /* skip whitespace */ }
"("                     { return symbol(SExprSymbols.LPAREN); }
")"                     { return symbol(SExprSymbols.RPAREN); }
{ATOM}                  { return symbol(SExprSymbols.ATOM, yytext()); }
<<EOF>>                 { return symbol(SExprSymbols.EOF); }
