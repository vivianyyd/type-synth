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
%class OCamlExprLexer
%unicode
%line
%column
%cup
%function next_token
%type java_cup.runtime.Symbol

WHITESPACE = [ \t\r\n\f]+
IDENT      = [a-zA-Z_][a-zA-Z0-9_']*
OP         = [^ \t\r\n\fa-zA-Z0-9_'()]+

%%

{WHITESPACE}            { /* skip */ }
"fun"                   { return symbol(OCamlExprSymbols.FUN); }
"->"                    { return symbol(OCamlExprSymbols.ARROW); }
"("                     { return symbol(OCamlExprSymbols.LPAREN); }
")"                     { return symbol(OCamlExprSymbols.RPAREN); }
{IDENT}                 { return symbol(OCamlExprSymbols.IDENT, yytext()); }
{OP}                    { return symbol(OCamlExprSymbols.OP, yytext()); }
<<EOF>>                 { return symbol(OCamlExprSymbols.EOF); }
