%option yylineno
%pointer

%{
    #include <cstdlib>
    #include <cstring>
    #include "ast.hpp"
    #include "parser.hpp"

    void yyerror(const char *); 
%}

/** WRITE ME:
 /*  Put any definitions you need here. Add your own regular expressions
 *  below for ALL tokens defined in the manual. You can choose not to use
 *  definitions here.
 */

/* HERE */

DIGIT       [0-9]
ALPHA       [a-zA-Z]
IDENTIFIER  {ALPHA}({ALPHA}|{DIGIT}|_)*
DECIMAL     [0-9]{DIGIT}*
HEX         0[xX][0-9a-fA-F]+
OCTAL       0[0-7]+
BINARY      [01]+[bB]
STRING_LITERAL    \"[^\"]*\"
CHAR_LITERAL     \'[^\']\'

/** The example below is very simple, but it shows almost everything you will
 /*  need to do for this first part. The syntax is as follows:
 *
 *  regular_expression      {  c code  }
 *
 * The lexer will try to match each regular expression. When it does it will
 * execute the corresponding C code.
*/

%x C_COMMENT
%%
"boolean"       { return BOOLEAN; }
"char"          { return CHAR; }
"integer"       { return INTEGER; }
"string"        { return STRING; }
"intptr"        { return INTPTR; }
"charptr"       { return CHARPTR; }
"if"            { return IF; }
"else"          { return ELSE; }
"while"         { return WHILE; }
"var"           { return VAR; }
"procedure"     { return PROCEDURE; }
"return"        { return RETURN; }
"null"          { return NULLTOKEN; }
"&&"            { return AND; }
"/"             { return DIV; }
"="             { return EQUAL; }
"=="            { return EQUALS; }
">"             { return GT; }
">="            { return GTE; }
"<"             { return LT; }
"<="            { return LTE; }
"-"             { return MINUS; }
"!"             { return NOT; }
"!="            { return NOTEQUAL; }
"||"            { return OR; }
"+"             { return PLUS; }
"*"             { return MUL; }
"&"             { return AMP; }
"^"             { return DEREFERENCE; }
"true"          { yylval.u_base_int = 1; return BOOL_LITERAL; }
"false"         { yylval.u_base_int = 0; return BOOL_LITERAL; }
"{"             { return LBRACE; }
"}"             { return RBRACE; }
";"             { return SEMICOLON; }
"("             { return LPAREN; }
")"             { return RPAREN; }
"["             { return LBRACKET; }
"]"             { return RBRACKET; }
","             { return COMMA; }
":"             { return COLON; }
"|"             { return BAR; }
{HEX}           { yylval.u_base_int = strtol(yytext, NULL, 16); return INT_LITERAL; }
{OCTAL}         { yylval.u_base_int = strtol(yytext, NULL, 8); return INT_LITERAL; }
{BINARY}        { yylval.u_base_int = strtol(yytext, NULL, 2); return INT_LITERAL; }
{DECIMAL}       { yylval.u_base_int = atoi(yytext); return INT_LITERAL; }
{STRING_LITERAL} { int length = strlen(yytext) - 2; 
                    char* literal = (char*) malloc(length + 1); 
                    strncpy(literal, yytext + 1, length); 
                    literal[length] = '\0';
                    yylval.u_base_charptr = literal;
                    return STRING_LITERAL;
                }
{CHAR_LITERAL}  { yylval.u_base_int = yytext[1]; return CHAR_LITERAL; } 
{IDENTIFIER}    { yylval.u_base_charptr = strdup(yytext); return IDENTIFIER; }

[\*\(\)\.\+\-\|]  { return *yytext; }

[ \t\n]             ; /* skip whitespace */

"/%"            { BEGIN(C_COMMENT); }
<C_COMMENT>"%/" { BEGIN(INITIAL); }
<C_COMMENT>\n   { }
<C_COMMENT>.    { }
.                   { yyerror((char *) "invalid character"); }

%%

/** You shall not pass!
 *  You should not  have to do or edit anything past this.
 */

int yywrap(void) {
    return 1;
}
