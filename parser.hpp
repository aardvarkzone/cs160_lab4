/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_YY_PARSER_HPP_INCLUDED
# define YY_YY_PARSER_HPP_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    IDENTIFIER = 258,              /* IDENTIFIER  */
    INT_LITERAL = 259,             /* INT_LITERAL  */
    CHAR_LITERAL = 260,            /* CHAR_LITERAL  */
    BOOL_LITERAL = 261,            /* BOOL_LITERAL  */
    STRING_LITERAL = 262,          /* STRING_LITERAL  */
    BOOLEAN = 263,                 /* BOOLEAN  */
    CHAR = 264,                    /* CHAR  */
    INTEGER = 265,                 /* INTEGER  */
    STRING = 266,                  /* STRING  */
    INTPTR = 267,                  /* INTPTR  */
    CHARPTR = 268,                 /* CHARPTR  */
    IF = 269,                      /* IF  */
    ELSE = 270,                    /* ELSE  */
    WHILE = 271,                   /* WHILE  */
    VAR = 272,                     /* VAR  */
    PROCEDURE = 273,               /* PROCEDURE  */
    RETURN = 274,                  /* RETURN  */
    NULLTOKEN = 275,               /* NULLTOKEN  */
    AND = 276,                     /* AND  */
    DIV = 277,                     /* DIV  */
    EQUAL = 278,                   /* EQUAL  */
    EQUALS = 279,                  /* EQUALS  */
    GT = 280,                      /* GT  */
    GTE = 281,                     /* GTE  */
    LT = 282,                      /* LT  */
    LTE = 283,                     /* LTE  */
    MINUS = 284,                   /* MINUS  */
    NOT = 285,                     /* NOT  */
    NOTEQUAL = 286,                /* NOTEQUAL  */
    OR = 287,                      /* OR  */
    PLUS = 288,                    /* PLUS  */
    MUL = 289,                     /* MUL  */
    AMP = 290,                     /* AMP  */
    DEREFERENCE = 291,             /* DEREFERENCE  */
    COMMA = 292,                   /* COMMA  */
    COLON = 293,                   /* COLON  */
    LBRACE = 294,                  /* LBRACE  */
    RBRACE = 295,                  /* RBRACE  */
    SEMICOLON = 296,               /* SEMICOLON  */
    LPAREN = 297,                  /* LPAREN  */
    RPAREN = 298,                  /* RPAREN  */
    BAR = 299,                     /* BAR  */
    LBRACKET = 300,                /* LBRACKET  */
    RBRACKET = 301                 /* RBRACKET  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 22 "parser.ypp"

    std::list<Proc_ptr>* u_proc_list;
    Program* u_program;
    std::list<Decl_ptr>* u_decl_list;
    Proc* u_proc;
    std::list<Stat_ptr>* u_stat_list;
    Procedure_block* u_procedure_block;
    Nested_block* u_nested_block;
    std::list<SymName_ptr>* u_symname_list;
    Decl* u_decl;
    Stat* u_stat;
    std::list<Expr_ptr>* u_expr_list;
    Return_stat* u_return_stat;
    Type* u_type;
    Expr* u_expr;
    Lhs* u_lhs;
    SymName* u_symname;
    Primitive* u_primitive;
    StringPrimitive* u_stringprimitive;
    char* u_base_charptr;
    int u_base_int;

#line 133 "parser.hpp"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;


int yyparse (void);


#endif /* !YY_YY_PARSER_HPP_INCLUDED  */
