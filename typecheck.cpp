#include <iostream>
#include <cstdio>
#include <cstring>
#include <typeinfo>
#include "ast.hpp"
#include "symtab.hpp"
#include "primitive.hpp"
#include "assert.h"
using namespace std;

// WRITEME: The default attribute propagation rule
#define default_rule(X) X

#include <typeinfo>

class Typecheck : public Visitor
{
  private:
    FILE* m_errorfile;
    SymTab* m_st;

    // The set of recognized errors
    enum errortype
    {
        no_main,
        nonvoid_main,
        dup_proc_name,
        dup_var_name,
        proc_undef,
        call_type_mismatch,
        narg_mismatch,
        expr_type_err,
        var_undef,
        ifpred_err,
        whilepred_err,
        incompat_assign,
        who_knows,
        ret_type_mismatch,
        array_index_error,
        no_array_var,
        arg_type_mismatch,
        expr_pointer_arithmetic_err,
        expr_abs_error,
        expr_addressof_error,
        invalid_deref
    };

    // Print the error to file and exit
    void t_error(errortype e, Attribute a)
    {
        fprintf(m_errorfile,"on line number %d, ", a.lineno);

        switch(e)
        {
            case no_main:
                fprintf(m_errorfile, "error: no main\n");
                exit(2);
            case nonvoid_main:
                fprintf(m_errorfile, "error: the Main procedure has arguments\n");
                exit(3);
            case dup_proc_name:
                fprintf(m_errorfile, "error: duplicate procedure names in same scope\n");
                exit(4);
            case dup_var_name:
                fprintf(m_errorfile, "error: duplicate variable names in same scope\n");
                exit(5);
            case proc_undef:
                fprintf(m_errorfile, "error: call to undefined procedure\n");
                exit(6);
            case var_undef:
                fprintf(m_errorfile, "error: undefined variable\n");
                exit(7);
            case narg_mismatch:
                fprintf(m_errorfile, "error: procedure call has different number of args than declaration\n");
                exit(8);
            case arg_type_mismatch:
                fprintf(m_errorfile, "error: argument type mismatch\n");
                exit(9);
            case ret_type_mismatch:
                fprintf(m_errorfile, "error: type mismatch in return statement\n");
                exit(10);
            case call_type_mismatch:
                fprintf(m_errorfile, "error: type mismatch in procedure call args\n");
                exit(11);
            case ifpred_err:
                fprintf(m_errorfile, "error: predicate of if statement is not boolean\n");
                exit(12);
            case whilepred_err:
                fprintf(m_errorfile, "error: predicate of while statement is not boolean\n");
                exit(13);
            case array_index_error:
                fprintf(m_errorfile, "error: array index not integer\n");
                exit(14);
            case no_array_var:
                fprintf(m_errorfile, "error: attempt to index non-array variable\n");
                exit(15);
            case incompat_assign:
                fprintf(m_errorfile, "error: type of expr and var do not match in assignment\n");
                exit(16);
            case expr_type_err:
                fprintf(m_errorfile, "error: incompatible types used in expression\n");
                exit(17);
            case expr_abs_error:
                fprintf(m_errorfile, "error: absolute value can only be applied to integers and strings\n");
                exit(17);
            case expr_pointer_arithmetic_err:
                fprintf(m_errorfile, "error: invalid pointer arithmetic\n");
                exit(18);
            case expr_addressof_error:
                fprintf(m_errorfile, "error: AddressOf can only be applied to integers, chars, and indexed strings\n");
                exit(19);
            case invalid_deref:
                fprintf(m_errorfile, "error: Deref can only be applied to integer pointers and char pointers\n");
                exit(20);
            default:
                fprintf(m_errorfile, "error: no good reason\n");
                exit(21);
        }
    }

    // Helpers
    // WRITEME: You might want write some helper functions.


    // Type Checking
    // WRITEME: You need to implement type-checking for this project
    void check_for_one_main(ProgramImpl* p) {
        Attribute main_attr;
        if (!m_st->lookup("Main")) {
            //  if (m_st->lexical_distance(m_st->get_scope(), p->m_attribute.m_scope) == 0) {
            //      cout << m_st->lexical_distance(m_st->get_scope(), p->m_attribute.m_scope);
            //     t_error(no_main, main_attr);
            //  }
            t_error(no_main, main_attr);
        } else if (!m_st->lookup("Main")->m_arg_type.empty()) {
            t_error(nonvoid_main, main_attr);
        }
    }


    void add_proc_symbol(ProcImpl* p) {
        char* name = strdup(p->m_symname->spelling());
        Symbol* s = new Symbol();
        s->m_basetype = bt_procedure;

        for (auto& declPtr : *(p->m_decl_list)) {
            DeclImpl* decl = dynamic_cast<DeclImpl*>(declPtr);
            if (decl) {  
                Basetype argType = decl->m_type->m_attribute.m_basetype;
                s->m_arg_type.push_back(argType);
            }
        }

        if (p->m_attribute.m_scope != nullptr && m_st->lookup(p->m_attribute.m_scope, name) == nullptr) {
            free(name);
            t_error(dup_proc_name, p->m_attribute);
            return;
        }

        if(!m_st->insert(name, s)) {
            free(name);
            this->t_error(dup_proc_name, p->m_attribute);
        }

        p->m_attribute.m_basetype = bt_procedure;
    }


    // Add symbol table information for all the declarations following
    void add_decl_symbol(DeclImpl* p) {
        for (auto symname_ptr : *(p->m_symname_list)) {
            char* name = strdup(symname_ptr->spelling());
            Symbol* s = new Symbol();

            if(dynamic_cast<TInteger*>(p->m_type)) {
                s->m_basetype = bt_integer;
            } else if(dynamic_cast<TCharacter*>(p->m_type)) {
                s->m_basetype = bt_char;
            } else if(dynamic_cast<TBoolean*>(p->m_type)) {
                s->m_basetype = bt_boolean;
            } else if(dynamic_cast<TCharPtr*>(p->m_type)) {
                s->m_basetype = bt_charptr;
            } else if(dynamic_cast<TIntPtr*>(p->m_type)) {
                s->m_basetype = bt_intptr;
            } else if(dynamic_cast<TString*>(p->m_type)) {
                s->m_basetype = bt_string;
            } 
            if (!m_st->insert(name, s)) {
                // cout << "Trying to insert duplicate variable '" << name << "' in scope " << m_st->get_scope() << endl;
                t_error(dup_var_name, p->m_attribute);
            } else {
                // cout << "Inserted variable '" << name << "' in scope " << m_st->get_scope() << endl;
            }
        }
        
    }
    
    // Check that the return statement of a procedure has the appropriate type
    void check_proc(ProcImpl *p) {
        // Basetype procDeclaredReturnType = p->m_type->m_attribute.m_basetype;
        // Procedure_blockImpl* procBlock = dynamic_cast<Procedure_blockImpl*>(p->m_procedure_block);
        // if (procBlock != nullptr && procBlock->m_return_stat != nullptr) {
        //     Return* returnStmt = dynamic_cast<Return*>(procBlock->m_return_stat);
        //     if (returnStmt != nullptr && returnStmt->m_expr != nullptr) {
        //         Basetype returnExprType = evaluate_expr_type(returnStmt->m_expr);

        //         // Check if return type is a pointer and the expression is null
        //         if ((returnExprType == bt_ptr && (procDeclaredReturnType == bt_charptr || procDeclaredReturnType == bt_intptr)) ||
        //             procDeclaredReturnType == returnExprType) {
        //             return; // Valid return type
        //         } else {
        //             t_error(ret_type_mismatch, p->m_attribute);
        //         }
        //     } 
        // }
        // Basetype returnDef = p->m_type->m_attribute.m_basetype;
        // Basetype returning = p->m_procedure_block->m_attribute.m_basetype;

        if((p->m_type->m_attribute.m_basetype == bt_charptr || 
            p->m_type->m_attribute.m_basetype == bt_intptr) && 
            p->m_procedure_block->m_attribute.m_basetype == bt_ptr) {
            return;
        }

        

        if(p->m_type->m_attribute.m_basetype != p->m_procedure_block->m_attribute.m_basetype) {
            this->t_error(ret_type_mismatch, p->m_attribute);
        }
        m_st->dump(stdout);
    }

    // Check that the declared return type is not an array
    void check_return(Return *p) {
        // Basetype returnType = evaluate_expr_type(p->m_expr);
        Basetype returnType = p->m_attribute.m_basetype;
        // Check if the return type is null, which is allowed for pointer types
        // if (returnType == bt_ptr) {
        //     return; // Valid for pointer return types
        // }

        if (returnType == bt_string) {
            t_error(call_type_mismatch, p->m_attribute);
        }
    }


    // Create a symbol for the procedure and check there is none already
    // existing
    void check_call(Call *p) {
        char* name = strdup(p->m_symname->spelling());
        // cout << "Checking call to procedure: " << name << endl;

        Symbol* procSymbol = m_st->lookup(name);
        if (!procSymbol || procSymbol->m_basetype != bt_procedure) {
            t_error(proc_undef, p->m_attribute);
            free(name);
            return;
        }

        // cout << "Number of arguments in call: " << p->m_expr_list->size() << endl;
        // cout << "Number of expected arguments: " << procSymbol->m_arg_type.size() << endl;

        if (p->m_expr_list->size() != procSymbol->m_arg_type.size()) {
            t_error(narg_mismatch, p->m_attribute);
            free(name);
            return;
        }
        size_t index = 0; 
        for (auto arg : *p->m_expr_list) {
            Basetype argType = arg->m_attribute.m_basetype;
            // if (argType == bt_ptr && procSymbol->m_arg_type == bt_charptr) { cout << "test"; }
            if (argType != procSymbol->m_arg_type[index]) {
                t_error(arg_type_mismatch, p->m_attribute);
            }
            index++;
        }
        free(name);
    }



    // For checking that this expressions type is boolean used in if/else
    void check_pred_if(Expr* p)
    {
        Basetype exprType = p->m_attribute.m_basetype;

        if (exprType != bt_boolean) {
            t_error(ifpred_err, p->m_attribute); 
        }
    }

    // For checking that this expressions type is boolean used in while
    void check_pred_while(Expr* p)
    {
        // Basetype exprType = p->m_attribute.m_basetype;
        Basetype exprType = p->m_attribute.m_basetype;

        if (exprType != bt_boolean) {
            t_error(whilepred_err, p->m_attribute); 
        }
    }

    void check_assignment(Assignment* p) {
       
        // if (p->m_lhs->m_attribute.m_basetype != p->m_expr->m_attribute.m_basetype) {
        //     t_error(incompat_assign, p->m_attribute);
        // }
        if (p->m_lhs->m_attribute.m_basetype == p->m_expr->m_attribute.m_basetype) {
            return;  
        }

        if (p->m_lhs->m_attribute.m_basetype == bt_string && p->m_expr->m_attribute.m_basetype == bt_char) {
            if(dynamic_cast<ArrayElement*>(p->m_lhs)) {
                return; 
            }
        }

        if (p->m_expr->m_attribute.m_basetype == bt_ptr) {
            if (p->m_lhs->m_attribute.m_basetype == bt_charptr || p->m_lhs->m_attribute.m_basetype == bt_intptr) {
                return; 
            }
        }

        t_error(incompat_assign, p->m_attribute);
    }


    void check_string_assignment(StringAssignment* p) {
        if (p->m_lhs->m_attribute.m_basetype != bt_string) {
             t_error(incompat_assign, p->m_lhs->m_attribute);
        }
    }

    void check_array_access(ArrayAccess* p)
    {   
        Symbol* arraySymbol = m_st->lookup(p->m_symname->spelling());
        if (!arraySymbol || arraySymbol->m_basetype != bt_string) { 
            t_error(no_array_var, p->m_attribute);
        }

        Basetype indexType = p->m_expr->m_attribute.m_basetype;
        if (indexType != bt_integer) {
            t_error(array_index_error, p->m_attribute); 
        }
        p->m_attribute.m_basetype = bt_char;
    }

    void check_array_element(ArrayElement* p)
    {
        Symbol* arraySymbol = m_st->lookup(p->m_symname->spelling());
        if (!arraySymbol || arraySymbol->m_basetype != bt_string) {
            t_error(no_array_var, p->m_attribute); 
        }

        Basetype indexType = p->m_expr->m_attribute.m_basetype;
        if (indexType != bt_integer) {
            t_error(array_index_error, p->m_attribute); 
        }
        p->m_attribute.m_basetype = bt_char;
        
    }

    // For checking boolean operations(and, or ...)
    void checkset_boolexpr(Expr* parent, Expr* child1, Expr* child2)
    {
        if (child1->m_attribute.m_basetype != bt_boolean || 
            child2->m_attribute.m_basetype != bt_boolean) {
            t_error(expr_type_err, parent->m_attribute); 
        }
        parent->m_attribute.m_basetype = bt_boolean;
    }

    // For checking arithmetic expressions(plus, times, ...)
    void checkset_arithexpr(Expr* parent, Expr* child1, Expr* child2) {
        Basetype type1 = child1->m_attribute.m_basetype;
        Basetype type2 = child2->m_attribute.m_basetype;

        if (type1 != bt_intptr || type2 != bt_intptr || type1 != bt_charptr || type2 != bt_charptr) {
            t_error(expr_pointer_arithmetic_err, parent->m_attribute);
        }

        if (type1 != bt_integer || type2 != bt_integer) {
            t_error(expr_type_err, parent->m_attribute);
        }

        parent->m_attribute.m_basetype = bt_integer;
    }


    // Called by plus and minus: in these cases we allow pointer arithmetics
    void checkset_arithexpr_or_pointer(Expr* parent, Expr* child1, Expr* child2)
    {
        Basetype type1 = child1->m_attribute.m_basetype;
        Basetype type2 = child2->m_attribute.m_basetype;


        if (type1 == bt_integer && type2 == bt_integer) {
            parent->m_attribute.m_basetype = bt_integer;
        } else if ((type1 == bt_charptr && type2 == bt_integer) ||  (type2 == bt_charptr && type1 == bt_integer)) {
            parent->m_attribute.m_basetype = bt_charptr;
        } else {
            t_error(expr_pointer_arithmetic_err, parent->m_attribute);
        }


       
    }
    

    // For checking relational(less than , greater than, ...)
    void checkset_relationalexpr(Expr* parent, Expr* child1, Expr* child2)
    {
        Basetype type1 = child1->m_attribute.m_basetype;
        Basetype type2 = child2->m_attribute.m_basetype;

        // Basetype type1 = evaluate_expr_type(child1);
        // Basetype type2 = evaluate_expr_type(child2);

        // bool isValidType1 = (type1 == bt_integer || (type1 == bt_undef && child1->m_attribute.m_basetype == bt_integer));
        // bool isValidType2 = (type2 == bt_integer || (type2 == bt_undef && child2->m_attribute.m_basetype == bt_integer));

        if (type1 != bt_integer || type2 != bt_integer) {
            t_error(expr_type_err, parent->m_attribute);
        }

        parent->m_attribute.m_basetype = bt_boolean;
    }

    // For checking equality ops(equal, not equal)
    void checkset_equalityexpr(Expr* parent, Expr* child1, Expr* child2)
    {
        Basetype type1 = child1->m_attribute.m_basetype;
        Basetype type2 = child2->m_attribute.m_basetype;
        // Basetype type1 = evaluate_expr_type(child1);
        // Basetype type2 = evaluate_expr_type(child2);

        if (type1 != type2) {
            t_error(expr_type_err, parent->m_attribute);
        }
        parent->m_attribute.m_basetype = bt_boolean;
    }

    // For checking not
    void checkset_not(Expr* parent, Expr* child)
    {
        Basetype childType = child->m_attribute.m_basetype;

        if (childType != bt_boolean) {
            t_error(expr_type_err, parent->m_attribute); 
        }

        parent->m_attribute.m_basetype = bt_boolean;
    }

    void checkset_uminus(Expr* parent, Expr* child)
    {
        Basetype childType = child->m_attribute.m_basetype;

        if (childType != bt_integer) {
            t_error(expr_type_err, parent->m_attribute); 
        }

        parent->m_attribute.m_basetype = childType;
    }

    void checkset_absolute_value(Expr* parent, Expr* child) {
        Basetype childType = child->m_attribute.m_basetype;

        
        if (childType != bt_integer && childType != bt_string) {
            t_error(expr_type_err, parent->m_attribute); 
        }

        parent->m_attribute.m_basetype = bt_integer;
    }


    void checkset_addressof(Expr* parent, Lhs* child) {
        // parent->m_attribute.m_basetype = bt_ptr;
        if (auto var = dynamic_cast<Variable*>(child)) {
            Symbol* s = m_st->lookup(var->m_symname->spelling());
            if (s) {
                if (s->m_basetype == bt_integer) {
                    parent->m_attribute.m_basetype = bt_intptr;
                } else if (s->m_basetype == bt_char) {
                    parent->m_attribute.m_basetype = bt_charptr;
                } else {
                    t_error(expr_addressof_error, child->m_attribute);
                }
            }
        } else if (auto arrayElem = dynamic_cast<ArrayElement*>(child)) {
            Symbol* arraySymbol = m_st->lookup(arrayElem->m_symname->spelling());
            if (arraySymbol && arraySymbol->m_basetype == bt_string) {
                parent->m_attribute.m_basetype = bt_charptr; 
            } else {
                t_error(expr_addressof_error, child->m_attribute);
            }
        } else {
            t_error(expr_addressof_error, child->m_attribute);
        }
    }


    void checkset_deref_expr(Deref* parent,Expr* child)
    {
        Basetype childType = child->m_attribute.m_basetype;

        if (childType != bt_charptr && childType != bt_intptr) {
            t_error(invalid_deref, parent->m_attribute);
        }

        if (childType == bt_charptr) {
            parent->m_attribute.m_basetype = bt_char;
        } else if (childType == bt_intptr) {
            parent->m_attribute.m_basetype = bt_integer;
        } 
    }

    // Check that if the right-hand side is an lhs, such as in case of
    // addressof
    void checkset_deref_lhs(DerefVariable* p)
    {
        Symbol* s = m_st->lookup(p->m_symname->spelling());
        if (!s) {
            t_error(var_undef, p->m_attribute);
        }

        if (s->m_basetype != bt_intptr && s->m_basetype != bt_charptr) {
            t_error(invalid_deref, p->m_attribute);
        }

        if (s->m_basetype == bt_intptr) {
            p->m_attribute.m_basetype = bt_integer;
        } else if (s->m_basetype == bt_charptr) {
            p->m_attribute.m_basetype = bt_char;
        } 
    }

    void checkset_variable(Variable* p)
    {
        Symbol* s = m_st->lookup(p->m_symname->spelling());
        if (!s) {
            t_error(var_undef, p->m_attribute);
        } else {
            p->m_attribute.m_basetype = s->m_basetype;

        }
    }


  public:

    Typecheck(FILE* errorfile, SymTab* st) {
        m_errorfile = errorfile;
        m_st = st;
    }

    void visitProgramImpl(ProgramImpl* p)
    {   
        p->visit_children(this);
        check_for_one_main(p);
    }

    void visitProcImpl(ProcImpl* p) {

        add_proc_symbol(p); 
        m_st->open_scope();
        p->visit_children(this);
        p->m_attribute.m_scope = m_st->get_scope();
        // if (p->m_type != nullptr) {
        //     p->m_type->accept(this);
        // }
        check_proc(p);
        m_st->close_scope();
    }

    void visitCall(Call* p)
    {
        // m_st->open_scope();
        check_call(p);
        p->visit_children(this);
        // m_st->close_scope();
    }

    void visitNested_blockImpl(Nested_blockImpl* p)
    {
        m_st->open_scope();
        
        p->visit_children(this);
        m_st->close_scope();
    }

    void visitProcedure_blockImpl(Procedure_blockImpl* p)
    {
        for (auto& proc : *(p->m_proc_list)) {
            proc->accept(this);
        }
        
        for (auto& decl : *(p->m_decl_list)) {
            decl->accept(this);
        }

        for (auto& stat : *(p->m_stat_list)) {
            stat->accept(this);
        }

        if (p->m_return_stat) {
            p->m_return_stat->accept(this);
        }

        p->m_attribute.m_basetype = p->m_return_stat->m_attribute.m_basetype;
    }

    void visitDeclImpl(DeclImpl* p)
    {
        
        p->visit_children(this);
        // m_st->open_scope();
        add_decl_symbol(p);
        // m_st->close_scope();
    }

    void visitAssignment(Assignment* p)
    {
        p->visit_children(this);
        check_assignment(p);
    }

    void visitStringAssignment(StringAssignment *p)
    {
        p->visit_children(this);
        check_string_assignment(p);
    }

    void visitIdent(Ident* p)
    {
        p->visit_children(this);
        char* name = strdup(p->m_symname->spelling());
        if(!m_st->exist(name)) {
            this->t_error(var_undef, p->m_attribute);
        }
        p->m_attribute.m_basetype = m_st->lookup(name)->m_basetype;
    }

    void visitReturn(Return* p)
    {
        p->visit_children(this);
        check_return(p);
        p->m_attribute.m_basetype = p->m_expr->m_attribute.m_basetype;
    }

    void visitIfNoElse(IfNoElse* p)
    {
        p->m_expr->accept(this);

        check_pred_if(p->m_expr);

        p->m_nested_block->accept(this);
    }

    void visitIfWithElse(IfWithElse* p)
    {
        p->m_expr->accept(this);

        check_pred_if(p->m_expr);

        p->m_nested_block_1->accept(this);
        p->m_nested_block_2->accept(this);
    }

    void visitWhileLoop(WhileLoop* p)
    {
        p->m_expr->accept(this);

        check_pred_while(p->m_expr);

        p->m_nested_block->accept(this);
    }

    void visitCodeBlock(CodeBlock *p)
    {
        p->m_nested_block->accept(this);
    }

    void visitTInteger(TInteger* p)
    {
        p->m_attribute.m_basetype = bt_integer;
    }

    void visitTBoolean(TBoolean* p)
    {
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitTCharacter(TCharacter* p)
    {
        p->m_attribute.m_basetype = bt_char;
    }

    void visitTString(TString* p)
    {
        p->m_attribute.m_basetype = bt_string;
    }

    void visitTCharPtr(TCharPtr* p)
    {
        p->m_attribute.m_basetype = bt_charptr;
    }

    void visitTIntPtr(TIntPtr* p)
    {
        p->m_attribute.m_basetype = bt_intptr;
    }

    void visitAnd(And* p)
    {
        p->visit_children(this);
        checkset_boolexpr(p, p->m_expr_1, p->m_expr_2);
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitDiv(Div* p)
    {
        p->visit_children(this);
        checkset_arithexpr(p, p->m_expr_1, p->m_expr_2);
    }

    void visitCompare(Compare* p)
    {
        p->visit_children(this);
        checkset_equalityexpr(p, p->m_expr_1, p->m_expr_2);
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitGt(Gt* p) {
        p->visit_children(this);

        checkset_relationalexpr(p, p->m_expr_1, p->m_expr_2);
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitGteq(Gteq* p) {
        p->visit_children(this);
        checkset_relationalexpr(p, p->m_expr_1, p->m_expr_2);
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitLt(Lt* p) {
        p->visit_children(this);
        checkset_relationalexpr(p, p->m_expr_1, p->m_expr_2);
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitLteq(Lteq* p) {
        p->visit_children(this);
        checkset_relationalexpr(p, p->m_expr_1, p->m_expr_2);
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitMinus(Minus* p)
    {
        p->visit_children(this);
        checkset_arithexpr_or_pointer(p, p->m_expr_1, p->m_expr_2);
    }

    void visitNoteq(Noteq* p)
    {
        p->visit_children(this);
        checkset_equalityexpr(p, p->m_expr_1, p->m_expr_2);
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitOr(Or* p)
    {
        p->visit_children(this);
        checkset_boolexpr(p, p->m_expr_1, p->m_expr_2);
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitPlus(Plus* p)
    {
        p->visit_children(this);
        checkset_arithexpr_or_pointer(p, p->m_expr_1, p->m_expr_2);
    }

    void visitTimes(Times* p)
    {
        p->visit_children(this);
        checkset_arithexpr(p, p->m_expr_1, p->m_expr_2);
    }

    void visitNot(Not* p)
    {
        p->visit_children(this);
        checkset_not(p, p->m_expr);
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitUminus(Uminus* p)
    {
        p->visit_children(this);
        checkset_uminus(p, p->m_expr);
    }

    void visitArrayAccess(ArrayAccess* p)
    {
        p->visit_children(this);
        check_array_access(p);
    }

    void visitIntLit(IntLit* p) {
        p->m_attribute.m_scope = m_st->get_scope();  
        p->visit_children(this);  
        p->m_attribute.m_basetype = bt_integer;
    }

    void visitCharLit(CharLit* p)
    {
        // Make sure to set the current scope of every type  
        p->m_attribute.m_scope = m_st->get_scope();  
        // visit the children - this implicitly type-checks all   
        // of the children node of this node  
        p->visit_children(this);  
        // Set the type of this node  
        p->m_attribute.m_basetype = bt_char;
    }

    void visitBoolLit(BoolLit* p)
    {
        // Make sure to set the current scope of every type  
        p->m_attribute.m_scope = m_st->get_scope();  
        // visit the children - this implicitly type-checks all   
        // of the children node of this node  
        p->visit_children(this);  
        // Set the type of this node  
        p->m_attribute.m_basetype = bt_boolean;
    }

    void visitNullLit(NullLit* p)
    {
        // Make sure to set the current scope of every type  
        p->m_attribute.m_scope = m_st->get_scope();  
        // visit the children - this implicitly type-checks all   
        // of the children node of this node  
        p->visit_children(this);  
        // Set the type of this node  
        p->m_attribute.m_basetype = bt_ptr;
    }

    void visitAbsoluteValue(AbsoluteValue* p) {
        p->visit_children(this);
        checkset_absolute_value(p, p->m_expr);
    }


    void visitAddressOf(AddressOf* p) {
        p->visit_children(this);

        checkset_addressof(p, p->m_lhs);
    }


    void visitVariable(Variable* p)
    {
        checkset_variable(p);
    }

    void visitDeref(Deref* p) {
        p->visit_children(this);
        checkset_deref_expr(p, p->m_expr); 
    }

   void visitDerefVariable(DerefVariable* p) {
        p->visit_children(this);
        checkset_deref_lhs(p);
   }

    void visitArrayElement(ArrayElement* p) {
        p->visit_children(this);
        check_array_element(p);
    }

    // Special cases
    void visitPrimitive(Primitive* p) {}
    void visitSymName(SymName* p) {}
    void visitStringPrimitive(StringPrimitive* p) {}
};


void dopass_typecheck(Program_ptr ast, SymTab* st)
{
    Typecheck* typecheck = new Typecheck(stderr, st);
    ast->accept(typecheck); // Walk the tree with the visitor above
    delete typecheck;
}
