%------------------------------------------------------------------------------
% File     : ALG235-1 : TPTP v6.4.0. Released v4.0.0.
% Domain   : Algebra (Non-associative)
% Problem  : Short equational base for two varieties of groupoids - part 1a
% Version  : Especial.
% English  :

% Refs     : [Phi06] Phillips (2006), Short Equational Bases for Two Variet
%          : [PS08]  Phillips & Stanovsky (2008), Using Automated Theorem P
%          : [Sta08] Stanovsky (2008), Email to G. Sutcliffe
% Source   : [Sta08]
% Names    : P06_1a [Sta08]

% Status   : Unsatisfiable
% Rating   : 0.05 v6.4.0, 0.11 v6.3.0, 0.12 v6.2.0, 0.14 v6.1.0, 0.00 v6.0.0, 0.10 v5.5.0, 0.11 v5.4.0, 0.00 v5.2.0, 0.07 v5.0.0, 0.14 v4.1.0, 0.18 v4.0.1, 0.21 v4.0.0
% Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR)
%            Number of atoms       :    4 (   4 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    5 (   4 constant; 0-2 arity)
%            Number of variables   :   10 (   0 singleton)
%            Maximal term depth    :    6 (   4 average)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments :
%------------------------------------------------------------------------------
cnf(c01,axiom,
    ( mult(A,mult(B,mult(A,B))) = mult(A,B) )).

cnf(c02,axiom,
    ( mult(A,mult(B,mult(C,D))) = mult(C,mult(B,mult(A,D))) )).

cnf(c03,axiom,
    ( mult(mult(A,mult(B,mult(C,B))),D) = mult(A,mult(D,mult(mult(C,B),D))) )).

cnf(goals,negated_conjecture,
    ( mult(a,mult(b,mult(a,mult(c,mult(d,c))))) != mult(a,mult(b,mult(d,c))) )).

%------------------------------------------------------------------------------
