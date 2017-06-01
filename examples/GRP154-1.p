%--------------------------------------------------------------------------
% File     : GRP154-1 : TPTP v6.4.0. Bugfixed v1.2.1.
% Domain   : Group Theory (Lattice Ordered)
% Problem  : Prove monotonicity axiom using the LUB transformation
% Version  : [Fuc94] (equality) axioms.
% English  : This problem proves the original mononicity axiom from the
%            equational axiomatization.

% Refs     : [Fuc94] Fuchs (1994), The Application of Goal-Orientated Heuri
%          : [Sch95] Schulz (1995), Explanation Based Learning for Distribu
% Source   : [Sch95]
% Names    : ax_mono1a [Sch95]

% Status   : Unsatisfiable
% Rating   : 0.05 v6.3.0, 0.12 v6.2.0, 0.14 v6.1.0, 0.06 v6.0.0, 0.10 v5.5.0, 0.05 v5.4.0, 0.00 v5.1.0, 0.07 v5.0.0, 0.14 v4.1.0, 0.18 v4.0.1, 0.14 v4.0.0, 0.15 v3.7.0, 0.11 v3.4.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   17 (   0 non-Horn;  17 unit;   2 RR)
%            Number of atoms       :   17 (  17 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    8 (   4 constant; 0-2 arity)
%            Number of variables   :   33 (   2 singleton)
%            Maximal term depth    :    3 (   2 average)
% SPC      : CNF_UNS_RFO_PEQ_UEQ

% Comments : ORDERING LPO inverse > product > greatest_lower_bound >
%            least_upper_bound > identity > a > b > c
%          : ORDERING LPO greatest_lower_bound > least_upper_bound >
%            inverse > product > identity > a > b > c
% Bugfixes : v1.2.1 - Duplicate axioms in GRP004-2.ax removed.
%--------------------------------------------------------------------------
%----Include equality group theory axioms
include('Axioms/GRP004-0.ax').
%----Include Lattice ordered group (equality) axioms
include('Axioms/GRP004-2.ax').
%--------------------------------------------------------------------------
cnf(ax_mono1a_1,hypothesis,
    ( least_upper_bound(a,b) = b )).

cnf(prove_ax_mono1a,negated_conjecture,
    (  least_upper_bound(multiply(a,c),multiply(b,c)) != multiply(b,c) )).

%--------------------------------------------------------------------------
