% This file implements a simple, sound but incomplete theorem prover
% for propositional logic. It uses a straightforward sequent calculus
% formulation with iteratively deepening depth-first search. It is
% hence unable to definitely conclude that a formula has no proof.
%
% The script defines three infix operators
%  a & b : conjunction
%  a + b : disjunction
%  a => b : implication
%
% The concrete syntax of formulas is given as
%
% A := a | A & A | A + A | A => A | top | bot
%
% Where "a" denotes atomic propositions that can be any constant. In
% addition to formulas, proof terms are also supported, with separate
% definitions for "checkable" proof terms M, and "synthesizable" proof
% terms R, defined as follows (see Pfenning's 2017 lecture notes on
% Constructive Logic).
%
% M ::= unit | pair(M,M) | fn(u,M) | inl(M) | inr(M)
%       | case(M, u, M, u, M) | abort(M) | R
% R ::= fst(R) | snd(R) | app(R, M)
%
% Where "u" denotes variable names.
%
% The following predicates are defined for outside use:
%
% prove(A) : Attempts to prove the proposition A
% provec(A, M) : Attempts to prove the proposition A and unifies M
%                with the associated proof term if successful.
%
% check(M, A) : Checks whether the given proof term M proves the proposition A
% synth(G, R, A) : Synthesizes a proposition A for the proof term R
%                  under the context G. The context is expected to
%                  contain labeled assumptions of the form lab(U,R).
%
% Some internal utilities are also defined to be used by other theorem
% prover implementations:
%
% ctx_pickleft(G, E, R) : picks an element E from the context G
%                         starting from the left, and unifies R with
%                         the remaining elements.
%
% rst_var : Resets the "fresh variable" counter.
% inc_var : Increments the "fresh variable" counter.
% get_var(V) : Unifies V with the current value of the "fresh variable" counter.
% newvar(VT) : Unifies VT with a new, freshly created variable term (u0, u1, ...)
%

:- op(150, yfx, [ & ]).
:- op(160, yfx, [ + ]).
:- op(170, xfy, [ => ]).

% --------- Theorem prover implementation --------------

% Attempts to prove the proposition A
prove(A) :- (write("Proving proposition "), write(A),
             set_limit(4), prove_iter(A), write(" : TRUE\n"));
            write(" : FALSE?\n").

% Performs iterative deepening DFS
prove_iter(A) :-
    set_cnt(0), % Initialize current depth count
    (
        prove( [], A ); % Attempt to construct a proof with the current limit
        inc_limit, get_limit( L ), L < 9, % Increase limit and retry
        %write('Trying with depth limit: '), write( L ), write('\n'),
        prove_iter( A )
    ).
        
% Top right rule
prove(_, top).



% Conjunction right rule
prove(G, A & B) :-prove(G,A), prove(G,B).

% Disjunction right rules
prove(G, A + _) :- prove(G,A).
prove(G, _ + B) :- prove(G,B).

% Implication right rule
prove(G, A => B) :- append(G, [A], GN), prove(GN, B).

% init rule
prove(G, A) :- member(A,G).

% prove_left(R,E,C) attempts to prove E,R --> C sequent by using left rule for E
prove(G, C) :- inc_cnt,
               ctx_pickleft(G, E, R),
               prove_left(R, E, C).


% Bot left rule I ADDED THIS BUT PROBABLY NECESSARY
prove_left(R, bot, C).

% Conjunction left rule
prove_left(R, A & B, C) :- append(R, [A, B], RN), prove(RN, C).

% Disjunction left rule
prove_left(R, A + B, C) :- append(R, [A], RN1), prove(RN1, C),
                           append(R, [B], RN2), prove(RN2, C).

% Implication left rule
prove_left(R, A => B, C) :- append(R, [A=>B], RN1), prove(RN1, A),
                            append(R, [B], RN2), prove(RN2, C).

% Top left rule MIGHT BE REDUNDANT
prove_left(R, top, C) :- prove(R, C).


% Proof checker ---------------------------------------
% Checks the proof term M agains the proposition A
check(M, A) :- check([], M, A).

% Input is G, M and A, output is provability
check(G, pair(M,N), A & B) :- check(G, M, A), check(G, N, B).
check(G, fn(U,M), A => B) :- append(G, [lab(U,A)], GN), check(GN, M, B).
check(G, inl(M), A + _) :- check(G, M, A).
check(G, inr(M), _ + B) :- check(G, M, B).
check(G, case(R, U, M, V, N), C) :-
    synth(G, R, A + B),
    append(G, [lab(U,A)], GN1), check(GN1, M, C),
    append(G, [lab(V,B)], GN2), check(GN2, N, C).
check(G, abort(R), _) :- synth(G, R, bot).
check(_, unit, top).
check(G, R, A) :- synth(G, R, A).

% Input is G and R, output is A
synth(G, fst(R), A) :- synth(G, R, A & _).
synth(G, snd(R), B) :- synth(G, R, _ & B).
synth(G, app(R, M), B) :- synth(G, R, A => B), check(G, M, A).
synth(G, U, A) :- member(lab(U,A),G).

% TOOLS -----------------------------------------------

% ctx_pickleft( L, E, R )
%
% This method picks an element E from the supplied multiset context L
% starting from the left and proceeding right, returns the rest in
% R. Does support backtracking, so this method can be used to cycle
% through all elements in a context from the left.
ctx_pickleft( [E | R], E, R ).
ctx_pickleft( [S | I], E, [S | R] ) :- ctx_pickleft( I, E, R ).

% =============== Depth counter and depth limit ==================

% Depth counter
set_cnt( V ) :- b_setval( prove_depth, V ).

inc_cnt :- 
    b_getval( prove_depth, V ), b_getval( prove_limit, L ), 
    VN is V + 1, VN < L,
    b_setval( prove_depth, VN ).

dec_cnt :- b_getval( prove_depth, V ), VN is V - 1, b_setval( prove_depth, VN ).

% Depth limit counter
set_limit( V ) :- nb_setval( prove_limit, V ).

get_limit( V ) :- nb_getval( prove_limit, V ).

inc_limit :-
    nb_getval( prove_limit, V ), VN is V + 1, nb_setval( prove_limit, VN ).

dec_limit :-
    nb_getval( prove_limit, V ), VN is V - 1, nb_setval( prove_limit, VN ).

% Fresh variable tools ------------------------
rst_var :- b_setval( newvar, 0 ).
inc_var :- nb_getval( newvar, V ), VN is V + 1, nb_setval( newvar, VN ).
get_var(V) :- nb_getval( newvar, V ).
newvar(VT) :- get_var( V ), inc_var, number_string(V,VS),
              string_concat("u",VS,VN), term_string(VT,VN).
              

% --------- TO BE FILLED ----------
% Template for the certifying theorem prover

pftestcert(A) :- provec(A,M), !, 
                 write('   Checking proof ... '),
                 (check(M,A), write('SUCCESS!\n');
                  write('FAIL-----------------------------------------------------------------------------------------------!\n'), fail).



provec(A,M) :- (write("Proving proposition "), write(A),rst_var,
             set_limit(6), provec_iter(A,M), write(" : TRUE\n")); % i increased the depth limit because one of the test cases were too deep.
            write(" : FALSE?\n").

% Performs iterative deepening DFS
provec_iter(A,M) :-
    set_cnt(0), % Initialize current depth count
    (
        provec2( [], M:A ); % Attempt to construct a proof with the current limit
        inc_limit, get_limit( L ), L < 9, % Increase limit and retry
        %write('Trying with depth limit: '), write( L ), write('\n'),
        provec_iter( A, MIGHT)
    ).

        
% Top right rule
% I used almost the same things as the lecture notes. I translated them into prolog. After that there were not much left.
% There is variable creation in disjunction left and implication left rules. So i used newvar inside them.
% Aside from that i used rst_var in provec function because instructions told me so.
% My implementation works because it is an exact copy of sequent calculus and,
% because of patter matching in prolog , prolog can add nested terms like app(u1, app(u2, u0)) while traversing the DFS.
% i needed to hold proof terms and their attached propositions together. So i needed a composite data type.
% I searched tuples a little bit in case my implementation would not work but turns out my implementation works fine.
% i used A:B as tuple. It was suprising that it worked nicely.
% i matched my proof terms according to "check", because syntax could differ. So i made syntax the same.
provec2(G, unit:top). 



% Conjunction right rule
provec2(G, pair(M,N) :A & B) :-provec2(G,M:A), provec2(G,N:B).

% Disjunction right rules
provec2(G, inl(M): A + B) :- provec2(G,M:A).
provec2(G, inr(N): A + B) :-provec2(G,N:B).

% Implication right rule
provec2(G, fn(U,M): A => B ) :- append(G, [U:A],  GN),newvar(U), provec2(GN, M:B).

% init rule
provec2(G, R:P) :- member(R:P,G).

% prove_left(R,E,C) attempts to prove E,R --> C sequent by using left rule for E
provec2(G, C) :- inc_cnt,
               ctx_pickleft(G, E, R),
               provec_left(R, E, C).


% Bot left rule I ADDED THIS BUT PROBABLY NECESSARY
provec_left(R, K:bot, abort(K):C).

% Conjunction left rule
provec_left(R, K:A & B, N:C) :- append(R, [fst(K):A, snd(K):B], RN), provec2(RN, N:C).

% Disjunction left rule
provec_left(R, K:A + B, case(K,U,M,V,N):C ) :- newvar(U), newvar(V),append(R, [U:A], RN1), provec2(RN1, M:C),
                           append(R, [V:B], RN2), provec2(RN2, N:C).

% Implication left rule
provec_left(R, K:A => B, N:C) :- append(R, [K:A=>B], RN1), provec2(RN1, M:A ),
                            append(R, [app(K,M):B], RN2), provec2(RN2, N:C).

% Top left rule 
provec_left(R, K:top, C) :- provec2(R, C).



pftest(A) :- pftestcert(A).

runtests :-
    pftest( a => a ), !,
    %pftest( a => b ), !,
    pftest( a => a+b ), !,
    pftest( a&b => b&a ), !,
    pftest( a+b => b+a ), !,
    pftest( a => (a=>b) => b ), !,
    pftest( ((a + (a => bot)) => bot) => bot), !,
    pftest( ((a&b)=>c) => (a => (b => c))), !,
    pftest( ((a => (b => c))=> (a&b)=>c)), !,
    pftest( ((a+b)=>c) => ((a=>c) & (b=>c))), !,
    %pftest( ((p=>q)=>bot) => (p&(q=>bot))), !,
    pftest( (p=>(r=>q)) => ((p&(q=>bot)) => (r=>bot))), !,
    pftest( p=>(b=>c)=> ((p=>b)=>c)), !, %a
    pftest( ((a1=>(a2=>b))=>c) => (((a1 & a2)=>b)=>c)), !, %b
    pftest( (b=>c)=>((top=>b)=>c)), !, %c
    pftest( ((a1=>b)=>((a2=>b)=>c))=>(((a1+a2)=>b)=>c)), !, %d
    pftest( c => ((bot=>b)=>c)), !, %e
    pftest( ((a2=>b)=>(a1=>a2))=>(b=>c)=>(((a1=>a2)=>b)=>c)), !, %f
    print("DONE").

