%    The contents of this file are subject to the Mozilla Public License
%    Version  1.1  (the "License"); you may not use this file except in
%    compliance with the License. You may obtain a copy of the License at:
%
%    http://www.mozilla.org/MPL/
%
%    Software  distributed  under  the License is distributed on an "AS
%    IS"  basis,  WITHOUT  WARRANTY  OF  ANY  KIND,  either  express or
%    implied.
%
% Purpose: TRY TO GET A DECOMPOSED FORMULA BY USING ONE THREE TECHNIQUES
% Author : Nicolas Beldiceanu, Ramiz Gindullin, IMT Atlantique

:- module(gen_decomp_formula,[search_diffs_decompositions/18,
                              search_unary_decompositions/18,
                              search_conds_decompositions/18]).

:- use_module(library(timeout)).
:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(tables).
:- use_module(table_access).
:- use_module(gen_formula).
:- use_module(gen_options_for_formulae).
:- use_module(utility).
:- use_module(bool_cond_utility).
:- use_module(gen_formula_term).
:- use_module(eval_formula).
:- use_module(gen_formula_write). %TO REMOVE

% search for a decomposition wrt the output column ColOutput of current table Table and wrt a functional dependency Fd: we isolate one input parameter,
% put it in a unary function and combine it with a formula that needs to be acquired;
% (assumes that the entries of the table Table and the corresponding metadata are already loaded; do not reclaim table entries);
% FoundDecomposition is a term of the form
% t(BinaryFunctionType: binary function used in the decomposition (that link the unary function with the formula to find)
%   UnaryFunctionType : unary function that is applied to the isolated input parameter
%   Coefs          : coefficients used within the unary function
%   MaxSlack          : 0 if do not use any slack, 1 if use a 0..1 slack (in this later case we also have to find a boolean formula)
%   Clusters          : clusters of the projected table
%   Vars           : give for each cluster the "output value" of the formula that the caller will try to find
%   NewRest           : input parameters of the formula that we will try to identify
%   FlatSlacks        : give for each table entry the "output value" of the boolean formula the caller will try to find (relevant only when MaxSlack=1)
%   NewRestSlacks)    : input parameters of the boolean formula we will try to identify
%------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
search_unary_decompositions(KindCombi, CallMap, Fd, Table, Col, OptionsBoolCond, TableEntries, ParamsList, _ColSetsBool, _OutputMin, _OutputMax,
                            Mode, CurMaxCost, Cost, Result, FormulaFamily, FormulaPattern, OptionUsedToGenerateConjecture) :-
    select(Isolate, Fd, Rest),                                      % select an input parameter that will be isolated (on backtrack get next candidate)
    tab_get_type(Isolate, TypeIsolate),                             % get type (cst, bool, int) of input parameter that will be isolated
    (TypeIsolate = cst -> write(search_decompositions), nl, halt ; true), % abort if constant, as an input param. of a minimal func.dep.should not be a constant
    % collect all valid decomposition candidates:
    search_all_unary_decompositions(TableEntries, ParamsList, Rest, Isolate, FoundDecompositionList),
    sort(FoundDecompositionList, FoundDecompositionListSorted),     % sort candidates by increasing cost of the unary component
    length(FoundDecompositionListSorted, LenFoundDecompositionList),
    TopLimit is min(LenFoundDecompositionList, 3),                  % we only consider at most first 4 candidates for decomposition
    prefix_length(FoundDecompositionListSorted, PrefixFoundDecompositionList, TopLimit),
    %member([_,_,FoundDecomposition, FlatSlacks], PrefixFoundDecompositionList), % select a decomposition candidate % TO RESTORE
    I in 1..TopLimit, indomain(I), nth1(I, PrefixFoundDecompositionList, [_,_,FoundDecomposition, FlatSlacks]), % TO REMOVE
    FoundDecomposition = t(BinaryFunctionType, UnaryFunctionType, CostUnary, MaxSlack,  % read the information about the decomposition
                           UnaryFunctionTerm, OpBinary1, Clusters, Vars, Shift),
    % if we use a binary operation with revered positions use a correct operation
    (OpBinary1 = rfloor -> OpBinary = floor     ;
     OpBinary1 = rceil  -> OpBinary = ceil      ;
                           OpBinary = OpBinary1 ),
    UnaryFunctionTerm = t(_,_,_,UnaryTerm),
    FormulaPatternUnary = UnaryFunctionTerm,    % use generated term as a formula pattern
    % generate table entries for the Rest part of the decomposition
    (foreach(ClusterVar-_, Clusters), foreach(Var, Vars), foreach(TableEntryVar, TableEntriesRest)
    do
     append(ClusterVar, [Var], TableEntryVar)
    ),
    (user:max_cost(Max) -> true ; Max = CurMaxCost),    
    CurMaxCostRest is Max - CostUnary,          % update the max cost for the rest part of the decomposition
    ForceToUseOnlySmallFd = 1,
    %write(d1),nl,
    formula_generator_base(KindCombi, CallMap, Table, Col, OptionsBoolCond, Vars, MaxSlack, TableEntriesRest, ParamsList, Rest, 0, CurMaxCostRest, ForceToUseOnlySmallFd,
                           Mode, RestMin, _RestMax, _FdRest, CostRest, _Penalty, FormulaFamilyRest, OptionUsedToGenerateConjectureRest, FormulaPatternRest),
    %write(d2(MaxSlack)),nl,
    /*
    min_member(RestMin, Vars),
    max_member(RestMax, Vars),                  % find minimum and maximum values of rest values
    (RestMin = RestMax ->                       % if TableEntriesRest can be expressed as an equivalent to a constant
         %TypeRest = 0,
         CostRest is abs(RestMin),
         FormulaFamilyRest = cst,
         OptionUsedToGenerateConjectureRest = [cst],
         InputColsList = [],
         InputNamesList = [],
         InputVarsList = [],
         FormulaTermRest = RestMin,
         FormulaPatternRest = t(InputColsList, InputNamesList, InputVarsList, FormulaTermRest)
    ;
     check_base_eq_output(TableEntriesRest, Rest, RestCol) -> % if TableEntriesRest can be expressed as equivalent to an input column
         %TypeRest = 0,
         CostRest = 1,
         FormulaFamilyRest = col,
         OptionUsedToGenerateConjectureRest = [eq_col],
         tab_get_name(RestCol, RestName),
         InputColsList = [RestCol],
         InputNamesList = [RestName],
         InputVarsList = [RestVar],
         FormulaTermRest = RestVar,
         FormulaPatternRest = t(InputColsList, InputNamesList, InputVarsList, FormulaTermRest)
    ;                                          % otherise call formula_generator proper and find a solution
         %TypeRest = 1,
         (MaxSlack = 1 ->  % if there's slack then we can use a subset of Rest columns
              find_split_fd(Rest, TableEntriesRest, ParamsList, Vars, FdRestList)
         ;                 % if no slack then we have to use all Rest columns
              FdRestList = [Rest]
         ),
         % to ensure reasonable performance we take only the first successful solution we use once/1
         once((member(FdRest, FdRestList),                      % select a functional dependency
               (FdRest = Rest ->
                    TableEntriesRestFd = TableEntriesRest
               ;
                    append(FdRest, [col(Table, Col)], AttrNamesOutput),
                    append(Rest,   [col(Table, Col)], ParamsOutput),
                    % firstly - collect column indices within AttrNamesOutput
                    match_list_indices_sublist(ParamsOutput, AttrPos, AttrNamesOutput), % get positions AttrPos of input columns
                    % secondly - use collected column indices AttrPos to extract relevant table entries
                    (foreach(TableEntryPassed, TableEntriesRest), foreach(TableEntryRest, TableEntriesRestFd), param(AttrPos)
                    do
                     match_list_indices_sublist(TableEntryPassed, AttrPos, TableEntryRest)
                    )
               ),
               ModeRest = preprocessed(RestMin, RestMax, 0, 1),       % select the preprocessed mode. Set 0 to Boolean formulae w/o restrictions 
               ForceToUseOnlySmallFd = 1,
               % generate lists of options for the rest part of the decomposition
               gen_options_lists_decomp_base(KindCombi, col(Table,Col), secondary, OptionsBoolCond, [], FdRest, ForceToUseOnlySmallFd,
                                             TableEntriesRestFd, ModeRest, ListsOptionsRest, SetsBoolRest),
               % search for the formula by calling formula_generator
               TimeOutRest = 3600000,
               time_out(formula_generator(CallMap, KindCombi, OptionsBoolCond, ListsOptionsRest, TableEntriesRestFd, ModeRest, SetsBoolRest,
                                          RestMin, secondary, Table, Col, CurMaxCostRest, FormulaPatternRest,
                                          FormulaFamilyRest, OptionUsedToGenerateConjectureRest, CostRest1, ResultRest),
                        TimeOutRest, success),
               ResultRest \== time_out,
               select_penalty(FormulaFamilyRest, OptionUsedToGenerateConjectureRest, Penalty),
               CostRest is CostRest1 + Penalty
              )
             )
    ),*/
    CostRest =< CurMaxCostRest,
    (MaxSlack = 1 ->    % if there is a slack part of the decomposition then search for the formula that explains it
         min_member(FlatSlacksMin, FlatSlacks),                                 
         max_member(FlatSlacksMax, FlatSlacks),                                 % select minimums and maximums values of the slack part of the decomposition
         (FlatSlacksMin < FlatSlacksMax ->
              find_split_fd(Fd, TableEntries, ParamsList, FlatSlacks, FdSlackList),  % generate the list of potential functional dependencies
              member(FdSlack, FdSlackList),                                          % select one of the fds
              ModeSlack = preprocessed(FlatSlacksMin, FlatSlacksMax, 0, 0),          % select the preprocessed mode. Set 0 to Boolean formulae w/o restrictions
              match_list_indices_sublist(ParamsList, AttrPos, FdSlack), 
              (foreach(TableEntry,TableEntries), foreach(FlatSlack, FlatSlacks),     % generate table entries corresponding to the slack part of
               foreach(TableEntrySlack, TableEntriesSlackUnsorted), param(AttrPos)   % the decomposition and selected functional dependency
              do
               match_list_indices_sublist(TableEntry, AttrPos, TableEntryFd),
               append(TableEntryFd, [FlatSlack], TableEntrySlack)
              ),
              sort(TableEntriesSlackUnsorted, TableEntriesSlack),                    % remove duplicates from table entries
              % generate the list of options for the slack part of the decomposition
              gen_options_lists_decomp_diff(KindCombi, col(Table,Col), secondary, OptionsBoolCond, [], FdSlack, ForceToUseOnlySmallFd,
                                            TableEntriesSlack, ModeSlack, ListsOptionsSlack, SetsBoolSlack),
              % search for the formula by calling formula_generator
              formula_generator(CallMap, KindCombi, OptionsBoolCond, ListsOptionsSlack, TableEntriesSlack, ModeSlack, SetsBoolSlack,
                                FlatSlacksMin, secondary, Table, Col, CurMaxCostRest, FormulaPatternSlack,
                                FormulaFamilySlack, OptionUsedToGenerateConjectureSlack, CostSlack, ResultSlack)
         ;
              FormulaPatternSlack = t([],[],[], FlatSlacksMin),
              FormulaFamilySlack = cst,
              OptionUsedToGenerateConjectureSlack = [cst],
              CostSlack is abs(FlatSlacksMin),
              ResultSlack = success
         ),
         ResultSlack \== time_out,
         % after both rest and slack parts of the decomposition are found:
         Result = success,                                      % select the success flag of the search
         Cost is CostSlack + CostRest + CostUnary,              % calculate the cost of the complete formula
         (user:max_cost(Max2) -> true ; Max2 = CurMaxCost),
         Cost in 0..Max2,                                       % ensure that the total cost doesn't exceed the current maximum
         FormulaFamily = families([unary_template([binary(BinaryFunctionType),   % formula family for the complete decomposition
                                                   unary(UnaryFunctionType)]),
                                   slack(FormulaFamilySlack),
                                   rest(FormulaFamilyRest)]),
         OptionUsedToGenerateConjecture = decomp(binary_op(OpBinary1),  % a list of options used to generate all parts of the decomposition 
                                                 [unary_template(UnaryTerm),
                                                  slack(OptionUsedToGenerateConjectureSlack),
                                                  rest(OptionUsedToGenerateConjectureRest)]),
         % generate the decomposition formula pattern
         %FormulaFamilyRest = cst,
         %RestMin
         ((FormulaFamilyRest = cst, OpBinary1 = plus,
           RestMin = 0) ->                                      % if add 0, we can simplify the pattern
              FormulaPatternC = [decomp(plus, FormulaPatternUnary, FormulaPatternSlack)]
         ;
          (FormulaFamilyRest = cst, memberchk(OpBinary1, [prod, floor, ceil]),
           RestMin = 1) ->                                      % if divide or multiply by 1, we can simplify the pattern
              FormulaPatternC = [decomp(plus, FormulaPatternUnary, FormulaPatternSlack)]
         ;
          (FormulaFamilyRest = cst, memberchk(OpBinary1, [prod, floor, ceil]),
           RestMin = -1) ->                                     % if divide or multiply by 1, we put Rest part first
              FormulaPatternC = [decomp(prod,                    % as multiplication for better readability of the final formula
                                        FormulaPatternRest,
                                        [decomp(plus, FormulaPatternUnary, FormulaPatternSlack)])]
         ;
          (FormulaFamilyRest = cst, OpBinary1 = prod) ->        % if we multiply by a cst we place cst first
              FormulaPatternC = [decomp(OpBinary,
                                        FormulaPatternRest,
                                        [decomp(plus, FormulaPatternUnary, FormulaPatternSlack)])]
         ;
          memberchk(OpBinary1, [rfloor, rceil]) ->              % binary operations where we place Rest part first
              FormulaPatternC = [decomp(OpBinary,
                                        FormulaPatternRest,
                                        [decomp(plus, FormulaPatternUnary, FormulaPatternSlack)])]
         ;                                                      % by default, the Rest part of the binary operation is placed second 
              FormulaPatternC = [decomp(OpBinary,
                                        [decomp(plus, FormulaPatternUnary, FormulaPatternSlack)],
                                        FormulaPatternRest)]
         )
    ;    % after the rest part of the decomposition is found:
         Result = success,                                      % select the success flag of the search
         Cost is CostRest + CostUnary,                          % calculate the cost of the complete formula
         (user:max_cost(Max2) -> true ; Max2 = CurMaxCost),
         Cost in 0..Max2,                                       % ensure that the total cost doesn't exceed the current maximum
         FormulaFamily = families([unary_template([binary(BinaryFunctionType),   % formula family for the complete decomposition
                                                   unary(UnaryFunctionType)]),
                                   rest(FormulaFamilyRest)]),
         OptionUsedToGenerateConjecture = decomp(binary_op(OpBinary1),  % a list of options used to generate all parts of the decomposition
                                                 [unary_template(UnaryTerm),
                                                  rest(OptionUsedToGenerateConjectureRest)]),
         % generate the decomposition formula pattern
         ((FormulaFamilyRest = cst, OpBinary1 = plus,
           RestMin = 0) ->                                      % if add 0, we can simplify the pattern
              FormulaPatternC = FormulaPatternUnary
         ;
          (FormulaFamilyRest = cst, memberchk(OpBinary1, [prod, floor, ceil]),
           RestMin = 1) ->                                      % if multiply or divide by 1, we can simplify the pattern
              FormulaPatternC = FormulaPatternUnary
         ;
          (FormulaFamilyRest = cst, memberchk(OpBinary1, [prod, floor, ceil]),
           RestMin = -1) ->                                     % if multiply or divide by -1, we can simplify the pattern
              FormulaPatternC = [decomp(prod, FormulaPatternRest, FormulaPatternUnary)]
         ;
          (FormulaFamilyRest = cst, OpBinary1 = prod) ->        % if we multiply by a cst we, we put Rest part first
              FormulaPatternC = [decomp(prod,                    % as multiplication for better readability of the final formula
                                        FormulaPatternRest, FormulaPatternUnary)]
         ;
          memberchk(OpBinary1, [rfloor, rceil]) ->
              FormulaPatternC = [decomp(OpBinary, FormulaPatternRest, FormulaPatternUnary)]
         ;
              FormulaPatternC = [decomp(OpBinary, FormulaPatternUnary, FormulaPatternRest)]
         )
    ),
    (Shift = 0 ->
         FormulaPattern = FormulaPatternC
    ;
     Shift > 0 ->
         FormulaPattern = [decomp(plus,  FormulaPatternC, t([],[],[],Shift))]
    ;
         ShiftAbs is abs(Shift),
         FormulaPattern = [decomp(minus, FormulaPatternC, t([],[],[],ShiftAbs))]
    ),
    %TO REMOVE start
    /*write(decomp_success(I,TopLimit)),nl,
    (foreach([_,_,T,_], FoundDecompositionListSorted)
    do
     arg(6, T, OB), arg(5, T, TC), arg(4, T, MS), arg(3, T, CostC), arg(2, T, UF),
     write([CostC,OB-UF,MS,TC]),nl),
    (TypeRest = 1 -> write(rest(FdRest-FdRestList)),nl ; true ),
    (MaxSlack = 1 -> write(slack(FdSlack-FdSlackList)),nl ; true ),*/
    %TO REMOVE end
    !. % after a solution is found, we stop looking for alternative decompositions

% collect all possible unary decompositions
search_all_unary_decompositions(TableEntries, ParamsList, Rest, Isolate,FoundDecompositionList) :-
    tab_get_min_max(Isolate, MinIsolate, MaxIsolate),               % get minimum and maximum value of input parameter that will be isolated
    MaxSlack in 0..1,                                               % 0: no slack, 1: slack values of 0..1
    BinaryFunctionType in 1..8,                                     % 1:+,  2:*,  3:min,  4:max,  5:floor,  6:ceil, 7:rfloor, 8:rceil
    UnaryFunctionType in 0..9,                                      % 0: Ax^2+Bx+C        1:floor(Ax^2+Bx,C), 2:ceil(Ax^2+Bx,C),
                                                                    % 3:min(A*x+B,C),     4:max(A*x+B,C),
                                                                    % 5:(Ax+B)mod C,      6:|Ax+B|,
                                                                    % 7:((x+A)mod B)=C,   8:((x+A)mod B)>=C,  9:((x+A)mod B)=<C
    % generate the list of possible combinations of MaxSlack, BinaryFunctionType and UnaryFunctionType
    findall([MaxSlack, BinaryFunctionType, UnaryFunctionType],
            (indomain(MaxSlack),
             indomain(BinaryFunctionType),
             indomain(UnaryFunctionType)),
            MaxSlackBinaryUnaryTypesList),
    UnaryVar = _,                                                   % all found unary terms must use the same variable 
    iterate_maxslack_binary_unary_types(MaxSlackBinaryUnaryTypesList,
                                        TableEntries, ParamsList, Isolate, Rest, MinIsolate, MaxIsolate, UnaryVar,
                                        FoundDecompositionList).

% for each MaxSlack, BinaryFunctionType and UnaryFunctionType combination:
% 1. generate clusters correspomding to isolated input values
% 2. generate and solve a constraint model to determine coefficients for the selected binary and unary functions:
%   - if it's successful then record the information about the decomposition
%   - if it's unsuccessful then do nothing
% 3. move to the next combination 
iterate_maxslack_binary_unary_types([], _, _, _, _, _, _, _, []) :- !.
iterate_maxslack_binary_unary_types([[MaxSlack, BinaryFunctionType, UnaryFunctionType]|R],
                                    TableEntries, ParamsList, Isolate, Rest, MinIsolate, MaxIsolate, UnaryVar,
                                    FoundDecompositionList):-
    extract_new_targets(TableEntries, ParamsList, Rest,
                        Isolate, NewTableEntries, FlatSlacks),      % extract pairs of the form t(non isolated input values)-t(isolate value,output value)
    sort(NewTableEntries, SortedNewTargets),                        % sort pairs wrt non isolated input values
    build_clusters(SortedNewTargets, Clusters, LSlacks),            % build cluster wrt projection where each cluster corresponds to non isolated input values
    (search_unary_function(Clusters, FlatSlacks, LSlacks, MaxSlack, % generate and solve a corresponding constraint model
                           BinaryFunctionType, UnaryFunctionType,
                           t(UnaryVar,Isolate,MinIsolate,MaxIsolate),
                           FoundDecomposition) ->
         arg(3,FoundDecomposition,CostUnaryCandidate),
         FoundDecompositionList = [[CostUnaryCandidate,MaxSlack,FoundDecomposition,FlatSlacks]|S]
         
    
    ;
         FoundDecompositionList = S
    ),
    iterate_maxslack_binary_unary_types(R,
                                        TableEntries, ParamsList, Isolate, Rest, MinIsolate, MaxIsolate, UnaryVar,
                                        S).

% reformat table entries wrt the isolated column 
extract_new_targets(TableEntries, ParamsList, Rest, IndIsolate, NewTableEntries, VarSlacks) :-
    % firstly - collect column indices within AttrNamesOutput
    match_list_indices_sublist(ParamsList, AttrPos, [IndIsolate|Rest]), % get positions AttrPos of input columns
    % secondly - use collected column indices AttrPos to extract relevant table entries
    (foreach(TableEntry, TableEntries), foreach(VarSlack, VarSlacks),
     foreach([NewTarget,t(ValIsolate,ValOutput),VarSlack], NewTableEntries),
     param([AttrPos, IndIsolate])
    do
     last(TableEntry, ValOutput),
     match_list_indices_sublist(TableEntry, AttrPos, [ValIsolate|NewTarget])
    ).

% generate clusters wrt isolated column
build_clusters([], [], []) :- !.                                          % as the list was sorted on the term corresponding to the non-isolated input parameters (see Key), scan this list
build_clusters([[Key,Term,Slack]|R], [Key-ClusterElems|S], [LSlack|T]) :- % to build the clusters associated with adjacent elements of the list which have the same key value
    build_cluster([[Key,Term,Slack]|R], Key, ClusterElems, LSlack, Rest),
    build_clusters(Rest, S, T).

build_cluster([[Key,Term,Slack]|R], Key, [Term|S], [Slack|T], Rest) :- !,   % extract all elements associated with the cluster whose key is Key
    build_cluster(R, Key, S, T, Rest).
build_cluster(SortedTargets, _, [], [], SortedTargets).

% try to isolate one parameter that will be used as an argument of a unary function;
% that is try to create a decomposition of the form f_decomposition_type(f_unary_function_type(Isolated Input Parameter), formula to identify)
%------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
search_unary_function(Clusters, FlatSlacks, LSlacks, MaxSlack, BinaryFunctionType, UnaryFunctionType, t(X,Isolate,MinIsolate,MaxIsolate), FoundDecomposition) :-
    maximum(MaxSlack, FlatSlacks),
    Cost in 0..100,
    length(Coefs, 4),                                                 % will use at most three coefficients in the decomposition (unused coefficients will be fixed to 0)
    domain(Coefs, -2, 2),                                             % create a small domain for the coefficients as look to "simple" formulae
    TimeOut = 5000,                                                   % needed as very rarely we come up on a combination of constraints
                                                                      % which propagate extremely poorly (e.g. sometime the reformulation of ceil)
    time_out(minimize(search_unary_function(Clusters, FlatSlacks, LSlacks, Cost, Coefs, % search for the simplest decomposition
                                            BinaryFunctionType, UnaryFunctionType,      % (the cost is the sum of the absolute value of its coefficients)
                                            MaxSlack, MinIsolate, MaxIsolate, Vars), Cost), TimeOut, Result),
    (Result \== time_out ->
        %search_minimal_fd(Clusters, Vars, Rest, NewRest),             % after the simplification, NewRest contains the remaining input parameters
        tab_get_name(Isolate,IsolateName),
        Coefs = [Shift, A, B, C],
        InputColsList =  [Isolate],
        InputNamesList = [IsolateName],
        InputVarsList =  [X],
        (memberchk(BinaryFunctionType-OpBinary,                       % select a corresponding binary operation
                   [1-plus,  2-prod, 3-min,    4-max,
                    5-floor, 6-ceil, 7-rfloor, 8-rceil]) ->
             true
        ;
             write(decompose_search_unary_function1),nl,halt
        ),
        % generate corresponding formula term
        (UnaryFunctionType = 0  -> FormulaTerm = plus(plus(prod(A,power(X,2)),prod(B,X)),C)     ;
         UnaryFunctionType = 1  -> FormulaTerm = floor(plus(prod(A,power(X,2)),prod(B,X)),C)    ;
         UnaryFunctionType = 2  -> FormulaTerm = ceil(plus(prod(A,power(X,2)),prod(B,X)),C)     ;
         UnaryFunctionType = 3  -> FormulaTerm = min(plus(prod(A,X),B),C)                       ;
         UnaryFunctionType = 4  -> FormulaTerm = max(plus(prod(A,X),B),C)                       ;
         UnaryFunctionType = 5  -> FormulaTerm = mod(plus(prod(A,X),B),C)                       ;
         UnaryFunctionType = 6  -> FormulaTerm = abs(plus(prod(A,X),B))                         ;
         UnaryFunctionType = 7  -> FormulaTerm = eq(mod(plus(A,X),B),C)                         ;
         UnaryFunctionType = 8  -> FormulaTerm = geq(mod(plus(A,X),B),C)                        ;
         UnaryFunctionType = 9  -> FormulaTerm = leq(mod(plus(A,X),B),C)                        ;
                                   write(decompose_search_unary_function2),nl,halt              ),
        simplify_term(FormulaTerm, FormulaTermSimplified),      % if possible, simplify the term
        UnaryFunctionTerm = t(InputColsList, InputNamesList, InputVarsList, FormulaTermSimplified),
        FoundDecomposition = t(BinaryFunctionType, UnaryFunctionType, Cost, MaxSlack, UnaryFunctionTerm, OpBinary, Clusters, Vars, Shift)
     ;                                                          % fail if cound not find a decomposition wrt parameter that was selected to be isolated
        false
    ).

% generate the complete constraint model and solve it
search_unary_function(Clusters, FlatSlacks, LSlacks, Cost, Coefs, BinaryFunctionType, UnaryFunctionType, MaxSlack, MinIsolate, MaxIsolate, Vars) :-
    set_unary_cost_constraint(UnaryFunctionType, Cost, Coefs),              % depending on the coefficients used in the decomposition build the cost
    search_unary_function(Clusters, LSlacks,
                          BinaryFunctionType, UnaryFunctionType,        % iterate over the different clusters to post the constraints related to the decomposition
                          MaxSlack, MinIsolate, MaxIsolate, Coefs, Vars),
    /*memberchk(BinaryFunctionType-OpBinary,
                [1-plus,  2-prod, 3-min,    4-max,
                5-floor, 6-ceil, 7-rfloor, 8-rceil])*/
    (BinaryFunctionType = 1 ->                  % we don't add 0 (as the decomposition can be expressed by using prod binary function)
         maximum(VarsMax, Vars),
         minimum(VarsMin, Vars),
         VarsMax #=  0 #=> VarsMin #\=  0
    ;
     memberchk(BinaryFunctionType, [5,6]) ->    % we don't divide by +1 or -1 (as the decomposition can be expressed by using prod binary function)
         maximum(VarsMax, Vars),
         minimum(VarsMin, Vars),
         VarsMax #=  1 #=> VarsMin #\=  1,
         VarsMax #= -1 #=> VarsMin #\= -1
    ;
         true
    ),
    (foreach(Coef, Coefs)                                             % label Coefs variables in a way that we check
    do                                                                % 0, +1, -1, +2, -2,... first
     fd_min(Coef, MinCoef), fd_max(Coef, MaxCoef),
     MaxVal is max(abs(MinCoef), abs(MaxCoef)), 
     CoefAbs in 0..MaxVal,
     CoefAbs #= abs(Coef),
     labeling([up],   [CoefAbs]),
     labeling([down], [Coef])                                         % try to find a value for each coefficient
    ),
    (foreach(Var, Vars)                                               % label Vars variables in a way that we check
    do                                                                % 0, +1, -1, +2, -2,... first
     fd_min(Var, MinVar), fd_max(Var, MaxVar),
     VarAbsMax is max(abs(MinVar), abs(MaxVar)), 
     VarAbs in 0..VarAbsMax,
     VarAbs #= abs(Var),
     labeling([up],   [VarAbs]),
     labeling([down], [Var])                                          % try to find a value for each Var
    ),
    once(labeling([], FlatSlacks)).                                   % FlatSlacks (as we do a check get only one solution by using once)

% iterate over the element of a cluster to set up the constraints associated with the decomposition
search_unary_function([], [], _, _, _, _, _, _, []) :- !.
search_unary_function([_Key-ClusterElems|R], [LSlack|S], BinaryFunctionType, UnaryFunctionType, MaxSlack, MinIsolate, MaxIsolate, Coefs, [Var|T]) :-
    Var in -10000..10000,                                             % variable corresponding to all entries of current cluster
    Coefs = [Shift, A, B, C],
    (UnaryFunctionType = 0 -> A #\= 0 #\/ B #\= 0                                                       ;
     UnaryFunctionType = 1 -> A #\= 0 #\/ B #\= 0,
                              A #>= 0 #/\ B #>= 0,
                              C #> 1,
                              A #= 0 #=> ((B #> 0) #/\ ((B mod C) #\= 0)),
                              B #= 0 #=> ((A #> 0) #/\ ((A mod C) #\= 0)),
                              ((A #> 0) #/\ (B #> 0)) #=> (((A mod C) #\= 0) #\/ ((B mod C) #\= 0))     ;
     UnaryFunctionType = 2 -> A #\= 0 #\/ B #\= 0,
                              A #>= 0 #/\ B #>= 0,
                              C #> 1,
                              A #= 0 #=> ((B #> 0) #/\ ((B mod C) #\= 0)),
                              B #= 0 #=> ((A #> 0) #/\ ((A mod C) #\= 0)),
                              ((A #> 0) #/\ (B #> 0)) #=> (((A mod C) #\= 0) #\/ ((B mod C) #\= 0))     ;
     UnaryFunctionType = 3 -> A #> 0,
                              abs(A)+abs(B)+abs(C) #< 5,
                              A #= 0 #\/ B #= 0 #\/ C #= 0,
                              C #> MinIsolate*A + B,
                              C #< MaxIsolate*A + B                                                     ;
     UnaryFunctionType = 4 -> A #> 0,
                              abs(A)+abs(B)+abs(C) #< 5,
                              A #= 0 #\/ B #= 0 #\/ C #= 0,
                              C #> MinIsolate*A + B,
                              C #< MaxIsolate*A + B                                                     ;
     UnaryFunctionType = 5 -> A #> 0, C #= 2,
                              A #=< C,
                              A*MinIsolate+B #< C,
                              A*MaxIsolate+B #> C,
                              (A mod C) #\= 0, (B mod C) #\= 0                                          ;
     UnaryFunctionType = 6 -> ((MinIsolate = 0, MaxIsolate=1) -> false ; true),
                              C = 0,
                              A #\= 0,
                              B #\= 0,
                              A #> 0 #/\ B #< 0,
                              (MinIsolate*A + B)*(MaxIsolate*A + B) #< 0                                ;
     UnaryFunctionType = 7 -> B #> 1,
                              A #= 0 #/\ B #= 1 #=> C #> MinIsolate #/\ C #< MaxIsolate,
                              C #>=0, C#< B,
                              B #= 1 #=> A #= 0,
                              MaxIsolate+A #> B,
                              A #< B                                                                    ;
     UnaryFunctionType = 8 -> B #> 1,
                              A #= 0 #/\ B #= 1 #=> C #> MinIsolate #/\ C #< MaxIsolate,
                              C #>=1, C#< B - 1,
                              B #= 1 #=> A #= 0,
                              MaxIsolate+A #> B,
                              A #< B                                                                    ;
     UnaryFunctionType = 9 -> B #> 1,
                              A #= 0 #/\ B #= 1 #=> C #> MinIsolate #/\ C #< MaxIsolate,
                              C #>=1, C#< B - 1,
                              B #= 1 #=> A #= 0,
                              MaxIsolate+A #> B,
                              A #< B                                                                    ;
                              write(search_unary_function1), nl, halt                                   ),
    (memberchk(BinaryFunctionType, [1,3,4]) -> Shift #= 0 ; true),
    post_ctr_wrt_unary_and_binary_functions_of_the_decomposition(ClusterElems, LSlack, BinaryFunctionType, UnaryFunctionType, MaxSlack, MinIsolate, MaxIsolate, Coefs, Var),
    search_unary_function(R, S, BinaryFunctionType, UnaryFunctionType, MaxSlack, MinIsolate, MaxIsolate, Coefs, T).

% [t(ValIsolate,ValOutput)|R]: for each entrie of a cluster this list give the value of the isolated input parameter and the value of the output parameter
% BinaryFunctionType         : binary function used in the current decomposition that we try to construct
% UnaryFunctionType          : unary  function used in the current decomposition that we try to construct
% MaxSlack                : 0 if no slack, 1 if a slack is allowed
% MinIsolate              : minimum value of the isolated input parameter
% MaxIsolate              : maximum value of the isolated input parameter
% [A,B,C]                 : coefficients used in the decomposition: correspond to variables that have to be determined
% Var                  : give for current cluster the value associated to the formula that occur in the decomposition
% [Slack|S]               : value of the slack associated to each entry of current cluster (0 if MaxSlack=0, 0 or 1 if MaxSlack=1)
post_ctr_wrt_unary_and_binary_functions_of_the_decomposition([t(ValIsolate,ValOutput)|R], [Slack|S],
                                                             BinaryFunctionType, UnaryFunctionType, MaxSlack, MinIsolate, MaxIsolate, [Shift,A,B,C], Var) :-
    !,
    %write(d1(t(ValIsolate,ValOutput))),nl,
    % depending on the unary function type, post the appropriate constraints where Delta is the value returned by the unary function
    %...............................................................................................................................
    (UnaryFunctionType = 0 -> Delta #= A*ValIsolate*ValIsolate + B*ValIsolate + C                                                           ;
     UnaryFunctionType = 1 -> Delta #= (A*ValIsolate*ValIsolate + B*ValIsolate) div C                                                       ;
     UnaryFunctionType = 2 -> Delta #= (A*ValIsolate*ValIsolate + B*ValIsolate + C - 1) div C                                               ;
     UnaryFunctionType = 3 -> Delta #= min(A*ValIsolate+B,C)                                                                                ;
     UnaryFunctionType = 4 -> Delta #= max(A*ValIsolate+B,C)                                                                                ;
     UnaryFunctionType = 5 -> Delta #= (A*ValIsolate+B) mod C                                                                               ;
     UnaryFunctionType = 6 -> Delta #= abs(A*ValIsolate + B)                                                                                ;
     UnaryFunctionType = 7 -> Delta #= (((ValIsolate + A) mod B) #= C)                                                                      ;
     UnaryFunctionType = 8 -> Delta #= (((ValIsolate + A) mod B) #>= C)                                                                     ;
     UnaryFunctionType = 9 -> Delta #= (((ValIsolate + A) mod B) #=< C)                                                                     ;
                              write(search_unary_function1), nl, halt                                                                       ),
    %write(d2),nl,
    Slack in 0..MaxSlack,                                             % slack of current entry: if MaxSlack=1 it will used for computing a boolean formula that occurs in the decomposition

    % depending on the binary function type, post the appropriate constraint that link the output value ValOutput with Delta
    %.......................................................................................................................
    (BinaryFunctionType =  1 ->            ValOutput #= (Delta+Slack) + Var                                                             ;
     BinaryFunctionType =  2 ->            ValOutput #= (Delta+Slack) * Var + Shift                                                     ; 
     BinaryFunctionType =  3 ->            ValOutput #= min(Delta+Slack, Var)                                                           ;
     BinaryFunctionType =  4 ->            ValOutput #= max(Delta+Slack, Var)                                                           ;
     BinaryFunctionType =  5 -> Var #> 0, ValOutput #=  (Delta+Slack) div Var + Shift                                                   ;
     BinaryFunctionType =  6 -> Var #> 0, ValOutput #= ((Delta+Slack) div Var) + (((Delta+Slack) mod Var) #> 0) + Shift                 ;
     BinaryFunctionType =  7 -> (Delta+Slack) #> 0, ValOutput #=  Var div (Delta+Slack) + Shift                                         ;
     BinaryFunctionType =  8 -> (Delta+Slack) #> 0, ValOutput #= (Var div (Delta+Slack)) + ((Var mod (Delta+Slack)) #> 0) + Shift       ; 
                                 write(search_unary_function2), nl, halt                                                                ),
    %write(d3),nl,
    post_ctr_wrt_unary_and_binary_functions_of_the_decomposition(R, S, BinaryFunctionType, UnaryFunctionType, MaxSlack, MinIsolate, MaxIsolate, [Shift,A,B,C], Var).
post_ctr_wrt_unary_and_binary_functions_of_the_decomposition([], [], _, _, _, _, _, _, _).

set_unary_cost_constraint(0, Cost, [Shift,A,B,C]) :- !, Cost #= abs(Shift)+abs(A)+abs(B)+abs(C).
set_unary_cost_constraint(1, Cost, [Shift,A,B,C]) :- !, Cost #= abs(Shift)+abs(A)+abs(B)+(C #> 1)*C.    % when C=1 there is no division and do not want to count C
set_unary_cost_constraint(2, Cost, [Shift,A,B,C]) :- !, Cost #= abs(Shift)+abs(A)+abs(B)+(C #> 1)*C.    % when C=1 there is no division and do not want to count C
set_unary_cost_constraint(3, Cost, [Shift,A,B,C]) :- !, Cost #= abs(Shift)+abs(A)+abs(B)+abs(C)    .
set_unary_cost_constraint(4, Cost, [Shift,A,B,C]) :- !, Cost #= abs(Shift)+abs(A)+abs(B)+abs(C)    .
set_unary_cost_constraint(5, Cost, [Shift,A,B,C]) :- !, Cost #= abs(Shift)+abs(A)+abs(B)+C         .
set_unary_cost_constraint(6, Cost, [Shift,A,B,C]) :- !, Cost #= abs(Shift)+abs(A)+abs(B)+abs(C)    .
set_unary_cost_constraint(7, Cost, [Shift,A,B,C]) :- !, Cost #= abs(Shift)+abs(A)+abs(C)+(B #> 1)*B.    % when B=1 there is no modulo and do not want to count B
set_unary_cost_constraint(8, Cost, [Shift,A,B,C]) :- !, Cost #= abs(Shift)+abs(A)+abs(C)+(B #> 1)*B.    % when B=1 there is no modulo and do not want to count B
set_unary_cost_constraint(9, Cost, [Shift,A,B,C]) :-    Cost #= abs(Shift)+abs(A)+abs(C)+(B #> 1)*B.    % when B=1 there is no modulo and do not want to count B

% for the new created function eliminates input parameters up to the point we converge to a minimal functional dependency
% as we start from minimal functional dependency this should normaly not be possible)
%------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
/*search_minimal_fd([_-_|_], _, NewRest, NewRest) :- !.                    % as we have one single parameter (i.e, Key is a term of arity 1) the current parameters correspond to a minimal functional dependency
search_minimal_fd(Clusters, Values, Rest, NewRest) :-                    % as we have more than one single parameter will try to eliminate each parameter successively
    put_together_key_and_value(Clusters, Values, KeyValues), 
    KeyValues = [Key-_|_],    
    functor(Key, t, NParams),                                            % get number of input parameters of the yet unknown function
    try_to_eliminate_param(1, NParams, Clusters, Rest, NewRest).

put_together_key_and_value([], [], []) :- !.                             % put together the key and the value of each cluster
put_together_key_and_value([Key-_|R], [Val|S], [Key-Val|T]) :-
    put_together_key_and_value(R, S, T).

try_to_eliminate_param(I, NParams, _, NewRest, NewRest) :-               % if try out without success to eliminate all input parameters
    I > NParams, !.                                                      % then we have a minimal functional dependency
try_to_eliminate_param(I, NParams, Clusters, Rest, NewRest) :-
    (check_if_can_eliminate_param(I, Clusters, SimplifiedClusters) ->    % if could eliminate the i-th input parameter then eliminate it,
        remove_ith_elem(I, Rest, NextRest),                              % and try further to simplify the parameters of the created function
        NParams_1 is NParams-1,                                          % to converge to a minimal functional dependency
        try_to_eliminate_param(1, NParams_1, SimplifiedClusters, NextRest, NewRest)
    ;                                                                    % if could not eliminate the i-th input parameter
        I1 is I+1,                                                       % then try to eliminate the next input parameter
        try_to_eliminate_param(I1, NParams, Clusters, Rest, NewRest)
    ).

check_if_can_eliminate_param(I, Clusters, SortedNewClusters) :-          % succeed if after eliminating the Ith input parameter there is no collision in the corresponding projection
    project_clusters(Clusters, I, NewClusters),                          % eliminate the Ith parameter
    sort(NewClusters, SortedNewClusters),                                % sort the projection wrt the remaining input parameters
    check_if_unique_value_for_each_cluster(SortedNewClusters).           % check if no collision within each cluster of the projection

project_clusters([], _, []) :- !.                                        % scan the different entries and create new entries where the Ith input parameter is removed
project_clusters([Cluster|R], I, [NewCluster|S]) :-
    project_cluster(Cluster, I, NewCluster),
    project_clusters(R, I, S).

project_cluster(Cluster, I, NewCluster) :-                               % create a new entry by eliminating the Ith input parameter
    Cluster = Key-Value,
    NewCluster = NewKey-Value,
    functor(Key, t, Arity),
    Arity_1 is Arity-1,
    functor(NewKey, t, Arity_1),
    project_key(1, 1, Arity, I, Key, NewKey).

project_key(J, _, Arity, _, _, _) :-                                     % copy the argument of current entry but skip Ith input parameter
    J > Arity, !.
project_key(J, K, Arity, I, Key, NewKey) :-
    J =< Arity,
    (J = I ->
        K1 = K
    ;
        arg(J, Key, ArgJ),
        arg(K, NewKey, ArgJ),
        K1 is K+1
    ),
    J1 is J+1,
    project_key(J1, K1, Arity, I, Key, NewKey).

check_if_unique_value_for_each_cluster([]) :- !.                            % succeed if within each cluster (where a cluster corresponds to all entries that have the same projected input parameters)
check_if_unique_value_for_each_cluster([_]) :- !.                           % the corresponding value is unique (which means that the formula to find in the decomposition only depend on the input
check_if_unique_value_for_each_cluster([Key-Val1,Key-Val2|R]) :- !,         % parameters that are different from the eliminated input parameter)
    (Val1 = Val2 -> check_if_unique_value_for_each_cluster([Key-Val2|R]) ; false).
check_if_unique_value_for_each_cluster([_,Key-Val|R]) :- !,
    check_if_unique_value_for_each_cluster([Key-Val|R]).
*/


% search for a decomposition wrt the output column ColOutput of current table Table and wrt a functional dependency Fd: we isolate one input parameter,
% put it in a unary function and combine it with a formula that needs to be acquired;
% (assumes that the entries of the table Table and the corresponding metadata are already loaded; do not reclaim table entries);
% FoundDecomposition is a term of the form
% t(BinaryFunctionType: binary function used in the decomposition (that link the unary function with the formula to find)
%   UnaryFunctionType : unary function that is applied to the isolated input parameter
%   Coefs          : coefficients used within the unary function
%   MaxSlack          : 0 if do not use any slack, 1 if use a 0..1 slack (in this later case we also have to find a boolean formula)
%   Clusters          : clusters of the projected table
%   Vars           : give for each cluster the "output value" of the formula that the caller will try to find
%   NewRest           : input parameters of the formula that we will try to identify
%   FlatSlacks        : give for each table entry the "output value" of the boolean formula the caller will try to find (relevant only when MaxSlack=1)
%   NewRestSlacks)    : input parameters of the boolean formula we will try to identify
%------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
search_conds_decompositions(KindCombi, CallMap, Fd, Table, Col, OptionsBoolCond, TableEntries, ParamsList, ColSetsBool, OutputMin, OutputMax,
                            Mode, CurMaxCost, Cost, Result, FormulaFamily, FormulaPattern, OptionUsedToGenerateConjecture) :-
    % collect all valid decomposition candidates:
    search_all_cond_decompositions(TableEntries, Fd, ParamsList, ColSetsBool, OutputMin, OutputMax, FoundDecompositionList),
   %false,
   %write_list(FoundDecompositionList),
    sort(FoundDecompositionList, FoundDecompositionListSorted),     % sort candidates by increasing cost of the unary component
    length(FoundDecompositionListSorted, LenFoundDecompositionList),
    TopLimit is min(LenFoundDecompositionList, 1),                  % we only consider at most first 3 candidates for decomposition
    prefix_length(FoundDecompositionListSorted, PrefixFoundDecompositionList, TopLimit),
    %member([_,FoundDecomposition], PrefixFoundDecompositionList), % select a decomposition candidate % TO RESTORE
    I in 1..TopLimit, indomain(I), nth1(I, PrefixFoundDecompositionList, [_,FoundDecomposition]), % TO REMOVE
    FoundDecomposition = t(CostCondThen, _CondVarsSum, CondFunctionType, ThenFunctionType, CondTerm, ThenTerm, CondVars),
    %length(TableEntries, NbRows),
    %5 * CondVarsSum =< 4 * NbRows,
    %write(cnd(CondVarsSum-NbRows)),nl,
    %tab_get_nb_rows(col(Table,_),NbRows),
    %write(t(CostCondThen, CondVarsSum-NbRows, CondFunctionType, ThenFunctionType, CondTerm, ThenTerm)),nl,
    append(Fd, [col(Table, Col)], FdOutput),
    match_list_indices_sublist(ParamsList, AttrPosFd, FdOutput),
    collect_else_entries(TableEntries, CondVars, AttrPosFd, TableEntriesFd, TableEntriesElse),
    %(foreach(C1, TableEntries), foreach(C2, CondVars) do write(C1-C2), nl),
    %nl,nl,
    %write_list(TableEntriesElse),nl,halt,
    (user:max_cost(Max) -> true ; Max = CurMaxCost),    
    CurMaxCostElse is Max - CostCondThen,       % update the max cost for the Else part of the decomposition
    (foreach(TableEntry, TableEntriesElse), foreach(Var, Vars) do last(TableEntry, Var)),
    statistics(total_runtime,[Start|_]),
    ForceToUseOnlySmallFd = 1,
    formula_generator_base(KindCombi, CallMap, Table, Col, OptionsBoolCond, Vars, -1, TableEntriesElse, ParamsList, Fd, 1, CurMaxCostElse, ForceToUseOnlySmallFd,
                           Mode, _ElseMin, _ElseMax, FdElse, CostElse, Penalty, FormulaFamilyElse, OptionUsedToGenerateConjectureElse, FormulaPatternElse),
    /*min_member(ElseMin, Vars),
    max_member(ElseMax, Vars),                  % find minimum and maximum values of Else values
    (ElseMin = ElseMax ->                       % if TableEntriesElse can be expressed as an equivalent to a constant
         %TypeElse = 0,
         FdElse = [],
         CostElse is abs(ElseMin),
         FormulaFamilyElse = cst,
         OptionUsedToGenerateConjectureElse = [cst],
         InputColsList = [],
         InputNamesList = [],
         InputVarsList = [],
         FormulaTermElse = ElseMin,
         FormulaPatternElse = t(InputColsList, InputNamesList, InputVarsList, FormulaTermElse)
    ;
     check_base_eq_output(TableEntriesElse, Fd, ElseCol) -> % if TableEntriesElse can be expressed as equivalent to an input column
         %TypeElse = 0,
         FdElse = [ElseCol],
         CostElse = 1,
         FormulaFamilyElse = col,
         OptionUsedToGenerateConjectureElse = [eq_col],
         tab_get_name(ElseCol, ElseName),
         InputColsList = [ElseCol],
         InputNamesList = [ElseName],
         InputVarsList = [ElseVar],
         FormulaTermElse = ElseVar,
         FormulaPatternElse = t(InputColsList, InputNamesList, InputVarsList, FormulaTermElse)
    ;                                          % otherise call formula_generator proper and find a solution
         %TypeElse = 1,
         find_split_fd(Fd, TableEntriesElse, ParamsList, Vars, FdElseList),
         % to ensure reasonable performance we take only the first successful solution we use once/1
         once((member(FdElse, FdElseList),                      % select a functional dependency
               (FdElse = Fd ->
                    TableEntriesElseFd = TableEntriesElse
               ;
                    append(FdElse, [col(Table, Col)], AttrNamesOutput),
                    append(Fd,     [col(Table, Col)], ParamsOutput),
                    % firstly - collect column indices within AttrNamesOutput
                    match_list_indices_sublist(ParamsOutput, AttrPos, AttrNamesOutput), % get positions AttrPos of input columns
                    % secondly - use collected column indices AttrPos to extract relevant table entries
                    (foreach(TableEntryPassed, TableEntriesElse), foreach(TableEntryElse, TableEntriesElseFd), param(AttrPos)
                    do
                     match_list_indices_sublist(TableEntryPassed, AttrPos, TableEntryElse)
                    )
               ),
               ModeElse = preprocessed(ElseMin, ElseMax, 1, 1),       % select the preprocessed mode. Set 0 to Boolean formulae w/ restrictions (2 terms, no mod functions)
               ForceToUseOnlySmallFd = 1,
               % generate lists of options for the Else part of the decomposition
               gen_options_lists_decomp_base(KindCombi, col(Table,Col), secondary, OptionsBoolCond, [], FdElse, ForceToUseOnlySmallFd,
                                             TableEntriesElseFd, ModeElse, ListsOptionsElse, SetsBoolElse),
               %gen_options_lists_decomp_else(KindCombi, col(Table,Col), secondary, OptionsBoolCond, [], FdElse, ForceToUseOnlySmallFd,
               %                              TableEntriesElseFd, ModeElse, ListsOptionsElse, SetsBoolElse),
               % search for the formula by calling formula_generator
               CostElse in 0..15,
               TimeOutElse = 3600000,
               time_out(formula_generator(CallMap, KindCombi, OptionsBoolCond, ListsOptionsElse, TableEntriesElseFd, ModeElse, SetsBoolElse,
                                          ElseMin, secondary, Table, Col, CurMaxCostElse, FormulaPatternElse,
                                          FormulaFamilyElse, OptionUsedToGenerateConjectureElse, CostElse, ResultElse),
                       TimeOutElse, success),
               ResultElse \== time_out
              ))
    ),*/
    statistics(total_runtime,[Stop|_]),
    Runtime is Stop - Start,
    write('else runtime: '), write(Runtime), write('ms. '),
    write('else cost: '), write(CostElse),nl,
    Result = success,                                      % select the success flag of the search
    formula_pattern_create_term(FormulaPatternElse, FormulaTermElseTest),
    
    % if Else part is verified on all entries, use it instead
    ((Fd = FdElse, eval_formula_term_on_entries(TableEntriesFd, FormulaTermElseTest)) ->
         Cost is CostElse - Penalty,
         Cost in 0..Max,
         FormulaFamily = FormulaFamilyElse,
         OptionUsedToGenerateConjecture = OptionUsedToGenerateConjectureElse,
         FormulaPattern = FormulaPatternElse
    ;
         %if the else part is a conditional formula (w/ or w/o decomposition) then add +1 penalty to the const
         Cost is CostCondThen + CostElse,
         Cost in 0..Max,
         FormulaFamily = families([cond_template([cond(CondFunctionType),     % formula family for the complete decomposition
                                                  then(ThenFunctionType)]),
                                   else(FormulaFamilyElse)]),
         OptionUsedToGenerateConjecture = decomp(if(cond(CondFunctionType),   % formula family for the complete decomposition
                                                    then(ThenFunctionType),
                                                    else(OptionUsedToGenerateConjectureElse))),
         % generate the decomposition formula pattern
         FormulaPattern = [decomp(cond, CondTerm-ThenTerm, FormulaPatternElse)]
    ),
    %write(bingo),nl,
    %TO REMOVE start
    /*write(decomp_success_cond(I,TopLimit)),nl,
    (foreach([_,T], PrefixFoundDecompositionList)
    do %t(CostCondThen, CondFunctionType, ThenFunctionType, CondTerm, ThenTerm, CondVars)
     arg(1, T, CostC), arg(2, T, CostC1), arg(3, T, TC), arg(4, T, TT), arg(5, T, TTC), arg(6, T, TTE),
     write([CostC-CostC1,TC-TT, TTC, TTE]),nl),
    (TypeElse = 1 -> write(else(FdElse-FdElseList)),nl ; true ),*/
    %TO REMOVE end
    !. % after a solution is found, we stop looking for alternative decompositions

% collect all possible unary decompositions
search_all_cond_decompositions(TableEntries, Fd, ParamsList, ColSetsBool, ColMin, ColMax, FoundDecompositionList) :-
    length(TableEntries, NbRows),
    CondFunctionType in 1..7,                                       % 1: Attr = min(Attr),    2: Attr = max(Attr),
                                                                    % 3: Attr1 = Attr2,       4: Attr1 =< Attr2,
                                                                    % 5: Attr1 mod Attr2 = 0, 6: Attr1 = Attr2*Attr3
                                                                    % 7: Cst * Attr1 =< Attr2
    CondFunctionType #\= 2,     % currently don't use condition 2
    ThenFunctionType in 1..7,                                       % 1: Cst, 2: Attr, 3: Attr = min(Attr), 4: Attr > min(Attr),
                                                                    % 5: Attr1*Attr2, 6: Attr1 = Attr2 + Cst, 7: Attr1 = Attr2 + Attr3
    % generate the list of possible combinations of MaxSlack, BinaryFunctionType and UnaryFunctionType
    findall([CondFunctionType, ThenFunctionType],
            (indomain(CondFunctionType),
             indomain(ThenFunctionType)),
            CondThenTypesList),
    iterate_cond_then_types(CondThenTypesList, TableEntries, NbRows, Fd, ParamsList, ColSetsBool, ColMin, ColMax, FoundDecompositionList).

% for each MaxSlack, BinaryFunctionType and UnaryFunctionType combination:
% 1. generate clusters correspomding to isolated input values
% 2. generate and solve a constraint model to determine coefficients for the selected binary and unary functions:
%   - if it's successful then record the information about the decomposition
%   - if it's unsuccessful then do nothing
% 3. move to the next combination 
iterate_cond_then_types([], _, _, _,  _, _, _, _, []) :- !.
iterate_cond_then_types([[CondFunctionType, ThenFunctionType]|R], TableEntries, NbRows, Fd, ParamsList, ColSetsBool, ColMin, ColMax, FoundDecompositionList):-
    (search_cond_function(CondFunctionType, ThenFunctionType, TableEntries, NbRows, Fd, ParamsList, ColSetsBool, ColMin, ColMax, FoundDecomposition) ->
         arg(2, FoundDecomposition, CostCandidate),
         FoundDecompositionList = [[CostCandidate,FoundDecomposition]|S]
    ;
         FoundDecompositionList = S
    ),
    iterate_cond_then_types(R, TableEntries, NbRows, Fd, ParamsList, ColSetsBool, ColMin, ColMax, S).

% For the selected Cond and Then functions construct a constraint model and if a solution is found - prepare the information for the search_conds_decompositions
search_cond_function(CondFunctionType, ThenFunctionType, TableEntries, NbRows, Fd, ParamsList, ColSetsBool, ColMin, ColMax, FoundDecomposition) :-
    Cost in 0..100,
    CoefMin = -3, CoefMax = 3,
    TimeOut = 5000,                                                   % needed as very rarely we come up on a combination of constraints
                                                                      % which propagate extremely poorly (e.g. sometime the reformulation of ceil)
    % The goal is to find the simplest combination Cond and Then that explains most of the output. So:
    % - first we maximize the number of explained entries CondVarsSum (explained means that Cond is true and Then is equal to the output
    % - then we minimize the Cost (if possible)
    %statistics(total_runtime,[Start|_]),  
    time_out(minimize(minimize(search_cond_function(CondFunctionType, ThenFunctionType, TableEntries, NbRows, Fd, ParamsList, ColSetsBool, CoefMin, CoefMax, ColMin, ColMax,
                                                    Cost, CondVarsSum, CondAttrs, CondCoefs, ThenAttrs, ThenCoefs, CondVars),
                               Cost, [all]), CondVarsSum, [all]), TimeOut, Result),
    %statistics(total_runtime,[Stop|_]),
    %Time is Stop - Start,
    %write(a1(CondFunctionType, ThenFunctionType, Result, Time)),nl,
    %write(a2(NbRows-CondVarsSum)),nl,
    !,
    Result \== time_out,
    %   1: Attr = min(Attr)
    (CondFunctionType = 1 ->
         CondAttrs = [CondAttr],
         CondCoefs = [CondCoef],
         nth1(CondAttr, Fd, AttrColCond),
         tab_get_name(AttrColCond, AttrNameCond),
         CondInputColsList = [AttrColCond],
         CondInputNamesList = [AttrNameCond],
         CondInputVarsList = [X],
         CondFormulaTerm = eq(X, CondCoef)
    ; % 2: Attr = max(Attr)
     CondFunctionType = 2 ->                                    
         CondAttrs = [CondAttr],
         CondCoefs = [CondCoef],
         nth1(CondAttr, Fd, AttrColCond),
         tab_get_name(AttrColCond, AttrNameCond),
         CondInputColsList = [AttrColCond],
         CondInputNamesList = [AttrNameCond],
         CondInputVarsList = [X],
         CondFormulaTerm = eq(X, CondCoef)
    ; % 3: Attr1 = Attr2
     CondFunctionType = 3 ->                                    
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [],
         nth1(CondAttr1, Fd, AttrColCond1),
         nth1(CondAttr2, Fd, AttrColCond2),
         tab_get_name(AttrColCond1, AttrNameCond1),
         tab_get_name(AttrColCond2, AttrNameCond2),
         CondInputColsList =  [AttrColCond1,  AttrColCond2],
         CondInputNamesList = [AttrNameCond1, AttrNameCond2],
         CondInputVarsList = [X1, X2],
         CondFormulaTerm = eq(X1, X2)
    ; % 4: Attr1 =< Attr2
     CondFunctionType = 4 ->                                    
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [],
         nth1(CondAttr1, Fd, AttrColCond1),
         nth1(CondAttr2, Fd, AttrColCond2),
         tab_get_name(AttrColCond1, AttrNameCond1),
         tab_get_name(AttrColCond2, AttrNameCond2),
         CondInputColsList =  [AttrColCond1,  AttrColCond2],
         CondInputNamesList = [AttrNameCond1, AttrNameCond2],
         CondInputVarsList =  [X1, X2],
         CondFormulaTerm = leq(X1, X2)
    ; % 5: Attr1 mod Attr2 = 0
     CondFunctionType = 5 ->                                    
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [],
         nth1(CondAttr1, Fd, AttrColCond1),
         nth1(CondAttr2, Fd, AttrColCond2),
         tab_get_name(AttrColCond1, AttrNameCond1),
         tab_get_name(AttrColCond2, AttrNameCond2),
         CondInputColsList =  [AttrColCond1,  AttrColCond2],
         CondInputNamesList = [AttrNameCond1, AttrNameCond2],
         CondInputVarsList = [X1, X2],
         CondFormulaTerm = eq(mod(X1, X2), 0)
    ; % 6: Attr1 = Attr2*Attr3
     CondFunctionType = 6 ->                                    
         CondAttrs = [CondAttr1, CondAttr2, CondAttr3],
         CondCoefs = [],
         nth1(CondAttr1, Fd, AttrColCond1),
         nth1(CondAttr2, Fd, AttrColCond2),
         nth1(CondAttr3, Fd, AttrColCond3),
         tab_get_name(AttrColCond1, AttrNameCond1),
         tab_get_name(AttrColCond2, AttrNameCond2),
         tab_get_name(AttrColCond3, AttrNameCond3),
         CondInputColsList =  [AttrColCond1,  AttrColCond2,  AttrColCond3],
         CondInputNamesList = [AttrNameCond1, AttrNameCond2, AttrNameCond3],
         CondInputVarsList = [X1, X2, X3],
         CondFormulaTerm = eq(X1, prod(X2,X3))
    ; % 7: Cst*Attr1 =< Attr2
     CondFunctionType = 7 ->                                    
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [CondCoef],
         nth1(CondAttr1, Fd, AttrColCond1),
         nth1(CondAttr2, Fd, AttrColCond2),
         tab_get_name(AttrColCond1, AttrNameCond1),
         tab_get_name(AttrColCond2, AttrNameCond2),
         CondInputColsList =  [AttrColCond1,  AttrColCond2],
         CondInputNamesList = [AttrNameCond1, AttrNameCond2],
         CondInputVarsList = [X1, X2],
         CondFormulaTerm = leq(prod(CondCoef,X1),X2)
    ;
         false
    ),
    CondTerm = t(CondInputColsList, CondInputNamesList, CondInputVarsList, CondFormulaTerm),
    % Then Functions -
      % 1: Cst,
    (ThenFunctionType = 1 ->
         ThenAttrs = [],
         ThenCoefs = [ThenCoef],
         ThenInputColsList = [],
         ThenInputNamesList = [],
         ThenInputVarsList = [],
         ThenFormulaTerm = ThenCoef
    ; % 2: Attr,
     ThenFunctionType = 2 ->
         ThenAttrs = [ThenAttr],
         ThenCoefs = [],
         nth1(ThenAttr, Fd, AttrColThen),
         tab_get_name(AttrColThen, AttrNameThen),
         ThenInputColsList = [AttrColThen],
         ThenInputNamesList = [AttrNameThen],
         ThenInputVarsList = [Y],
         ThenFormulaTerm = Y
    ; % 3: Attr = min(Attr),
     ThenFunctionType = 3 ->
         ThenAttrs = [ThenAttr],
         ThenCoefs = [ThenCoef],
         nth1(ThenAttr, Fd, AttrColThen),
         tab_get_name(AttrColThen, AttrNameThen),
         ThenInputColsList = [AttrColThen],
         ThenInputNamesList = [AttrNameThen],
         ThenInputVarsList = [Y],
         ThenFormulaTerm = eq(Y, ThenCoef)
    ; % 4: Attr > min(Attr)
     ThenFunctionType = 4 ->
         ThenAttrs = [ThenAttr],
         ThenCoefs = [ThenCoef],
         ThenCoef1 is ThenCoef + 1,
         nth1(ThenAttr, Fd, AttrColThen),
         tab_get_name(AttrColThen, AttrNameThen),
         ThenInputColsList = [AttrColThen],
         ThenInputNamesList = [AttrNameThen],
         ThenInputVarsList = [Y],
         ThenFormulaTerm = geq(Y, ThenCoef1)
    ; % 5: Attr1*Attr2
     ThenFunctionType = 5 ->
         ThenAttrs = [ThenAttr1, ThenAttr2],
         ThenCoefs = [],
         nth1(ThenAttr1, Fd, AttrColThen1),
         nth1(ThenAttr2, Fd, AttrColThen2),
         tab_get_name(AttrColThen1, AttrNameThen1),
         tab_get_name(AttrColThen2, AttrNameThen2),
         ThenInputColsList = [AttrColThen1, AttrColThen2],
         ThenInputNamesList = [AttrNameThen1, AttrNameThen2],
         ThenInputVarsList = [Y1, Y2],
         ThenFormulaTerm = prod(Y1, Y2)
    ; % 6: Attr1 = Attr2 + Coef
     ThenFunctionType = 6 ->
         ThenAttrs = [ThenAttr1, ThenAttr2],
         ThenCoefs = [ThenCoef],
         nth1(ThenAttr1, Fd, AttrColThen1),
         nth1(ThenAttr2, Fd, AttrColThen2),
         tab_get_name(AttrColThen1, AttrNameThen1),
         tab_get_name(AttrColThen2, AttrNameThen2),
         ThenInputColsList = [AttrColThen1, AttrColThen2],
         ThenInputNamesList = [AttrNameThen1, AttrNameThen2],
         ThenInputVarsList = [Y1, Y2],
         ThenFormulaTerm = eq(Y1, plus(Y2, ThenCoef))
    ; % 7: Attr1 = Attr2 + Attr3
     ThenFunctionType = 7 ->
         ThenAttrs = [ThenAttr1, ThenAttr2, ThenAttr3],
         ThenCoefs = [],
         nth1(ThenAttr1, Fd, AttrColThen1),
         nth1(ThenAttr2, Fd, AttrColThen2),
         nth1(ThenAttr3, Fd, AttrColThen3),
         tab_get_name(AttrColThen1, AttrNameThen1),
         tab_get_name(AttrColThen2, AttrNameThen2),
         tab_get_name(AttrColThen3, AttrNameThen3),
         ThenInputColsList = [AttrColThen1, AttrColThen2, AttrColThen3],
         ThenInputNamesList = [AttrNameThen1, AttrNameThen2, AttrNameThen3],
         ThenInputVarsList = [Y1, Y2, Y3],
         ThenFormulaTerm = eq(Y1, plus(Y2, Y3))
    ;
         false
    ),
    ThenTerm = t(ThenInputColsList, ThenInputNamesList, ThenInputVarsList, ThenFormulaTerm),
    FoundDecomposition = t(Cost, CondVarsSum, CondFunctionType, ThenFunctionType, CondTerm, ThenTerm, CondVars), 
    true.

% construct a constraint model that corresponds to the selected Cond and Then functions
search_cond_function(CondFunctionType, ThenFunctionType, TableEntries, NbRows, Fd, ParamsList, ColSetsBool, CoefMin, CoefMax, ColMin, ColMax,
                     Cost, CondVarsSumR, CondAttrs, CondCoefs, ThenAttrs, ThenCoefs, CondVars) :-
    length(Fd, N),
    Cost #= CostCond + CostThen,
    match_list_indices_sublist(ParamsList, AttrPos, Fd), % get positions AttrPos of input columns
    %   1: Attr = min(Attr)
    (CondFunctionType = 1 ->
         CondAttrs = [CondAttr],
         CondCoefs = [CondCoef],
         tab_get_mins_attr_names(Fd, MinAttrs), % get list of min. values of the mandatory attr
         sort(MinAttrs, MinAttrsSorted),
         list_to_fdset(MinAttrsSorted, CondCoefSet),
         CondAttr in 1..N,
         CondCoef in_set CondCoefSet,
         element(CondAttr, MinAttrs, CondCoef),
         CostCond #= CondCoef 
    ; % 2: Attr = max(Attr)
     CondFunctionType = 2 ->
         CondAttrs = [CondAttr],
         CondCoefs = [CondCoef],
         tab_get_maxs_attr_names(Fd, MaxAttrs), % get list of max. values of the mandatory attr
         sort(MaxAttrs, MinAttrsSorted),
         list_to_fdset(MinAttrsSorted, CondCoefSet),
         CondAttr in 1..N,
         CondCoef in_set CondCoefSet,
         element(CondAttr, MaxAttrs, CondCoef),
         CostCond #= CondCoef
    ; % 3: Attr1 = Attr2,
     CondFunctionType = 3 ->
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [],
         CondAttr1 in 1..N,
         CondAttr2 in 1..N,
         gen_table_ctr_wrt_forbidden_cmp(N, Fd, [eq,lt,gt,neq], 0, CondAttrs),
         CondAttr1 #\= CondAttr2,
         CostCond #= 0
    ; % 4: Attr1 =< Attr2
     CondFunctionType = 4 ->
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [],
         CondAttr1 in 1..N,
         CondAttr2 in 1..N,
         gen_table_ctr_wrt_forbidden_cmp(N, Fd, [leq,eq,lt,gt], 0, CondAttrs),
         CondAttr1 #\= CondAttr2,
         CostCond #= 0
    ;
      % 5: Attr1 mod Attr2 = 0
     CondFunctionType = 5 ->
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [],
         CondAttr1 in 1..N,
         CondAttr2 in 1..N,
         CondAttr1 #\= CondAttr2,
         CostCond #= 2
    ;
      % 6: Attr1 = Attr2*Attr3
     CondFunctionType = 6 ->
         CondAttrs = [CondAttr1, CondAttr2, CondAttr3],
         CondCoefs = [],
         CondAttr1 in 1..N,
         CondAttr2 in 1..N,
         CondAttr3 in 1..N,
         all_different(CondAttrs),
         CostCond #= 2
    ; % 7: Cst*Attr1 =< Attr2
     CondFunctionType = 7 ->                             
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [CondCoef],
         CondAttr1 in 1..N,
         CondAttr2 in 1..N,
         CondCoef in CoefMin..CoefMax,
         CondCoef #>= 2,
         CondAttr1 #\= CondAttr2,
         get_set_of_unaryf_values_for_each_pair_of_mandatory_attributes(Fd, 0, unary_leq_attr, prod, ColSetsBool, CoefMin, CoefMax, [_|CstValuesList]),
                                                                                       % first element of the output list is only useful
                                                                                       % for Boolean formulae search
         table([[CondAttr1,CondAttr2,CondCoef]],CstValuesList),                        % restrict to compatible triples
         CostCond #= 0
    ;
         false
    ),
    % Then Functions -
    % 1: Cst
    (ThenFunctionType = 1 ->
         ThenAttrs = [],
         ThenCoefs = [ThenCoef],
         ThenCoef in CoefMin..CoefMax,
         ThenCoef in ColMin..ColMax,
         CostThen #= ThenCoef
    ; % 2: Attr
     ThenFunctionType = 2 ->
         ThenAttrs = [ThenAttr],
         ThenCoefs = [],
         ThenAttr in 1..N,
         CostThen #= 1
    ; % 3: Attr = min(Attr)
     ThenFunctionType = 3 ->
         ThenAttrs = [ThenAttr],
         ThenCoefs = [ThenCoef],
         tab_get_mins_attr_names(Fd, MinAttrs), % get list of min. and max. values of the mandatory attr
         sort(MinAttrs, MinAttrsSorted),
         list_to_fdset(MinAttrsSorted, ThenCoefSet),
         ThenAttr in 1..N,
         ThenCoef in_set ThenCoefSet,
         element(ThenAttr, MinAttrs, ThenCoef),
         CostThen #= 1
    ; % 4: Attr > min(Attr)
     ThenFunctionType = 4 ->
         ThenAttrs = [ThenAttr],
         ThenCoefs = [ThenCoef],
         tab_get_mins_attr_names(Fd, MinAttrs), % get list of min. and max. values of the mandatory attr
         tab_get_maxs_attr_names(Fd, MaxAttrs),
         sort(MinAttrs, MinAttrsSorted),
         list_to_fdset(MinAttrsSorted, ThenCoefSet),
         ThenAttr in 1..N,
         ThenCoef in_set ThenCoefSet,
         element(ThenAttr, MinAttrs, ThenCoef),
         element(ThenAttr, MaxAttrs, ThenCoefMax),
         ThenCoef + 1 #\= ThenCoefMax,          % can't be replaced w/ Attr = max(Attr)
         CostThen #= 1
    ; % 5: Attr1*Attr2
     ThenFunctionType = 5 ->
         ThenAttrs = [ThenAttr1, ThenAttr2],
         ThenCoefs = [],
         ThenAttr1 in 1..N,
         ThenAttr2 in 1..N,
         ThenAttr1 #\= ThenAttr2,
         CostThen #= 1
    ; % 6: Attr1 = Attr2 + Coef
     ThenFunctionType = 6 ->
         ThenAttrs = [ThenAttr1, ThenAttr2],
         ThenCoefs = [ThenCoef],
         ThenAttr1 in 1..N,
         ThenAttr2 in 1..N,
         ThenAttr1 #\= ThenAttr2,
         ThenCoef \= 0,
         ThenCoef in CoefMin..CoefMax,
         CostThen #= abs(ThenCoef) + 3
    ; % 7: Attr1 = Attr2 + Attr3
     ThenFunctionType = 7 ->
         ThenAttrs = [ThenAttr1, ThenAttr2, ThenAttr3],
         ThenCoefs = [],
         ThenAttr1 in 1..N,
         ThenAttr2 in 1..N,
         ThenAttr3 in 1..N,
         all_different(CondAttrs),
         CostThen #= 2
    ;
         false
    ),
    (memberchk(CondFunctionType, [1,2]) ->              % when [Attr = Coef] don't use Attr in Then
         (foreach(ThenAttrI, ThenAttrs), param(CondAttr) do CondAttr #\= ThenAttrI )
    ;
     CondFunctionType = 3 ->                            % when [Attr1 = Attr2] don't use Attr2 in Then
         (foreach(ThenAttrI, ThenAttrs), param(CondAttr2) do CondAttr2 #\= ThenAttrI )
    ;/* % TO REMOVE later
     (CondFunctionType = 7, ThenFunctionType = 1) ->    % since this pair often reaches TimeOut, we simplify the problem
         ThenCoef #= ColMin
    ;*/
         true
    ),
    post_ctr_wrt_cond_and_then_functions(TableEntries, ParamsList, AttrPos,
                                         CondFunctionType, ThenFunctionType,
                                         CondAttrs, CondCoefs, ThenAttrs, ThenCoefs, CondVars),
    NbRows1 is NbRows - 1,
    sum(CondVars, #=, CondVarsSum),
    CondVarsSum #>= 1,                                                % make sure that the condition is not always True or always False
    CondVarsSum #=< NbRows1,
    CondVarsSumR #= NbRows - CondVarsSum,
    labeling([], CondAttrs),
    (foreach(Coef, CondCoefs)                                         % label Coefs variables in a way that we check
    do                                                                % 0, +1, -1, +2, -2,... first
     fd_min(Coef, MinCoef), fd_max(Coef, MaxCoef),
     MaxVal is max(abs(MinCoef), abs(MaxCoef)), 
     CoefAbs in 0..MaxVal,
     CoefAbs #= abs(Coef),
     labeling([up],   [CoefAbs]),
     labeling([down], [Coef])                                         % try to find a value for each coefficient
    ),
    %labeling([], CondCoefs),
    labeling([], ThenAttrs),
    (foreach(Coef, ThenCoefs)                                         % label Coefs variables in a way that we check
    do                                                                % 0, +1, -1, +2, -2,... first
     fd_min(Coef, MinCoef), fd_max(Coef, MaxCoef),
     MaxVal is max(abs(MinCoef), abs(MaxCoef)), 
     CoefAbs in 0..MaxVal,
     CoefAbs #= abs(Coef),
     labeling([up],   [CoefAbs]),
     labeling([down], [Coef])                                         % try to find a value for each coefficient
    ).
    %labeling([], ThenCoefs).

post_ctr_wrt_cond_and_then_functions([], _, _, _, _, _, _, _, _, []) :- !.
post_ctr_wrt_cond_and_then_functions([TableEntry|R], ParamsList, AttrPos, CondFunctionType, ThenFunctionType,
                                     CondAttrs, CondCoefs, ThenAttrs, ThenCoefs, [CondVal|S]) :-
    match_list_indices_sublist(TableEntry, AttrPos, TableEntryVars),
    last(TableEntry, ResVal),
      % 1: Attr = min(Attr)
    (CondFunctionType = 1 ->
         CondAttrs = [CondAttr],
         CondCoefs = [CondCoef],
         element(CondAttr, TableEntryVars, CondAttrI),
         CondVal #= (CondAttrI #= CondCoef)
    ; % 2: Attr = max(Attr)
     CondFunctionType = 2 ->
         CondAttrs = [CondAttr],
         CondCoefs = [CondCoef],
         element(CondAttr, TableEntryVars, CondAttrI),
         CondVal #= (CondAttrI #= CondCoef)
    ; % 3: Attr1 = Attr2,
     CondFunctionType = 3 ->
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [],
         element(CondAttr1, TableEntryVars, CondAttrI1),
         element(CondAttr2, TableEntryVars, CondAttrI2),
         CondVal #= (CondAttrI1 #= CondAttrI2)
    ; % 4: Attr1 =< Attr2
     CondFunctionType = 4 ->
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [],
         element(CondAttr1, TableEntryVars, CondAttrI1),
         element(CondAttr2, TableEntryVars, CondAttrI2),
         CondVal #= (CondAttrI1 #=< CondAttrI2)
    ; % 5: Attr1 mod Attr2 = 0
     CondFunctionType = 5 ->
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [],
         element(CondAttr1, TableEntryVars, CondAttrI1),
         element(CondAttr2, TableEntryVars, CondAttrI2),
         CondVal #= ((CondAttrI1 mod CondAttrI2) #= 0)
    ; % 6: Attr1 = Attr2*Attr3 
     CondFunctionType = 6 ->
         CondAttrs = [CondAttr1, CondAttr2, CondAttr3],
         CondCoefs = [],
         element(CondAttr1, TableEntryVars, CondAttrI1),
         element(CondAttr2, TableEntryVars, CondAttrI2),
         element(CondAttr3, TableEntryVars, CondAttrI3),
         CondVal #= (CondAttrI1 #= CondAttrI2 * CondAttrI3)
    ; % 7: Cst*Attr1 =< Attr2
     CondFunctionType = 7 ->                                    
         CondAttrs = [CondAttr1, CondAttr2],
         CondCoefs = [CondCoef],
         element(CondAttr1, TableEntryVars, CondAttrI1),
         element(CondAttr2, TableEntryVars, CondAttrI2),
         CondVal #= (CondCoef * CondAttrI1 #=< CondAttrI2)
    ;
         false
    ),
    % Then Functions -
      % 1: Cst
    (ThenFunctionType = 1 ->
         ThenCoefs = [ThenCoef],
         ThenVal #= ThenCoef
    ; % 2: Attr
     ThenFunctionType = 2 ->
         ThenAttrs = [ThenAttr],
         element(ThenAttr, TableEntryVars, ThenAttrI),
         ThenVal #= ThenAttrI
    ; % 3: Attr = min(Attr)
     ThenFunctionType = 3 ->
         ThenAttrs = [ThenAttr],
         ThenCoefs = [ThenCoef],
         element(ThenAttr, TableEntryVars, ThenAttrI),
         ThenVal #= (ThenAttrI #= ThenCoef)
    ; % 4: Attr > min(Attr)
     ThenFunctionType = 4 ->
         ThenAttrs = [ThenAttr],
         ThenCoefs = [ThenCoef],
         element(ThenAttr, TableEntryVars, ThenAttrI),
         ThenVal #= (ThenAttrI #>= (ThenCoef + 1))
    ; % 5: Attr1*Attr2
     ThenFunctionType = 5 ->
         ThenAttrs = [ThenAttr1, ThenAttr2],
         element(ThenAttr1, TableEntryVars, ThenAttrI1),
         element(ThenAttr2, TableEntryVars, ThenAttrI2),
         ThenVal #= (ThenAttrI1 * ThenAttrI2)
    ; % 6: Attr1 = Attr2 + Coef
     ThenFunctionType = 6 ->
         ThenAttrs = [ThenAttr1, ThenAttr2],
         ThenCoefs = [ThenCoef],
         element(ThenAttr1, TableEntryVars, ThenAttrI1),
         element(ThenAttr2, TableEntryVars, ThenAttrI2),
         ThenVal #= (ThenAttrI1 #= (ThenAttrI2 + ThenCoef))
    ; % 7: Attr1 = Attr2 + Attr3
     ThenFunctionType = 7 ->
         ThenAttrs = [ThenAttr1, ThenAttr2, ThenAttr3],
         element(ThenAttr1, TableEntryVars, ThenAttrI1),
         element(ThenAttr2, TableEntryVars, ThenAttrI2),
         element(ThenAttr3, TableEntryVars, ThenAttrI3),
         ThenVal #= (ThenAttrI1 #= (ThenAttrI2 + ThenAttrI3))
    ;
         false
    ),
    (CondVal #= 1) #=> (ThenVal #= ResVal),
    post_ctr_wrt_cond_and_then_functions(R, ParamsList, AttrPos, CondFunctionType, ThenFunctionType,
                                         CondAttrs, CondCoefs, ThenAttrs, ThenCoefs, S).

% collect two lists:
% - entries TableEntries     with columns matching to the selected functional dependency
% - entries TableEntriesElse with columns matching to the selected functional dependency when then condition is False (Var = 0)
collect_else_entries([], [], _, [], []) :- !.
collect_else_entries([TableEntry|R], [1|S], AttrPos, TableEntries, TableEntriesElse) :-
    !,
    TableEntries = [TableEntry|T],
    collect_else_entries(R, S, AttrPos, T, TableEntriesElse).
collect_else_entries([TableEntry|R], [0|S], AttrPos, [TableEntryFd|T], [TableEntryFd|U]) :-
    match_list_indices_sublist(TableEntry, AttrPos, TableEntryFd),
    collect_else_entries(R, S, AttrPos, T, U).

%----------------------------------------------------------------------------------------------------
% CODE FOR DECOMPOSITION FORMULAE (where we remove a column and the remaining Fd will have collisions w/)

% Iterate through possible splits of a given FD to find if it is possible to decompose the formula
search_diffs_decompositions(KindCombi, CallMap, Fd, Table, Col, OptionsBoolCond, TableEntries, ParamsList, _ColSetsBool, _OutputMin, _OutputMax,
                            Mode, CurMaxCost, Cost, Result, FormulaFamily, FormulaPattern, OptionUsedToGenerateConjecture):-
    iterate_splits_fd(Fd, Fd, KindCombi, CallMap, Table, Col, OptionsBoolCond,  TableEntries, ParamsList,
                      Mode, CurMaxCost, Cost, Result, FormulaFamily, FormulaPattern, OptionUsedToGenerateConjecture).

% Iterate through all possible splits of a given Fd to find if it is possible to decompose the formula
iterate_splits_fd([ColSplit|R], ColSet, KindCombi, CallMap, Table, Col, OptionsBoolCond, TableEntries, ParamsList,
                  Mode, CurMaxCost, Cost, Result, FormulaFamily, FormulaPattern, OptionUsedToGenerateConjecture) :-
    % 1.  decompose current fd ColSet in two parts: a column ColSplit and a remaning subset ColSetSplit
    selectchk(ColSplit, ColSet, ColSetSplit),
    ForceToUseOnlySmallFd = 1,
    ((check_split(ColSetSplit, TableEntries, ParamsList,        % check that the maximum difference within each collision MaxDiff is not greater than 3
                  ListOfMinsForEachColSetUniqueEntry, MaxDiff, _LongestConflict, _TotalConflicts),
      MaxDiff =< 3) ->
        OutputColDiffMin = 0,
        OutputColDiffMax = MaxDiff,
    % 1a. recalculate output column into the base and the Boolean parts (OutputColBase and OutputColDiff, correspondingly),
    %     prepare table entries for the base part search (TableEntriesSearch)
        member(OpSplit, [plus, minus]),
        calculate_output_cols_wrt_split(ColSetSplit, OpSplit, MaxDiff, ListOfMinsForEachColSetUniqueEntry, TableEntries,  ParamsList,
                                        TableEntriesBase, OutputColBase, OutputColDiff),
        /*min_member(OutputColBaseMin, OutputColBase),
        max_member(OutputColBaseMax, OutputColBase),
        (OutputColBaseMin = OutputColBaseMax ->
             %TypeBase = 0,
             ResultBase = success,
             CostBase = 1,
             FormulaFamilyBase = cst,
             OptionUsedToGenerateConjectureBase = [cst],
             InputColsList = [],
             InputNamesList = [],
             InputVarsList = [],
             FormulaPatternBase = t(InputColsList, InputNamesList, InputVarsList, OutputColBaseMin)
        ;
         check_base_eq_output(TableEntriesBase, ColSetSplit, BaseCol) ->
             %TypeBase = 0,
             ResultBase = success,
             CostBase = 1,
             FormulaFamilyBase = col,
             OptionUsedToGenerateConjectureBase = [eq_col],
             tab_get_name(BaseCol, BaseName),
             InputColsList = [BaseCol],
             InputNamesList = [BaseName],
             InputVarsList = [BaseVar],
             FormulaTermBase = BaseVar,
             FormulaPatternBase = t(InputColsList, InputNamesList, InputVarsList, FormulaTermBase)
        ;
    % 2.  generate option lists for the base part of the formula
             %TypeBase = 1,
             find_split_fd(ColSetSplit, TableEntries, ParamsList, OutputColBase, FdBaseList),
             member(FdBase, FdBaseList),
             (FdBase = ColSetSplit ->
                  TableEntriesBaseFd = TableEntriesBase
             ;
                  append(FdBase,      [col(Table, Col)], AttrNamesOutput),
                  append(ColSetSplit, [col(Table, Col)], ParamsOutput),
                  % firstly - collect column indices within AttrNamesOutput
                  match_list_indices_sublist(ParamsOutput, AttrPos, AttrNamesOutput), % get positions AttrPos of input columns
                  % secondly - use collected column indices AttrPos to extract relevant table entries
                  (foreach(TableEntryPassed, TableEntriesBase), foreach(TableEntryBase, TableEntriesBaseFd), param(AttrPos)
                  do
                   match_list_indices_sublist(TableEntryPassed, AttrPos, TableEntryBase)
                  )
             ),
             ModeBase = preprocessed(OutputColBaseMin,              % select preproccessed mode for the formula search, pass down min and max values
                                     OutputColBaseMax,              % of the output column
                                     0,                             % set 0 to Boolean formulae w/o restrictions
                                     1),
             % to generate options for the base formula:
             %  - use ModeBase mode,
             %  - [] as PrevInputParams,
             %  - FdBase as InputParams,
             %  - force ForceToUseOnlySmallFd
             gen_options_lists_decomp_base(KindCombi, col(Table,Col), secondary, OptionsBoolCond, [], FdBase, ForceToUseOnlySmallFd, 
                                           TableEntriesBaseFd, ModeBase, ListsOptionsBase, SetsBoolBase),
    % 3.  enumerate on options to find the base part of the formula
             (user:max_cost(Max) -> true ; Max = CurMaxCost),
             CurMaxCostBase = Max,
             TimeOutBase = 3600000,
             (time_out((formula_generator(CallMap, KindCombi, OptionsBoolCond, ListsOptionsBase, TableEntriesBaseFd, ModeBase, SetsBoolBase,
                                          OutputColBaseMin, secondary, Table, Col, CurMaxCostBase, FormulaPatternBase,
                                          FormulaFamilyBase, OptionUsedToGenerateConjectureBase, CostBase1, ResultBase),
                        ResultBase \== time_out), TimeOutBase, success) ->
                  !,
                  select_penalty(FormulaFamilyBase, OptionUsedToGenerateConjectureBase, Penalty),
                  CostBase is CostBase1 + Penalty
             ;
                  ResultBase = time_out
             )
        ),*/
        (user:max_cost(Max) -> true ; Max = CurMaxCost),
        CurMaxCostBase = Max,
        %write(b1),nl,
        (formula_generator_base(KindCombi, CallMap, Table, Col, OptionsBoolCond, OutputColBase, -1, TableEntriesBase, ParamsList, ColSetSplit, 0, CurMaxCostBase, ForceToUseOnlySmallFd,
                                Mode, _BaseMin, _BaseMax, _FdBase, CostBase, _Penalty, FormulaFamilyBase, OptionUsedToGenerateConjectureBase, FormulaPatternBase) ->
    % 4.  calculate table entries and generate options for the bool part of the formula.
         %write(b2),nl,
             find_split_fd(ColSplit, ColSet, TableEntries, ParamsList, OutputColDiff, FdDiffList),
             member(FdDiff, FdDiffList),
             calculate_diff_entries(FdDiff, TableEntries, ParamsList, OutputColDiff, EntriesDiffUnsorted),
             sort(EntriesDiffUnsorted, TableEntriesDiff),
        % to generate options for the Boolean part of the formula:
        %  - use ModeDiff mode,
        %  - [] as PrevInputParams,
        %  - FdBase as InputParams,
        %  - force ForceToUseOnlySmallFd
             ModeDiff = preprocessed(OutputColDiffMin, OutputColDiffMax, 0, 0),  % select the preprocessed mode. Set 0 to Boolean formulae w/o restrictions
             gen_options_lists_decomp_diff(KindCombi, col(Table,Col), secondary, OptionsBoolCond, [], FdDiff, ForceToUseOnlySmallFd,
                                      TableEntriesDiff, ModeDiff, ListsOptionsDiff, SetsBoolDiff),
             (user:max_cost(Max2) -> true ; Max2 = CurMaxCost),
             CurMaxCostDiff is Max2 - CostBase,
    % 5.  enumerate on options to find the Boolean part of the formula
             ((formula_generator(CallMap, KindCombi, OptionsBoolCond, ListsOptionsDiff, TableEntriesDiff, ModeDiff, SetsBoolDiff,
                                 OutputColDiffMin, secondary, Table, Col, CurMaxCostDiff, FormulaPatternDiff,
                                 FormulaFamilyDiff, OptionUsedToGenerateConjectureDiff, CostDiff, ResultDiff),
              ResultDiff \== time_out) ->
    % 6.  create the unified formula pattern
                  Result = success,
                  Cost is CostBase + CostDiff,
                  Cost in 0..Max2,
                  FormulaFamily = families([splits, base(FormulaFamilyBase), diff(FormulaFamilyDiff)]),
                  OptionUsedToGenerateConjecture = decomp(binary_op(OpSplit),
                                                          [base(OptionUsedToGenerateConjectureBase),
                                                           rest(OptionUsedToGenerateConjectureDiff)]),
                  IterateNextSplit = 0  % flag to make it easier to select whether or not to iterate on the next split
             ;
                  IterateNextSplit = 1
             )
        ;
             IterateNextSplit = 1
        )
    ;
        IterateNextSplit = 1
    ),
    (IterateNextSplit = 1 ->
        iterate_splits_fd(R,  ColSet, KindCombi, CallMap, Table, Col, OptionsBoolCond, TableEntries, ParamsList,
                          Mode, CurMaxCost, Cost, Result, FormulaFamily, FormulaPattern, OptionUsedToGenerateConjecture)
    ;
        % the resulting formula pattern:
        FormulaPattern = [decomp(OpSplit, FormulaPatternBase, FormulaPatternDiff)],
        % TO REMOVE start
        %(TypeBase = 1 -> write(base(FdBase-FdBaseList)),nl ; true ),
        %write(diff(FdDiff-FdDiffList)),nl,
        % TO REMOVE end
        !
    ).

% calculate maximum difference within each collision for the given set of columns ColSet
check_split(ColSet, TableEntries, ParamsList, 
            ListOfMinsForEachColSetUniqueEntry, MaxDiff, LongestConflict, TotalConflicts):-
    match_list_indices_sublist(ParamsList, AttrPos, ColSet), % get positions AttrPos of input columns
    (foreach(TableEntry, TableEntries), foreach(ValsSet-ValI, EntriesPaired), param(AttrPos)
    do
     match_list_indices_sublist(TableEntry, AttrPos, ValsSet),
     last(TableEntry, ValI)
    ),
    keysort(EntriesPaired, EntriesPairedSorted),
    collect_diffs(EntriesPairedSorted, ListOfMinsForEachColSetUniqueEntry, DiffNbs, Diffs),
    Diffs \== [_|_],
    max_member(MaxDiff, Diffs),
    max_member(LongestConflict, DiffNbs),
    sumlist(DiffNbs, TotalConflicts).

% collect differences within each collision
collect_diffs([], ListOfMinsForEachColSetUniqueEntry, [], []) :- !, ListOfMinsForEachColSetUniqueEntry = [].
collect_diffs([EntryCurr-OutputCurr|R], ListOfMinsForEachColSetUniqueEntry, DiffNbs, Diffs) :-
    collect_diffs1([EntryCurr-OutputCurr|R], EntryCurr, RemainingEntries, EntryPrevOutputs),
    max_member(MaxOutput, EntryPrevOutputs),
    min_member(MinOutput, EntryPrevOutputs),
    Diff is MaxOutput - MinOutput,
    (Diff < 0 ->
         write(EntryCurr-OutputCurr),nl,halt
    ;
     Diff > 0 ->
         length(EntryPrevOutputs, LengthDiff),
         ListOfMinsForEachColSetUniqueEntry = [EntryCurr-MinOutput|ListOfMinsForEachColSetUniqueEntryOld],
         DiffNbs = [LengthDiff|DiffNbsOld],
         Diffs = [Diff|DiffsOld]
    ;
         ListOfMinsForEachColSetUniqueEntry = ListOfMinsForEachColSetUniqueEntryOld,
         DiffNbs = DiffNbsOld,
         Diffs = DiffsOld
    ),
    collect_diffs(RemainingEntries, ListOfMinsForEachColSetUniqueEntryOld, DiffNbsOld, DiffsOld).

collect_diffs1([], _, RemainingEntries, EntryOutputs) :-
    !,
    RemainingEntries = [],
    EntryOutputs = [].
collect_diffs1([EntryCurr-OutputCurr|R], EntryPrev, RemainingEntries, EntryOutputs) :-
    EntryCurr \== EntryPrev,
    !,
    RemainingEntries = [EntryCurr-OutputCurr|R],
    EntryOutputs = [].
collect_diffs1([Entry-Output|R], Entry, RemainingEntries, [Output|S]) :-
    collect_diffs1(R, Entry, RemainingEntries, S).

% given a list of table entries TableEntries, a functional dependency Fd and a list of recalculated outputs OutputColDiff
% produce a list of table entries TableEntriesDiff containing only a columns from the given Fd and the corresponding output
calculate_diff_entries(Fd, TableEntries, ParamsList, OutputColDiff, TableEntriesDiff):-
    match_list_indices_sublist(ParamsList, AttrPos, Fd), % get positions AttrPos of input columns
    (foreach(TableEntry, TableEntries),
     foreach(Diff, OutputColDiff),
     foreach(EntryDiff, TableEntriesDiff),
     param(AttrPos)
    do
     match_list_indices_sublist(TableEntry, AttrPos, EntryFd),
     append(EntryFd, [Diff], EntryDiff)
    ).

% given a list of table entries TableEntries, a functional dependency ColSetSplit and
% a list of minimum outputs for each collision within ColSetSplit then:
% - calculate base and Boolean parts of the output column (OutputColBase and OutputColDiff, correspondingly)
% - produce a list of table entries TableEntriesBase containing only a columns from the given Fd and the corresponding base part
%   of the output column
calculate_output_cols_wrt_split(ColSetSplit, OpSplit, MaxDiff, ListOfMinsForEachColSetUniqueEntry, TableEntries, ParamsList,
                                TableEntriesBase, OutputColBase, OutputColDiff) :-
    match_list_indices_sublist(ParamsList, AttrPos, ColSetSplit), % get positions AttrPos of input columns
    (foreach(Entry,            TableEntries),
     foreach(EntryBase,        TableEntriesBaseUnsorted),
     foreach(EntryDiffCol,     OutputColDiff),
     param([OpSplit, MaxDiff, AttrPos, ListOfMinsForEachColSetUniqueEntry])
    do
     last(Entry, XI),
     match_list_indices_sublist(Entry, AttrPos, EntryColSetSplit),
     % first we calculate the list of all input columns projected to the entry
     %(for(ISet, 1, EntryColSetSplit), foreach(XSet, XsSet), param(EntryColSetSplit) do arg(ISet, EntryColSetSplit, XSet)),
     % then we calculate values Base and Diff columns within the entry
     (memberchk(EntryColSetSplit-MinOutput, ListOfMinsForEachColSetUniqueEntry) ->
          (OpSplit = plus ->
               EntryBaseCol is MinOutput,
               EntryDiffCol is XI - MinOutput
          ;
           OpSplit = minus ->
               EntryBaseCol is MinOutput + MaxDiff,
               EntryDiffCol is MinOutput + MaxDiff - XI
          ;
               write(calculate_output_cols_wrt_split(OpSplit)),nl,halt
          )
     ;
          EntryBaseCol is XI,
          EntryDiffCol is 0
     ),
     (EntryDiffCol < 0 ->
          write(calculate_output_cols_wrt_split),nl,
          write([EntryColSetSplit, XI, EntryBaseCol, EntryDiffCol]),nl,
          write(ListOfMinsForEachColSetUniqueEntry),nl, halt
     ;
          true
     ),
     append(EntryColSetSplit, [EntryBaseCol], EntryBase)
    ),
    sort(TableEntriesBaseUnsorted, TableEntriesBase),
    (foreach(TableEntry, TableEntriesBase),
     foreach(OutputCol, OutputColBase)
    do
     last(TableEntry, OutputCol)
    ).

formula_generator_base(KindCombi, CallMap, Table, Col, OptionsBoolCond, Vars, MaxSlack, TableEntries, ParamsList, Fd, CondDecomp, CurMaxCost, ForceToUseOnlySmallFd,
                       ModeOld, VarsMin, VarsMax, FdCand, Cost, Penalty, FormulaFamily, OptionUsedToGenerateConjecture, FormulaPattern) :-
    min_member(VarsMin, Vars),
    max_member(VarsMax, Vars),                  % find minimum and maximum values of rest values
    (VarsMin = VarsMax ->                       % if TableEntriesRest can be expressed as an equivalent to a constant
         FdCand = [],
         Penalty is 0,
         Cost is abs(VarsMin),
         FormulaFamily = cst,
         OptionUsedToGenerateConjecture = [cst],
         InputColsList = [],
         InputNamesList = [],
         InputVarsList = [],
         FormulaTerm = VarsMin,
         FormulaPattern = t(InputColsList, InputNamesList, InputVarsList, FormulaTerm)
    ;
     check_base_eq_output(TableEntries, Fd, EqCol) -> % if TableEntriesRest can be expressed as equivalent to an input column
         FdCand = [EqCol],
         Penalty is 0,
         Cost = 1,
         FormulaFamily = col,
         OptionUsedToGenerateConjecture = [eq_col],
         tab_get_name(EqCol, Name),
         InputColsList = [EqCol],
         InputNamesList = [Name],
         InputVarsList = [EqVar],
         FormulaTerm = EqVar,
         FormulaPattern = t(InputColsList, InputNamesList, InputVarsList, FormulaTerm)
    ;                                          % otherise call formula_generator proper and find a solution
          (MaxSlack = 0 ->  % if no slack then we have to use all Rest columns
              FdList = [Fd]
         ;                 % if there's slack (MaxSlack = 0) or no slack is mentioned (MaxSlack = -1) then we can use a subset of Rest columns
              find_split_fd(Fd, TableEntries, ParamsList, Vars, FdList)
         ),
         % to ensure reasonable performance we take only the first successful solution we use once/1
         once((member(FdCand, FdList),                          % select a functional dependency
               (FdCand = Fd ->
                    TableEntriesFd = TableEntries
               ;
                    append(FdCand, [col(Table, Col)], AttrNamesOutput),
                    append(Fd,     [col(Table, Col)], ParamsOutput),
                    % firstly - collect column indices within AttrNamesOutput
                    match_list_indices_sublist(ParamsOutput, AttrPos, AttrNamesOutput), % get positions AttrPos of input columns
                    % secondly - use collected column indices AttrPos to extract relevant table entries
                    (foreach(TableEntryPassed, TableEntries), foreach(TableEntry, TableEntriesFdUnsorted), param(AttrPos)
                    do
                     match_list_indices_sublist(TableEntryPassed, AttrPos, TableEntry)
                    ),
                    sort(TableEntriesFdUnsorted, TableEntriesFd)
               ),
               (/*CondDecomp = 0 ->
                    LayerOld is 2
               ;*/
                ModeOld = main(_) ->
                    LayerOld is 0
               ;/*
                (CondDecomp = 1, FdCand = Fd) ->
                    LayerOld is 2
               ;*/
                    ModeOld = preprocessed(_, _, _, LayerOld)
               ),
               Layer is LayerOld + 1,
               Mode = preprocessed(VarsMin, VarsMax, CondDecomp, Layer),            % select the preprocessed mode 
               % generate lists of options for the rest part of the decomposition
               gen_options_lists_decomp_base(KindCombi, col(Table,Col), secondary, OptionsBoolCond, [], FdCand, ForceToUseOnlySmallFd,
                                             TableEntriesFd, Mode, ListsOptions, SetsBool),
               % search for the formula by calling formula_generator
               (CondDecomp = 1 -> Cost1 in 0..15 ; true),
               (ModeOld = preprocessed(_, _, _, _) -> TimeOut = 300000 ; TimeOut = 3600000),
               %TimeOut = 3600000,
               time_out(formula_generator(CallMap, KindCombi, OptionsBoolCond, ListsOptions, TableEntriesFd, Mode, SetsBool,
                                          VarsMin, secondary, Table, Col, CurMaxCost, FormulaPattern,
                                          FormulaFamily, OptionUsedToGenerateConjecture, Cost1, Result),
                        TimeOut, success),
               Result \== time_out,
               select_penalty(FormulaFamily, OptionUsedToGenerateConjecture, Penalty),
               Cost is Cost1 + Penalty
              )
             )
    ),
    !.

% get the list of functional dependencies FdDiffListFiltered to explain a given list of output values with given set of columns ColSet
% where each functional dependency contains column Col
find_split_fd(Col, ColSet,  TableEntries,  ParamsList, OutputColDiff, FdDiffListFiltered) :-
    length(ColSet, MaxSize),
    findall(FdCandidate,
            (sublist_max_card(ColSet, MaxSize, FdCandidate),
             memberchk(Col, FdCandidate)),
            FdCandidates),
    find_split_fd1(FdCandidates, TableEntries,  ParamsList, OutputColDiff, FdDiffList),
    select_fds_min_length_plus_one(FdDiffList, FdDiffListFiltered).

% get the list of functional dependencies to explain a given list FdDiffListFiltered of output values with given set of columns ColSet
find_split_fd(ColSet,  TableEntries,  ParamsList, OutputColDiff, FdDiffListFiltered) :-
    length(ColSet, MaxSize),
    findall(FdCandidate,
            sublist_max_card(ColSet, MaxSize, FdCandidate),
            FdCandidates),
    find_split_fd1(FdCandidates, TableEntries,  ParamsList, OutputColDiff, FdDiffList),
    select_fds_min_length_plus_one(FdDiffList, FdDiffListFiltered).

find_split_fd1([], _, _, _, []) :- !.
find_split_fd1([FdCandidate|S], TableEntries,  ParamsList, OutputColDiff, FdDiffListNew):-
    match_list_indices_sublist(ParamsList, AttrPos, FdCandidate), % get positions AttrPos of input columns
    (foreach(TableEntry, TableEntries), foreach(Diff, OutputColDiff), foreach(EntryFd-Diff, Projected),
     param(AttrPos)
    do
     match_list_indices_sublist(TableEntry, AttrPos, EntryFd)
    ),
    sort(Projected, SortedProjected),
    (fd_same_key(SortedProjected) ->
        FdDiffListNew = FdDiffListOld,
        FdCandidates  = S
    ;
        FdDiffListNew = [FdCandidate|FdDiffListOld],
        FdCandidates = S                                        % we search for all FDs 
       %restrict_pks_candidates(S, FdCandidate, FdCandidates)   % as we only search for minimal FDs (for testing purposes)
    ),
    find_split_fd1(FdCandidates, TableEntries,  ParamsList, OutputColDiff, FdDiffListOld).


% given a list of FDs sorted in the order of increasing lengths, e.g. [[c1], [c2], [c1,c2], [c1,c3], [c2,c3], [c1,c2,c3]),
% keep only those of minimum legth and minimum length plus 1. As in the example above it'll remove [c1, c2, c3] from the list 
select_fds_min_length_plus_one(FdList, FdListFiltered) :-
    FdList = [FdFirst|_],
    length(FdFirst, NMin),
    findall(Fd, (member(Fd, FdList),
                 length(Fd, N),
                 N =< NMin + 1),
            FdListFiltered).

check_base_eq_output(TableEntries, ColSet, BaseCol) :-
    nth1(I, ColSet, BaseCol),
    (foreach(TableEntry, TableEntries), param(I)
    do
     nth1(I, TableEntry, Val),
     last(TableEntry, Val)
    ), !.

% whether or not a part of the formula result in a +1 penalty to the cost of the final formula
select_penalty(FormulaFamily, OptionUsedToGenerateConjecture, Penalty) :-
    (memberchk(FormulaFamily, [cond, cond_ex]) ->
         Penalty is 1
    ;
     (FormulaFamily = decomp, OptionUsedToGenerateConjecture = [decomp([FormulaFamilyElsePart,_])],
      memberchk(FormulaFamilyElsePart, [cond, cond_ex,
                                        families([cond_template(_),else(_)])])) ->
         Penalty is 1
    ;
         Penalty is 0
    ).

eval_formula_term_on_entries([TableEntry|R], FormulaTerm) :-
    !,
    remove_last_elem(TableEntry,ParametersValues,ResultValue),
    FormulaTerm = t(_ListOfParemeters, _ListOfNames, ListOfSourceVariables, SourceTerm),
    copy_term(ListOfSourceVariables-SourceTerm, ParametersValues-TargetTerm),
    eval_formula_term(TargetTerm, ResultValue),
    eval_formula_term_on_entries(R, FormulaTerm).
eval_formula_term_on_entries([], _) :- !.