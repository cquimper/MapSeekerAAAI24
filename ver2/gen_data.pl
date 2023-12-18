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
% Purpose: GENERATE THE TABLES ASSOCIATED TO EACH BOUND WE ARE LOOKING FOR: BOUNDS FOR DIGRAPHS AND PARTITIONS
% Author : Nicolas Beldiceanu, IMT Atlantique

:- use_module(library(lists)).
:- use_module(library(samsort)).
:- use_module(library(clpfd)).
:- use_module(utility).

% maximum number of input parameters for which we generate the data tables:
% used to avoid to generate tables with many input parameters as after sharp bounds are hard to obtain
% (also genrating such tables and the corresponding metadata can take a lot of time: e.g. this is the
%  case for group and cgroup which have 11 primary characteristics and 14 secondary characteristics)
% as used custom program for forest, forest0 and tree, the fact max_nb_of_input_parameters/2 is not used for such combinatorial objects
max_nb_of_input_parameters(graph,      4).
max_nb_of_input_parameters(partition,  4).
max_nb_of_input_parameters(partition0, 4).
max_nb_of_input_parameters(group,      3).
max_nb_of_input_parameters(cgroup,     3).

% KindCombi              : combinatorial object for which generate tables, namely graph, partition or partition0
% MaxParams              : if KindCombi=graph      then maximum number of vertices of the graphs      we generate
%                          if KindCombi=partition  then maximum number of elements of the partitions  we generate
%                          if KindCombi=partition0 then maximum number of elements of the partitions0 we generate
%                          if KindCombi=group      then maximum sequence length                       we generate
%                          if KindCombi=cgroup     then maximum sequence length                       we generate
%
% KeepOnlySecondaryWithFD: 1 if should only keep those secondary characteristics that are functionally determined
%                          by the primary characteristics, 0 if should keep all secondary characteristics
%                          (1 used for initial learning, 0 for transfer learning)
top(KindCombi, MaxParams, KeepOnlySecondaryWithFD) :-
    (KeepOnlySecondaryWithFD = 1 ->
        atoms_concat(['data/',KindCombi,'/tables_',KindCombi], PrologTable0)
    ;
        atoms_concat(['data/',KindCombi,'/tablestransfer_',KindCombi], PrologTable0)
    ),
    atom_concat(PrologTable0, '.pl', PrologTable),
    open(PrologTable, write, Tout),                                                     % create the file containing all table names that will be created for KindCombi
    (KindCombi = graph      -> format(Tout, '% Purpose: Tables giving the lower/upper bound of a graph characteristics wrt a set of graph characteristics~n',           []) ;
     KindCombi = partition  -> format(Tout, '% Purpose: Tables giving the lower/upper bound of a partition characteristics wrt a set of partition characteristics~n',   []) ;
     KindCombi = partition0 -> format(Tout, '% Purpose: Tables giving the lower/upper bound of a partition0 characteristics wrt a set of partition0 characteristics~n', []) ;
     KindCombi = group      -> format(Tout, '% Purpose: Tables giving the lower/upper bound of a group characteristics wrt a set of group characteristics~n',           []) ;
     KindCombi = cgroup     -> format(Tout, '% Purpose: Tables giving the lower/upper bound of a circular group characteristics wrt a set of cgroup characteristics~n', []) ;
                               write(top(KindCombi)), nl, halt                                                                                                              ),

    format(Tout, '% Warning: should be added within the tables.pl and tables_list.pl file containing all the tables of all combinatorial objects.~n', []),
    format(Tout, '%          do not forget to add both the max_size_combi/2 in tables.pl and the table/5 in tables_list.pl facts.~n',                 []),
    format(Tout, '% Author : Nicolas Beldiceanu, IMT Atlantique~n~n',                                                                                 []),

    format(Tout, ':- module(tables,[attributes_combi/2,~n',                             []),
    format(Tout, '                  low_up_attributes_combi/2,~n',                      []),
    format(Tout, '                  max_size_combi/2,~n',                               []),
    format(Tout, '                  get_tables/5,~n',                                   []),
    format(Tout, '                  get_table/5,~n',                                    []),
    format(Tout, '                  table/6,~n',                                        []),
    format(Tout, '                  extract_index_names_from_table_signature/3]).~n~n', []),
    
    format(Tout, 'attributes_combi(graph,      [v,c,minc,maxc,s,mins,maxs,mina,maxa]).                                 % digraph (partition of partition)~n',                            []),
    format(Tout, 'attributes_combi(forest,     [v,t,f,minf,maxf,mind,maxd,minp,maxp,mint,maxt]).                       % forest~n',                                                      []),
    format(Tout, 'attributes_combi(forest0,    [v,t,f,minf,maxf,mind,maxd,minp,maxp,mint,maxt]).                       % forest without isolated vertex~n',                              []),
    format(Tout, 'attributes_combi(tree,       [v,f,mind,maxd,minp,maxp]).                                             % one single tree~n',                                             []),
    format(Tout, 'attributes_combi(partition,  [n,nval,min,max,range,sum_squares]).                                    % partition (extend nvalue)~n',                                   []),
    format(Tout, 'attributes_combi(partition0, [n,m,nval,min,max,range,sum_squares]).                                  % partition (extend nvalue but do not consider unsued values)~n', []),
    format(Tout, 'attributes_combi(group,      [n,ng,nv,smin,smax,srange,ssum_squares,dmin,dmax,drange,dsum_squares]). % group constraint~n',                                            []),
    format(Tout, 'attributes_combi(cgroup,     [n,ng,nv,smin,smax,srange,ssum_squares,dmin,dmax,drange,dsum_squares]). % cyclic group constraint~n~n',                                   []),

    format(Tout, 'low_up_attributes_combi(graph,      [low-v,low-c,low-minc,low-maxc,low-s,low-mins,low-maxs,low-mina,~n',                                               []),
    format(Tout, '                                     up-v, up-c, up-minc, up-maxc, up-s, up-mins, up-maxs, up-maxa]).~n',                                              []),
    format(Tout, 'low_up_attributes_combi(forest,     [low-t,low-f,low-minf,low-maxf,low-mind,low-maxd,low-minp,low-maxp,low-mint,low-maxt,~n',                          []),
    format(Tout, '                                     up-t, up-f, up-minf, up-maxf, up-mind, up-maxd, up-minp, up-maxp, up-mint, up-maxt]).~n',                         []),
    format(Tout, 'low_up_attributes_combi(forest0,     [low-t,low-f,low-minf,low-maxf,low-mind,low-maxd,low-minp,low-maxp,low-mint,low-maxt,~n',                         []),
    format(Tout, '                                     up-t, up-f, up-minf, up-maxf, up-mind, up-maxd, up-minp, up-maxp, up-mint, up-maxt]).~n',                         []),
    format(Tout, 'low_up_attributes_combi(tree,       [low-f,low-mind,low-maxd,low-minp,low-maxp,~n',                                                                    []),
    format(Tout, '                                     up-f, up-mind, up-maxd, up-minp, up-maxp]).~n',                                                                   []),
    format(Tout, 'low_up_attributes_combi(partition,  [low-nval,low-min,low-max,low-range,low-sum_squares,~n',                                                           []),
    format(Tout, '                                     up-nval, up-min, up-max, up-range, up-sum_squares]).~n',                                                          []),
    format(Tout, 'low_up_attributes_combi(partition0, [low-nval,low-min,low-max,low-range,low-sum_squares,~n',                                                           []),
    format(Tout, '                                     up-nval, up-min, up-max, up-range, up-sum_squares]).~n',                                                          []),
    format(Tout, 'low_up_attributes_combi(group,      [low-ng,low-nv,low-smin,low-smax,low-srange,low-ssum_squares,low-dmin,low-dmax,low-drange,low-dsum_squares,~n',    []),
    format(Tout, '                                     up-ng, up-nv, up-smin, up-smax, up-srange, up-ssum_squares, up-dmin, up-dmax, up-drange, up-dsum_squares]).~n',   []),
    format(Tout, 'low_up_attributes_combi(cgroup,     [low-ng,low-nv,low-smin,low-smax,low-srange,low-ssum_squares,low-dmin,low-dmax,low-drange,low-dsum_squares,~n',    []),
    format(Tout, '                                     up-ng, up-nv, up-smin, up-smax, up-srange, up-ssum_squares, up-dmin, up-dmax, up-drange, up-dsum_squares]).~n~n', []),

    format(Tout, 'max_size_combi(model_seeker,  0). % no nodes when in model_seeker mode~n',                                 []),
    format(Tout, 'max_size_combi(forest,       18). % maximum number of nodes for which we generate forests~n',              []),
    format(Tout, 'max_size_combi(forest0,      18). % maximum number of nodes for which we generate forests~n',              []),
    format(Tout, 'max_size_combi(tree,         18). % maximum number of nodes for which we generate trees~n',                []),
    format(Tout, 'max_size_combi(graph,        26). % maximum number of nodes for which we generate graphs~n',               []),
    format(Tout, 'max_size_combi(partition,    30). % maximum number of elements for which we generate partitions~n',        []),
    format(Tout, 'max_size_combi(partition0,   30). % maximum number of elements for which we generate partitions0~n',       []),
    format(Tout, 'max_size_combi(group,        30). % maximum number of elements for which we generate groups~n',            []),
    format(Tout, 'max_size_combi(cgroup,       30). % maximum number of elements for which we generate circular groups~n~n', []),
    
    format(Tout, 'get_tables(KindCombi, MaxN, NParam, BoundOrOptions, TableNames) :-~n',                   []),
    format(Tout, '    findall(Name, table(KindCombi,Name,MaxN,_,NParam,BoundOrOptions), TableNames).~n~n', []),
    format(Tout, 'get_table(KindCombi, MaxN, NParam, BoundOrOptions, TableName) :-~n',                     []),
    format(Tout, '    table(KindCombi, TableName, MaxN, _, NParam, BoundOrOptions),~n',                    []),
    format(Tout, '    !. % normally table names should be distinct, but who knows~n~n',                    []),
    format(Tout, 'table(KindCombi, Name, MaxN, NCol, NParam, BoundOrOptions) :-~n',                        []),
    format(Tout, '    table(KindCombi, Name, ListMaxNNCol, NParam, BoundOrOptions),~n',                    []),
    format(Tout, '    member(MaxN-NCol, ListMaxNNCol).~n~n',                                               []),

    format(Tout, '% Each table has the following arguments:~n',                                                                                                                         []),
    format(Tout, '%  . the type of combinatorial object (graph forest, forest0, tree, partition, partition0, group, cgroup) or the fact that we use the model seeker (model_seeker)~n', []),
    format(Tout, '%  . the name of the table~n',                                                                                                                                        []),
    format(Tout, '%  . the list of pairs of the form MaxN-NCol where~n',                                                                                                                []),
    format(Tout, '%     - MaxN is the maximum number of elements used to generate a table~n',                                                                                           []),
    format(Tout, '%     - NCol is the corresponding number of columns of the same table~n',                                                                                             []),
    format(Tout, '%  . the number of parameters of the lower/upper bound~n',                                                                                                            []),
    format(Tout, '%  . the lower/upper bound considered~n~n',                                                                                                                           []),

    gen_data(KindCombi, MaxParams, KeepOnlySecondaryWithFD, Tout),
    close(Tout).

gen_data(KindCombi, MaxParams, KeepOnlySecondaryWithFD, _Tout) :-
    atom_concat('data/', KindCombi, Directory0),  
    (KeepOnlySecondaryWithFD = 1 ->                 % if initial learning then
        MaxN in 2..MaxParams,                       % generates tables for all sizes
        atom_concat(Directory0, '/data', Directory)
    ;                                               % if transfer learning then
        MaxN = MaxParams,                           % generates only table for largest size
        atom_concat(Directory0, '/datatransfer', Directory)
    ),
    indomain(MaxN),
    write(gen(MaxN)), nl,
    statistics(runtime, [Time0|_]),
    number_codes(MaxN, CodesMaxN),                  % convert MaxN to an atom in order to create
    atom_codes(AtomMaxN, CodesMaxN),                % the name of the subfolder that will contain
    atom_concat(Directory, AtomMaxN, PrefixName0),  % all tables corresponding to combinatorial objects that have up to MaxN vertices
    atom_concat(PrefixName0, '/', PrefixName),
    gen_tables_up_to_a_given_parameter_size(KindCombi, MaxN, KeepOnlySecondaryWithFD, PrefixName),
    statistics(runtime, [Time1|_]), Time is Time1-Time0, write(time(Time)), nl,
    false.
gen_data(KindCombi, _, _, Tout) :-
    findall(Name, table(Name,_,_,_,_), TableNames),
    sort(TableNames, Names),
    gen_table_data(Names, KindCombi, Tout).         % generate one fact for each table

gen_table_data([], _, _) :- !, retractall(table(_,_,_,_,_)).             % once printed, remove all table facts
gen_table_data([Name|R], KindCombi, Tout) :-                             % for each table regroup
    findall(Size-NCol, table(Name, Size, NCol, _, _), Pairs),            % size and number of columns
    once(table(Name, _, _, LenCombination, Bound)),
    format(Tout, 'table(~w, ~w, ~w, ~w, ~w).~n', [KindCombi,Name,Pairs,LenCombination,Bound]),
    gen_table_data(R, KindCombi, Tout).

gen_tables_up_to_a_given_parameter_size(KindCombi, MaxN, KeepOnlySecondaryWithFD, PrefixName) :-
    (KindCombi = graph ->
        Primaries   = [1-v,2-c,3-minc,4-maxc,5-s,6-mins,7-maxs,8-mina,9-maxa],                                                                        % primary and secondary char.
        Secondaries = [10-minmaxc,11-midc,12-rminc,13-ominc,14-omaxc,15-omidc,16-oc,17-oc23,18-omins,19-omaxs,20-os]
    ;
     KindCombi = partition ->
        Primaries   = [1-n,2-nval,3-min,4-max,5-range,6-sum_squares],                                                                                 % primary and secondary char.
        Secondaries = [7-minmax,8-mid,9-rmin,10-omin,11-omax,12-omid,13-oc]
    ;
     KindCombi = partition0 ->
        Primaries   = [1-n,2-m,3-nval,4-min,5-max,6-range,7-sum_squares],                                                                             % primary and secondary char.
        Secondaries = [8-mid,9-rmin,10-omin,11-omax,12-omid,13-oc,14-oc1]
    ;
     KindCombi = group ->
        Primaries   = [1-n,2-ng,3-nv,4-smin,5-smax,6-srange,7-ssum_squares,8-dmin,9-dmax,10-drange,11-dsum_squares],                                  % primary and secondary char.
        Secondaries = [12-sminsmax,13-smid,14-rsmin,15-osmin,16-osmax,17-osmid,18-osc,19-dmindmax,20-dmid,21-rdmin,22-odmin,23-odmax,24-odmid,25-odc]
    ;
     KindCombi = cgroup ->
        Primaries   = [1-n,2-ng,3-nv,4-smin,5-smax,6-srange,7-ssum_squares,8-dmin,9-dmax,10-drange,11-dsum_squares],                                  % primary and secondary char.
        Secondaries = [12-sminsmax,13-smid,14-rsmin,15-osmin,16-osmax,17-osmid,18-osc,19-dmindmax,20-dmid,21-rdmin,22-odmin,23-odmax,24-odmid,25-odc]
    ;
        write(gen_tables_up_to_a_given_parameter_size(KindCombi)), nl, halt
    ),
    append(Primaries, Secondaries, PrimariesSecondaries),
    (KindCombi = graph ->
        findall(Char, gen_partitions_of_partitions(MaxN, Char), Sol), sort(Sol, SortedSol) % compute all partitions of partitions
    ;
     KindCombi = partition ->
        findall(Char,               gen_partitions(MaxN, Char), Sol), sort(Sol, SortedSol) % compute all partitions
    ;
     KindCombi = partition0 ->
        findall(Char,              gen_partitions0(MaxN, Char), Sol), sort(Sol, SortedSol) % compute all partitions0
    ;
     KindCombi = group ->
        findall(Char,                   gen_groups(MaxN, Char), Sol), sort(Sol, SortedSol) % compute all groups
    ;
        findall(Char,                  gen_cgroups(MaxN, Char), Sol), sort(Sol, SortedSol) % compute all circular groups
    ),
    SortedSol = [FirstSol|_],
    functor(FirstSol, t, LenSource),
    length(Primaries, LenPrimary),
    gen_combination(KindCombi, Primaries, Bound, LenCombination, Combination), % generate a combination of primary char. and a bound
    arg(1, Bound, PrimaryBound),
    append(Combination, [PrimaryBound], CombinationBound),                     % extract unselected primaries as they will used as secondary char.
    findall(Char, (member(Char,Primaries),
                   \+ memberchk(Char,CombinationBound),
                   Char \= _-mina, Char \= _-maxa), UnselectedPrimaries),
    gen_extraction_terms(KindCombi, LenSource, LenPrimary, LenCombination, Combination,
                         Bound, UnselectedPrimaries, SelectedPrimaryNames,
                         LenSecondary, Functor, TargetTerm, SourceTerm, ITargetISource),
    handle_one_combination_of_characteristics(SortedSol, KeepOnlySecondaryWithFD, LenSecondary,
                                              LenCombination, TargetTerm, SourceTerm, Bound,
                                              IndexSelectedSecondary, NormalisedOptimalSol),
    filter_invalid_optimals(KindCombi, Bound, Combination, MaxN, NormalisedOptimalSol, FilteredOptimalSol),
    findall(Char, (member(I,IndexSelectedSecondary),
                   memberchk(I-J, ITargetISource),
                   memberchk(J-Char, PrimariesSecondaries)), SelectedSecondaryNames),
    append(SelectedPrimaryNames, SelectedSecondaryNames, SelectedNames),
    build_signature(MaxN, Functor, SelectedNames, Combination, Bound, Signature),
    length(SelectedNames, A),
    (FilteredOptimalSol = [] ->
        nl, write('COULD NO GENERATE A TABLE FOR '), write(Functor), write(' AS MAXIMUM NUMBER OF NODES '), write(MaxN), write(' IS TOO SMALL'), nl
    ;
        % assert the table facts as will have to group together size and number of columns of tables
        % which have the same name in a list of pairs to reduce the number of facts: one fact for each name
        functor(Bound, FBound, _),
        arg(1, Bound, _-ABound),
        functor(FABound, FBound, 1), arg(1, FABound, ABound),
        assert(table(Functor, MaxN, A, LenCombination, FABound))
    ),
    atom_concat(PrefixName, Functor, PrefixNameFunctor),
    atom_concat(PrefixNameFunctor, '.pl', PrologFile),
    open(PrologFile, write, Sout),
    format(Sout,':- multifile signature/3.~n',[]),
    format(Sout,':- multifile ~w/~w.~n',[Functor,A]),
    format(Sout,':- dynamic signature/3.~n',[]),
    format(Sout,':- dynamic ~w/~w.~n~n',[Functor,A]),
    format(Sout,'~w.~n~n',[Signature]),
    write_list(FilteredOptimalSol, Sout),
    close(Sout),
    false.
gen_tables_up_to_a_given_parameter_size(_, _, _, _).

build_signature(MaxN, Functor, Args, Combination, Bound, Signature) :-
    functor(Signature, signature, 3),
    arg(1, Signature, Functor),
    arg(2, Signature, MaxN),
    arg(3, Signature, Arg3),
    length(Args, A),
    functor(Arg3, t, A),
    build_signature1(Args, 1, Combination, Bound, Arg3).

build_signature1([], _, _, _, _) :- !.
build_signature1([Name|R], I, Combination, Bound, Term) :-
    (Bound = low(_-Name)            -> P = low,       S = output ;  % lower bound tagged as low
     Bound =  up(_-Name)            -> P = up,        S = output ;  % upper bound tagged as up
     memberchk(_-Name, Combination) -> P = primary,   S = input  ;  % selected primary char. tagged as primary char.
                                       P = secondary, S = input  ), % unselected primary char. will be tagged as secondary char.
    arg(I, Term, t(Name, P, S)),
    I1 is I+1,
    build_signature1(R, I1, Combination, Bound, Term).

gen_combination(KindCombi, Primaries, Bound, LenCombination, Combination) :-
    length(Primaries, NPrimary),                                        % number of primary characteristics
    length(Selection, NPrimary),                                        % create a selection variable for each primary characteristics whose value is:
    Ignored  = 0,                                                       %  . do no consider a primary characteristics
    Selected = 1,                                                       %  . a primary characteristics is keept in the projection
    Lower    = 2,                                                       %  . a primary characteristics is the lower bound we are focussing on
    Upper    = 3,                                                       %  . a primary characteristics is the upper bound we are focussing on
    domain(Selection, Ignored, Upper),
    max_nb_of_input_parameters(KindCombi, MaxNbOfInputParameters),      % get maximum number of input parameters used for generating tables
    MinIgnored is max(0,NPrimary-MaxNbOfInputParameters-1),             % minimum number of primary characteristics to ignored in order not to exceed (-1 for bound parameter)
    count(Ignored, Selection, #>=, MinIgnored),                         % maxiumm number of input parameters of a table (used to generate fewer tables)
    (KindCombi = graph ->
        memberchk(V-v,                    Primaries), nth1(V,          Selection, SV),          % get selection variable associated with the primary characteristics v
        memberchk(C-c,                    Primaries), nth1(C,          Selection, SC),          % get selection variable associated with the primary characteristics c
        memberchk(Minc-minc,              Primaries), nth1(Minc,       Selection, SMinc),       % get selection variable associated with the primary characteristics minc
        memberchk(Maxc-maxc,              Primaries), nth1(Maxc,       Selection, SMaxc),       % get selection variable associated with the primary characteristics maxc
        memberchk(S-s,                    Primaries), nth1(S,          Selection, SS),          % get selection variable associated with the primary characteristics s
        memberchk(Mins-mins,              Primaries), nth1(Mins,       Selection, SMins),       % get selection variable associated with the primary characteristics mins
        memberchk(Maxs-maxs,              Primaries), nth1(Maxs,       Selection, SMaxs),       % get selection variable associated with the primary characteristics maxs
        memberchk(Mina-mina,              Primaries), nth1(Mina,       Selection, SMina),       % get selection variable associated with the primary characteristics mina
        memberchk(Maxa-maxa,              Primaries), nth1(Maxa,       Selection, SMaxa),       % get selection variable associated with the primary characteristics maxa
        SMina #\= Selected, SMina #\= Upper,                                                    % mina cannot be selected, and cannot be used as an upper bound
        SMaxa #\= Selected, SMaxa #\= Lower,                                                    % maxa cannot be selected, and cannot be used as an lower bound
                                                                                                % selecting an upper bound may require selecting some primary characteristics
        SV    #= Upper #=> ((SC#=Selected #/\ SMaxc#=Selected) #\/ (SS#=Selected #/\ SMaxs#=Selected) #\/ (SS#=Selected #/\ SMaxc#=Selected)),
        SC    #= Upper #=> (SV#=Selected #\/ SS#=Selected),
        SMinc #= Upper #=> (SV#=Selected #\/ SMaxc#=Selected #\/ (SS#=Selected #/\ SMaxs#=Selected)),
        SMaxc #= Upper #=> (SV#=Selected),
        SS    #= Upper #=> (SV#=Selected #\/ (SC#=Selected #/\ SMaxc#=Selected)),
        SMins #= Upper #=> (SV#=Selected #\/ SMaxc#=Selected #\/ SMaxs#=Selected),
        SMaxs #= Upper #=> (SV#=Selected #\/ SMaxc#=Selected),
        SMaxa #= Upper #=> (SV#=Selected #\/ (SC#=Selected #/\ SMaxc#=Selected) #\/ (SS#=Selected #/\ SMaxs#=Selected) #\/ (SS#=Selected #/\ SMaxc#=Selected))
    ;
     KindCombi = partition ->
        memberchk(N-n,                      Primaries), nth1(N,           Selection,  SN),          % get selection variable associated with the primary characteristics n
        memberchk(NVal-nval,                Primaries), nth1(NVal,        Selection, _SNVal),       % get selection variable associated with the primary characteristics nval
        memberchk(Min-min,                  Primaries), nth1(Min,         Selection, _SMin),        % get selection variable associated with the primary characteristics min
        memberchk(Max-max,                  Primaries), nth1(Max,         Selection, _SMax),        % get selection variable associated with the primary characteristics max
        memberchk(Range-range,              Primaries), nth1(Range,       Selection, _SRange),      % get selection variable associated with the primary characteristics range
        memberchk(SumSquares-sum_squares,   Primaries), nth1(SumSquares,  Selection, _SSumSquares), % get selection variable associated with the primary characteristics sum_squares
        SN #= 1                                                                                     % n has to be selected (the number of elements of a partition is always an input parameter)
    ; 
     KindCombi = partition0 ->
        memberchk(N-n,                      Primaries), nth1(N,           Selection,  SN),          % get selection variable associated with the primary characteristics n
        memberchk(M-m,                      Primaries), nth1(M,           Selection,  SM),          % get selection variable associated with the primary characteristics m
        memberchk(NVal-nval,                Primaries), nth1(NVal,        Selection, _SNVal),       % get selection variable associated with the primary characteristics nval
        memberchk(Min-min,                  Primaries), nth1(Min,         Selection, _SMin),        % get selection variable associated with the primary characteristics min
        memberchk(Max-max,                  Primaries), nth1(Max,         Selection, _SMax),        % get selection variable associated with the primary characteristics max
        memberchk(Range-range,              Primaries), nth1(Range,       Selection, _SRange),      % get selection variable associated with the primary characteristics range
        memberchk(SumSquares-sum_squares,   Primaries), nth1(SumSquares,  Selection, _SSumSquares), % get selection variable associated with the primary characteristics sum_squares
        SN #= 1,                                                                                    % n has to be selected (the number of elements of a partition is always an input parameter)
        SM #= 1                                                                                     % m has to be selected (the maximum number of values is always an input parameter)
    ;
     memberchk(KindCombi, [group,cgroup]) ->
        memberchk(N-n,                      Primaries), nth1(N,           Selection,  SN),          % get selection variable associated with the primary characteristics n
        memberchk(NG-ng,                    Primaries), nth1(NG,          Selection, _NG),          % get selection variable associated with the primary characteristics ng
        memberchk(NV-nv,                    Primaries), nth1(NV,          Selection, _NV),          % get selection variable associated with the primary characteristics nv
        memberchk(SMin-smin,                Primaries), nth1(SMin,        Selection, _SMin),        % get selection variable associated with the primary characteristics smin
        memberchk(SMax-smax,                Primaries), nth1(SMax,        Selection, _SMax),        % get selection variable associated with the primary characteristics smax
        memberchk(SRange-srange,            Primaries), nth1(SRange,      Selection, _SRange),      % get selection variable associated with the primary characteristics srange
        memberchk(SSumSquares-ssum_squares, Primaries), nth1(SSumSquares, Selection, _SSumSquares), % get selection variable associated with the primary characteristics ssum_squares
        memberchk(DMin-dmin,                Primaries), nth1(DMin,        Selection, _DMin),        % get selection variable associated with the primary characteristics dmin
        memberchk(DMax-dmax,                Primaries), nth1(DMax,        Selection, _DMax),        % get selection variable associated with the primary characteristics dmax
        memberchk(DRange-drange,            Primaries), nth1(DRange,      Selection, _DRange),      % get selection variable associated with the primary characteristics drange
        memberchk(DSumSquares-dsum_squares, Primaries), nth1(DSumSquares, Selection, _DSumSquares), % get selection variable associated with the primary characteristics dsum_squares
        SN #= 1                                                                                     % n has to be selected (the sequence length is always an input parameter)
    ;
        write(gen_combination(KindCombi)), nl, halt
    ),
    domain([Low,Up], 0, 1),                                             % Low=1 if focus on lower bound, Low=0 if focus on upper bound
    count(Lower,    Selection, #=,  Low),                               % set Low wrt selection variables
    count(Upper,    Selection, #=,  Up),                                % set Up  wrt selection variables
    count(Selected, Selection, #>=, 1),                                 % at least one primary characteristics is keept in the projection
    Low + Up #= 1,                                                      % we focus either on the lower bound, either on the upper bound
    gen_sum_term(Selection, var, SumTerm),                              % as want to label by increasing number of primary characteristics
    call(Sum #= SumTerm),
    labeling_select(Selection, [Lower,Upper]),                          % first choose a bound
    indomain(Sum),                                                      % then label by increasing number of primary characteristics
    labeling_vals(Selection, [Selected,Ignored,Lower,Upper]),           % generate a feasible combination of primary characteristics
    get_combination(Primaries, Selection, Selected, Combination),       % translate back the found combination
    get_bound(Selection, 1, Lower, Upper, Primaries, Bound),            % translate back the found bound
    length(Combination, LenCombination).

get_combination([], _, _, []) :- !.
get_combination([I-C|R], Selection, Selected, Res) :-
    nth1(I, Selection, Val),
    (Val = Selected -> Res = [I-C|Combination] ; Res = Combination),
     get_combination(R, Selection, Selected, Combination).

get_bound([Lower|_], Index, Lower, _, Primaries, Bound) :- !, memberchk(Index-Name, Primaries), Bound = low(Index-Name).
get_bound([Upper|_], Index, _, Upper, Primaries, Bound) :- !, memberchk(Index-Name, Primaries), Bound = up(Index-Name).
get_bound([_|R], Index, Lower, Upper, Primaries, Bound) :-
    Index1 is Index+1,
    get_bound(R, Index1, Lower, Upper, Primaries, Bound).

gen_extraction_terms(KindCombi, LenSource, LenPrimary, LenCombination, Combination, Bound, UnselectedPrimaries, SelectedPrimaryNames,
                     LenSecondary, Functor, TargetTerm, SourceTerm, ITargetISource) :-
    functor(Bound, LowUp, 1),
    arg(1, Bound, Opt),
    append(Combination, [Opt], Names),
    keys_and_values(Names, _, SelectedPrimaryNames),
    build_functor_name(Names, LowUp, Functor),
    length(Combination, LenCombination),
    Opt = _-B,
    (KindCombi = graph ->
        (memberchk(B, [mina,maxa]) ->  % if B corresponds to mina then maxa will not occur in the target term
            Correction = 1             % if B corresponds to maxa then mina will not occur in the target term
        ;                              % if B does not correspond to mina or maxa
            Correction = 2             % then both mina and maxa will not occur in the target term
        )
    ;
        Correction = 0                 % no correction if on partition or partition0
    ),
    LenTarget is LenSource-Correction,
    functor(TargetTerm, Functor, LenTarget),
    functor(SourceTerm, t,       LenSource),
    unify_vars_extraction_terms_primary(Combination, 1, Opt, TargetTerm, SourceTerm),                      % handle selected primary characteristics
    ITarget1 is LenCombination+2,
    unify_vars_extraction_terms_unselected_primary(UnselectedPrimaries, ITarget1,                          % handle unselected primary characteristics
                                                   TargetTerm, SourceTerm, ITargetISource1),
    ISource2 is LenPrimary+1,                                                                              % index of first secondary characteristics
    ITarget2 is ISource2-Correction,
    unify_vars_extraction_terms_secondary(ISource2, ITarget2, LenSource,                                   % handle secondary characteristics
                                          TargetTerm, SourceTerm, ITargetISource2),
    LenSecondary is LenTarget-LenCombination-1,
    append(ITargetISource1, ITargetISource2, ITargetISource).

build_functor_name([], FunctorName, FunctorName) :- !.
build_functor_name([_-NameChar|R], Prefix, FunctorName) :-
    atom_concat(Prefix, '_', P),
    atom_concat(P, NameChar, Q),
    build_functor_name(R, Q, FunctorName).

unify_vars_extraction_terms_primary([], I, J-_, TargetTerm, SourceTerm) :- !,
    arg(J, SourceTerm, Var),    
    arg(I, TargetTerm, Var).
unify_vars_extraction_terms_primary([J-_|R], I, Opt, TargetTerm, SourceTerm) :-
    arg(J, SourceTerm, Var),
    arg(I, TargetTerm, Var),
    I1 is I+1,
    unify_vars_extraction_terms_primary(R, I1, Opt, TargetTerm, SourceTerm).

unify_vars_extraction_terms_unselected_primary([], _, _, _, []) :- !.
unify_vars_extraction_terms_unselected_primary([J-Char|R], I, TargetTerm, SourceTerm, [I-J|S]) :-
    (memberchk(Char,[mina,maxa]) -> % the unselected primary characteristics that correspond to mina or maxa
        I1 = I                      % are never used as secondary characteristics
    ;
        arg(J, SourceTerm, Var),
        arg(I, TargetTerm, Var),
        I1 is I+1
    ),
    unify_vars_extraction_terms_unselected_primary(R, I1, TargetTerm, SourceTerm, S).

unify_vars_extraction_terms_secondary(ISource, _, Len, _, _, []) :-
    ISource > Len, !.
unify_vars_extraction_terms_secondary(ISource, ITarget, Len, TargetTerm, SourceTerm, [ITarget-ISource|S]) :-
    ISource =< Len,
    arg(ISource, SourceTerm, Var),
    arg(ITarget, TargetTerm, Var),
    ISource1 is ISource+1,
    ITarget1 is ITarget+1,
    unify_vars_extraction_terms_secondary(ISource1, ITarget1, Len, TargetTerm, SourceTerm, S).

handle_one_combination_of_characteristics(SortedSol, KeepOnlySecondaryWithFD, LenSecondary, LenCombination, Term1, Term2, Bound, NewSecondary, NormalisedOptimalSol) :-
    findall(Term1, member(Term2, SortedSol), ProjectedSol),
    sort(ProjectedSol, SortedProjectedSol),
    LenCombination1 is LenCombination+1,
    StartSecondary is LenCombination1+1,
    EndSecondary is LenCombination1+LenSecondary,
    findall(Ind, (Ind in StartSecondary..EndSecondary, indomain(Ind)), IndSecondary),
    (Bound = low(_) -> NormalisedSortedProjectedSol = SortedProjectedSol ; reverse(SortedProjectedSol, NormalisedSortedProjectedSol)),
    keep_optimal(KeepOnlySecondaryWithFD, NormalisedSortedProjectedSol, LenCombination, LenCombination1, IndSecondary, OptimalSol, NewSecondary),
    length(NewSecondary, LenNewSecondary),
    (LenNewSecondary = LenSecondary ->
        Optimal = OptimalSol
    ;
        filter_non_fd_secondary(OptimalSol, LenCombination, LenSecondary, LenNewSecondary, NewSecondary, Optimal)
    ),
    (Bound = low(_) -> NormalisedOptimalSol = Optimal ; reverse(Optimal, NormalisedOptimalSol)).

keep_optimal(1, NormalisedSortedProjectedSol, LenCombination, LenCombination1, IndSecondary, OptimalSol, NewSecondary) :- !,
    keep_optimal1(NormalisedSortedProjectedSol, LenCombination, LenCombination1, IndSecondary, OptimalSol, NewSecondary).
keep_optimal(0, NormalisedSortedProjectedSol, LenCombination, LenCombination1, IndSecondary, OptimalSol, IndSecondary) :-
    keep_optimal0(NormalisedSortedProjectedSol, LenCombination, LenCombination1, OptimalSol).

% keep only secondary characteristics which are functionaly determined by the primary characteristics
keep_optimal1([], _, _, NewSecondary, [], NewSecondary) :- !.
keep_optimal1([Char|R], LenCombination, LenCombination1, IndSecondary, [Char|S], NewSecondary) :-
    skip_same_optimal(R, Char, LenCombination1, IndSecondary, Rest, RestSecondary),
    skip_non_optimal(Rest, Char, LenCombination, NewRest),
    keep_optimal1(NewRest, LenCombination, LenCombination1, RestSecondary, S, NewSecondary).

% keep a secondary characteristics even it may not be functionally determined by the primary characteristics
keep_optimal0([], _, _, []) :- !.
keep_optimal0([Char|R], LenCombination, LenCombination1, [Char|Anchor]) :- % keep first solution Char (as solutions sorted on cost)
    keep_opt0(R, Char, LenCombination, LenCombination1, Anchor).           % complete the end of the resulting list

keep_opt0([], _, _, _, []) :- !.                                        % set anchor to empty to "close" the list
keep_opt0([Char2|R], Char1, LenCombination, LenCombination1, Anchor) :- % if current solution Char2 has the same cost as
    same_args(1, LenCombination1, Char1, Char2), !,                     % the already keept solution then
    Anchor = [Char2|NewAnchor],                                         % keep Char2 (add it at the end of the list)
    keep_opt0(R, Char1, LenCombination, LenCombination1, NewAnchor).
keep_opt0(Sols, Char1, LenCombination, LenCombination1, Anchor) :-      % the first element of Sols is suboptimal, so we
    skip_non_opt(Sols, Char1, LenCombination, Rest),                    % skip all suboptimal solutions wrt to sol Char1
    (Rest = [] ->                                                       % if after skipping suboptimal solutions there is nothing
        Anchor = []                                                     % to handle we close the list of kept optimal solutions
    ;                                                                   % if after skipping suboptimal solutions there is still
        Rest = [NextChar1|NextRest],                                    % some solutions then record the next optimal solution
        Anchor = [NextChar1|NewAnchor],                                 % and complete the end of the resulting list
        keep_opt0(NextRest, NextChar1, LenCombination, LenCombination1, NewAnchor)
    ).

skip_non_opt([], _, _, []) :- !.                       % if not more solutions return an empty list
skip_non_opt([Char2|R], Char1, LenCombination, Res) :- % if at least one solution
    same_args(1, LenCombination, Char1, Char2), !,     % if current solution Char2 has the same input parameters
    !,                                                 % then skip Char2 and continue to remove solutions that have the
    skip_non_opt(R, Char1, LenCombination, Res).       % same input parameters as Char1
skip_non_opt(Res, _, _, Res).

keep_same_optimal([], _, _, RestSecondary, [], RestSecondary) :- !.
keep_same_optimal([Char1|R], Char, LenCombination1, IndSecondary, Rest, RestSecondary) :-
    same_args(1, LenCombination1, Char1, Char), !,
    keep_same_optimal(R, Char, LenCombination1, IndSecondary, Rest, RestSecondary).
keep_same_optimal(Rest, _, _, RestSecondary, Rest, RestSecondary).

skip_same_optimal([], _, _, RestSecondary, [], RestSecondary) :- !.
skip_same_optimal([Char1|R], Char, LenCombination1, IndSecondary, Rest, RestSecondary) :-
    same_args(1, LenCombination1, Char1, Char), !,
    update_functional_dependency_secondary(IndSecondary, Char1, Char, NewSecondary),
    skip_same_optimal(R, Char, LenCombination1, NewSecondary, Rest, RestSecondary).
skip_same_optimal(Rest, _, _, RestSecondary, Rest, RestSecondary).

skip_non_optimal([], _, _, []) :- !.
skip_non_optimal([Char1|R], Char, LenCombination, Rest) :-
    same_args(1, LenCombination, Char1, Char), !,
    skip_non_optimal(R, Char, LenCombination, Rest).
skip_non_optimal(Rest, _, _, Rest).

update_functional_dependency_secondary([], _, _, []) :- !.
update_functional_dependency_secondary([I|R], Term1, Term2, [I|S]) :-
    arg(I, Term1, Val),
    arg(I, Term2, Val),
    !,
    update_functional_dependency_secondary(R, Term1, Term2, S).
update_functional_dependency_secondary([_|R], Term1, Term2, S) :-
    update_functional_dependency_secondary(R, Term1, Term2, S).

filter_non_fd_secondary(OptimalSol, LenCombination, LenSecondary, LenNewSecondary, NewSecondary, Optimal) :-
    (OptimalSol = [Sol|_] -> functor(Sol, Functor, _) ; write(filter_non_fd_secondary), nl, halt),
    LenCombination1 is LenCombination+1,
    LenCombination2 is LenCombination1+1,
    LenSource is LenCombination1+LenSecondary,
    LenTarget is LenCombination1+LenNewSecondary,
    functor(SourceTerm, Functor, LenSource),
    functor(TargetTerm, Functor, LenTarget),
    unify_consecutive_vars(1, LenCombination1, SourceTerm, TargetTerm),
    unify_non_consecutive_vars(NewSecondary, LenCombination2, SourceTerm, TargetTerm),
    findall(TargetTerm, member(SourceTerm, OptimalSol), Optimal).

filter_invalid_optimals(KindCombi, BoundTerm, Combination, MaxN, NormalisedOptimalSol, FilteredOptimalSol) :-
    arg(1, BoundTerm, _-Bound),                                           % extract characteristics for which compute lower or upper bound
    functor(BoundTerm, BoundType, 1),                                     % extract the type of bound we are looking at: low or up
    gen_target_combination(Combination, 1, TargetCombination),
    filter_invalid_optimals1(NormalisedOptimalSol, KindCombi, BoundType, Bound,
                             TargetCombination, MaxN, FilteredOptimalSol).

filter_invalid_optimals1([], _, _, _, _, _, []) :- !.
filter_invalid_optimals1([Sol|R], KindCombi, BoundType, Bound, Combination, MaxN, [Sol|S]) :-
    valid_optimal(KindCombi, BoundType, Bound, Sol, Combination, MaxN), !,
    filter_invalid_optimals1(R, KindCombi, BoundType, Bound, Combination, MaxN, S).
filter_invalid_optimals1([_|R], KindCombi, BoundType, Bound, Combination, MaxN, S) :-
    filter_invalid_optimals1(R, KindCombi, BoundType, Bound, Combination, MaxN, S).

gen_target_combination([], _, []) :- !.
gen_target_combination([_-Char|R], I, [I-Char|S]) :-
    I1 is I+1,
    gen_target_combination(R, I1, S).

valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxc],        Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxs],        Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxc,_-maxs], Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxc,J-s],    Combination), arg(I,Sol,MaxC), arg(J,Sol,S), MaxC = MaxN, S > 1, !, false.
valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxc,J-s,K-maxs], Combination), arg(I,Sol,MaxC), arg(J,Sol,S), arg(K,Sol,MaxS),
                                                           A is (MaxC+MaxS-1) // MaxS, A < S, MaxC = MaxN, !, false.
valid_optimal(graph, low, mins, Sol, Combination, MaxN) :- eq_memberchks([I-maxs],        Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, mins, Sol, Combination, MaxN) :- eq_memberchks([_-maxc,I-maxs], Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, mins, Sol, Combination, MaxN) :- eq_memberchks([I-c,J-maxs],    Combination), arg(I,Sol,C), arg(J,Sol,MaxS), C = 1, MaxS = MaxN, !, false.
valid_optimal(graph, low, mins, Sol, Combination, MaxN) :- eq_memberchks([I-minc,J-maxs], Combination), arg(I,Sol,MinC), arg(J,Sol,MaxS), 
                                                           MinC = MaxS, MinC2 is MinC+MinC, MinC2 > MaxN, !, false.
valid_optimal(graph, low, _,    _,   _,           _)    :- !.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-c,J-maxc], Combination),
                                                           arg(I,Sol,C), arg(J,Sol,MaxC), P is C*MaxC, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-s,J-maxs], Combination),
                                                           arg(I,Sol,S), arg(J,Sol,MaxS), P is S*MaxS, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-c,J-minc], Combination),
                                                           arg(I,Sol,C), arg(J,Sol,MinC), P is C*MinC, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-s,J-mins], Combination),
                                                           arg(I,Sol,S), arg(J,Sol,MinS), P is S*MinS, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-minc,J-maxc], Combination),
                                                           arg(I,Sol,MinC), arg(J,Sol,MaxC), P is MinC+MaxC, MinC < MaxC, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-mins,J-maxs], Combination),
                                                           arg(I,Sol,MinS), arg(J,Sol,MaxS), P is MinS+MaxS, MinS < MaxS, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-c,J-minc,K-maxc], Combination),
                                                           arg(I,Sol,C), arg(J,Sol,MinC), arg(K,Sol,MaxC), P is (C-1)*MaxC+MinC, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-s,J-mins,K-maxs], Combination),
                                                           arg(I,Sol,S), arg(J,Sol,MinS), arg(K,Sol,MaxS), P is (S-1)*MaxS+MinS, P > MaxN, !, false.
valid_optimal(graph, up,  v,    Sol, Combination, MaxN) :- memberchks([I-c,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  v,    Sol, Combination, MaxN) :- memberchks([I-s,J-maxs], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  v,    Sol, Combination, MaxN) :- memberchks([I-s,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  c,    _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  c,    _,   Combination, _)    :- memberchk(_-s,           Combination), !.
valid_optimal(graph, up,  minc, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  minc, _,   Combination, _)    :- memberchk(_-maxc,        Combination), !.
valid_optimal(graph, up,  minc, Sol, Combination, MaxN) :- memberchks([I-s,J-maxs], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  maxc, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  s,    _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  s,    Sol, Combination, MaxN) :- memberchks([I-c,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  mins, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  mins, _,   Combination, _)    :- memberchk(_-maxc,        Combination), !.
valid_optimal(graph, up,  mins, _,   Combination, _)    :- memberchk(_-maxs,        Combination), !.
valid_optimal(graph, up,  maxs, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  maxs, _,   Combination, _)    :- memberchk(_-maxc,        Combination), !.
valid_optimal(graph, up,  maxa, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  maxa, Sol, Combination, MaxN) :- memberchks([I-c,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  maxa, Sol, Combination, MaxN) :- memberchks([I-s,J-maxs], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  maxa, Sol, Combination, MaxN) :- memberchks([I-s,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(partition,  _, _, _, _, _).
valid_optimal(partition0, _, _, _, _, _).
valid_optimal(group,      _, _, _, _, _).
valid_optimal(cgroup,     _, _, _, _, _).

unify_consecutive_vars(I, N, _, _) :-
    I > N, !.
unify_consecutive_vars(I, N, T1, T2) :-
    I =< N,
    arg(I, T1, Var),
    arg(I, T2, Var),
    I1 is I+1,
    unify_consecutive_vars(I1, N, T1, T2).

unify_non_consecutive_vars([], _, _, _) :- !.
unify_non_consecutive_vars([I|R], J, T1, T2) :-
    arg(I, T1, Var),
    arg(J, T2, Var),
    J1 is J+1,
    unify_non_consecutive_vars(R, J1, T1, T2).

labeling_select([V|_], Values) :-
    member(V, Values).
labeling_select([_|R], Values) :-
    labeling_select(R, Values).

labeling_vals([], _) :- !.
labeling_vals([V|R], Values) :-
    member(V, Values),
    labeling_vals(R, Values).

%----------------------------------------------------------------------------------------------------------------------------------------------------------------
% Program that generates digraphs:
%  Only the repartition of N vertices in connected components and strongly connected components,
%  i.e. no arc is generated.
%
% avoid symmetries by:
%  a) Inside each connected component sort strongly connected components by increasing size
%  b) all connected components are sorted in lexicographically increasing order
%
% Filter initial domain of the variables wrt constraints a) and b):
%  We assume that the connected components are labeled from I=N down to 1 and
%  that inside a connected component the strongly connected components are labeled from J=N down to 1.
%  Let Vij denote the number of vertices of the j-th strongly connected component of the i-th connected component.
%  . V11\geq 1
%  . I*J>N     => Vij = 0
%  . I*J\leq N => Vij < \max(1,\lfloor\frac{(N-(J+1)*(I-1))}{J}\rfloor)
%
% For instance for N=5 we get the following initial domains:
% I=5              I=4             I=3             I=2 I=1
% [[0,0,0,0,0..1], [0,0,0,0,0..1], [0,0,0,0,0..1], [0,0,0,0..1,0..3], [0..1,0..1,0..1,0..2,1..5]]
% And 27 solutions:
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],       [0,0,0,0,5]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],       [0,0,0,1,4]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],       [0,0,0,2,3]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],       [0,0,1,1,3]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],       [0,0,1,2,2]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],       [0,1,1,1,2]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],       [1,1,1,1,1]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],       [0,0,0,0,4]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],       [0,0,0,1,3]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],       [0,0,0,2,2]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],       [0,0,1,1,2]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],       [0,1,1,1,1]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,2],       [0,0,0,0,3]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,2],       [0,0,0,1,2]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,2],       [0,0,1,1,1]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,3],       [0,0,0,1,1]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,1,1],       [0,0,0,1,2]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,1,1],       [0,0,1,1,1]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],    [0,0,0,0,1],       [0,0,0,0,3]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],    [0,0,0,0,1],       [0,0,0,1,2]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],    [0,0,0,0,1],       [0,0,1,1,1]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],    [0,0,0,0,2],       [0,0,0,0,2]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],    [0,0,0,0,2],       [0,0,0,1,1]]
% [[0,0,0,0,0],    [0,0,0,0,0],    [0,0,0,0,1],    [0,0,0,1,1],       [0,0,0,1,1]]
% [[0,0,0,0,0],    [0,0,0,0,1],    [0,0,0,0,1],    [0,0,0,0,1],       [0,0,0,0,2]]
% [[0,0,0,0,0],    [0,0,0,0,1],    [0,0,0,0,1],    [0,0,0,0,1],       [0,0,0,1,1]]
% [[0,0,0,0,1],    [0,0,0,0,1],    [0,0,0,0,1],    [0,0,0,0,1],       [0,0,0,0,1]]
%
% The number of solutions for N = 1,2,...,20 is given below:
%  1, 3, 6, 14, 27, 58, 111, 223, 424, 817, 1527, 2870, 5279, 9710, 17622, 31877, 57100, 101887, 180406, 318106
% corresponds to the sequence A001970 of OEIS (partitions of partitions)
%
% with    bound_prefix/5, reverse, ffc, down: ?-top(20). nsol_time(318106,  22080)
% with    bound_prefix/5, reverse           : ?-top(20). nsol_time(318106,  28790)
% with    bound_prefix/5                    : ?-top(20). nsol_time(318106,  40110)
% without bound_prefix/5                    : ?-top(20). nsol_time(318106, 705510)
%
% If we just focus on the vectors of characteristics we get the following number of solutions for N = 1,2,...,20
%  1, 3, 6, 14, 26, 55, 99, 192, 340, 619, 1056, 1844, 3046, 5072, 8109, 12988, 20143, 31219, 46966, 70303
%
% For each vector of characteristics compute the corresponding minimum and maximum number of arcs.
%
% The program considers the following main set of characteristics:
%  . v      : number of vertices of the digraph
%  . c      : number of connected components
%  . minc   : number of vertices of the smallest connected component
%  . maxc   : number of vertices of the largest connected component
%  . s      : number of strongly connected components
%  . mins   : number of vertices of the smallest strongly connected component
%  . maxs   : number of vertices of the largest strongly connected component
%  . mina   : minimum number of arcs
%  . maxa   : maximum number of arcs
%
% In addition to the main characteristics, the program also considers these additional characteristics:
%  . minmaxc: if minc=maxc then 0 else minc
%  . midc   : minimum number of vertices of the intermediate connected components (i.e. second minimum size, 0 if minc=maxc)
%  . rminc  : sum of the number of vertices of the connected components over minc (do not count the first minc vertices of each connected component)
%  . ominc  : number of connected components which have the smallest size minc
%  . omaxc  : number of connected components which have the largest size maxc
%  . omidc  : number of connected components which have size midc (0 if midc=0)
%  . oc     : number of connected components which have more than one vertex
%  . oc23   : number of connected components which have two or three vertices and where all strongly connected components have a size of 1
%  . omins  : number of strongly connected components which have the smallest size mins
%  . omaxs  : number of strongly connected components which have the largest size maxs
%  . os     : number of strongly connected components which have more than one vertex

gen_partitions_of_partitions(MaxN, Sol) :-
    N in 1..MaxN,
    indomain(N),
    N2 is N*N,
    length(L, N2),
    domain(L, 0, N),
    gen_sum_term(L, var, Sum),
    call(Sum #= N),
    gen_partition(L, N, N, Part),
    lex_chain(Part),
    reverse(L,LR),
    N1 is N+1,
    labeling([ffc,down], LR),
    compute_characteristics(Part,                                           % all characteristics + mina,maxa at the end
                            N1,                                             % needed for setting initial value of intermediate characteristics
                            t(0,0,N1,0,0,N1,0,0,0,N1,N1,0,0,0,0,0,0,0,0,0), % start with under & over approximations
                            Sol).                                           % (required except for mina,maxa)

gen_partition([], _, _, []) :- !.
gen_partition(L, N, I, [Prefix|R]) :-
    append_length(Prefix, Suffix, L, N),
    increasing(Prefix),
    bound_prefix(Prefix, I, N, Suffix, N),
    I1 is I-1,
    gen_partition(Suffix, N, I1, R).

increasing([_]) :- !.
increasing([U,V|R]) :-
    U #=< V,
    increasing([V|R]).

bound_prefix([], _, _, _, _) :- !.
bound_prefix([V|R], I, J, S, N) :-
    ((R = [], S = []) -> V #> 0 ; true),
    IJ is I*J,
    MaxV is max(1,(N-(J+1)*(I-1)) // J),
    (IJ > N -> V = 0 ; V #=< MaxV),
    J1 is J-1,
    bound_prefix(R, I, J1, S, N).

compute_characteristics(Part, N1, InitValCharacteristics, Result) :-
    compute_characteristics1(Part, t(N1,0), IntermediateResult, InitValCharacteristics, Result),
    IntermediateResult = t(MinC2,OMinC2),                             % get size of second small connected component (and nb. of occ.)
    Result = t(_,_,MinC,MaxC,_,_,_,_,_,_,MidC,_,_,_,OMidC,_,_,_,_,_), % in order to compute MidC and OMidC
    (MinC  = MaxC -> MidC = 0,     OMidC = 0     ;                    % all connected components have the same size
     MinC2 = MaxC -> MidC = 0,     OMidC = 0     ;                    % only two distinct sizes for all connected components 
                     MidC = MinC2, OMidC = OMinC2).                   % at least three distinct sizes for all connected components: init. MinC2 and OMinC2
                                                                      % remark: this would be the place for a program that check the computed characteristics

compute_characteristics1([], IntermediateResult, IntermediateResult, Result, Result) :- !,
    Result = t(V, C, MinC, MaxC,  _, _, _, _, _, MinMaxC, _, RMinC, _, _, _, _, _, _, _, _), % all 18 characteristics + mina,maxa
    (MinC = MaxC -> MinMaxC = 0 ; MinMaxC = MinC),
    RMinC is V-C*MinC.
compute_characteristics1([P|R], CurResult, IntermediateResult, CurCharacteristics, Result) :-
    remove_values(P, 0, Q),                     % remove all lefmost 0 corresponding to "unused" scc of current cc
    remove_values(Q, 1, Q1),                    % remove all lefmost 1 (to count number of scc whose size is greater than 1)
    (Q = [_|_] ->                               % if we are on a non-empty connected component
         length(Q, Len),                        % number of strongly connected components of current connected component
         min_member(Min, Q),                    % size of smallest strongly connected component of current connected component
         max_member(Max, Q),                    % size of largest strongly connected component of current connected component
         length_same_prefix(Q, OMin),           % number of occurrences of the smallest value (value Min)
         reverse(Q, QR),                        % put the max at the beginning (Q is sorted in increasing order)
         length_same_prefix(QR, OMax),          % number of occurrences of the largest value (value Max)
         sumlist(Q, Sum),                       % number of vertices of current connected component
         (Sum =< 0 -> write(broken_invariant(compute_characteristics1)), nl, halt ; true),
         CurResult  = t(MinC2,  OMinC2),        % number of vertices of the second smallest cc over the cc seen so far (and nb. of occ.)
         NextResult = t(MinC21, OMinC21),       % updated number of vertices of the second smallest connected component (and nb. of occ.)
         CurCharacteristics  = t(V, C, MinC, MaxC, S, MinS, MaxS, MinA, MaxA, _MinMaxC, _MidC, _RMinC, OMinC, OMaxC, _OMidC, OC, OC23, OMinS, OMaxS, OS),
         NextCharacteristics = t(V1,C1,MinC1,MaxC1,S1,MinS1,MaxS1,MinA1,MaxA1,_MinMaxC1,_MidC1,_RMinC1,OMinC1,OMaxC1,_OMidC1,OC1,OC231,OMinS1,OMaxS1,OS1),
         V1    is V+Sum,                        % update number of vertices
         C1    is C+1,                          % update number of connected components
         MinC1 is min(MinC,Sum),                % update number of vertices of smallest connected component
         MaxC1 is max(MaxC,Sum),                % update number of vertices of largest connected component
         (Sum < MinC  -> MinC21  =  MinC,       % if MinC was updated the second smallest connected component becomes the old MinC
                         OMinC21 =  OMinC    ;  %   copy number of occurrences of connected component of size MinC
          Sum = MinC  -> MinC21  =  MinC2,      % elsif size of current cc corresponds to smallest size seen so far
                         OMinC21 =  OMinC2   ;  %   then nothing change: copy old number of occurrences of second smallest connected component seen so far
          Sum < MinC2 -> MinC21  =  Sum,        % elsif size of current cc smaller than second smallest cc seen so far then update it
                         OMinC21 =  1        ;  %   we found a second smallest size
          Sum = MinC2 -> MinC21  =  MinC2,      % elsif size of current cc is equal to the second smallest cc seen so far
                         OMinC21 is OMinC2+1 ;  %   one more second smallest cc
                         MinC21  =  MinC2,      % else copy old size of the second smallest connected component seen so far
                         OMinC21 =  OMinC2   ), %   nothing change: copy old number of occurrences of second smallest connected component seen so far
         (Sum = MinC -> OMinC1 is OMinC+1 ;     % update number of connected components of minimal size
          Sum < MinC -> OMinC1 =  1       ;     % reset to 1 since found a smaller connected component
                        OMinC1 =  OMinC   ),    % result unchanged since minimal size did not change
         (Sum = MaxC -> OMaxC1 is OMaxC+1 ;     % update number of connected components of maximal size
          Sum > MaxC -> OMaxC1 =  1       ;     % reset to 1 since found a larger connected component
                        OMaxC1 =  OMaxC   ),    % result unchanged since maximal size did not change
         (Sum > 1 -> OC1 is OC+1 ; OC1 = OC),   % update number of connected components whose size is greater than 1
         (Q=[1,1]   -> OC231 is OC23 + 1 ;      % update number of connected components with two or three vertices and
          Q=[1,1,1] -> OC231 is OC23 + 1 ;      % where all strongly connected components have only one single vertex
                       OC231 =  OC23     ),
         S1    is S+Len,                        % update number of strongly connected components
         MinS1 is min(MinS,Min),                % update number of vertices of smallest strongly connected component
         MaxS1 is max(MaxS,Max),                % update number of vertices of largest strongly connected component
         (Min = MinS -> OMinS1 is OMinS+OMin ;  % update number of strongly connected components of minimal size
          Min < MinS -> OMinS1 =  OMin       ;  % reset since found a smaller strongly connected component
                        OMinS1 =  OMinS      ), % result unchanged since minimal size did not change
         (Max = MaxS -> OMaxS1 is OMaxS+OMax ;  % update number of strongly connected components of maximal size
          Max > MaxS -> OMaxS1 =  OMax       ;  % reset since found a larger strongly connected component
                        OMaxS1 =  OMaxS      ), % result unchanged since maximal size did not change
         length(Q1, Len1),                      % number of scc whose size is greater than 1 in the current connected component
         OS1 is OS+Len1,                        % update number of strongly connected components whose size is greater than 1
         (Sum = 1 ->                            % update minimum number of arcs of the different connected components
              MinA1 is MinA + 1
         ;
              sumlist(Q1, Sum1),
              MinA1 is MinA+Sum1+Len-1
         ),
         sum_prod_after(Q, Arcs),               % max.nb.of arcs in the current connected component (wrt its strongly connected components)
         MaxA1 is MaxA+Arcs                     % update maximum number of arcs of the different connected components
    ;
         NextCharacteristics = CurCharacteristics
    ),
    compute_characteristics1(R, NextResult, IntermediateResult, NextCharacteristics, Result).

%----------------------------------------------------------------------------------------------------------------------------------------------------------------
% The next program considers the following main set of characteristics for a partition:
%  . n          : number of elements of the partition
%  . nval       : number of distinct values used
%  . min        : size of the smallest equivalence class
%  . max        : size of the largest equivalence class
%  . range      : different between min and max
%  . sum_squares: sum of the square of the sizes of the different equivalence classes
%
% In addition to the main characteristics, the program also considers these additional characteristics:
%  . minmax     : if min=max then 0 else min
%  . mid        : size of the second smallest equivalence class, 0 if min=max
%  . rmin       : sum of the sizes of the equivalence classes over min (do not count the first min elements of each equivalence class)
%  . omin       : number of equivalence classes which have the smallest size min
%  . omax       : number of equivalence classes which have the largest  size max
%  . omid       : number of equivalence classes which have size mid (0 if mid=0)
%  . oc         : number of equivalence classes which have more than one element

gen_partitions(MaxN, Characteristics) :-
    gen_partitions(MaxN, 0, Characteristics).

% The next program considers the following main set of characteristics for a partition:
%  . n          : number of elements of the partition
%  . m          : maximum number of values
%  . nval       : number of distinct values used
%  . min        : size of the smallest equivalence class (consider also unused values)
%  . max        : size of the largest equivalence class
%  . range      : different between min and max
%  . sum_squares: sum of the square of the sizes of the different equivalence classes
%
% In addition to the main characteristics, the program also considers these additional characteristics:
%  . mid        : size of the second smallest equivalence class, 0 if min=max (consider also unused values)
%  . rmin       : sum of the sizes of the equivalence classes over min (do not count the first min elements of each equivalence class)
%  . omin       : number of equivalence classes which have the smallest size min
%  . omax       : number of equivalence classes which have the largest  size max
%  . omid       : number of equivalence classes which have size mid (0 if mid=0)
%  . oc         : number of equivalence classes which have more than one element
%  . oc1        : number of equivalence classes which have one element
gen_partitions0(MaxN, Characteristics) :-
    gen_partitions(MaxN, 1, Characteristics).

% generate the vector characteristics of the next partition:
%  . MaxN           : maximum number of elements of a partition
%  . All            : 1 if consider unused values, 0 otherwise
%  . Characteristics: vector of characteristics of the next potential partition
gen_partitions(MaxN, All, Characteristics) :-
    N in 1..MaxN,                    % number of variables
    indomain(N),
    (All = 1 ->
        M in 1..N,                   % number of potential values (does not exceed N)
        indomain(M),
        AllM = M
    ;
        M = N,                       % number of potential values is equal to N
        AllM = 0
    ),
    length(LOcc, M),                 % occurrence vars (consider that main vars take a value in [1,M])
    domain(LOcc, 0, N),              % between 0 and the number of variables
    gen_sum_term(LOcc, var, SumOcc),
    call(SumOcc #= N),               % sum of the occurrence variables is equal to number of variables
    increasing(LOcc),                % break symmetries
    labeling([ffc,down], LOcc),
    compute_characteristics0(LOcc, N, AllM, Characteristics).

compute_characteristics0(Partition, N, AllM, Result) :-
    remove_first_elem(Partition, 0, Partition0),
    length(Partition0, NVal),
    (AllM = 0 ->
        Result = t(N,       NVal, Min, Max, Range, SumSquares, MinMax, Mid, RMin, OMin, OMax, OMid, OC),
        [Min|_] = Partition0
    ;
        Result = t(N, AllM, NVal, Min, Max, Range, SumSquares, Mid, RMin, OMin, OMax, OMid, OC, OC1),
        [Min|_] = Partition,
        length_prefix(Partition0, 1, 0, OC1)
    ),
    last(Partition0, Max),
    Range is Max-Min,
    sum_squares(Partition0, SumSquares),
    (Min = Max ->
        (AllM = 0 -> MinMax = 0 ; true),
        Mid    = 0,
        OMin   = NVal,
        OMax   = NVal,
        OMid   = 0
    ;
        (AllM = 0 ->
            MinMax = Min,
            length_prefix(Partition0, Min, 0, OMin)
        ;
            length_prefix(Partition,  Min, 0, OMin)
        ),
        reverse(Partition0, ReversePartition0),
        length_prefix(ReversePartition0, Max, 0, OMax),
        remove_first_elem(Partition0, Min, Partition1),
        (Partition1 = [Max|_] ->
            Mid  = 0,
            OMid = 0
        ;
            [Mid|_] = Partition1,
            length_prefix(Partition1, Mid, 0, OMid)
        )
    ),
    RMin is N - NVal*Min,
    remove_first_elem(Partition0, 1, Partition01),
    length(Partition01, OC).
%   write(Partition), write(': '), write(Result), nl.

%----------------------------------------------------------------------------------------------------------------------------------------------------------------
% The next program considers the following set of primary characteristics for a group or a circular group:
%  . n           : number of variables of the sequence
%  . ng          : number of groups where a group is a maximum subsequence of 1
%  . nv          : number of variables that belong to a group
%  . smin        : number of variables of the smallest group
%  . smax        : number of variables of the largest group
%  . srange      : smax-smin
%  . ssum_squares: sum of the squares of the sizes of the different groups
%  . dmin        : minimum distance between two consecutive groups
%  . dmax        : maximum distance between two consecutive groups
%  . drange      : dmax-dmin
%  . dsum_squares: sum of the squares of the distances between consecutive groups
%
% In addition to the main characteristics, we also considers these secondary characteristics:
%  . sminsmax   : if smin=smax then 0 else smin
%  . smid       : size of the second smallest group, 0 if not at least three distinct groups sizes
%  . rsmin      : sum of the sizes of the groups over smin (do not count the first smin elements of each group)
%  . osmin      : number of groups which have the smallest size smin
%  . osmax      : number of groups which have the largest  size smax
%  . osmid      : number of groups which have size smid (0 if smid=0)
%  . osc        : number of groups which have more than one element
%  . dmindmax   : if dmin=dmax then 0 else dmin
%  . dmid       : size of the second smallest inter distance, 0 if not at least three distinct inter distances sizes
%  . rdmin      : sum of the sizes of the inter distances over dmin (do not count the first dmin elements of each inter distance)
%  . odmin      : number of inter distances corresponding to the smallest inter distance dmin
%  . odmax      : number of inter distances corresponding to the largest  inter distance dmax
%  . odmid      : number of inter distances corresponding to dmid (0 if dmid=0)
%  . odc        : number of inter distances that are strictly greater than one

gen_groups(MaxN, Characteristics) :-
    gen_groups(MaxN, 0, Characteristics).

gen_cgroups(MaxN, Characteristics) :-
    gen_groups(MaxN, 1, Characteristics).

gen_groups(MaxN, Circular, Characteristics) :-
    Characteristics = t(N, NG, NV, SMin, SMax, SRange, SSumSquares, DMin, DMax, DRange, DSumSquares, % primary   characteristics
                        SMinSMax, SMid, RSMin, OSMin, OSMax, OSMid, OSC,                             % secondary characteristics related to groups
                        DMinDMax, DMid, RDMin, ODMin, ODMax, ODMid, ODC),                            % secondary characteristics related to inter distances between consecutive groups
    N in 1..MaxN,
    indomain(N),
    length(VARS, N),
    domain(VARS, 0, 1),
    (Circular = 0 ->
        States = [source(s),sink(a),sink(b),sink(c),sink(d),sink(e)]
    ;
        States = [source(s),sink(a),sink(b),sink(d),sink(e)]
    ),
    Transitions = [arc(s,0,e                                   ),
                   arc(s,1,a,             [P0,  1,   C0,  C1  ]),
                   arc(a,0,b,             [ 1,  P1,  C0,  C1  ]),
                   arc(a,1,a,             [P0,  P1+1,C0,  C1  ]),
                   arc(b,0,b,             [P0+1,P1,  C0,  C1  ]),
                   arc(b,1,c,             [P0,  P1,  C0,  1   ]),
                   arc(c,0,d,             [P0,  C1,  1,   C1  ]),
                   arc(c,1,c,(P1 #> C1 -> [P0,  P1,  C0,  C1+1])),
                   arc(d,0,d,(P0 #> C0 -> [P0,  P1,  C0+1,C1  ])),
                   arc(d,1,c,             [C0,  P1,  C0,  1   ]),
                   arc(e,0,e,             [P0,  P1,  C0,  C1  ])],
    automaton(VARS, _, VARS, States, Transitions, [P0,P1,C0,C1], [0,0,0,0], [_,_,_,_]),
    labeling([], VARS),
    extract_sizes(VARS, Circular, Sizes1, Sizes0),
    compute_characteristics_groups(Sizes1, [NG, NV, SMin, SMax, SRange, SSumSquares, SMinSMax, SMid, RSMin, OSMin, OSMax, OSMid, OSC]),
    compute_characteristics_groups(Sizes0, [        DMin, DMax, DRange, DSumSquares, DMinDMax, DMid, RDMin, ODMin, ODMax, ODMid, ODC]),
    length(Sizes1, LenSizes1), (LenSizes1 = 0 -> Cor1 = 1 ; Cor1 = 0),
    length(Sizes0, LenSizes0), (LenSizes0 = 0 -> Cor0 = 1 ; Cor0 = 0).

compute_characteristics_groups(Sizes, Primaries) :-
    (length(Primaries, 11) ->
        Primaries = [      Min, Max, Range, SumSquares, MinMax, Mid, RMin, OMin, OMax, OMid, OC] % the inter distances between consecutive groups
    ;
        Primaries = [G, V, Min, Max, Range, SumSquares, MinMax, Mid, RMin, OMin, OMax, OMid, OC] % the groups
    ),
    (Sizes = [] ->
        G          = 0,
        V          = 0,
        Min        = 0,
        Max        = 0,
        Range      = 0,
        SumSquares = 0,
        MinMax     = 0,
        Mid        = 0,
        RMin       = 0,
        OMin       = 0,
        OMax       = 0,
        OMid       = 0,
        OC         = 0
    ;
        reverse(Sizes, RSizes),
        length(Sizes, G),
        sumlist(Sizes, V),
        min_member(Min, Sizes),
        max_member(Max, Sizes),
        Range is Max - Min,
        sum_squares(Sizes, SumSquares),
        (Min = Max -> MinMax = 0 ; MinMax = Min),
        sort(Sizes, SortedSizes),                                       % sort by increasing order and remove duplicates
        (SortedSizes = [_,_,_|_] ->
            SortedSizes = [_,Mid|_],
            remove_first_elem(RSizes, Min, SizesWithoutMin),
            length_prefix(SizesWithoutMin, Mid, 0, OMid)
        ;
            Mid = 0,
            OMid = 0
        ),
        RMin is V - Min*G,
        length_prefix(RSizes, Min, 0, OMin),
        length_prefix( Sizes, Max, 0, OMax),
        remove_first_elem(RSizes, 1, SizesWithoutOne),
        length(SizesWithoutOne, OC)
    ).

extract_sizes(L, 1, [], []) :- % if Circular and no groups return empty lists
    max_member(0, L),
    !.
extract_sizes(L, Circular, S, T) :-
    extract_sizes1(L, Circular, S, T).

extract_sizes1([], _, [], []) :- !.
extract_sizes1([1|R], Circular, [Size|S], T) :- !,
    extract_sizes2(R, 1, 1, Size, Rest),
    extract_sizes1(Rest, Circular, S, T).
extract_sizes1([0|R], 1, S, [Size|T]) :- !,
    extract_sizes2(R, 0, 1, Size, Rest), % do not skip last group of 0 (since Circular=1)
    extract_sizes1(Rest, 1, S, T).
extract_sizes1([0|R], 0, S, [Size|T]) :-
    extract_sizes2(R, 0, 1, Size, Rest),
    Rest = [_|_], !,                     % as skip last group of 0 as not between two groups of 1 (since Circular=0)
    extract_sizes1(Rest, 0, S, T).
extract_sizes1([0|_], 0, [], []).        % skip last group of 0

extract_sizes2([], _, Size, Size, []) :- !.
extract_sizes2([Val|R], Val, CurSize, Size, Rest) :- !,
    NextSize is CurSize+1,
    extract_sizes2(R, Val, NextSize, Size, Rest).
extract_sizes2(Rest, _, Size, Size, Rest).
