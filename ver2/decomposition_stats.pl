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
% PURPOSE: USED TO AGGREGATE RESULTS FOR THE CP 2023 SUBMITTED PAPER

:- use_module(library(lists)).
:- use_module(table_access).
:- use_module(tables).
:- use_module(utility).
:- use_module(gen_candidate_tables).


% set_prolog_flag(informational,off), [decomposition_stats], create_stats.
% [decomposition_stats], create_stats, halt.

create_stats:-
    DirectoryWODecomp = 'conjecture_files',
    DirectoryWDecomp  = 'conjecture_files_decomp',
    maps(Maps),
    collect_main_stats_common_tables(DirectoryWODecomp, DirectoryWDecomp, CommonTables),

    % collect the number of output parameters
    count_characteristics_per_object(CommonTables),
    
    nl,nl,write('---ver1---'),nl,nl,
    (foreach(Map, Maps),
     foreach(ColListWODecomp, ColListsWODecomp),
     foreach(ColInputCostListWODecomp, ColInputCostListsWODecomp),
     foreach([ColListAllTablesWODecomp,ColListInputAllTablesWODecomp], ColListAllTablesWODecompAll),
     param([DirectoryWODecomp,CommonTables])
    do
     consult_maps(Map, DirectoryWODecomp, CommonTables, ColListWODecomp, ColInputCostListWODecomp,
                  ColListAllTablesWODecomp, ColListInputAllTablesWODecomp)
    ),
    nl,nl,write('---ver2---'),nl,nl,
    (foreach(Map, Maps),
     foreach(ColListWDecomp, ColListsWDecomp),
     foreach(ColInputCostListWDecomp, ColInputCostListsWDecomp),
     foreach([ColListAllTablesWDecomp,ColListInputAllTablesWDecomp], ColListAllTablesWDecompAll),
     param([DirectoryWDecomp, CommonTables])
    do
     consult_maps(Map, DirectoryWDecomp, CommonTables, ColListWDecomp, ColInputCostListWDecomp,
                  ColListAllTablesWDecomp, ColListInputAllTablesWDecomp)
    ),
    nl,nl,write('---all---'),nl,nl,
    (foreach(L1,ColListAllTablesWODecompAll),
     foreach(L2,ColListAllTablesWDecompAll)
    do
     L1 = [Obj-ColListWODecomp1,Obj-ColListInputWODecomp1],
     L2 = [Obj-ColListWDecomp1,Obj-ColListInputWDecomp1],
     length(ColListWODecomp1, NColListWODecomp1),
     length(ColListInputWODecomp1, NColListInputWODecomp1),
     write(ver1_chars_input_chars_all_tables(Obj, NColListWODecomp1, NColListInputWODecomp1)), nl,
     length(ColListWDecomp1, NColListWDecomp1),
     length(ColListInputWDecomp1, NColListInputWDecomp1),
     write(ver2_chars_input_chars_all_tables(Obj, NColListWDecomp1, NColListInputWDecomp1)), nl,
     append(ColListWODecomp1,ColListWDecomp1, ColListAll),
     append(ColListInputWODecomp1,ColListInputWDecomp1, ColListInputAll),
     sort(ColListAll, ColListAllSorted), length(ColListAllSorted, NColListAllSorted),
     sort(ColListInputAll, ColListInputAllSorted), length(ColListInputAllSorted, NColListInputAllSorted),
     write(total_chars_input_chars_all_tables(Obj, NColListAllSorted, NColListInputAllSorted)), nl
    ),
    nl,nl,write('---total---'),nl,nl,
    count_new_characteristics(ColListsWODecomp, ColListsWDecomp, Maps),
    nl,nl,nl,
    compare_costs(ColInputCostListsWODecomp, ColInputCostListsWDecomp, Maps),
    true.

consult_maps([Obj, MapDir, FileNames], Directory, CommonTablesAll, ColListAll, ColInputCostAll,
             Obj-ColListAllTablesAll1,
             Obj-ColListInputAllTablesAll1) :-
    write(Obj),write(':'),nl,
    memberchk(Obj-CommonTables, CommonTablesAll),
    (foreach(FileName, FileNames),
     foreach(ColList, ColListAll),
     foreach(ColInputCost, ColInputCost0All),
     foreach(ColListBoundsN, NBTs),
     foreach(NT,  NTs),
     foreach(NA,  NAs),
     foreach(N1,  N1s),
     foreach(NDT, NDTs),
     foreach(ND1, ND1s),
     foreach(ND2, ND2s),
     foreach(ND3, ND3s),
     foreach(ND4, ND4s),
     foreach(NDS, NDSs),
     foreach(ColListAllTables, ColListAllTablesAll),
     foreach(ColListInputAllTables, ColListInputAllTablesAll),
     param([MapDir, Directory, CommonTables])
    do
     consult_map(FileName, Directory, MapDir, CommonTables, ColList, ColListBoundsN, ColInputCost,
                 NT, NA, N1, NDT, ND1, ND2, ND3, ND4, NDS,
                 ColListAllTables, ColListInputAllTables)
    ),
    sumlist(NTs,   TotalTt), write(total_chars_total(TotalTt)), nl,
    sumlist(NAs,   TotalA),  write(total_chars_allch(TotalA)), nl,
    sumlist(NBTs,  TotalBTs),write(total_chats_bound(TotalBTs)), nl,
    sumlist(N1s,   Total1),  write(total_chars_input(Total1)), nl,
    sumlist(NDTs,  TotalDT), write(total_decomps_total(TotalDT)), nl,
    sumlist(ND1s,  TotalD1), write(total_decomps_type1(TotalD1)), nl,
    sumlist(ND2s,  TotalD2), write(total_decomps_type2(TotalD2)), nl,
    sumlist(ND3s,  TotalD3), write(total_decomps_type3(TotalD3)), nl,
    sumlist(ND4s,  TotalD4), write(total_decomps_type4(TotalD4)), nl,
    sumlist(NDSs,  TotalDS), write(total_decomps_nests(TotalDS)), nl,
    nl,nl,
    append(ColInputCost0All, ColInputCostAll),
    append(ColListAllTablesAll, ColListAllTablesAll1),
    append(ColListInputAllTablesAll, ColListInputAllTablesAll1).

collect_map_common_tables(Map, Dirs, CommonTables) :-
    (foreach(Dir, Dirs),
     foreach(TablesMap, TablesLists),
     param([Map])
    do
     collect_map_tables(Map, Dir, TablesMap)
    ),
    TablesLists = [_, CommonTables].

collect_map_tables([_Obj, MapDir, FileNames], Directory, TablesFlat) :-
    (foreach(FileName, FileNames),
     foreach(TablesFile, TablesAll),
     param([Directory, MapDir])
    do
     atoms_concat([Directory, MapDir, FileName], FilePath),
     consult(FilePath),
     findall(Table,
             (functor(Conjecture, conjecture, 9),
              call(Conjecture),
              get_col(Conjecture, col(Table, _))
             ),
             TablesFileUnsorted),
     sort(TablesFileUnsorted, TablesFile),
     retractall(conjecture(_,_,_,_,_,_,_,_,_))
    ),
    append(TablesAll, TablesFlat).

consult_map(FileName, Directory, MapDir, CommonTables, ColListSorted, ColListBoundsN, ColInputCostFinal, ColListTN, ColListN, ColListInputN,
            FamListDecompN, FamListType1N, FamListType2N, FamListType3N, FamListType4N, FamListNestedN,
            ColListAllSorted, ColListInputAllSorted) :-
    atoms_concat([Directory, MapDir, FileName], FilePath),
    consult(FilePath),


    % Step 0 - count the nb of all conjectures
    findall(Col-Formula,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables),
             get_formula(Conjecture, Formula)
            ),
            ColFormulaList),
    sort(ColFormulaList, ColFormulaListSorted),
    length(ColFormulaListSorted, ColListTN),

    % Step 1 - count if found at least one formula for each characteristics.
    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables)
            ),
            ColList),
    sort(ColList, ColListSorted),
    length(ColListSorted, ColListN),

    % Step 1a - count if found at least one formula for each bound
    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_kind(Conjecture, Kind),
             Kind \== secondary,
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables)
            ),
            ColListBounds),
    sort(ColListBounds, ColListBoundsSorted),
    length(ColListBoundsSorted, ColListBoundsN),

    % Step 2 - if found at least one formula which only depend of the input parameters for each characteristics
    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables),
             get_formula(Conjecture, t(_,InputNames,_,_)),
             get_primaries(Table, Primaries),
             (foreach(Input, InputNames), param(Primaries) do memberchk(Input, Primaries))
            ),
            ColListInput),
    sort(ColListInput, ColListInputSorted),
    length(ColListInputSorted, ColListInputN),

    % Step 3-4 - for each bias/decomposition
    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables),
             get_family(Conjecture, decomp)
            ),
            FamListDecomp),
    sort(FamListDecomp, FamListDecompSorted),
    length(FamListDecompSorted, FamListDecompN),

    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables),
             get_family(Conjecture, decomp),
             get_option(Conjecture, Option),
             collect_decomposition_types(Option, DecompTypes),
             memberchk(decomp1, DecompTypes)
            ),
            FamListType1),
    sort(FamListType1, FamListType1Sorted),
    length(FamListType1Sorted, FamListType1N),
    
    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables),
             get_family(Conjecture, decomp),
             get_option(Conjecture, Option),
             collect_decomposition_types(Option, DecompTypes),
             memberchk(decomp2, DecompTypes)
            ),
            FamListType2),
    sort(FamListType2, FamListType2Sorted),
    length(FamListType2Sorted, FamListType2N),
    
    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables),
             get_family(Conjecture, decomp),
             get_option(Conjecture, Option),
             collect_decomposition_types(Option, DecompTypes),
             memberchk(decomp3, DecompTypes)
            ),
            FamListType3),
    sort(FamListType3, FamListType3Sorted),
    length(FamListType3Sorted, FamListType3N),
    
    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables),
             get_family(Conjecture, decomp),
             get_option(Conjecture, Option),
             collect_decomposition_types(Option, DecompTypes),
             memberchk(decomp4, DecompTypes)
            ),
            FamListType4),
    sort(FamListType4, FamListType4Sorted),
    length(FamListType4Sorted, FamListType4N),
    
    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables),
             get_family(Conjecture, decomp),
             get_option(Conjecture, [decomp([Family,_])]),
             collect_nested_families(Family, NestedFamilies),
             memberchk(decomp, NestedFamilies)
            ),
            FamListNested),
    sort(FamListNested, FamListNestedSorted),
    length(FamListNestedSorted, FamListNestedN),

    findall([Col, InputNames, Cost],
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _), memberchk(Table, CommonTables),
             get_formula(Conjecture, t(_,InputNames,_,_)),
             get_cost(Conjecture, Cost)
            ),
            ColInputCost),
    sort(ColInputCost, ColInputCostSorted),
    filter_min_cost(ColInputCostSorted, ColInputCostFinal),


    % last step - count nbs of chars w/o looking at common tables - later to be 
    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col)
            ),
            ColListAll),
    sort(ColListAll, ColListAllSorted),

    findall(Col,
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             get_col(Conjecture, Col),
             Col = col(Table, _),
             get_formula(Conjecture, t(_,InputNames,_,_)),
             get_primaries(Table, Primaries),
             (foreach(Input, InputNames), param(Primaries) do memberchk(Input, Primaries))
            ),
            ColListInputAll),
    sort(ColListInputAll, ColListInputAllSorted),
    
    retractall(conjecture(_,_,_,_,_,_,_,_,_)).

%  . id(KindCombi, MapId, ConjId): conjecture identifier,
%  . Kind                        : low (if lower bound); up (if upper bound); primary, secondary (if equality),
%  . col(Table,Col)              : table and column for which the conjecture holds (left-hand side of the conjecture),
%  . Name                        : name corresponding to col(Table,Col),
%  . MaxN                        : size that was used for generating the conjecture,
%  . Cost                        : cost associated with the conjecture,
%  . Formula                     : formula associated with the conjecture (right-hand side of the conjecture),
%  . ConjFamily                  : family to which belong the conjecture,
%  . Option                      : option that was used to generate the conjecture.
get_id(     Conjecture,      ID) :- arg(1, Conjecture, ID).
get_kind(   Conjecture,    Kind) :- arg(2, Conjecture, Kind).
get_col(    Conjecture,     Col) :- arg(3, Conjecture, Col).
get_name(   Conjecture,    Name) :- arg(4, Conjecture, Name).
get_maxn(   Conjecture,    MaxN) :- arg(5, Conjecture, MaxN).
get_cost(   Conjecture,    Cost) :- arg(6, Conjecture, Cost).
get_formula(Conjecture, Formula) :- arg(7, Conjecture, Formula).
get_family( Conjecture,  Family) :- arg(8, Conjecture, Family).
get_option( Conjecture,  Option) :- arg(9, Conjecture, Option).

get_primaries(Table, Primaries) :-
    atom_chars(Table, Chars),
    filter_chars(Chars, Primaries1),
    append([[_], Primaries, [_]], Primaries1).

filter_chars(Chars, Inputs) :-
    filter_chars(Chars, [], Inputs).

filter_chars([], AtomChars, [Input]) :-
    !,
    reverse(AtomChars, AtomCharsR),
    atoms_concat(AtomCharsR, Input).
filter_chars([Char|R], AtomChars, Inputs) :-
    Char = '_',
    !,
    reverse(AtomChars, AtomCharsR),
    atoms_concat(AtomCharsR, Input),
    Inputs = [Input|S],
    filter_chars(R, [], S).
filter_chars([Char|R], AtomChars, Inputs) :-
    filter_chars(R, [Char|AtomChars], Inputs).

collect_nested_families(Family, NestedFamilies) :-
    Family = families([splits, base(FamilyBase), diff(FamilyDiff)]),
    !,
    NestedFamilies = [FamilyBase, FamilyDiff].
collect_nested_families(Family, NestedFamilies) :-
    Family = families([unary_template(_),rest(FamilyRest)]),
    !,
    NestedFamilies = [FamilyRest].
collect_nested_families(Family, NestedFamilies) :-
    Family = families([unary_template(_),slack(FamilyDiff),rest(FamilyRest)]),
    !,
    NestedFamilies = [FamilyDiff, FamilyRest].
collect_nested_families(Family, NestedFamilies) :-
    Family = families([cond_template([cond(_), then(_)]), else(FamilyElse)]),
    !,
    NestedFamilies = [FamilyElse].

collect_decomposition_types(OptionsToGenerateConjecture, DecompTypes) :-
    OptionsToGenerateConjecture = [decomp([Family, NestedOptions])],
    Family = families([splits, base(_), diff(_)]),
    !,
    NestedOptions = decomp(binary_op(_), [base(Options1), rest(Options2)]),
    collect_decomposition_types(Options1, List1),
    collect_decomposition_types(Options2, List2),
    append([[decomp1], List1, List2], DecompTypes).
collect_decomposition_types(OptionsToGenerateConjecture, DecompTypes) :-
    OptionsToGenerateConjecture = [decomp([Family, NestedOptions])],
    Family = families([unary_template(_),rest(_)]),
    !,
    NestedOptions = decomp(binary_op(_), [unary_template(_), rest(Options1)]),
    collect_decomposition_types(Options1, List1),
    DecompTypes = [decomp2|List1].
collect_decomposition_types(OptionsToGenerateConjecture, DecompTypes) :-
    OptionsToGenerateConjecture = [decomp([Family, NestedOptions])],
    Family = families([unary_template(_),slack(_),rest(_)]),
    !,
    NestedOptions = decomp(binary_op(_), [unary_template(_), slack(Options1), rest(Options2)]),
    collect_decomposition_types(Options1, List1),
    collect_decomposition_types(Options2, List2),
    append([[decomp3], List1, List2], DecompTypes).
collect_decomposition_types(OptionsToGenerateConjecture, DecompTypes) :-
    OptionsToGenerateConjecture = [decomp([Family, NestedOptions])],
    Family = families([cond_template([cond(_), then(_)]), else(_)]),
    !,
    NestedOptions = decomp(if(cond(_), then(_), else(Options1))),
    collect_decomposition_types(Options1, List1),
    DecompTypes = [decomp4|List1].
collect_decomposition_types(_, []).


count_new_characteristics(ListsBefore, ListsAfter, Maps) :-
    (foreach(ListBefore, ListsBefore),
     foreach(ListAfter,  ListsAfter),
     foreach([Map, _, _], Maps)
    do
     write(Map), write(': '), count_new_characteristics1(ListBefore, ListAfter)
    ).
    
count_new_characteristics1(ListBefore, ListAfter) :-
   %write(ListsBefore),nl,
    (foreach(Elem, ListAfter),
     foreach(Flag, Flags),
     param(ListBefore)
    do
     (memberchk(Elem, ListBefore) -> Flag is 0 ; Flag is 1)
    ),
    sumlist(Flags, NewElems),
    write(new_characteristics(NewElems)),nl.


compare_costs(ColInputCostListsWODecomp, ColInputCostListsWDecomp, Maps) :-
    (foreach(ColInputCostListWODecomp, ColInputCostListsWODecomp),
     foreach(ColInputCostListWDecomp, ColInputCostListsWDecomp),
     foreach([Map,_,_], Maps)
    do
     %write(a1(Map)),nl,
     %write_list(ColInputCostListWODecomp),halt,
     (foreach([Col,Input,CostWODecomp], ColInputCostListWODecomp),
      foreach(Replaced, AllReplaced),
      param(ColInputCostListWDecomp)
     do
      %write(b1),nl,
      (memberchk([Col,Input,CostWDecomp], ColInputCostListWDecomp) ->
      % write(b2a),nl,
           (CostWODecomp > CostWDecomp ->  Replaced is 1 ; Replaced is 0)
      ;
      % write(b2b),nl,
           Replaced is 0
      )
     ),
     %write(b3),nl,
     sumlist(AllReplaced, SumReplaced),
     write(replaced_chars(Map, SumReplaced)),nl
    ).


% filter_min_cost([[a, b, 3], [a, b, 2], [a, c, 3], [a, d, 4], [a, d, 3], [a, d, 2], [b, a, 3], [b, a, 2]], X).
% filter_min_cost([[a, b, 3], [a, b, 2], [a, c, 3], [a, d, 4], [a, d, 3], [a, d, 2], [b, a, 3], [b, a, 2], [c, a, 1]], X).
filter_min_cost([], []) :- !.
filter_min_cost([[Col, Inputs, Cost1], [Col, Inputs, Cost2]|R], Filtered) :-
    !,
    (Cost1 >= Cost2 -> Cost is Cost2 ; Cost is Cost1),
    filter_min_cost([[Col, Inputs, Cost]|R], Filtered).
filter_min_cost([[Col, Inputs, Cost]|R], [[Col, Inputs, Cost]|S]) :-
    filter_min_cost(R, S).
    

collect_main_stats_common_tables(DirectoryWODecomp, DirectoryWDecomp, CommonTables) :-
    object_commands(ObjectCommands),
    transform_object(ObjectCommands, ObjectCommands1),
    atoms_concat([DirectoryWODecomp, '/table_slice_time.pl'], CmdTimeWODecomp),
    consult(CmdTimeWODecomp),

    findall([CmdTO],
            table_slice_time(_, CmdTO, time(_), state(timeout), group_job(_), job_id_group(_)),
            Timeouts),
    sort(Timeouts, TimeoutsSorted),
    length(TimeoutsSorted, NbTimeouts),
    findall([Table, Obj, Time],
            (table_slice_time(Table, Cmd, time(Time), state(finish), group_job(_), job_id_group(_)),
             Table \== table_not_printed,
             memberchk(Cmd-Obj, ObjectCommands1)
            ),
            Times),
    sort(Times, TimesSorted),
    
    findall(Obj-Table,
            (table_slice_time(Table, Cmd, time(_), state(finish), group_job(_), job_id_group(_)),
             Table \== table_not_printed,
             memberchk(Cmd-Obj, ObjectCommands1)),
            ObjTables),

    findall(Cmd,
            (table_slice_time(Table, Cmd, time(_), state(State), group_job(_), job_id_group(_)),
             (State = timeout ; Table \== table_not_printed)
            ),
            UniqCmds),
    retractall(table_slice_time(_,_,_,_,_,_)),

    sort(ObjTables, ObjTablesSorted),
    length(ObjTablesSorted, NbTables),
    
    write(slices_no_decomp(finished-NbTables, timeouts-NbTimeouts)),nl,
    
    atoms_concat([DirectoryWDecomp, '/table_slice_time.pl'], CmdTimeWDecomp),
    consult(CmdTimeWDecomp),
    findall(CmdTO,
            table_slice_time(_, CmdTO, time(_), state(timeout), group_job(_), job_id_group(_)),
            TimeoutsD),
    sort(TimeoutsD, TimeoutsDSorted),
    length(TimeoutsDSorted, NbTimeoutsD),
    findall([Table, Obj, Time],
            (table_slice_time(Table, Cmd, time(Time), state(finish), group_job(_), job_id_group(_)),
             Table \== table_not_printed,
             memberchk(Cmd-Obj, ObjectCommands1)
            ),
            TimesD),
    sort(TimesD, TimesDSorted),
    
    findall(Obj-Table,
            (table_slice_time(Table, Cmd, time(_), state(finish), group_job(_), job_id_group(_)),
             Table \== table_not_printed,
             memberchk(Cmd-Obj, ObjectCommands1)),
            ObjTablesD),
    findall(Cmd,
            (table_slice_time(Table, Cmd, time(_), state(State), group_job(_), job_id_group(_)),
             (State = timeout ; Table \== table_not_printed)
            ),
            UniqCmdsD),
    retractall(table_slice_time(_,_,_,_,_,_)),

    
    sort(ObjTablesD, ObjTablesDSorted),
    length(ObjTablesDSorted, NbTablesD),
    
    write(slices_decomp(finished-NbTablesD, timeouts-NbTimeoutsD)),nl,

    findall(Obj-Table,
            (member(Obj-Table, ObjTablesSorted),
             memberchk(Obj-Table, ObjTablesDSorted)),
            ObjTablesCommon),

    length(ObjTablesCommon, NCommon),
    write(nb_common_tables(NCommon)),nl,

    findall(Cmd,
            (member(   Cmd, UniqCmds),
             memberchk(Cmd, UniqCmdsD)),
            CmdCommon),

    sort(CmdCommon, CmdCommonSorted),
    length(CmdCommonSorted, NUniqCmds),

    write(nb_all_tables(NUniqCmds)),nl,
    
    aggregate_tables_by_object(ObjTablesCommon, ObjTablesStructured),
    CommonTables = ObjTablesStructured,

    
    findall([Table, Obj, Time],
            (member([Table, Obj, Time], TimesSorted),
             memberchk(Obj-Table, ObjTablesCommon)),
            TimesFiltered),
    findall([Table, Obj, Time],
            (member([Table, Obj, Time], TimesDSorted),
             memberchk(Obj-Table, ObjTablesCommon)),
            TimesDFiltered),
    
    (foreach([_,_,T], TimesFiltered), foreach(T, TimesFiltered1) do true),
    sumlist(TimesFiltered1, TotalTimes), write(total_time(TotalTimes)),nl,

    (foreach([_,_,T], TimesDFiltered), foreach(T, TimesDFiltered1) do true),
    sumlist(TimesDFiltered1, TotalTimesD), write(total_time_decomp(TotalTimesD)),nl.


transform_object(ObjectCommands, ObjectCommandsTransformed) :-
    (foreach(Object-Commands, ObjectCommands),
     foreach(ObjectCommandPairs, ObjectCommandAllPairs)
    do
     (foreach(Command, Commands),
      foreach(Command-Object, ObjectCommandPairs),
      param(Object)
     do
      true
     )
    ),
    append(ObjectCommandAllPairs, ObjectCommandsTransformed).

aggregate_tables_by_object([], []) :- !.
aggregate_tables_by_object([Obj-Table|R], [Obj-Tables|S]) :-
    aggregate_tables_by_object1([Obj-Table|R], Tables, R1),
    aggregate_tables_by_object(R1, S).

aggregate_tables_by_object1([], [], []) :- !.
aggregate_tables_by_object1([Obj-Table1, Obj-Table2|R], [Table1|S], Remain) :-
    !,
    aggregate_tables_by_object1([Obj-Table2|R], S, Remain).
aggregate_tables_by_object1([_Obj-Table1|R], [Table1], R).

count_characteristics_per_object(CommonTables) :-
    write('Nb of output columns (bound + secondaries) per combinatorial object:'),nl,
    (foreach(KindCombi-Tables, CommonTables)
    do
     atoms_concat(['data/',KindCombi,'/data'], DirData),
     max_size_combi(KindCombi, MaxN),
     (foreach(Table, Tables),
      foreach(Ns1, Ns1All),
      param([DirData, MaxN])
     do
      gen_table_and_metadata_file_names(DirData, MaxN, Table, _TableFile, MetadataFile),
      consult(MetadataFile),
      tab_get_secondaries(Table, Ss), length(Ss, Ns), Ns1 is Ns + 1,
      remove_metadata_facts(Table)
     ),
     sumlist(Ns1All, NbChars),
     write(KindCombi-NbChars),nl
    ).

object_commands([graph-[g1(_,_,_,_), g2(_,_,_,_), g3(_,_,_,_), g4(_,_,_,_), g5(_,_,_,_), g6(_,_,_,_), g7(_,_,_,_), g8(_,_,_,_), g9(_,_,_,_), g10(_,_,_,_), g11(_,_,_,_), g12(_,_,_,_), g13(_,_,_,_), g14(_,_,_,_), g15(_,_,_,_), g16(_,_,_,_)],
                 tree-[t1(_,_,_,_), t2(_,_,_,_), t3(_,_,_,_), t4(_,_,_,_), t5(_,_,_,_), t6(_,_,_,_), t7(_,_,_,_), t8(_,_,_,_), t9(_,_,_,_), t10(_,_,_,_)],
                 forest-[f1(_,_,_,_), f2(_,_,_,_), f3(_,_,_,_), f4(_,_,_,_), f5(_,_,_,_), f6(_,_,_,_), f7(_,_,_,_), f8(_,_,_,_), f9(_,_,_,_), f10(_,_,_,_), f11(_,_,_,_), f12(_,_,_,_), f13(_,_,_,_), f14(_,_,_,_), f15(_,_,_,_), f16(_,_,_,_), f17(_,_,_,_), f18(_,_,_,_), f19(_,_,_,_), f20(_,_,_,_)],
                 forest0-[f01(_,_,_,_), f02(_,_,_,_), f03(_,_,_,_), f04(_,_,_,_), f05(_,_,_,_), f06(_,_,_,_), f07(_,_,_,_), f08(_,_,_,_), f09(_,_,_,_), f010(_,_,_,_), f011(_,_,_,_), f012(_,_,_,_), f013(_,_,_,_), f014(_,_,_,_), f015(_,_,_,_), f016(_,_,_,_), f017(_,_,_,_), f018(_,_,_,_), f019(_,_,_,_), f020(_,_,_,_)],
                 partition-[p1(_,_,_,_), p2(_,_,_,_), p3(_,_,_,_), p4(_,_,_,_), p5(_,_,_,_), p6(_,_,_,_), p7(_,_,_,_), p8(_,_,_,_), p9(_,_,_,_), p10(_,_,_,_)],
                 partition0-[p01(_,_,_,_), p02(_,_,_,_), p03(_,_,_,_), p04(_,_,_,_), p05(_,_,_,_), p06(_,_,_,_), p07(_,_,_,_), p08(_,_,_,_), p09(_,_,_,_), p010(_,_,_,_)],
                 group-[group01(_,_,_,_), group02(_,_,_,_), group03(_,_,_,_), group04(_,_,_,_), group05(_,_,_,_), group06(_,_,_,_), group07(_,_,_,_), group08(_,_,_,_), group09(_,_,_,_), group10(_,_,_,_), group11(_,_,_,_), group12(_,_,_,_), group13(_,_,_,_), group14(_,_,_,_), group15(_,_,_,_), group16(_,_,_,_), group17(_,_,_,_), group18(_,_,_,_), group19(_,_,_,_), group20(_,_,_,_)],
                 cgroup-[cgroup01(_,_,_,_), cgroup02(_,_,_,_), cgroup03(_,_,_,_), cgroup04(_,_,_,_), cgroup05(_,_,_,_), cgroup06(_,_,_,_), cgroup07(_,_,_,_), cgroup08(_,_,_,_), cgroup09(_,_,_,_), cgroup10(_,_,_,_), cgroup11(_,_,_,_), cgroup12(_,_,_,_), cgroup13(_,_,_,_), cgroup14(_,_,_,_), cgroup15(_,_,_,_), cgroup16(_,_,_,_), cgroup17(_,_,_,_), cgroup18(_,_,_,_), cgroup19(_,_,_,_), cgroup20(_,_,_,_)]                 
                 ]).

maps(               [[graph,      '/conjectures_graph/',      ['found_conjectures_graph_up_v.pl',
                                                               'found_conjectures_graph_low_c.pl',
                                                               'found_conjectures_graph_low_maxc.pl',
                                                               'found_conjectures_graph_low_maxs.pl',
                                                               'found_conjectures_graph_low_mina.pl',
                                                               'found_conjectures_graph_low_minc.pl',
                                                               'found_conjectures_graph_low_mins.pl',
                                                               'found_conjectures_graph_low_s.pl',
                                                               'found_conjectures_graph_low_v.pl',
                                                               'found_conjectures_graph_up_c.pl',
                                                               'found_conjectures_graph_up_maxa.pl',
                                                               'found_conjectures_graph_up_maxc.pl',
                                                               'found_conjectures_graph_up_maxs.pl',
                                                               'found_conjectures_graph_up_minc.pl',
                                                               'found_conjectures_graph_up_mins.pl',
                                                               'found_conjectures_graph_up_s.pl']],
                     [forest,     '/conjectures_forest/',     ['found_conjectures_forest_low_f.pl',
                                                               'found_conjectures_forest_low_maxd.pl',
                                                               'found_conjectures_forest_low_maxf.pl',
                                                               'found_conjectures_forest_low_maxp.pl',
                                                               'found_conjectures_forest_low_maxt.pl',
                                                               'found_conjectures_forest_low_mind.pl',
                                                               'found_conjectures_forest_low_minf.pl',
                                                               'found_conjectures_forest_low_minp.pl',
                                                               'found_conjectures_forest_low_mint.pl',
                                                               'found_conjectures_forest_low_t.pl',
                                                               'found_conjectures_forest_up_f.pl',
                                                               'found_conjectures_forest_up_maxd.pl',
                                                               'found_conjectures_forest_up_maxf.pl',
                                                               'found_conjectures_forest_up_maxp.pl',
                                                               'found_conjectures_forest_up_maxt.pl',
                                                               'found_conjectures_forest_up_mind.pl',
                                                               'found_conjectures_forest_up_minf.pl',
                                                               'found_conjectures_forest_up_minp.pl',
                                                               'found_conjectures_forest_up_mint.pl',
                                                               'found_conjectures_forest_up_t.pl']],
                     [forest0,    '/conjectures_forest0/',    ['found_conjectures_forest0_low_f.pl',
                                                               'found_conjectures_forest0_low_maxd.pl',
                                                               'found_conjectures_forest0_low_maxf.pl',
                                                               'found_conjectures_forest0_low_maxp.pl',
                                                               'found_conjectures_forest0_low_maxt.pl',
                                                               'found_conjectures_forest0_low_mind.pl',
                                                               'found_conjectures_forest0_low_minf.pl',
                                                               'found_conjectures_forest0_low_minp.pl',
                                                               'found_conjectures_forest0_low_mint.pl',
                                                               'found_conjectures_forest0_low_t.pl',
                                                               'found_conjectures_forest0_up_f.pl',
                                                               'found_conjectures_forest0_up_maxd.pl',
                                                               'found_conjectures_forest0_up_maxf.pl',
                                                               'found_conjectures_forest0_up_maxp.pl',
                                                               'found_conjectures_forest0_up_maxt.pl',
                                                               'found_conjectures_forest0_up_mind.pl',
                                                               'found_conjectures_forest0_up_minf.pl',
                                                               'found_conjectures_forest0_up_minp.pl',
                                                               'found_conjectures_forest0_up_mint.pl',
                                                               'found_conjectures_forest0_up_t.pl']],
                     [tree,       '/conjectures_tree/',       ['found_conjectures_tree_low_f.pl',
                                                               'found_conjectures_tree_low_maxd.pl',
                                                               'found_conjectures_tree_low_maxp.pl',
                                                               'found_conjectures_tree_low_mind.pl',
                                                               'found_conjectures_tree_low_minp.pl',
                                                               'found_conjectures_tree_up_f.pl',
                                                               'found_conjectures_tree_up_maxd.pl',
                                                               'found_conjectures_tree_up_maxp.pl',
                                                               'found_conjectures_tree_up_mind.pl',
                                                               'found_conjectures_tree_up_minp.pl']],
                     [partition,  '/conjectures_partition/',  ['found_conjectures_partition_low_max.pl',
                                                               'found_conjectures_partition_low_min.pl',
                                                               'found_conjectures_partition_low_nval.pl',
                                                               'found_conjectures_partition_low_range.pl',
                                                               'found_conjectures_partition_low_sum_squares.pl',
                                                               'found_conjectures_partition_up_max.pl',
                                                               'found_conjectures_partition_up_min.pl',
                                                               'found_conjectures_partition_up_nval.pl',
                                                               'found_conjectures_partition_up_range.pl',
                                                               'found_conjectures_partition_up_sum_squares.pl']],
                     [partition0, '/conjectures_partition0/', ['found_conjectures_partition0_low_max.pl',
                                                               'found_conjectures_partition0_low_min.pl',
                                                               'found_conjectures_partition0_low_nval.pl',
                                                               'found_conjectures_partition0_low_range.pl',
                                                               'found_conjectures_partition0_low_sum_squares.pl',
                                                               'found_conjectures_partition0_up_max.pl',
                                                               'found_conjectures_partition0_up_min.pl',
                                                               'found_conjectures_partition0_up_nval.pl',
                                                               'found_conjectures_partition0_up_range.pl',
                                                               'found_conjectures_partition0_up_sum_squares.pl']],
                     [group,      '/conjectures_group/',      ['found_conjectures_group_low_dmax.pl',
                                                               'found_conjectures_group_low_dmin.pl',
                                                               'found_conjectures_group_low_drange.pl',
                                                               'found_conjectures_group_low_dsum_squares.pl',
                                                               'found_conjectures_group_low_ng.pl',
                                                               'found_conjectures_group_low_nv.pl',
                                                               'found_conjectures_group_low_smax.pl',
                                                               'found_conjectures_group_low_smin.pl',
                                                               'found_conjectures_group_low_srange.pl',
                                                               'found_conjectures_group_low_ssum_squares.pl',
                                                               'found_conjectures_group_up_dmax.pl',
                                                               'found_conjectures_group_up_dmin.pl',
                                                               'found_conjectures_group_up_drange.pl',
                                                               'found_conjectures_group_up_dsum_squares.pl',
                                                               'found_conjectures_group_up_ng.pl',
                                                               'found_conjectures_group_up_nv.pl',
                                                               'found_conjectures_group_up_smax.pl',
                                                               'found_conjectures_group_up_smin.pl',
                                                               'found_conjectures_group_up_srange.pl',
                                                               'found_conjectures_group_up_ssum_squares.pl']],
                     [cgroup,     '/conjectures_cgroup/',     ['found_conjectures_cgroup_low_dmax.pl',
                                                               'found_conjectures_cgroup_low_dmin.pl',
                                                               'found_conjectures_cgroup_low_drange.pl',
                                                               'found_conjectures_cgroup_low_dsum_squares.pl',
                                                               'found_conjectures_cgroup_low_ng.pl',
                                                               'found_conjectures_cgroup_low_nv.pl',
                                                               'found_conjectures_cgroup_low_smax.pl',
                                                               'found_conjectures_cgroup_low_smin.pl',
                                                               'found_conjectures_cgroup_low_srange.pl',
                                                               'found_conjectures_cgroup_low_ssum_squares.pl',
                                                               'found_conjectures_cgroup_up_dmax.pl',
                                                               'found_conjectures_cgroup_up_dmin.pl',
                                                               'found_conjectures_cgroup_up_drange.pl',
                                                               'found_conjectures_cgroup_up_dsum_squares.pl',
                                                               'found_conjectures_cgroup_up_ng.pl',
                                                               'found_conjectures_cgroup_up_nv.pl',
                                                               'found_conjectures_cgroup_up_smax.pl',
                                                               'found_conjectures_cgroup_up_smin.pl',
                                                               'found_conjectures_cgroup_up_srange.pl',
                                                               'found_conjectures_cgroup_up_ssum_squares.pl']]
                    ]).
