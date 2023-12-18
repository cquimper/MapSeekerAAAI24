% Contains all found conjectures generated by main, where each conjecture is a conjecture\9 fact of the form:
%  . id(KindCombi, MapId, ConjId): conjecture identifier,
%  . Kind                        : low (if lower bound); up (if upper bound); primary, secondary (if equality),
%  . col(Table,Col)              : table and column for which the conjecture holds (left-hand side of the conjecture),
%  . Name                        : name corresponding to col(Table,Col),
%  . MaxN                        : size that was used for generating the conjecture,
%  . Cost                        : cost associated with the conjecture,
%  . Formula                     : formula associated with the conjecture (right-hand side of the conjecture),
%  . ConjFamily                  : family to which belong the conjecture,
%  . Option                      : option that was used to generate the conjecture.
% Contains also all characteritics for which could not find any formula, see missing\3 facts.

:- multifile conjecture/9.
:- multifile missing/3.
:- dynamic conjecture/9.
:- dynamic missing/3.

conjecture(id(tree,low(minp),1),low,col(low_v_minp,2),minp,18,3,t([col(low_v_minp,1)],[v],[_14781],bool(0,0,and,1,[geq(_14781,2)])),bool,[bool([neg(0),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]).
conjecture(id(tree,low(minp),2),low,col(low_v_minp,2),minp,18,1,t([col(low_v_minp,1)],[v],[_14781],bool(1,0,and,1,[eq(_14781,1)])),bool,[bool([neg(1),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]).
conjecture(id(tree,low(minp),1),low,col(low_v_f_minp,3),minp,18,3,t([col(low_v_f_minp,1),col(low_v_f_minp,2)],[v,f],[_14813,_14817],if(eq(_14817,1),minus(_14813,1),1)),cond,[cond(attr_eq_coef(coef(-3,3))),then(unary_term([minus(1,3)])),else(coef(-3,3))]).
conjecture(id(tree,low(minp),1),low,col(low_v_maxd_minp,3),minp,18,3,t([col(low_v_maxd_minp,1),col(low_v_maxd_minp,2)],[v,maxd],[_14813,_14817],if(leq(_14817,1),minus(_14813,1),1)),cond,[cond(attr_leq_coef(coef(-3,3))),then(unary_term([minus(1,3)])),else(coef(-3,3))]).
conjecture(id(tree,low(minp),1),low,col(low_v_maxp_minp,3),minp,18,2,t([col(low_v_maxp_minp,1),col(low_v_maxp_minp,2)],[v,maxp],[_14813,_14817],if(eq(minus(_14813,_14817),1),_14817,1)),cond,[cond(binary_term_eq_coef([minus],coef(0,3))),then(attr),else(coef(-3,3))]).
conjecture(id(tree,low(minp),1),low,col(low_v_mind_minp,3),minp,18,8,t([col(low_v_mind_minp,1),col(low_v_mind_minp,2)],[v,mind],[_14813,_14817],bool(0,0,sum,2,[geq(_14813,2),eq(minus(_14813,_14817),2)])),bool,[bool([neg(0),op([sum]),nb_terms(2,2),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(0)])]).
conjecture(id(tree,low(minp),2),low,col(low_v_mind_minp,3),minp,18,7,t([col(low_v_mind_minp,1),col(low_v_mind_minp,2)],[v,mind],[_14813,_14817],bool(0,0,sum,2,[geq(_14817,1),eq(minus(_14813,_14817),2)])),bool,[bool([neg(0),op([sum]),nb_terms(2,2),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(0)])]).
conjecture(id(tree,low(minp),3),low,col(low_v_mind_minp,3),minp,18,3,t([col(low_v_mind_minp,1),col(low_v_mind_minp,2)],[v,mind],[_14813,_14817],if(leq(prod(_14813,_14817),3),minus(_14813,1),1)),cond,[cond(binary_term_leq_coef([prod,abs],coef(0,3))),then(unary_term([minus(1,3)])),else(coef(-3,3))]).
conjecture(id(tree,low(minp),1),low,col(low_v_f_maxd_minp,4),minp,13,3,t([col(low_v_f_maxd_minp,1),col(low_v_f_maxd_minp,2)],[v,f],[_14813,_14817],if(eq(_14817,1),minus(_14813,1),1)),cond,[cond(attr_eq_coef(coef(-3,3))),then(unary_term([minus(1,3)])),else(coef(-3,3))]).
conjecture(id(tree,low(minp),1),low,col(low_v_f_mind_minp,4),minp,16,3,t([col(low_v_f_mind_minp,1),col(low_v_f_mind_minp,2)],[v,f],[_14813,_14817],if(eq(_14817,1),minus(_14813,1),1)),cond,[cond(attr_eq_coef(coef(-3,3))),then(unary_term([minus(1,3)])),else(coef(-3,3))]).
conjecture(id(tree,low(minp),1),low,col(low_v_mind_maxd_minp,4),minp,15,3,t([col(low_v_mind_maxd_minp,1),col(low_v_mind_maxd_minp,3)],[v,maxd],[_14817,_14821],if(leq(_14821,1),minus(_14817,1),1)),cond,[cond(attr_leq_coef(coef(-3,3))),then(unary_term([minus(1,3)])),else(coef(-3,3))]).
conjecture(id(tree,low(minp),1),low,col(low_v_mind_maxp_minp,4),minp,16,2,t([col(low_v_mind_maxp_minp,1),col(low_v_mind_maxp_minp,3)],[v,maxp],[_14803,_14807],if(eq(minus(_14803,_14807),1),_14807,1)),cond,[cond(binary_term_eq_coef([minus],coef(0,3))),then(attr),else(coef(-3,3))]).

missing(low_v_f_maxp_minp,low,minp).
missing(low_v_maxd_maxp_minp,low,minp).