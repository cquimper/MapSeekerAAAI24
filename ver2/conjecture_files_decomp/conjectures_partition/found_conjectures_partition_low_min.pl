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

conjecture(id(partition,low(min),1),low,col(low_n_min,2),min,30,0,t([],[],[],1),cst,[]).
conjecture(id(partition,low(min),1),secondary,col(low_n_max_min,4),range,30,3,t([col(low_n_max_min,1),col(low_n_max_min,2)],[n,max],[_14753,_14757],if(eq(_14753,_14757),0,minus(_14757,1))),cond,[cond(attr_eq_attr),then(coef(-3,3)),else(unary_term([minus(1,3)]))]).
conjecture(id(partition,low(min),2),secondary,col(low_n_max_min,5),minmax,30,8,t([col(low_n_max_min,1),col(low_n_max_min,2)],[n,max],[_14753,_14757],bool(0,0,and,2,[geq(_14757,2),geq(minus(_14753,_14757),1)])),bool,[bool([neg(0),op([and]),nb_terms(2,2),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(0)])]).
conjecture(id(partition,low(min),3),secondary,col(low_n_max_min,5),minmax,30,1,t([col(low_n_max_min,1),col(low_n_max_min,2)],[n,max],[_14753,_14757],bool(1,0,or,2,[eq(_14753,_14757),eq(_14757,1)])),bool,[bool([neg(1),op([or]),nb_terms(2,2),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(0)])]).
conjecture(id(partition,low(min),4),low,col(low_n_max_min,3),min,30,2,t([col(low_n_max_min,1),col(low_n_max_min,2)],[n,max],[_14753,_14757],if(eq(_14753,_14757),_14753,1)),cond,[cond(attr_eq_attr),then(attr),else(coef(-3,3))]).
conjecture(id(partition,low(min),5),low,col(low_n_max_min,3),min,30,2,t([col(low_n_max_min,2),col(low_n_max_min,4)],[max,range],[_14753,_14757],if(eq(_14757,0),_14753,1)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(coef(-3,3))]).
conjecture(id(partition,low(min),1),secondary,col(low_n_nval_min,4),minmax,20,8,t([col(low_n_nval_min,1),col(low_n_nval_min,2)],[n,nval],[_14753,_14757],bool(0,0,and,2,[geq(_14757,2),geq(minus(_14753,_14757),1)])),bool,[bool([neg(0),op([and]),nb_terms(2,2),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(0)])]).
conjecture(id(partition,low(min),2),secondary,col(low_n_nval_min,4),minmax,20,1,t([col(low_n_nval_min,1),col(low_n_nval_min,2)],[n,nval],[_14753,_14757],bool(1,0,or,2,[eq(_14753,_14757),eq(_14757,1)])),bool,[bool([neg(1),op([or]),nb_terms(2,2),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(0)])]).
conjecture(id(partition,low(min),3),secondary,col(low_n_nval_min,5),rmin,20,3,t([col(low_n_nval_min,1),col(low_n_nval_min,2)],[n,nval],[_14753,_14757],if(eq(_14757,1),0,minus(_14753,_14757))),cond,[cond(attr_eq_coef(coef(-3,3))),then(coef(-3,3)),else(binary_term([minus]))]).
conjecture(id(partition,low(min),4),low,col(low_n_nval_min,3),min,20,2,t([col(low_n_nval_min,1),col(low_n_nval_min,2)],[n,nval],[_14753,_14757],if(eq(_14757,1),_14753,1)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(coef(-3,3))]).
conjecture(id(partition,low(min),1),secondary,col(low_n_range_min,4),max,21,2,t([col(low_n_range_min,2)],[range],[_14739],polynom([monome([t(_14739,1)],1),monome([],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,low(min),2),secondary,col(low_n_range_min,5),minmax,21,2,t([col(low_n_range_min,2)],[range],[_14739],bool(0,0,and,1,[geq(_14739,1)])),bool,[bool([neg(0),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]).
conjecture(id(partition,low(min),3),secondary,col(low_n_range_min,5),minmax,21,0,t([col(low_n_range_min,2)],[range],[_14739],bool(1,0,and,1,[eq(_14739,0)])),bool,[bool([neg(1),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]).
conjecture(id(partition,low(min),4),low,col(low_n_range_min,3),min,21,0,t([],[],[],1),cst,[]).
conjecture(id(partition,low(min),1),secondary,col(low_n_max_range_min,5),minmax,14,4,t([col(low_n_max_range_min,2),col(low_n_max_range_min,3)],[max,range],[_14753,_14757],if(eq(_14757,0),eq(_14753,plus(_14753,_14753)),polynom([monome([t(_14757,1)],-1),monome([t(_14753,1)],1)]))),decomp,[decomp([families([cond_template([cond(1),then(7)]),else(formula)]),decomp(if(cond(1),then(7),else([nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])])))])]).
conjecture(id(partition,low(min),2),low,col(low_n_max_range_min,4),min,14,2,t([col(low_n_max_range_min,2),col(low_n_max_range_min,3)],[max,range],[_14753,_14757],polynom([monome([t(_14757,1)],-1),monome([t(_14753,1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,low(min),3),low,col(low_n_max_range_min,4),min,14,2,t([col(low_n_max_range_min,2),col(low_n_max_range_min,5)],[max,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,low(min),1),low,col(low_n_max_sum_squares_min,4),min,12,2,t([col(low_n_max_sum_squares_min,2),col(low_n_max_sum_squares_min,6)],[max,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,low(min),1),secondary,col(low_n_nval_max_min,5),range,12,4,t([col(low_n_nval_max_min,1),col(low_n_nval_max_min,2),col(low_n_nval_max_min,3)],[n,nval,max],[_14767,_14771,_14775],min(polynom([monome([t(_14771,1),t(_14775,1)],1),monome([t(_14767,1)],-1)]),polynom([monome([t(_14775,1)],1),monome([],-1)]))),decomp,[decomp([formula,[nb_polynom([2]),nb_unary([0]),nb_binary([0]),non_zero_coeffs_in_all_polynomials(4,6),binary_function([min,max,ceil,floor,prod,mod,cmod,dmod]),main_formula([3-t([degree(1,2),non_zero(1,2,0,4),coef(-2,2),cst(-1,1)],[degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)])])]])]).
conjecture(id(partition,low(min),2),secondary,col(low_n_nval_max_min,6),minmax,12,6,t([col(low_n_nval_max_min,1),col(low_n_nval_max_min,2),col(low_n_nval_max_min,3)],[n,nval,max],[_14767,_14771,_14775],if(eq(_14767,prod(_14771,_14775)),0,max(polynom([monome([t(_14771,1),t(_14775,1)],-1),monome([t(_14775,1)],1),monome([t(_14767,1)],1)]),1))),decomp,[decomp([families([cond_template([cond(6),then(1)]),else(formula)]),decomp(if(cond(6),then(1),else([nb_polynom([1]),nb_unary([0]),nb_binary([0]),unary_function([min(-2,2),max(-2,2),floor(2,2),2 mod 2,geq0,in,power(2),sum_consec]),main_formula([2-t([degree(2,2),non_zero(1,2,3,3),coef(-2,2),cst(-1,1)])])])))])]).
conjecture(id(partition,low(min),3),secondary,col(low_n_nval_max_min,5),range,12,3,t([col(low_n_nval_max_min,3),col(low_n_nval_max_min,6)],[max,minmax],[_14753,_14757],polynom([monome([t(_14757,1),t(min(_14757,1),1)],-1),monome([t(_14753,1),t(min(_14757,1),1)],1)])),formula,[nb_polynom([1]),nb_unary([1]),nb_binary([0]),unary([min(-2,2),max(-2,2),floor(2,2),ceil(2,2),2 mod 2,in,geq(0,2),power(2),sum_consec]),main_formula([1-t([degree(2,2),non_zero(1,2,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,low(min),4),secondary,col(low_n_nval_max_min,7),rmin,12,4,t([col(low_n_nval_max_min,1),col(low_n_nval_max_min,2),col(low_n_nval_max_min,5)],[n,nval,range],[_14767,_14771,_14775],min(polynom([monome([t(_14771,1),t(_14775,1)],1),monome([t(_14775,1)],-1)]),polynom([monome([t(_14771,1)],-1),monome([t(_14767,1)],1)]))),formula,[nb_polynom([2]),nb_unary([0]),nb_binary([0]),non_zero_coeffs_in_all_polynomials(4,6),binary_function([min,max,ceil,floor,prod,mod,cmod,dmod]),main_formula([3-t([degree(1,2),non_zero(1,2,0,4),coef(-2,2),cst(-1,1)],[degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,low(min),5),secondary,col(low_n_nval_max_min,7),rmin,12,3,t([col(low_n_nval_max_min,1),col(low_n_nval_max_min,2),col(low_n_nval_max_min,6)],[n,nval,minmax],[_14767,_14771,_14775],polynom([monome([t(_14771,1),t(_14775,1)],-1),monome([t(_14767,1),t(min(_14775,1),1)],1)])),formula,[nb_polynom([1]),nb_unary([1]),nb_binary([0]),unary([min(-2,2),max(-2,2),floor(2,2),ceil(2,2),2 mod 2,in,geq(0,2),power(2),sum_consec]),main_formula([1-t([degree(2,2),non_zero(1,2,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,low(min),6),low,col(low_n_nval_max_min,4),min,12,4,t([col(low_n_nval_max_min,1),col(low_n_nval_max_min,2),col(low_n_nval_max_min,3)],[n,nval,max],[_14767,_14771,_14775],max(polynom([monome([t(_14771,1),t(_14775,1)],-1),monome([t(_14775,1)],1),monome([t(_14767,1)],1)]),1)),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),unary_function([min(-2,2),max(-2,2),floor(2,2),2 mod 2,geq0,in,power(2),sum_consec]),main_formula([2-t([degree(2,2),non_zero(1,2,3,3),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,low(min),7),low,col(low_n_nval_max_min,4),min,12,2,t([col(low_n_nval_max_min,3),col(low_n_nval_max_min,6)],[max,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,low(min),1),low,col(low_n_nval_range_min,4),min,12,2,t([col(low_n_nval_range_min,5),col(low_n_nval_range_min,6)],[max,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,low(min),1),low,col(low_n_nval_sum_squares_min,4),min,14,3,t([col(low_n_nval_sum_squares_min,1),col(low_n_nval_sum_squares_min,2),col(low_n_nval_sum_squares_min,6)],[n,nval,rmin],[_14771,_14775,_14779],floor(polynom([monome([t(_14779,1)],-1),monome([t(_14771,1)],1)]),_14775)),decomp,[decomp([families([unary_template([binary(7),unary(0)]),rest(formula)]),decomp(binary_op(rfloor),[unary_template(_14775),rest([nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])])])])]).
conjecture(id(partition,low(min),1),low,col(low_n_range_sum_squares_min,4),min,12,2,t([col(low_n_range_sum_squares_min,5),col(low_n_range_sum_squares_min,6)],[max,minmax],[_14743,_14747],if(eq(_14747,0),_14743,_14747)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).

missing(low_n_nval_min,low,min).
missing(low_n_sum_squares_min,col,minmax).
missing(low_n_sum_squares_min,low,min).
missing(low_n_max_sum_squares_min,col,range).
missing(low_n_max_sum_squares_min,col,minmax).
missing(low_n_max_sum_squares_min,low,min).
missing(low_n_nval_range_min,col,max).
missing(low_n_nval_range_min,col,minmax).
missing(low_n_nval_range_min,col,rmin).
missing(low_n_nval_range_min,low,min).
missing(low_n_nval_sum_squares_min,col,minmax).
missing(low_n_nval_sum_squares_min,col,rmin).
missing(low_n_nval_sum_squares_min,low,min).
missing(low_n_range_sum_squares_min,col,max).
missing(low_n_range_sum_squares_min,col,minmax).
missing(low_n_range_sum_squares_min,low,min).