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

conjecture(id(partition0,low(nval),1),secondary,col(low_n_m_nval,4),min,30,2,t([col(low_n_m_nval,1),col(low_n_m_nval,2)],[n,m],[_14731,_14735],if(eq(_14735,1),_14731,0)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(coef(-3,3))]).
conjecture(id(partition0,low(nval),2),secondary,col(low_n_m_nval,5),max,30,1,t([col(low_n_m_nval,1)],[n],[_14717],polynom([monome([t(_14717,1)],1)])),formula,[]).
conjecture(id(partition0,low(nval),3),secondary,col(low_n_m_nval,6),range,30,2,t([col(low_n_m_nval,1),col(low_n_m_nval,2)],[n,m],[_14731,_14735],if(eq(_14735,1),0,_14731)),cond,[cond(attr_eq_coef(coef(-3,3))),then(coef(-3,3)),else(attr)]).
conjecture(id(partition0,low(nval),4),secondary,col(low_n_m_nval,7),sum_squares,30,1,t([col(low_n_m_nval,1)],[n],[_14717],polynom([monome([t(_14717,2)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(2,2),non_zero(1,2,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition0,low(nval),5),secondary,col(low_n_m_nval,8),mid,30,0,t([],[],[],0),cst,[]).
conjecture(id(partition0,low(nval),6),secondary,col(low_n_m_nval,10),omin,30,3,t([col(low_n_m_nval,2)],[m],[_14717],if(eq(_14717,1),1,minus(_14717,1))),cond,[cond(attr_eq_coef(coef(-3,3))),then(coef(-3,3)),else(unary_term([minus(1,3)]))]).
conjecture(id(partition0,low(nval),7),secondary,col(low_n_m_nval,11),omax,30,0,t([],[],[],1),cst,[]).
conjecture(id(partition0,low(nval),8),secondary,col(low_n_m_nval,13),oc,30,3,t([col(low_n_m_nval,1)],[n],[_14717],bool(0,0,and,1,[geq(_14717,2)])),bool,[bool([neg(0),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]).
conjecture(id(partition0,low(nval),9),secondary,col(low_n_m_nval,13),oc,30,1,t([col(low_n_m_nval,1)],[n],[_14717],bool(1,0,and,1,[eq(_14717,1)])),bool,[bool([neg(1),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]).
conjecture(id(partition0,low(nval),10),secondary,col(low_n_m_nval,14),oc1,30,1,t([col(low_n_m_nval,1)],[n],[_14717],bool(0,0,and,1,[eq(_14717,1)])),bool,[bool([neg(0),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]).
conjecture(id(partition0,low(nval),11),secondary,col(low_n_m_nval,9),rmin,30,1,t([col(low_n_m_nval,6)],[range],[_14717],polynom([monome([t(_14717,1)],1)])),formula,[]).
conjecture(id(partition0,low(nval),12),secondary,col(low_n_m_nval,12),omid,30,1,t([col(low_n_m_nval,8)],[mid],[_14717],polynom([monome([t(_14717,1)],1)])),formula,[]).
conjecture(id(partition0,low(nval),13),low,col(low_n_m_nval,3),nval,30,0,t([],[],[],1),cst,[]).
conjecture(id(partition0,low(nval),1),low,col(low_n_m_max_nval,4),nval,9,1,t([col(low_n_m_max_nval,1),col(low_n_m_max_nval,3)],[n,max],[_14749,_14753],polynom([monome([t(ceil(_14749,_14753),1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition0,low(nval),1),secondary,col(low_n_m_min_nval,5),rmin,13,2,t([col(low_n_m_min_nval,1),col(low_n_m_min_nval,2),col(low_n_m_min_nval,3)],[n,m,min],[_14763,_14767,_14771],polynom([monome([t(_14767,1),t(_14771,1)],-1),monome([t(_14763,1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(2,2),non_zero(1,2,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition0,low(nval),2),low,col(low_n_m_min_nval,4),nval,13,2,t([col(low_n_m_min_nval,2),col(low_n_m_min_nval,3)],[m,min],[_14749,_14753],if(eq(_14753,0),1,_14749)),cond,[cond(attr_eq_coef(coef(-3,3))),then(coef(-3,3)),else(attr)]).
conjecture(id(partition0,low(nval),1),low,col(low_n_m_range_nval,4),nval,9,9,t([col(low_n_m_range_nval,1),col(low_n_m_range_nval,2),col(low_n_m_range_nval,3)],[n,m,range],[_14763,_14767,_14771],min(_14767,if(eq(_14771,0),_14763,ceil(polynom([monome([t(max(_14771,2),1)],-1),monome([t(_14771,1)],1),monome([t(_14763,1)],1)]),polynom([monome([t(_14771,1)],1)]))))),decomp,[decomp([families([unary_template([binary(3),unary(0)]),rest(decomp)]),decomp(binary_op(min),[unary_template(_14767),rest([decomp([families([cond_template([cond(1),then(2)]),else(formula)]),decomp(if(cond(1),then(2),else([nb_polynom([2]),nb_unary([1]),nb_binary([0]),non_zero_coeffs_in_all_polynomials(4,6),unary([min(-2,2),max(-2,2),floor(2,2),ceil(2,2),2 mod 2,in,geq(0,2),power(2),sum_consec]),binary_function([min,max,ceil,floor,prod,mod,cmod,dmod]),main_formula([3-t([degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)],[degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)])])])))])])])])]).

missing(low_n_m_min_nval,low,nval).
missing(low_n_m_sum_squares_nval,low,nval).
