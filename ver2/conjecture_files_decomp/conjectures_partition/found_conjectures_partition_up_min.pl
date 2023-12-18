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

conjecture(id(partition,up(min),1),secondary,col(up_n_min,3),nval,30,0,t([],[],[],1),cst,[]).
conjecture(id(partition,up(min),2),secondary,col(up_n_min,4),max,30,1,t([col(up_n_min,1)],[n],[_14721],polynom([monome([t(_14721,1)],1)])),formula,[]).
conjecture(id(partition,up(min),3),secondary,col(up_n_min,5),range,30,0,t([],[],[],0),cst,[]).
conjecture(id(partition,up(min),4),secondary,col(up_n_min,6),sum_squares,30,1,t([col(up_n_min,1)],[n],[_14721],polynom([monome([t(_14721,2)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(2,2),non_zero(1,2,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,up(min),5),secondary,col(up_n_min,13),oc,30,3,t([col(up_n_min,1)],[n],[_14721],bool(0,0,and,1,[geq(_14721,2)])),bool,[bool([neg(0),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]).
conjecture(id(partition,up(min),6),secondary,col(up_n_min,13),oc,30,1,t([col(up_n_min,1)],[n],[_14721],bool(1,0,and,1,[eq(_14721,1)])),bool,[bool([neg(1),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]).
conjecture(id(partition,up(min),7),secondary,col(up_n_min,7),minmax,30,1,t([col(up_n_min,5)],[range],[_14721],polynom([monome([t(_14721,1)],1)])),formula,[]).
conjecture(id(partition,up(min),8),secondary,col(up_n_min,8),mid,30,1,t([col(up_n_min,5)],[range],[_14721],polynom([monome([t(_14721,1)],1)])),formula,[]).
conjecture(id(partition,up(min),9),secondary,col(up_n_min,9),rmin,30,1,t([col(up_n_min,5)],[range],[_14721],polynom([monome([t(_14721,1)],1)])),formula,[]).
conjecture(id(partition,up(min),10),secondary,col(up_n_min,10),omin,30,1,t([col(up_n_min,3)],[nval],[_14721],polynom([monome([t(_14721,1)],1)])),formula,[]).
conjecture(id(partition,up(min),11),secondary,col(up_n_min,11),omax,30,1,t([col(up_n_min,3)],[nval],[_14721],polynom([monome([t(_14721,1)],1)])),formula,[]).
conjecture(id(partition,up(min),12),secondary,col(up_n_min,12),omid,30,1,t([col(up_n_min,5)],[range],[_14721],polynom([monome([t(_14721,1)],1)])),formula,[]).
conjecture(id(partition,up(min),13),up,col(up_n_min,2),min,30,1,t([col(up_n_min,1)],[n],[_14721],polynom([monome([t(_14721,1)],1)])),formula,[]).
conjecture(id(partition,up(min),1),up,col(up_n_max_min,3),min,20,2,t([col(up_n_max_min,2),col(up_n_max_min,5)],[max,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,up(min),1),secondary,col(up_n_nval_min,4),minmax,20,3,t([col(up_n_nval_min,1),col(up_n_nval_min,2)],[n,nval],[_14753,_14757],if(eq(_14753 mod _14757,0),0,polynom([monome([t(floor(_14753,_14757),1)],1)]))),decomp,[decomp([families([cond_template([cond(5),then(1)]),else(formula)]),decomp(if(cond(5),then(1),else([nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])])))])]).
conjecture(id(partition,up(min),2),secondary,col(up_n_nval_min,5),rmin,20,1,t([col(up_n_nval_min,1),col(up_n_nval_min,2)],[n,nval],[_14753,_14757],polynom([monome([t(_14753 mod _14757,1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,up(min),3),up,col(up_n_nval_min,3),min,20,1,t([col(up_n_nval_min,1),col(up_n_nval_min,2)],[n,nval],[_14753,_14757],polynom([monome([t(floor(_14753,_14757),1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,up(min),1),up,col(up_n_range_min,3),min,21,2,t([col(up_n_range_min,1),col(up_n_range_min,5)],[n,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,up(min),1),secondary,col(up_n_max_range_min,5),minmax,14,4,t([col(up_n_max_range_min,2),col(up_n_max_range_min,3)],[max,range],[_14753,_14757],if(eq(_14757,0),eq(_14753,plus(_14753,_14753)),polynom([monome([t(_14757,1)],-1),monome([t(_14753,1)],1)]))),decomp,[decomp([families([cond_template([cond(1),then(7)]),else(formula)]),decomp(if(cond(1),then(7),else([nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])])))])]).
conjecture(id(partition,up(min),2),up,col(up_n_max_range_min,4),min,14,2,t([col(up_n_max_range_min,2),col(up_n_max_range_min,3)],[max,range],[_14753,_14757],polynom([monome([t(_14757,1)],-1),monome([t(_14753,1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,up(min),3),up,col(up_n_max_range_min,4),min,14,2,t([col(up_n_max_range_min,2),col(up_n_max_range_min,5)],[max,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,up(min),1),up,col(up_n_max_sum_squares_min,4),min,12,2,t([col(up_n_max_sum_squares_min,2),col(up_n_max_sum_squares_min,6)],[max,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,up(min),1),secondary,col(up_n_nval_max_min,5),range,12,6,t([col(up_n_nval_max_min,1),col(up_n_nval_max_min,2),col(up_n_nval_max_min,3)],[n,nval,max],[_14767,_14771,_14775],if(eq(_14767,prod(_14771,_14775)),0,ceil(polynom([monome([t(_14771,1),t(_14775,1)],1),monome([t(_14767,1)],-1)]),polynom([monome([t(_14771,1)],1),monome([],-1)])))),decomp,[decomp([families([cond_template([cond(6),then(1)]),else(formula)]),decomp(if(cond(6),then(1),else([nb_polynom([2]),nb_unary([0]),nb_binary([0]),non_zero_coeffs_in_all_polynomials(4,6),binary_function([min,max,floor,ceil,prod,mod,cmod,dmod]),main_formula([3-t([degree(1,2),non_zero(1,2,0,4),coef(-2,2),cst(-1,1)],[degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)])])])))])]).
conjecture(id(partition,up(min),2),secondary,col(up_n_nval_max_min,6),minmax,12,6,t([col(up_n_nval_max_min,1),col(up_n_nval_max_min,2),col(up_n_nval_max_min,3)],[n,nval,max],[_14767,_14771,_14775],if(eq(_14767,prod(_14771,_14775)),0,floor(polynom([monome([t(_14775,1)],-1),monome([t(_14767,1)],1)]),minus(_14771,1)))),decomp,[decomp([families([cond_template([cond(6),then(1)]),else(decomp)]),decomp(if(cond(6),then(1),else([decomp([families([unary_template([binary(7),unary(0)]),rest(formula)]),decomp(binary_op(rfloor),[unary_template(minus(_15003,1)),rest([nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])])])])])))])]).
conjecture(id(partition,up(min),3),secondary,col(up_n_nval_max_min,7),rmin,12,3,t([col(up_n_nval_max_min,1),col(up_n_nval_max_min,2),col(up_n_nval_max_min,6)],[n,nval,minmax],[_14767,_14771,_14775],polynom([monome([t(_14771,1),t(_14775,1)],-1),monome([t(_14767,1),t(min(_14775,1),1)],1)])),formula,[nb_polynom([1]),nb_unary([1]),nb_binary([0]),unary([min(-2,2),max(-2,2),floor(2,2),ceil(2,2),2 mod 2,in,geq(0,2),power(2),sum_consec]),main_formula([1-t([degree(2,2),non_zero(1,2,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,up(min),4),up,col(up_n_nval_max_min,4),min,12,7,t([col(up_n_nval_max_min,1),col(up_n_nval_max_min,2),col(up_n_nval_max_min,3)],[n,nval,max],[_14767,_14771,_14775],floor(if(eq(_14767,_14775),_14767,minus(_14767,_14775)),plus(minus(_14771,1),bool(0,0,and,1,[eq(_14771,1)])))),decomp,[decomp([families([unary_template([binary(7),unary(0)]),slack(bool),rest(cond)]),decomp(binary_op(rfloor),[unary_template(minus(_14771,1)),slack([bool([neg(0),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]),rest([cond(attr_eq_attr),then(attr),else(binary_term([minus]))])])])]).
conjecture(id(partition,up(min),5),up,col(up_n_nval_max_min,4),min,12,2,t([col(up_n_nval_max_min,3),col(up_n_nval_max_min,6)],[max,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,up(min),1),secondary,col(up_n_nval_range_min,5),max,12,4,t([col(up_n_nval_range_min,1),col(up_n_nval_range_min,2),col(up_n_nval_range_min,3)],[n,nval,range],[_14767,_14771,_14775],floor(polynom([monome([t(_14771,1),t(_14775,1)],1),monome([t(_14775,1)],-1),monome([t(_14767,1)],1)]),polynom([monome([t(_14771,1)],1)]))),decomp,[decomp([decomp,[decomp([formula,[nb_polynom([2]),nb_unary([0]),nb_binary([0]),non_zero_coeffs_in_all_polynomials(4,6),binary_function([min,max,floor,ceil,prod,mod,cmod,dmod]),main_formula([3-t([degree(1,2),non_zero(1,2,0,4),coef(-2,2),cst(-1,1)],[degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)])])]])]])]).
conjecture(id(partition,up(min),2),secondary,col(up_n_nval_range_min,6),minmax,12,6,t([col(up_n_nval_range_min,1),col(up_n_nval_range_min,2),col(up_n_nval_range_min,3)],[n,nval,range],[_14767,_14771,_14775],floor(if(eq(_14775,0),eq(_14767,plus(_14767,_14767)),polynom([monome([t(_14775,1)],-1),monome([t(_14767,1)],1)])),_14771)),decomp,[decomp([families([unary_template([binary(7),unary(0)]),rest(decomp)]),decomp(binary_op(rfloor),[unary_template(_14771),rest([decomp([families([cond_template([cond(1),then(7)]),else(formula)]),decomp(if(cond(1),then(7),else([nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])])))])])])])]).
conjecture(id(partition,up(min),3),secondary,col(up_n_nval_range_min,7),rmin,12,3,t([col(up_n_nval_range_min,1),col(up_n_nval_range_min,2),col(up_n_nval_range_min,6)],[n,nval,minmax],[_14767,_14771,_14775],polynom([monome([t(_14771,1),t(_14775,1)],-1),monome([t(_14767,1),t(min(_14775,1),1)],1)])),formula,[nb_polynom([1]),nb_unary([1]),nb_binary([0]),unary([min(-2,2),max(-2,2),floor(2,2),ceil(2,2),2 mod 2,in,geq(0,2),power(2),sum_consec]),main_formula([1-t([degree(2,2),non_zero(1,2,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition,up(min),4),up,col(up_n_nval_range_min,4),min,12,3,t([col(up_n_nval_range_min,1),col(up_n_nval_range_min,2),col(up_n_nval_range_min,3)],[n,nval,range],[_14767,_14771,_14775],floor(polynom([monome([t(_14775,1)],-1),monome([t(_14767,1)],1)]),_14771)),decomp,[decomp([families([unary_template([binary(7),unary(0)]),rest(formula)]),decomp(binary_op(rfloor),[unary_template(_14771),rest([nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])])])])]).
conjecture(id(partition,up(min),5),up,col(up_n_nval_range_min,4),min,12,2,t([col(up_n_nval_range_min,5),col(up_n_nval_range_min,6)],[max,minmax],[_14753,_14757],if(eq(_14757,0),_14753,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).
conjecture(id(partition,up(min),1),up,col(up_n_nval_sum_squares_min,4),min,17,3,t([col(up_n_nval_sum_squares_min,1),col(up_n_nval_sum_squares_min,2),col(up_n_nval_sum_squares_min,6)],[n,nval,rmin],[_14771,_14775,_14779],floor(polynom([monome([t(_14779,1)],-1),monome([t(_14771,1)],1)]),_14775)),decomp,[decomp([families([unary_template([binary(7),unary(0)]),rest(formula)]),decomp(binary_op(rfloor),[unary_template(_14775),rest([nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])])])])]).
conjecture(id(partition,up(min),1),up,col(up_n_range_sum_squares_min,4),min,12,2,t([col(up_n_range_sum_squares_min,5),col(up_n_range_sum_squares_min,6)],[max,minmax],[_14743,_14747],if(eq(_14747,0),_14743,_14747)),cond,[cond(attr_eq_coef(coef(-3,3))),then(attr),else(attr)]).

missing(up_n_max_min,col,range).
missing(up_n_max_min,col,minmax).
missing(up_n_max_min,up,min).
missing(up_n_nval_min,up,min).
missing(up_n_range_min,col,max).
missing(up_n_range_min,col,minmax).
missing(up_n_range_min,up,min).
missing(up_n_sum_squares_min,col,minmax).
missing(up_n_sum_squares_min,up,min).
missing(up_n_max_sum_squares_min,col,range).
missing(up_n_max_sum_squares_min,col,minmax).
missing(up_n_max_sum_squares_min,up,min).
missing(up_n_nval_sum_squares_min,col,minmax).
missing(up_n_nval_sum_squares_min,col,rmin).
missing(up_n_nval_sum_squares_min,up,min).
missing(up_n_range_sum_squares_min,col,max).
missing(up_n_range_sum_squares_min,col,minmax).
missing(up_n_range_sum_squares_min,up,min).
