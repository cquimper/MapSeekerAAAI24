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

conjecture(id(graph,low(maxs),1),secondary,col(low_c_maxs,3),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_c_maxs,4),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),3),low,col(low_c_maxs,2),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_maxc_maxs,3),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_maxc_maxs,4),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),3),low,col(low_maxc_maxs,2),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_minc_maxs,3),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_minc_maxs,4),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),3),low,col(low_minc_maxs,2),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),low,col(low_mins_maxs,2),maxs,26,1,t([col(low_mins_maxs,1)],[mins],[_14739],polynom([monome([t(_14739,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_s_maxs,3),v,26,1,t([col(low_s_maxs,1)],[s],[_14739],polynom([monome([t(_14739,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_s_maxs,4),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_s_maxs,5),omins,26,1,t([col(low_s_maxs,1)],[s],[_14739],polynom([monome([t(_14739,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),4),secondary,col(low_s_maxs,6),omaxs,26,1,t([col(low_s_maxs,1)],[s],[_14739],polynom([monome([t(_14739,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),5),secondary,col(low_s_maxs,7),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),6),low,col(low_s_maxs,2),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_v_maxs,3),s,26,1,t([col(low_v_maxs,1)],[v],[_14739],polynom([monome([t(_14739,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_v_maxs,4),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_v_maxs,5),omins,26,1,t([col(low_v_maxs,1)],[v],[_14739],polynom([monome([t(_14739,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),4),secondary,col(low_v_maxs,6),omaxs,26,1,t([col(low_v_maxs,1)],[v],[_14739],polynom([monome([t(_14739,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),5),secondary,col(low_v_maxs,7),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),6),low,col(low_v_maxs,2),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_c_maxc_maxs,4),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_c_maxc_maxs,5),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),3),low,col(low_c_maxc_maxs,3),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_c_minc_maxs,4),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_c_minc_maxs,5),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),3),low,col(low_c_minc_maxs,3),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),low,col(low_c_mins_maxs,3),maxs,26,1,t([col(low_c_mins_maxs,2)],[mins],[_14739],polynom([monome([t(_14739,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_c_s_maxs,4),v,26,1,t([col(low_c_s_maxs,2)],[s],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_c_s_maxs,5),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_c_s_maxs,6),omins,26,1,t([col(low_c_s_maxs,2)],[s],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),4),secondary,col(low_c_s_maxs,7),omaxs,26,1,t([col(low_c_s_maxs,2)],[s],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),5),secondary,col(low_c_s_maxs,8),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),6),low,col(low_c_s_maxs,3),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),low,col(low_maxc_s_maxs,3),maxs,15,1,t([col(low_maxc_s_maxs,1),col(low_maxc_s_maxs,2)],[maxc,s],[_14757,_14761],polynom([monome([t(ceil(_14757,_14761),1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(graph,low(maxs),1),secondary,col(low_minc_maxc_maxs,4),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_minc_maxc_maxs,5),minmaxc,26,2,t([col(low_minc_maxc_maxs,1),col(low_minc_maxc_maxs,2)],[minc,maxc],[_14757,_14761],if(eq(_14757,_14761),0,_14757)),cond,[cond(attr_eq_attr),then(coef(-3,3)),else(attr)]).
conjecture(id(graph,low(maxs),3),secondary,col(low_minc_maxc_maxs,6),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),4),low,col(low_minc_maxc_maxs,3),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),low,col(low_minc_s_maxs,3),maxs,16,8,t([col(low_minc_s_maxs,1),col(low_minc_s_maxs,2)],[minc,s],[_14757,_14761],if(leq(prod(2,_14757),_14761),1,if(eq(_14757,_14761),1,if(leq(_14757,_14761),2,ceil(_14757,_14761))))),decomp,[decomp([families([cond_template([cond(7),then(1)]),else(decomp)]),decomp(if(cond(7),then(1),else([decomp([families([cond_template([cond(3),then(1)]),else(cond)]),decomp(if(cond(3),then(1),else([cond(attr_leq_attr),then(coef(-3,3)),else(binary_term([ceil]))])))])])))])]).
conjecture(id(graph,low(maxs),2),low,col(low_minc_s_maxs,3),maxs,16,5,t([col(low_minc_s_maxs,1),col(low_minc_s_maxs,2)],[minc,s],[_14757,_14761],if(eq(floor(_14761,_14757),1),ceil(_14761,_14757),ceil(_14757,_14761))),cond,[cond(binary_term_eq_coef([floor],coef(0,3))),then(binary_term([ceil])),else(binary_term([ceil]))]).
conjecture(id(graph,low(maxs),1),secondary,col(low_s_mins_maxs,4),v,26,1,t([col(low_s_mins_maxs,1),col(low_s_mins_maxs,2)],[s,mins],[_14757,_14761],polynom([monome([t(_14757,1),t(_14761,1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(2,2),non_zero(1,2,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(graph,low(maxs),2),secondary,col(low_s_mins_maxs,5),omins,26,1,t([col(low_s_mins_maxs,1)],[s],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_s_mins_maxs,6),omaxs,26,1,t([col(low_s_mins_maxs,1)],[s],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),4),secondary,col(low_s_mins_maxs,7),os,26,2,t([col(low_s_mins_maxs,1),col(low_s_mins_maxs,2)],[s,mins],[_14757,_14761],if(eq(_14761,1),0,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(coef(-3,3)),else(attr)]).
conjecture(id(graph,low(maxs),5),low,col(low_s_mins_maxs,3),maxs,26,1,t([col(low_s_mins_maxs,2)],[mins],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_v_c_maxs,4),s,26,1,t([col(low_v_c_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_v_c_maxs,5),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_v_c_maxs,6),omins,26,1,t([col(low_v_c_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),4),secondary,col(low_v_c_maxs,7),omaxs,26,1,t([col(low_v_c_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),5),secondary,col(low_v_c_maxs,8),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),6),low,col(low_v_c_maxs,3),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_v_maxc_maxs,4),s,26,1,t([col(low_v_maxc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_v_maxc_maxs,5),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_v_maxc_maxs,6),omins,26,1,t([col(low_v_maxc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),4),secondary,col(low_v_maxc_maxs,7),omaxs,26,1,t([col(low_v_maxc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),5),secondary,col(low_v_maxc_maxs,8),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),6),low,col(low_v_maxc_maxs,3),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_v_minc_maxs,4),s,26,1,t([col(low_v_minc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_v_minc_maxs,5),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_v_minc_maxs,6),omins,26,1,t([col(low_v_minc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),4),secondary,col(low_v_minc_maxs,7),omaxs,26,1,t([col(low_v_minc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),5),secondary,col(low_v_minc_maxs,8),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),6),low,col(low_v_minc_maxs,3),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),low,col(low_v_s_maxs,3),maxs,20,1,t([col(low_v_s_maxs,1),col(low_v_s_maxs,2)],[v,s],[_14757,_14761],polynom([monome([t(ceil(_14757,_14761),1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(graph,low(maxs),1),low,col(low_c_maxc_s_maxs,4),maxs,9,4,t([col(low_c_maxc_s_maxs,1),col(low_c_maxc_s_maxs,2),col(low_c_maxc_s_maxs,3)],[c,maxc,s],[_14771,_14775,_14779],ceil(_14775,polynom([monome([t(_14779,1)],1),monome([t(_14771,1)],-1),monome([],1)]))),decomp,[decomp([families([unary_template([binary(6),unary(0)]),rest(formula)]),decomp(binary_op(ceil),[unary_template(_14775),rest([nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])])])])]).
conjecture(id(graph,low(maxs),1),secondary,col(low_c_minc_maxc_maxs,5),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_c_minc_maxc_maxs,6),minmaxc,26,2,t([col(low_c_minc_maxc_maxs,2),col(low_c_minc_maxc_maxs,3)],[minc,maxc],[_14757,_14761],if(eq(_14757,_14761),0,_14757)),cond,[cond(attr_eq_attr),then(coef(-3,3)),else(attr)]).
conjecture(id(graph,low(maxs),3),secondary,col(low_c_minc_maxc_maxs,7),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),4),low,col(low_c_minc_maxc_maxs,4),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),low,col(low_c_minc_s_maxs,4),maxs,12,3,t([col(low_c_minc_s_maxs,1),col(low_c_minc_s_maxs,2),col(low_c_minc_s_maxs,3)],[c,minc,s],[_14771,_14775,_14779],ceil(_14775,polynom([monome([t(floor(_14779,_14771),1)],1)]))),decomp,[decomp([families([unary_template([binary(6),unary(0)]),rest(formula)]),decomp(binary_op(ceil),[unary_template(_14775),rest([nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])])])])]).
conjecture(id(graph,low(maxs),1),secondary,col(low_c_s_mins_maxs,5),v,16,1,t([col(low_c_s_mins_maxs,2),col(low_c_s_mins_maxs,3)],[s,mins],[_14757,_14761],polynom([monome([t(_14757,1),t(_14761,1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(2,2),non_zero(1,2,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(graph,low(maxs),2),secondary,col(low_c_s_mins_maxs,6),omins,16,1,t([col(low_c_s_mins_maxs,2)],[s],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_c_s_mins_maxs,7),omaxs,16,1,t([col(low_c_s_mins_maxs,2)],[s],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),4),secondary,col(low_c_s_mins_maxs,8),os,16,2,t([col(low_c_s_mins_maxs,2),col(low_c_s_mins_maxs,3)],[s,mins],[_14757,_14761],if(eq(_14761,1),0,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(coef(-3,3)),else(attr)]).
conjecture(id(graph,low(maxs),5),low,col(low_c_s_mins_maxs,4),maxs,16,1,t([col(low_c_s_mins_maxs,3)],[mins],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_minc_maxc_s_maxs,5),minmaxc,10,2,t([col(low_minc_maxc_s_maxs,1),col(low_minc_maxc_s_maxs,2)],[minc,maxc],[_14757,_14761],if(eq(_14757,_14761),0,_14757)),cond,[cond(attr_eq_attr),then(coef(-3,3)),else(attr)]).
conjecture(id(graph,low(maxs),1),secondary,col(low_v_c_maxc_maxs,5),s,26,1,t([col(low_v_c_maxc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_v_c_maxc_maxs,6),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_v_c_maxc_maxs,7),omins,26,1,t([col(low_v_c_maxc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),4),secondary,col(low_v_c_maxc_maxs,8),omaxs,26,1,t([col(low_v_c_maxc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),5),secondary,col(low_v_c_maxc_maxs,9),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),6),low,col(low_v_c_maxc_maxs,4),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),secondary,col(low_v_c_minc_maxs,5),s,26,1,t([col(low_v_c_minc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_v_c_minc_maxs,6),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_v_c_minc_maxs,7),minmaxc,26,3,t([col(low_v_c_minc_maxs,1),col(low_v_c_minc_maxs,2),col(low_v_c_minc_maxs,3)],[v,c,minc],[_14771,_14775,_14779],if(eq(_14771,prod(_14775,_14779)),0,_14779)),decomp,[decomp([families([cond_template([cond(6),then(1)]),else(col)]),decomp(if(cond(6),then(1),else([eq_col])))])]).
conjecture(id(graph,low(maxs),4),secondary,col(low_v_c_minc_maxs,8),rminc,26,2,t([col(low_v_c_minc_maxs,1),col(low_v_c_minc_maxs,2),col(low_v_c_minc_maxs,3)],[v,c,minc],[_14771,_14775,_14779],polynom([monome([t(_14775,1),t(_14779,1)],-1),monome([t(_14771,1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(2,2),non_zero(1,2,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(graph,low(maxs),5),secondary,col(low_v_c_minc_maxs,9),omins,26,1,t([col(low_v_c_minc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),6),secondary,col(low_v_c_minc_maxs,10),omaxs,26,1,t([col(low_v_c_minc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),7),secondary,col(low_v_c_minc_maxs,11),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),8),secondary,col(low_v_c_minc_maxs,7),minmaxc,26,2,t([col(low_v_c_minc_maxs,3),col(low_v_c_minc_maxs,8)],[minc,rminc],[_14757,_14761],if(eq(_14761,0),0,_14757)),cond,[cond(attr_eq_coef(coef(-3,3))),then(coef(-3,3)),else(attr)]).
conjecture(id(graph,low(maxs),9),low,col(low_v_c_minc_maxs,4),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),low,col(low_v_c_mins_maxs,4),maxs,14,9,t([col(low_v_c_mins_maxs,1),col(low_v_c_mins_maxs,3)],[v,mins],[_14757,_14761],if(eq(_14757 mod _14761,0),_14761,if(leq(_14757,prod(_14761,3)),minus(_14757,_14761),plus(_14761,1)))),decomp,[decomp([families([cond_template([cond(5),then(2)]),else(cond)]),decomp(if(cond(5),then(2),else([cond(attr_leq_unary([prod(2,3)])),then(binary_term([minus])),else(unary_term([plus(1,3)]))])))])]).
conjecture(id(graph,low(maxs),1),low,col(low_v_c_s_maxs,4),maxs,10,1,t([col(low_v_c_s_maxs,1),col(low_v_c_s_maxs,3)],[v,s],[_14757,_14761],polynom([monome([t(ceil(_14757,_14761),1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(graph,low(maxs),1),secondary,col(low_v_minc_maxc_maxs,5),s,26,1,t([col(low_v_minc_maxc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),2),secondary,col(low_v_minc_maxc_maxs,6),mins,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),3),secondary,col(low_v_minc_maxc_maxs,7),minmaxc,26,2,t([col(low_v_minc_maxc_maxs,2),col(low_v_minc_maxc_maxs,3)],[minc,maxc],[_14757,_14761],if(eq(_14757,_14761),0,_14757)),cond,[cond(attr_eq_attr),then(coef(-3,3)),else(attr)]).
conjecture(id(graph,low(maxs),4),secondary,col(low_v_minc_maxc_maxs,8),omins,26,1,t([col(low_v_minc_maxc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),5),secondary,col(low_v_minc_maxc_maxs,9),omaxs,26,1,t([col(low_v_minc_maxc_maxs,1)],[v],[_14743],polynom([monome([t(_14743,1)],1)])),formula,[]).
conjecture(id(graph,low(maxs),6),secondary,col(low_v_minc_maxc_maxs,10),os,26,0,t([],[],[],0),cst,[]).
conjecture(id(graph,low(maxs),7),low,col(low_v_minc_maxc_maxs,4),maxs,26,0,t([],[],[],1),cst,[]).
conjecture(id(graph,low(maxs),1),low,col(low_v_s_mins_maxs,4),maxs,15,7,t([col(low_v_s_mins_maxs,1),col(low_v_s_mins_maxs,2),col(low_v_s_mins_maxs,3)],[v,s,mins],[_14757,_14761,_14765],ceil(if(eq(_14757,_14765),_14757,minus(_14757,_14765)),plus(minus(_14761,1),bool(0,0,and,1,[eq(_14761,1)])))),decomp,[decomp([families([unary_template([binary(8),unary(0)]),slack(bool),rest(cond)]),decomp(binary_op(rceil),[unary_template(minus(_14761,1)),slack([bool([neg(0),op([and]),nb_terms(1,1),conds([t(cond(attr_eq_attr),no_negation,2),t(cond(attr_leq_attr),no_negation,2),t(cond(attr_eq_coef(coef(-5,5))),no_negation,3),t(cond(attr_leq_coef(coef(-5,5))),no_negation,3),t(cond(attr_geq_coef(coef(-5,5))),no_negation,3),t(cond(attr_in_interval(1,5)),no_restriction,3),t(cond(attr_eq_unary([prod(2,5)])),no_negation,1),t(cond(attr_leq_unary([prod(2,5)])),no_negation,1),t(cond(unary_leq_attr([prod(2,5)])),no_negation,1),t(cond(sum_leq_attr),no_negation,1),t(cond(ceil_leq_floor),no_negation,1),t(cond(unary_term_eq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_leq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(unary_term_geq_coef([2 mod 5],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([plus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([minus],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([min],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([max],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([prod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([abs],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([floor],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([ceil],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mfloor],coef(0,5))),no_negation,1),t(cond(minus_mod_eq0),no_negation,1),t(cond(attr_geq_fmod),no_negation,1),t(cond(mod_gt_mod),no_negation,1),t(cond(binary_term_eq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_eq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_leq_coef([fmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([mod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([cmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([dmod],coef(0,5))),no_negation,1),t(cond(binary_term_geq_coef([fmod],coef(0,5))),no_negation,1)]),use_mods(2)])]),rest([cond(attr_eq_attr),then(attr),else(binary_term([minus]))])])])]).

missing(low_v_mins_maxs,low,maxs).
missing(low_c_maxc_mins_maxs,low,maxs).
missing(low_maxc_s_mins_maxs,low,maxs).
missing(low_minc_maxc_s_maxs,low,maxs).
missing(low_minc_s_mins_maxs,low,maxs).
missing(low_v_maxc_mins_maxs,low,maxs).
missing(low_v_maxc_s_maxs,low,maxs).
missing(low_v_minc_mins_maxs,low,maxs).
missing(low_v_minc_s_maxs,low,maxs).
