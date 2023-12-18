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

conjecture(id(partition0,up(min),1),secondary,col(up_n_m_min,4),nval,20,1,t([col(up_n_m_min,2)],[m],[_14769],polynom([monome([t(_14769,1)],1)])),formula,[]).
conjecture(id(partition0,up(min),2),secondary,col(up_n_m_min,5),rmin,20,1,t([col(up_n_m_min,1),col(up_n_m_min,2)],[n,m],[_14783,_14787],polynom([monome([t(_14783 mod _14787,1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition0,up(min),3),up,col(up_n_m_min,3),min,20,1,t([col(up_n_m_min,1),col(up_n_m_min,2)],[n,m],[_14783,_14787],polynom([monome([t(floor(_14783,_14787),1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([1]),binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),main_formula([1-t([degree(1,1),non_zero(1,1,1,1),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition0,up(min),1),up,col(up_n_m_max_min,4),min,9,2,t([col(up_n_m_max_min,3),col(up_n_m_max_min,5)],[max,range],[_14801,_14805],polynom([monome([t(_14805,1)],-1),monome([t(_14801,1)],1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition0,up(min),1),secondary,col(up_n_m_nval_min,5),rmin,10,3,t([col(up_n_m_nval_min,1),col(up_n_m_nval_min,2),col(up_n_m_nval_min,3)],[n,m,nval],[_14815,_14819,_14823],if(eq(_14819,_14823),_14815 mod _14819,_14815)),cond,[cond(attr_eq_attr),then(binary_term([mod])),else(attr)]).
conjecture(id(partition0,up(min),2),up,col(up_n_m_nval_min,4),min,10,3,t([col(up_n_m_nval_min,1),col(up_n_m_nval_min,2),col(up_n_m_nval_min,3)],[n,m,nval],[_14815,_14819,_14823],if(eq(_14819,_14823),floor(_14815,_14819),0)),cond,[cond(attr_eq_attr),then(binary_term([floor])),else(coef(-3,3))]).
conjecture(id(partition0,up(min),3),up,col(up_n_m_nval_min,4),min,10,3,t([col(up_n_m_nval_min,1),col(up_n_m_nval_min,2),col(up_n_m_nval_min,5)],[n,m,rmin],[_14815,_14819,_14823],if(eq(_14815,_14823),0,floor(_14815,_14819))),cond,[cond(attr_eq_attr),then(coef(-3,3)),else(binary_term([floor]))]).
conjecture(id(partition0,up(min),1),secondary,col(up_n_m_range_min,5),max,9,4,t([col(up_n_m_range_min,1),col(up_n_m_range_min,2),col(up_n_m_range_min,3)],[n,m,range],[_14815,_14819,_14823],floor(polynom([monome([t(_14819,1),t(_14823,1)],1),monome([t(_14823,1)],-1),monome([t(_14815,1)],1)]),polynom([monome([t(_14819,1)],1)]))),formula,[nb_polynom([2]),nb_unary([0]),nb_binary([0]),non_zero_coeffs_in_all_polynomials(4,6),binary_function([min,max,floor,ceil,prod,mod,cmod,dmod]),main_formula([3-t([degree(1,2),non_zero(1,2,0,4),coef(-2,2),cst(-1,1)],[degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition0,up(min),2),up,col(up_n_m_range_min,4),min,9,3,t([col(up_n_m_range_min,1),col(up_n_m_range_min,2),col(up_n_m_range_min,3)],[n,m,range],[_14815,_14819,_14823],floor(polynom([monome([t(_14823,1)],-1),monome([t(_14815,1)],1)]),polynom([monome([t(_14819,1)],1)]))),formula,[nb_polynom([2]),nb_unary([0]),nb_binary([0]),non_zero_coeffs_in_all_polynomials(4,6),binary_function([min,max,floor,prod,mod,cmod,dmod]),main_formula([3-t([degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)],[degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition0,up(min),3),up,col(up_n_m_range_min,4),min,9,2,t([col(up_n_m_range_min,3),col(up_n_m_range_min,5)],[range,max],[_14801,_14805],polynom([monome([t(_14805,1)],1),monome([t(_14801,1)],-1)])),formula,[nb_polynom([1]),nb_unary([0]),nb_binary([0]),main_formula([1-t([degree(1,1),non_zero(1,1,2,2),coef(-2,2),cst(-1,1)])])]).
conjecture(id(partition0,up(min),1),up,col(up_n_m_sum_squares_min,4),min,13,3,t([col(up_n_m_sum_squares_min,1),col(up_n_m_sum_squares_min,2),col(up_n_m_sum_squares_min,5)],[n,m,rmin],[_14801,_14805,_14809],floor(polynom([monome([t(_14809,1)],-1),monome([t(_14801,1)],1)]),polynom([monome([t(_14805,1)],1)]))),formula,[nb_polynom([2]),nb_unary([0]),nb_binary([0]),non_zero_coeffs_in_all_polynomials(4,6),binary_function([min,max,floor,prod,mod,cmod,dmod]),main_formula([3-t([degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)],[degree(1,1),non_zero(1,1,0,4),coef(-2,2),cst(-1,1)])])]).

missing(up_n_m_min,up,min).
missing(up_n_m_max_min,col,range).
missing(up_n_m_max_min,col,rmin).
missing(up_n_m_max_min,up,min).
missing(up_n_m_range_min,col,rmin).
missing(up_n_m_sum_squares_min,col,rmin).
missing(up_n_m_sum_squares_min,up,min).
