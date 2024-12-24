require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem44425 [A B] (a : El (prod A B)) : Prf (= ((@ABS_prod A B) ((@REP_prod A B) a)) a);
