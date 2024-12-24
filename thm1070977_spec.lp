require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1070977 [A] (a : El (list A)) : Prf (= ((@_mk_list A) ((@_dest_list A) a)) a);
