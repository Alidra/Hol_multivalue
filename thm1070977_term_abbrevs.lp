require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (list a0)) ≔ ((@_mk_list a0) ((@_dest_list a0) x0));
