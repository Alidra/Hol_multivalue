require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (prod a0 a1)) ≔ ((@ABS_prod a0 a1) ((@REP_prod a0 a1) x0));
