require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El bool) (x1: El int) (x2: El int) ≔ (real_of_int ((@COND int) x0 x1 x2));
symbol term1 (x0: El bool) (x1: El int) (x2: El int) ≔ ((@COND real) x0 (real_of_int x1) (real_of_int x2));
