require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) (x1: El real) ≔ (real_gt (real_sub x0 x1) (real_of_num (NUMERAL _0)));
