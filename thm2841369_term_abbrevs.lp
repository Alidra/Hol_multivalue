require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El num) (x1: El num) ≔ (int_min (int_of_num x0) (int_of_num x1));
symbol term1 (x0: El num) (x1: El num) ≔ (int_of_num (MIN x0 x1));
symbol term0 (x0: El num) (x1: El num) ≔ ((λ y0 : El num, (= (int_of_num (MIN x0 y0)) (int_min (int_of_num x0) (int_of_num y0)))) x1);
