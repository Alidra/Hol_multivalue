require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) (x2: El num) ≔ ((λ y0 : El num, (= ((@== num) x0 x1 (num_mod y0)) ((@== int) (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0))))) x2);
symbol term1 (x0: El num) (x1: El num) (x2: El num) ≔ ((@== num) x0 x1 (num_mod x2));
symbol term2 (x0: El num) (x1: El num) (x2: El num) ≔ ((@== int) (int_of_num x0) (int_of_num x1) (int_mod (int_of_num x2)));
