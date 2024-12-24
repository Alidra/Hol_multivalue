require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El int) (x1: El int) ≔ (real_mul (real_of_int x0) (real_of_int x1));
symbol term1 (x0: El int) (x1: El int) ≔ (real_of_int (int_mul x0 x1));
symbol term0 (x0: El int) (x1: El int) ≔ ((λ y0 : El int, (= (real_of_int (int_mul x0 y0)) (real_mul (real_of_int x0) (real_of_int y0)))) x1);
