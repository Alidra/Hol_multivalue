require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El int) ≔ (real_of_int (int_abs x0));
symbol term0 (x0: El int) ≔ ((λ y0 : El int, (= (real_abs (real_of_int y0)) (real_of_int (int_abs y0)))) x0);
symbol term1 (x0: El int) ≔ (real_abs (real_of_int x0));
