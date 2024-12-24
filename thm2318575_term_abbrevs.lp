require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) (x1: El int) ≔ ((λ y0 : El int, (= (= x0 y0) (= (real_of_int x0) (real_of_int y0)))) x1);
