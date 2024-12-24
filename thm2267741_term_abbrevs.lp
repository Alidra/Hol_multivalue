require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El real) ≔ (real_of_int (int_of_real x0));
symbol term0 (x0: El real) ≔ ((λ y0 : El real, (= (integer y0) (= (real_of_int (int_of_real y0)) y0))) x0);
