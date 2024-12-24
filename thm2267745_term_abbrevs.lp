require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El int) ≔ (int_of_real (real_of_int x0));
symbol term0 (x0: El int) ≔ ((λ y0 : El int, (= (int_of_real (real_of_int y0)) y0)) x0);
