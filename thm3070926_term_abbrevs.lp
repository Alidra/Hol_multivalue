require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) ≔ ((λ y0 : El int, (= (int_abs (int_abs y0)) (int_abs y0))) x0);
symbol term1 (x0: El int) ≔ (int_abs (int_abs x0));
