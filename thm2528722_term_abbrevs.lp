require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) (x1: El int) (x2: El int) ≔ ((λ y0 : El int, (= (= (rem x0 y0) (rem x1 y0)) ((@== int) x0 x1 (int_mod y0)))) x2);
symbol term1 (x0: El int) (x1: El int) (x2: El int) ≔ ((@== int) x0 x1 (int_mod x2));
