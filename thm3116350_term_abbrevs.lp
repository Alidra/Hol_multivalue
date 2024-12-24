require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) ≔ ((λ y0 : El num, (= (= x0 y0) (∧ (num_divides x0 y0) (num_divides y0 x0)))) x1);
symbol term1 (x0: El num) (x1: El num) ≔ (∧ (num_divides x1 x0) (num_divides x0 x1));
