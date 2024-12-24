require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El int) (x1: El int) (x2: El int) ≔ (∧ (int_divides x1 x0) (int_divides x1 x2));
symbol term0 (x0: El int) (x1: El int) (x2: El int) ≔ ((λ y0 : El int, (= (int_divides x1 (int_gcd ((@̦‚ int int) x0 y0))) (∧ (int_divides x1 x0) (int_divides x1 y0)))) x2);
symbol term1 (x0: El int) (x1: El int) (x2: El int) ≔ (int_divides x0 (int_gcd ((@̦‚ int int) x1 x2)));
