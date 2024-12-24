require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) ≔ ((λ y0 : El real, (= (real_mul (real_of_num (NUMERAL (BIT1 _0))) y0) y0)) x0);
symbol term1 (x0: El real) ≔ (real_mul (real_of_num (NUMERAL (BIT1 _0))) x0);
