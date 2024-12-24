require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) (x1: El real) ≔ (real_add (real_mul x0 x1) x1);
symbol term1 (x0: El real) (x1: El real) ≔ (real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 _0)))) x1);
