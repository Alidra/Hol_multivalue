require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El real) (x1: El real) (x2: El real) (x3: El real) ≔ (real_mul x0 (real_mul x1 (real_mul x2 x3)));
symbol term0 (x0: El real) (x1: El real) (x2: El real) (x3: El real) ≔ (real_mul (real_mul x0 x1) (real_mul x2 x3));
