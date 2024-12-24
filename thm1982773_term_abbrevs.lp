require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) (x1: El real) (x2: El num) ≔ (real_pow (real_mul x0 x1) x2);
symbol term1 (x0: El real) (x1: El real) (x2: El num) ≔ (real_mul (real_pow x0 x2) (real_pow x1 x2));
