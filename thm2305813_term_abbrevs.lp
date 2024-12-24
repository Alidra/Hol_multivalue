require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) (x1: El real) (x2: El real) ≔ (∧ (= (real_mul (real_mul x1 x0) x2) (real_mul x1 (real_mul x0 x2))) (= (real_mul x1 (real_mul x0 x2)) (real_mul x0 (real_mul x1 x2))));
