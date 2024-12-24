require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) (x1: El real) (x2: El real) (x3: El num) ≔ (∧ (= (real_pow x2 (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0)))) (∧ (= (real_pow x2 (NUMERAL (BIT1 _0))) x2) (∧ (= (real_mul x2 (real_add x0 x1)) (real_add (real_mul x2 x0) (real_mul x2 x1))) (= (real_pow x2 (SUC x3)) (real_mul x2 (real_pow x2 x3))))));
