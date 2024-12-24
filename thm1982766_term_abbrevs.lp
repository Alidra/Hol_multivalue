require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El real) (x2: El real) (x3: El real) (x4: El num) ≔ (∧ (= (real_mul (real_pow x3 x4) x3) (real_pow x3 (SUC x4))) (∧ (= (real_mul x3 x3) (real_pow x3 (NUMERAL (BIT0 (BIT1 _0))))) (∧ (= (real_pow (real_mul x3 x1) x4) (real_mul (real_pow x3 x4) (real_pow x1 x4))) (∧ (= (real_pow (real_pow x3 x0) x4) (real_pow x3 (* x0 x4))) (∧ (= (real_pow x3 (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0)))) (∧ (= (real_pow x3 (NUMERAL (BIT1 _0))) x3) (∧ (= (real_mul x3 (real_add x1 x2)) (real_add (real_mul x3 x1) (real_mul x3 x2))) (= (real_pow x3 (SUC x4)) (real_mul x3 (real_pow x3 x4))))))))));
